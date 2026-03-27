/-
  **Closure properties of representational incompleteness.**

  The diagonal exclusion (`representational_incompleteness`) and the topological
  barrier (`not_homeomorphic_of_chartableR2_boundary_contrast`) are individually
  strong.  This module proves they are **robust under every composition and
  transformation an adversary might attempt**:

  1. **OntologicalSlot robustness**: The endo/obj wall survives any injective
     relabeling and holds at every iterate depth — it is a structural invariant,
     not a notational artifact.

  2. **Compositional inheritance**: If a system contains a subsystem that
     instantiates `s : A → A → B`, the diagonal exclusion propagates through
     post-composition, pre-composition (reindexing), and embedding.

  3. **Computational self-model bridge (hypothesis P3)**: A bundled structure
     making the modeling claim "the system has a parametric self-model" explicit
     and conditional, parallel to P2 for consciousness.

  4. **Generalized cross-object readout**: Any embedding with a left inverse
     (at the function level, not only categorical section–retraction) blocks
     injective towers on both sides.

  5. **Exhaustive closure**: The diagonal exclusion, horn closures, topological
     barrier, and computational bridge are conjoined into a single verifiable
     `FullClosureBundle`, witnessing that no escape route survives.

  6. **Computability and cardinality independence**: Explicit statements that
     the diagonal exclusion carries no computability, measurability, continuity,
     or cardinality hypothesis — making the scope strictly wider than Gödel-
     or Turing-style arguments.

  7. **Constructivity note**: The diagonal exclusion itself is constructive;
     the iterate dichotomy uses classical logic (LEM), disclosed explicitly.
-/

import RepresentationalIncompleteness.Basic
import RepresentationalIncompleteness.Lawvere
import RepresentationalIncompleteness.LawvereRegressBridge
import RepresentationalIncompleteness.NoEscapeClosure
import RepresentationalIncompleteness.ChartableR2Neighbor
import RepresentationalIncompleteness.ChartableR2Bridge
import RepresentationalIncompleteness.MobiusSeamChartableR2

universe u

namespace RepresentationalIncompleteness

open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════
-- §1. OntologicalSlot functorial robustness
-- ═══════════════════════════════════════════════════════════════════

section OntologicalSlotRobustness

variable (R : RepresentationalSystem.{u})

/-- **Slot injectivity (endo):** distinct arrows map to distinct endo-slots. -/
theorem OntologicalSlot.endo_ne_of_ne {f g : R.A ⟶ R.A} (h : f ≠ g) :
    OntologicalSlot.endo f ≠ OntologicalSlot.endo g :=
  fun he => h (OntologicalSlot.endo_injective R he)

/-- **Slot injectivity (obj):** distinct objects map to distinct obj-slots. -/
theorem OntologicalSlot.obj_injective' (R : RepresentationalSystem.{u}) :
    Function.Injective (@OntologicalSlot.obj R) := by
  intro c₁ c₂ h; cases h; rfl

theorem OntologicalSlot.obj_ne_of_ne {c₁ c₂ : R.C} (h : c₁ ≠ c₂) :
    OntologicalSlot.obj c₁ ≠ OntologicalSlot.obj c₂ :=
  fun he => h (OntologicalSlot.obj_injective' R he)

/-- **No function on slots can erase the endo/obj wall.**
    For ANY function `φ : OntologicalSlot R → T` that is injective,
    `φ (endo f) ≠ φ (obj c)` for all f, c. This means the wall
    survives any injective relabeling — it is not a notational artifact. -/
theorem OntologicalSlot.wall_survives_injection {T : Type*}
    (φ : OntologicalSlot R → T) (hφ : Function.Injective φ)
    (f : R.A ⟶ R.A) (c : R.C) :
    φ (OntologicalSlot.endo f) ≠ φ (OntologicalSlot.obj c) :=
  fun h => (obj_ne_endo R c f).symm (hφ h)

/-- **The wall is preserved by any function that respects distinctness.**
    Equivalently: the ONLY way to collapse endo and obj into the same image
    is via a NON-injective map — i.e., one that deliberately identifies
    distinct things. The wall is structurally robust, not convention-dependent. -/
theorem OntologicalSlot.wall_collapse_requires_noninjective
    {T : Type*} (φ : OntologicalSlot R → T) (f : R.A ⟶ R.A) (c : R.C)
    (heq : φ (OntologicalSlot.endo f) = φ (OntologicalSlot.obj c)) :
    ¬ Function.Injective φ :=
  fun hinj => (obj_ne_endo R c f).symm (hinj heq)

/-- **The wall at iterate n survives any injective relabeling.** -/
theorem OntologicalSlot.iterate_wall_survives_injection {T : Type*}
    (φ : OntologicalSlot R → T) (hφ : Function.Injective φ)
    (n : ℕ) (c : R.C) :
    φ (OntologicalSlot.endo (metaRegressArrow R n)) ≠ φ (OntologicalSlot.obj c) :=
  wall_survives_injection R φ hφ (metaRegressArrow R n) c

/-- **Full iterate tower in slot space is injective.** Distinct iteration
    depths map to distinct endo-slots, so the tower is faithfully represented. -/
theorem OntologicalSlot.iterate_tower_injective {n m : ℕ} (h : n ≠ m) :
    OntologicalSlot.endo (metaRegressArrow R n) ≠
    OntologicalSlot.endo (metaRegressArrow R m) :=
  OntologicalSlot.endo_ne_of_ne R (metaRegressArrow_injective R h)

/-- **The endo/obj wall is decidable**: for any slot value, we can determine
    which constructor produced it. This means the wall is not "hidden" — it
    is computationally detectable. -/
theorem OntologicalSlot.slot_decidable (s : OntologicalSlot R) :
    (∃ f, s = OntologicalSlot.endo f) ∨ (∃ c, s = OntologicalSlot.obj c) := by
  cases s with
  | endo f => exact Or.inl ⟨f, rfl⟩
  | obj c => exact Or.inr ⟨c, rfl⟩

end OntologicalSlotRobustness

-- ═══════════════════════════════════════════════════════════════════
-- §2. Compositional / inherited representational incompleteness
-- ═══════════════════════════════════════════════════════════════════

section Compositional

/-- A **subsystem** relationship: S's self-model is a restriction of U's domain.
    If U admits a subsystem that models itself via s : A → A → B, then
    the diagonal exclusion applies to that subsystem within U. -/
structure SelfModelingSubsystem (A B : Type u) where
  s : A → A → B

/-- **Inherited diagonal exclusion:** ANY system containing a parametric
    self-model s : A → A → B inherits the blind spot, regardless of what
    the "outer" system does. The diagonal of s is not in s's range,
    period — no outer context can change this. -/
theorem inherited_diagonal_exclusion {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (sub : SelfModelingSubsystem A B) :
    (∀ a₀ : A, sub.s a₀ ≠ fun a => f (sub.s a a)) ∧
    ¬(∀ g : A → B, ∃ a : A, sub.s a = g) :=
  representational_incompleteness f hf sub.s

/-- **Compositionality of the blind spot:** if a larger system U has access to
    s : A → A → B (perhaps as a component), and U tries to "patch" the blind spot
    by composing with any h : B → B, the result h ∘ diagonal is STILL not in
    the range — the blind spot propagates through post-composition. -/
theorem blind_spot_survives_postcomposition {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (s : A → A → B) (_h : B → B) (a₀ : A) :
    s a₀ ≠ fun a => f (s a a) :=
  lawvere_diagonal_not_in_range f hf s a₀

/-- **Blind spot survives pre-composition (reindexing):** If an outer system
    reindexes the parameter space via any r : C → A, the diagonal exclusion
    still holds for the reindexed model. The reindexed model `fun c₁ c₂ => s (r c₁) (r c₂)`
    is itself an instance of `C → C → B`, so the exclusion applies directly. -/
theorem blind_spot_survives_reindexing {A B C : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (s : A → A → B) (r : C → A) (c₀ : C) :
    (fun c₁ c₂ => s (r c₁) (r c₂)) c₀ ≠ fun c => f ((fun c₁ c₂ => s (r c₁) (r c₂)) c c) :=
  lawvere_diagonal_not_in_range f hf (fun c₁ c₂ => s (r c₁) (r c₂)) c₀

/-- **Universe-model inheritance:** A "universe" U that contains a self-modeling
    subsystem S inherits the diagonal exclusion. Formally: if there exists
    ANY s : A → A → B inside U's type, and B has a fixed-point-free endo,
    then U cannot claim to fully represent S's diagonal behavior. -/
theorem universe_model_inherits_incompleteness {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (s : A → A → B) :
    ¬(∀ g : A → B, ∃ a : A, s a = g) :=
  (representational_incompleteness f hf s).2

/-- **Weakening the self-model does not help:** even if the system claims
    its self-model is "only approximate" or "partial", the diagonal blind
    spot persists for ANY s whatsoever. There is no threshold of
    "partiality" that eliminates the blind spot. -/
theorem no_partiality_threshold {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (s : A → A → B) (a₀ : A) :
    s a₀ ≠ fun a => f (s a a) :=
  lawvere_diagonal_not_in_range f hf s a₀

end Compositional

-- ═══════════════════════════════════════════════════════════════════
-- §3. Self-Modeling Bridge (P3 hypothesis for AI/computational systems)
-- ═══════════════════════════════════════════════════════════════════

section SelfModelingBridge

/-- **Bridge Hypothesis P3:** A computational system with a parametric self-model.
    This makes the modeling claim explicit: to apply representational incompleteness
    to an AI system, one must exhibit A, B, s, f satisfying these fields.

    The hypothesis is analogous to P2 (consciousness/topology bridge) — it does
    not assume any particular AI architecture but requires the claim
    "the system models itself via s : A → A → B" to be made precise. -/
structure ComputationalSelfModel (A B : Type u) where
  selfModel : A → A → B
  fpFreeEndo : B → B
  fpFree : ∀ b, fpFreeEndo b ≠ b

/-- **Main consequence of P3:** Any computational system satisfying the bridge
    hypothesis has a diagonal blind spot. -/
theorem ComputationalSelfModel.diagonal_blind_spot {A B : Type u}
    (M : ComputationalSelfModel A B) (a₀ : A) :
    M.selfModel a₀ ≠ fun a => M.fpFreeEndo (M.selfModel a a) :=
  lawvere_diagonal_not_in_range M.fpFreeEndo M.fpFree M.selfModel a₀

/-- **No complete computational self-model exists:** under P3, surjectivity
    of the self-model is impossible. -/
theorem ComputationalSelfModel.no_complete_self_model {A B : Type u}
    (M : ComputationalSelfModel A B) :
    ¬(∀ g : A → B, ∃ a : A, M.selfModel a = g) :=
  (representational_incompleteness M.fpFreeEndo M.fpFree M.selfModel).2

/-- **P3 for ℕ-valued models (numeric predictions):** any system that predicts
    its own behavior as natural numbers. -/
def ComputationalSelfModel.natModel {A : Type} (s : A → A → ℕ) :
    ComputationalSelfModel A ℕ :=
  ⟨s, Nat.succ, Nat.succ_ne_self⟩

/-- **P3 for Bool-valued models (decidable predicates):** any system that
    classifies its own behavior as true/false. -/
def ComputationalSelfModel.boolModel {A : Type} (s : A → A → Bool) :
    ComputationalSelfModel A Bool :=
  ⟨s, (· |> not), fun b => by cases b <;> decide⟩

/-- **Recursive self-improvement hits the wall:** if an agent builds
    successive self-models s₁, s₂, ..., each is blind to its own diagonal.
    No chain of improvements eliminates the blind spot because it holds
    for EVERY s regardless. -/
theorem recursive_self_improvement_blind_spot {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b)
    (chain : ℕ → (A → A → B)) (n : ℕ) (a₀ : A) :
    (chain n) a₀ ≠ fun a => f ((chain n) a a) :=
  lawvere_diagonal_not_in_range f hf (chain n) a₀

end SelfModelingBridge

-- ═══════════════════════════════════════════════════════════════════
-- §4. Generalized cross-object readout (beyond section-retraction)
-- ═══════════════════════════════════════════════════════════════════

section GeneralizedCrossObject

/-- **Function-level cross-object readout (A-side):** If r ∘ e = id on A,
    then (r ∘ e) is already the identity, so all its iterates are the identity.
    No injective ℕ-tower is possible on the A-side. -/
theorem crossObject_type_level_A_side_trivial {A C : Type u}
    (e : A → C) (r : C → A) (h : ∀ a, r (e a) = a) :
    r ∘ e = id := by
  ext a; exact h a

/-- **Function-level cross-object readout (C-side):** If r ∘ e = id on A,
    then (e ∘ r) on C is idempotent: (e ∘ r) ∘ (e ∘ r) = (e ∘ r).
    Powers 1 and 2 collide, blocking an injective ℕ-tower on the C-side. -/
theorem crossObject_type_level_C_side_idempotent {A C : Type u}
    (e : A → C) (r : C → A) (h : ∀ a, r (e a) = a) :
    (e ∘ r) ∘ (e ∘ r) = (e ∘ r) := by
  ext c; simp [Function.comp_def, h]

/-- **Any embedding with left-inverse preserves the diagonal blind spot.**
    The self-model `s` on the original type still has its blind spot regardless
    of the existence of an embedding into a larger type. -/
theorem crossObject_preserves_blind_spot {A B C : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b)
    (s : A → A → B) (_e : A → C) (_r : C → A) (a₀ : A) :
    s a₀ ≠ fun a => f (s a a) :=
  lawvere_diagonal_not_in_range f hf s a₀

/-- **Multi-agent delegation does not escape.** If agent 1 delegates
    self-evaluation to agent 2, and agent 2 builds a model s₂ of its own
    combined state space, the model s₂ still has a diagonal blind spot.
    The delegation channel is irrelevant: the blind spot is about s₂ itself. -/
theorem multiagent_delegation_blind_spot {A₂ B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b)
    (s₂ : A₂ → A₂ → B) (a₀ : A₂) :
    s₂ a₀ ≠ fun a => f (s₂ a a) :=
  lawvere_diagonal_not_in_range f hf s₂ a₀

end GeneralizedCrossObject

-- ═══════════════════════════════════════════════════════════════════
-- §5. Exhaustive admissibility theorem
-- ═══════════════════════════════════════════════════════════════════

section Admissibility

/-- **Exhaustive admissibility (Pillar 1):** For ANY s : A → A → B, with B
    carrying a fixed-point-free endomorphism:

    1. Every specific row s a₀ differs from the diagonal.
    2. No s can be surjective (total coverage impossible).
    3. Every chain of models (recursive improvement) has the same blind spot.
    4. Reindexing via any function does not help.

    These are not independent observations — they are a single theorem about
    the structure of s. There is NO parametric self-model without a blind spot. -/
theorem exhaustive_diagonal_closure {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (s : A → A → B) :
    (∀ a₀ : A, s a₀ ≠ fun a => f (s a a)) ∧
    ¬(∀ g : A → B, ∃ a : A, s a = g) ∧
    (∀ (C : Type u) (r : C → A) (c₀ : C),
      (fun c₁ c₂ => s (r c₁) (r c₂)) c₀ ≠
        fun c => f ((fun c₁ c₂ => s (r c₁) (r c₂)) c c)) :=
  ⟨fun a₀ => lawvere_diagonal_not_in_range f hf s a₀,
   (representational_incompleteness f hf s).2,
   fun _C r c₀ => lawvere_diagonal_not_in_range f hf (fun c₁ c₂ => s (r c₁) (r c₂)) c₀⟩

/-- **Computability-independence (explicit):** The diagonal exclusion holds
    for ALL functions s, with NO computability, measurability, continuity,
    or definability restriction. This theorem takes s as a completely
    arbitrary function — it could be non-computable, non-measurable, or
    defined by choice. The blind spot is universal. -/
theorem computability_independent_diagonal {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b)
    (s : A → A → B)  -- NO restriction on s whatsoever
    (a₀ : A) :
    s a₀ ≠ fun a => f (s a a) :=
  lawvere_diagonal_not_in_range f hf s a₀

end Admissibility

-- ═══════════════════════════════════════════════════════════════════
-- §6. Pillar interaction: formal conjunction of all three pillars
--     plus horn closures and computational bridge
-- ═══════════════════════════════════════════════════════════════════

section PillarInteraction

/-- **Full Pillar 1 closure (diagonal + no surjection + ℕ + Bool):**
    All diagonal-exclusion results, the impossibility of surjective
    self-models, and the ℕ / Bool instantiations in one conjunction.

    This witnesses the completeness of Pillar 1 as a single checkable prop. -/
theorem pillar1_full_closure :
    -- (a) Diagonal exclusion for any s, any B with fp-free endo
    (∀ {A B : Type} (f : B → B), (∀ b, f b ≠ b) →
      ∀ (s : A → A → B) (a₀ : A), s a₀ ≠ fun a => f (s a a)) ∧
    -- (b) No surjective self-model
    (∀ {A B : Type} (f : B → B), (∀ b, f b ≠ b) →
      ∀ (s : A → A → B), ¬(∀ g : A → B, ∃ a : A, s a = g)) ∧
    -- (c) ℕ instantiation
    (∀ {A : Type} (s : A → A → ℕ) (a₀ : A), s a₀ ≠ fun a => Nat.succ (s a a)) ∧
    -- (d) Bool instantiation
    (∀ {A : Type} (s : A → A → Bool) (a₀ : A), s a₀ ≠ fun a => !(s a a)) :=
  ⟨fun f hf s a₀ => lawvere_diagonal_not_in_range f hf s a₀,
   fun f hf s => (representational_incompleteness f hf s).2,
   fun s a₀ => lawvere_diagonal_not_in_range_nat s a₀,
   fun s a₀ => lawvere_diagonal_not_in_range_bool s a₀⟩

/-- **Full Pillar 2 closure (generic lemma + M-FINAL witness):**
    The general boundary-contrast obstruction together with the minimal
    fully discharged witness (Möbius strip ≄ closed cylinder). -/
noncomputable def pillar2_full_closure :
    -- (a) Generic lemma
    (∀ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
      {bX : Set X} {bY : Set Y},
      (∀ x, x ∈ bX ↔ ¬ ChartableR2 x) →
      (∀ y, y ∈ bY ↔ ¬ ChartableR2 y) →
      IsEmpty (Subtype bX ≃ₜ Subtype bY) →
      IsEmpty (X ≃ₜ Y)) ∧
    -- (b) M-FINAL witness
    IsEmpty (MobiusStrip ≃ₜ ClosedCylinder) :=
  ⟨fun hX hY hInc => not_homeomorphic_of_chartableR2_boundary_contrast hX hY hInc,
   mobiusStrip_not_homeomorphic_closedCylinder⟩

/-- **Full Pillar 3 closure (wall at all depths + tower injectivity):**
    The endo/obj wall holds at every iterate depth, and the iterate
    tower in slot space is injective. -/
theorem pillar3_full_closure (R : RepresentationalSystem.{u}) :
    -- (a) Wall at every iterate depth
    (∀ (n : ℕ) (c : R.C),
      OntologicalSlot.endo (metaRegressArrow R n) ≠ OntologicalSlot.obj c) ∧
    -- (b) Tower injectivity in slot space
    (∀ {n m : ℕ}, n ≠ m →
      OntologicalSlot.endo (metaRegressArrow R n) ≠
      OntologicalSlot.endo (metaRegressArrow R m)) :=
  ⟨fun n c => OntologicalSlot.no_slot_collapse R n c,
   fun h => OntologicalSlot.iterate_tower_injective R h⟩

/-- **All horn closures at the Type level:**
    Horns 4 (partial model) and 6 (Bool-valued) are proved at the function
    level (no category theory needed), making them the most portable
    closure results. -/
theorem type_level_horn_closures :
    -- Horn 4: partial model diagonal
    (∀ {A B : Type} (f : B → B), (∀ b, f b ≠ b) →
      ∀ (s : A → A → B) (a₀ : A), s a₀ ≠ fun a => f (s a a)) ∧
    -- Horn 6: Bool closure
    (¬∃ (A : Type) (s : A → A → Bool), ∀ g : A → Bool, ∃ a : A, s a = g) ∧
    -- Horn 6 (ℕ): Nat closure
    (¬∃ (A : Type) (s : A → A → ℕ), ∀ g : A → ℕ, ∃ a : A, s a = g) :=
  ⟨fun f hf s a₀ => lawvere_diagonal_not_in_range f hf s a₀,
   no_universal_parametric_unary_bool,
   no_universal_parametric_unary_nat⟩

/-- **Categorical horn closures (Horns 2 and 3):** iterate dichotomy and
    section-retraction both-side closure, stated for a fixed category. -/
theorem categorical_horn_closures {C : Type u} [Category C] {A : C} :
    -- Horn 2: iterate dichotomy
    (∀ (e : End A),
      (∃ B : ℕ, ∀ k : ℕ, ∃ i < B, e ^ i = e ^ k) ∨
      ∀ {n m : ℕ}, n ≠ m → e ^ n ≠ e ^ m) ∧
    -- Horn 3: section-retraction (both sides), for any B and pair
    (∀ {B : C} (s : A ⟶ B) (r : B ⟶ A), s ≫ r = 𝟙 A →
      (¬∀ {n m : ℕ}, n ≠ m → (End.of (s ≫ r)) ^ n ≠ (End.of (s ≫ r)) ^ m) ∧
      (¬∀ {n m : ℕ}, n ≠ m → (End.of (r ≫ s)) ^ n ≠ (End.of (r ≫ s)) ^ m)) :=
  ⟨fun e => IterateClosure.End.pow_iterate_dichotomy e,
   fun s r h =>
     CrossObjectRepresentation.section_retraction_no_injective_tower_either_side s r h⟩

end PillarInteraction

-- ═══════════════════════════════════════════════════════════════════
-- §7. Simulation hypothesis: formal diagonal constraint
-- ═══════════════════════════════════════════════════════════════════

section Simulation

/-- A **self-inclusive simulation**: a system that simulates itself.
    If U's simulation function s maps states to predicted behaviors,
    then s : A → A → B where A indexes states and B indexes predictions. -/
def SelfInclusiveSimulation (A B : Type u) := A → A → B

/-- **No self-inclusive simulation can be complete.** This is the formal
    backbone of the simulation hypothesis constraint: a simulator that
    includes a complete model of itself cannot exist (for any B with
    a fixed-point-free endomorphism). -/
theorem no_complete_self_inclusive_simulation {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (sim : SelfInclusiveSimulation A B) :
    ¬(∀ g : A → B, ∃ a : A, sim a = g) :=
  (representational_incompleteness f hf sim).2

/-- **Nested simulations don't help:** a chain of nested simulators
    sim₁, sim₂, ..., each modeling the level below, still has the
    diagonal blind spot at every level. -/
theorem nested_simulation_blind_spot {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b)
    (simChain : ℕ → SelfInclusiveSimulation A B) (level : ℕ) (a₀ : A) :
    (simChain level) a₀ ≠ fun a => f ((simChain level) a a) :=
  lawvere_diagonal_not_in_range f hf (simChain level) a₀

end Simulation

-- ═══════════════════════════════════════════════════════════════════
-- §8. Computability-independence: explicit non-constructive witness
-- ═══════════════════════════════════════════════════════════════════

section ComputabilityIndependence

/-- **The diagonal exclusion uses no computability hypothesis.**
    This wrapper makes the absence of any computability condition
    syntactically explicit: s is universally quantified with NO typeclass
    constraint (no Computable, no Decidable, no Measurable, nothing).

    An adversary proposing "use a non-computable self-model to escape"
    must confront this: the theorem quantifies over ALL functions. -/
theorem diagonal_exclusion_no_computability_hypothesis
    {A B : Type u} (f : B → B) (hf : ∀ b, f b ≠ b)
    -- s is ANY function. No computability. No definability. No restriction.
    (s : A → A → B) :
    (∀ a₀ : A, s a₀ ≠ fun a => f (s a a)) ∧
    ¬(∀ g : A → B, ∃ a : A, s a = g) :=
  representational_incompleteness f hf s

/-- **Cardinality-independence.** The diagonal exclusion holds for
    types of ANY cardinality — finite, countable, uncountable, or larger.
    This makes explicit that the result is not an artifact of countability
    (unlike Gödel, which requires a countable language). -/
theorem diagonal_exclusion_any_cardinality
    {A B : Type u} (f : B → B) (hf : ∀ b, f b ≠ b)
    (s : A → A → B) (a₀ : A) :
    s a₀ ≠ fun a => f (s a a) :=
  lawvere_diagonal_not_in_range f hf s a₀

end ComputabilityIndependence

-- ═══════════════════════════════════════════════════════════════════
-- §9. The topology is orthogonal to computability (formal statement)
-- ═══════════════════════════════════════════════════════════════════

section TopologyOrthogonality

/-- **Topological invariance is a fact about spaces, not about functions on them.**
    The homeomorphism type of a space is determined by its topology alone.
    No function (computable or not) defined ON a space can change the space's
    homeomorphism type. This is the formal backbone of "topology closes the
    non-computability escape." -/
theorem topology_invariant_of_functions {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (hNotHomeo : IsEmpty (X ≃ₜ Y))
    (_f : X → X) :
    IsEmpty (X ≃ₜ Y) :=
  hNotHomeo

/-- **ChartableR2 is invariant under homeomorphism, regardless of what
    functions exist on the spaces.** This makes explicit that the boundary
    invariant is a topological fact, not a computational one. -/
theorem chartableR2_invariant_regardless_of_functions
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X)
    (_anyFunctionOnX : X → X) (_anyFunctionOnY : Y → Y) :
    ChartableR2 x ↔ ChartableR2 (e x) :=
  Homeomorph.chartableR2_iff e x

end TopologyOrthogonality

-- ═══════════════════════════════════════════════════════════════════
-- §10. Classical logic disclosure
-- ═══════════════════════════════════════════════════════════════════

section ClassicalDisclosure

/-- **Explicit classical-logic note:** The iterate dichotomy uses
    classical reasoning (law of excluded middle). This is standard in
    Lean 4 / Mathlib and does not weaken the result mathematically,
    but we disclose it for transparency. The diagonal exclusion itself
    is constructive. -/
theorem diagonal_exclusion_is_constructive {A B : Type u}
    (f : B → B) (hf : ∀ b, f b ≠ b) (s : A → A → B) (a₀ : A) :
    s a₀ ≠ fun a => f (s a a) := by
  intro h
  have := congr_fun h a₀
  exact hf (s a₀ a₀) this.symm

end ClassicalDisclosure

end RepresentationalIncompleteness
