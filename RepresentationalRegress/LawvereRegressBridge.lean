/-
  **Lawvere / diagonal arguments ↔ representational regress (interface lemmas).**

  * `no_universal_parametric_unary*` — classic “no universal self-interpreter” packaging of
    `lawvere_fixed_point_corollary_no_universal` (symbol grounding / Gödel informal gloss).
  * `lawvere_fixed_point_stays_representational` — categorical sense in which **iterates** of
    `represent` never inhabit the **object** `OntologicalSlot` (tower does not “collapse” to a bare
    object witness); this is `OntologicalSlot.no_slot_collapse`, renamed for papers linking Lawvere
    to `OntologicalSlot`.
-/

import RepresentationalRegress.Lawvere
import RepresentationalRegress.FixedPoints

universe u

namespace RepresentationalRegress

theorem no_universal_parametric_unary (B : Type u) (succ : B → B) (hsucc : ∀ b, succ b ≠ b) :
    ¬∃ (A : Type u) (_s : A → A → B), ∀ g : A → B, ∃ a : A, _s a = g := by
  rintro ⟨A, s, hs⟩
  exact lawvere_fixed_point_corollary_no_universal succ hsucc s hs

theorem no_universal_parametric_unary_nat :
    ¬∃ (A : Type) (_s : A → A → ℕ), ∀ g : A → ℕ, ∃ a : A, _s a = g := by
  rintro ⟨A, s, hs⟩
  exact lawvere_fixed_point_corollary_no_universal Nat.succ Nat.succ_ne_self s hs

/-- `Bool.not` has no fixed point: `!b ≠ b` for every `b : Bool`. -/
private theorem Bool.not_ne_self : ∀ b : Bool, (!b) ≠ b := by decide

/-- **No universal binary evaluator into `Bool`:** closes the computability horn.
    Any proposed `s : A → A → Bool` covering all `g : A → Bool` contradicts Lawvere,
    since `Bool.not` is fixed-point-free. This is the finite/decidable analogue of the
    Kleene diagonal (Rice's theorem setting). -/
theorem no_universal_parametric_unary_bool :
    ¬∃ (A : Type) (_s : A → A → Bool), ∀ g : A → Bool, ∃ a : A, _s a = g := by
  rintro ⟨A, s, hs⟩
  exact lawvere_fixed_point_corollary_no_universal (fun b => !b) Bool.not_ne_self s hs

/-- **Diagonal exclusion (partial models):** for ANY `s : A → A → B` and any
    fixed-point-free `f : B → B`, the diagonal `fun a => f (s a a)` is **never** equal
    to `s a₀` for any `a₀`.  This does NOT require surjectivity of `s`; it says the
    adversary's self-model necessarily has a blind spot containing its own diagonal. -/
theorem lawvere_diagonal_not_in_range {A B : Type u} (f : B → B) (hf : ∀ b, f b ≠ b)
    (s : A → A → B) (a₀ : A) :
    s a₀ ≠ fun a => f (s a a) := by
  intro h
  have := congr_fun h a₀
  exact hf (s a₀ a₀) this.symm

/-- Corollary for `ℕ`: the successor-diagonal is never a row of `s`. -/
theorem lawvere_diagonal_not_in_range_nat {A : Type} (s : A → A → ℕ) (a₀ : A) :
    s a₀ ≠ fun a => Nat.succ (s a a) :=
  lawvere_diagonal_not_in_range Nat.succ Nat.succ_ne_self s a₀

/-- Corollary for `Bool`: the negation-diagonal is never a row of `s`. -/
theorem lawvere_diagonal_not_in_range_bool {A : Type} (s : A → A → Bool) (a₀ : A) :
    s a₀ ≠ fun a => !(s a a) :=
  lawvere_diagonal_not_in_range (fun b => !b) Bool.not_ne_self s a₀

/--
  **Categorical “no collapse” (all iterates):** `represent^n` never equals the **object** slot of
  any `c : R.C`. Distinct from `lawvere_fixed_point_Type` (fixed points of `B → B` in `Type`), but
  this is the precise sense in which diagonal / Lawvere phenomena remain on the **endo** side of
  `OntologicalSlot` in the regress formalism.
-/
theorem lawvere_fixed_point_stays_representational (R : RepresentationalSystem.{u}) (n : ℕ) (c : R.C) :
    OntologicalSlot.endo (metaRegressArrow R n) ≠ OntologicalSlot.obj c :=
  OntologicalSlot.no_slot_collapse R n c

theorem ontological_wall_never_collapses_represent (R : RepresentationalSystem.{u}) (c : R.C) :
    OntologicalSlot.endo R.represent ≠ OntologicalSlot.obj c :=
  lawvere_wall_is_not_dissolution R c

/--
  **Representational Incompleteness (summit theorem).**

  Any self-modeling system `s : A → A → B` is necessarily incomplete with respect
  to its own diagonal behavior, provided `B` admits a fixed-point-free
  endomorphism `f`.  Concretely:

  1. **Diagonal exclusion:** The function `fun a => f (s a a)` — the system's own
     diagonal twisted by `f` — is *never* equal to any row `s a₀` of the self-model.
     This holds for EVERY `a₀ : A`, with no surjectivity assumption on `s`.

  2. **Total coverage impossible:** There is no `s` whatsoever (on any type `A`)
     such that every `g : A → B` appears as some row `s a`.

  Together these say: a self-modeling system either fails to model its own diagonal
  behavior (if partial), or cannot exist at all (if claimed total).  The blind spot
  is structural — not a resource limitation — and persists for every codomain `B`
  with a fixed-point-free endomorphism (including `ℕ` with `succ` and `Bool` with `not`).

  This is the representational analogue of Gödel incompleteness: not for formal
  theories and provability, but for any system that models itself via a parametric
  family of functions.
-/
theorem representational_incompleteness {A B : Type u} (f : B → B) (hf : ∀ b, f b ≠ b)
    (s : A → A → B) :
    (∀ a₀ : A, s a₀ ≠ fun a => f (s a a)) ∧
    ¬(∀ g : A → B, ∃ a : A, s a = g) :=
  ⟨fun a₀ => lawvere_diagonal_not_in_range f hf s a₀,
   fun hU => lawvere_fixed_point_corollary_no_universal f hf s hU⟩

/-- Representational incompleteness for `ℕ`-valued self-models. -/
theorem representational_incompleteness_nat {A : Type} (s : A → A → ℕ) :
    (∀ a₀ : A, s a₀ ≠ fun a => Nat.succ (s a a)) ∧
    ¬(∀ g : A → ℕ, ∃ a : A, s a = g) :=
  representational_incompleteness Nat.succ Nat.succ_ne_self s

/-- Representational incompleteness for `Bool`-valued self-models (decidable predicates). -/
theorem representational_incompleteness_bool {A : Type} (s : A → A → Bool) :
    (∀ a₀ : A, s a₀ ≠ fun a => !(s a a)) ∧
    ¬(∀ g : A → Bool, ∃ a : A, s a = g) :=
  representational_incompleteness (fun b => !b) Bool.not_ne_self s

end RepresentationalRegress
