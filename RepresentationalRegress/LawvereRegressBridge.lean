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

end RepresentationalRegress
