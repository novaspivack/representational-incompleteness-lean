/-
  Fixed-point analysis: Lawvere / CCC layer and the object–morphism distinction
  at fixed points (`SPEC_001_RR1`).

  Mathlib’s cartesian closed API is currently expressed via
  `CartesianMonoidalCategory` + `MonoidalClosed`; wire this file to those
  typeclasses when stating Lawvere’s theorem precisely.
-/

import Mathlib.CategoryTheory.Category.Basic

import RepresentationalRegress.Basic

open CategoryTheory

universe u

namespace RepresentationalRegress

variable {C : Type u} [Category C]

/--
  Placeholder: connect mathlib’s fixed-point / exponential machinery once the
  CCC instance and statement are chosen (`SPEC_001_RR1`).

  Avoid comparing `f : A ⟶ A` with `x : A` using `≠` (ill-typed); use typed
  internal-language elements or `HEq` as appropriate.
-/
theorem fixed_point_preserves_distinction (A : C) (_f : A ⟶ A) :
    True := trivial

/--
  No object term is heterogeneous-equal to the representation morphism.

  TODO (`SPEC_001_RR1`): derive from `morphism_obj_not_heq` or a general lemma.
-/
theorem lawvere_wall_is_not_dissolution (R : RepresentationalSystem) :
    ∀ fp : R.C, ¬ HEq R.represent fp := by
  sorry

end RepresentationalRegress
