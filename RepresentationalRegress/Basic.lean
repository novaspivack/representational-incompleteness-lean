/-
  Core definitions: representational system as a category with an awareness object
  and a self-representation endomorphism.
-/

import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

universe u

/-- A representational system: a category `C`, a designated "awareness" object `A`,
and a morphism `represent : A ⟶ A` (self-representation). -/
structure RepresentationalSystem where
  C : Type u
  categoryData : Category C
  A : C
  represent : A ⟶ A

instance (R : RepresentationalSystem) : Category R.C :=
  R.categoryData

/--
  A morphism `A ⟶ A` and an object term of type `C` lie in different sorts; they
  cannot be heterogeneous-equal. (Raw `f ≠ x` is ill-typed in Lean.)

  TODO (`SPEC_001_RR1`): replace `sorry` with a `HEq` elimination on
  `CategoryStruct`/`Category` to derive `A ⟶ A = C`, then contradict cardinality
  or known `Hom`/`Obj` discipline from mathlib if available; otherwise keep as the
  sanctioned cross-sort separation lemma.
-/
theorem morphism_obj_not_heq (R : RepresentationalSystem) :
    ¬ HEq R.represent R.A := by
  sorry

/--
  Meta-representation levels: `0` is the awareness object; deeper levels are
  refined in `Regress.lean`.
-/
noncomputable def metaRepresent (R : RepresentationalSystem) : ℕ → R.C
  | 0 => R.A
  | n + 1 => sorry
