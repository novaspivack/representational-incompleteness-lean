/-
  Core definitions: a representational system is a category with an awareness object
  `A`, a self-representation endomorphism `represent`, and (**hypothesis**) injective
  iterated powers `(represent : End A)^n`.

  **Meta-levels:** For each `n : ℕ`, the *formal* meta-stage is the morphism
  `metaRegressArrow R n = represent^n` (iteration in the monoid `End A`). Distinct
  stages are **distinct arrows**; categorically these package as objects of the
  slice `Over A` via `Over.mk (represent^n)` — the “new object” at level `n` is
  the structured arrow `(A, represent^n)`, not a fresh object of `C` unrelated
  to `A`.

  This ties the regress **definitionally** to `represent`; the remaining
  mathematical content is **`iter_injective`**: e.g. in free categories, or
  whenever the endomorphism has infinite order without collisions.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endomorphism

open CategoryTheory

universe u

/-- Representational system: category, awareness object, self-representation, and
injectivity of monoid powers in `End A`. -/
structure RepresentationalSystem where
  C : Type u
  categoryData : Category C
  A : C
  represent : A ⟶ A
  iter_injective : ∀ {n m : ℕ}, n ≠ m → (End.of represent)^n ≠ (End.of represent)^m

instance (R : RepresentationalSystem) : Category R.C :=
  R.categoryData

/-- `represent^n` in the endomorphism monoid. -/
def representIter (R : RepresentationalSystem) (n : ℕ) : End R.A :=
  (End.of R.represent) ^ n

/-- The meta-level `n` as an **arrow** `A ⟶ A` (iteration of `represent`). -/
def metaRegressArrow (R : RepresentationalSystem) (n : ℕ) : R.A ⟶ R.A :=
  (representIter R n).asHom

/-- Categorical packaging: `Over A` object with structure map `represent^n`. -/
def metaOver (R : RepresentationalSystem) (n : ℕ) : Over R.A :=
  Over.mk (metaRegressArrow R n)

/-- `Over.mk` is injective on parallel endomorphisms `A ⟶ A` (costructured-arrow case). -/
theorem Over_mk_inj_parallel (R : RepresentationalSystem) {f g : R.A ⟶ R.A}
    (h : Over.mk f = Over.mk g) : f = g := by
  cases h
  rfl

/-- Backward-compatible name: “`metaRepresent`” is the regress **arrow** at level `n`. -/
abbrev metaRepresent (R : RepresentationalSystem) (n : ℕ) : R.A ⟶ R.A :=
  metaRegressArrow R n

theorem representIter_injective (R : RepresentationalSystem) {n m : ℕ} (h : n ≠ m) :
    representIter R n ≠ representIter R m :=
  R.iter_injective h

theorem metaRegressArrow_injective (R : RepresentationalSystem) {n m : ℕ} (h : n ≠ m) :
    metaRegressArrow R n ≠ metaRegressArrow R m := fun he =>
  R.iter_injective h (End.ext he)

theorem metaOver_injective (R : RepresentationalSystem) {n m : ℕ} (h : n ≠ m) :
    metaOver R n ≠ metaOver R m := fun he => by
  refine metaRegressArrow_injective R h ?_
  simp_rw [metaOver] at he
  exact Over_mk_inj_parallel R he

theorem metaRepresent_zero (R : RepresentationalSystem) : metaRepresent R 0 = 𝟙 R.A := by
  simp [metaRepresent, metaRegressArrow, representIter, End.one_def]

theorem representIter_zero (R : RepresentationalSystem) : representIter R 0 = 1 :=
  rfl

/-- Tag objects of `C` and endomorphisms `A ⟶ A` into a common type so their
disjointness is provable by constructor discrimination. -/
inductive OntologicalSlot (R : RepresentationalSystem) : Type u
  | obj : R.C → OntologicalSlot R
  | endo : (R.A ⟶ R.A) → OntologicalSlot R

theorem obj_ne_endo (R : RepresentationalSystem) (c : R.C) (f : R.A ⟶ R.A) :
    OntologicalSlot.obj c ≠ OntologicalSlot.endo f := by
  intro h
  cases h

/-- Distinct endomorphisms yield distinct `endo` slots (constructor injectivity). -/
theorem OntologicalSlot.endo_injective (R : RepresentationalSystem) :
    Function.Injective (@OntologicalSlot.endo R) := by
  intro _ _ h
  cases h
  rfl

/-- Distinct meta-level indices give distinct `endo` slots (SPEC P2-1, `representational_tower_preserves_slot`). -/
theorem OntologicalSlot.representational_tower_preserves_slot (R : RepresentationalSystem) {n m : ℕ}
    (h : n ≠ m) :
    OntologicalSlot.endo (metaRegressArrow R n) ≠ OntologicalSlot.endo (metaRegressArrow R m) :=
  fun he => absurd (OntologicalSlot.endo_injective R he) (metaRegressArrow_injective R h)

/-- No iterate slot `endo (represent^n)` collapses to an object slot (SPEC P2-1, `no_slot_collapse`). -/
theorem OntologicalSlot.no_slot_collapse (R : RepresentationalSystem) (n : ℕ) (c : R.C) :
    OntologicalSlot.endo (metaRegressArrow R n) ≠ OntologicalSlot.obj c :=
  (obj_ne_endo R c (metaRegressArrow R n)).symm

theorem represent_slot_ne_A (R : RepresentationalSystem) :
    OntologicalSlot.endo R.represent ≠ OntologicalSlot.obj R.A :=
  (obj_ne_endo _ _ _).symm

theorem metaRepresent_injective (R : RepresentationalSystem) :
    Function.Injective (metaRepresent R) := fun _ _ h =>
  by_contra fun hne => R.iter_injective hne (End.ext h)
