/-
  Fixed-point layer: (i) disjointness of endomorphisms vs global elements `⊤_ C ⟶ A`
  when a terminal exists, and (ii) injective currying in any monoidal closed
  category — the structural fact behind Lawvere-style fixed-point arguments.

  A bundled statement of Lawvere's fixed-point theorem for CCCs is not in Mathlib
  under that name; the lemmas here are the audited fragments used by this library.
  The concrete **Type** diagonal theorem is `lawvere_fixed_point_Type` in
  `RepresentationalRegress.Lawvere`.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

import RepresentationalRegress.Basic

open CategoryTheory
open CategoryTheory.Limits
open MonoidalClosed

universe u

namespace RepresentationalRegress

variable {C : Type u} [Category C]

/-! ## Tagged witnesses: endomorphism vs global element (terminal) -/

/-- Endomorphism vs global element (`⊤_ C ⟶ A`), disjoint constructors. -/
inductive EndoVsPoint (A : C) [HasTerminal C] : Type u
  | endo : (A ⟶ A) → EndoVsPoint A
  | point : (⊤_ C ⟶ A) → EndoVsPoint A

theorem endo_ne_point (A : C) [HasTerminal C] (f : A ⟶ A) (p : ⊤_ C ⟶ A) :
    EndoVsPoint.endo f ≠ EndoVsPoint.point p := by
  intro h
  cases h

theorem point_ne_endo (A : C) [HasTerminal C] (f : A ⟶ A) (p : ⊤_ C ⟶ A) :
    EndoVsPoint.point p ≠ EndoVsPoint.endo f :=
  (endo_ne_point A f p).symm

/-! ## Monoidal closed: curry is injective (Lawvere backbone) -/

variable [MonoidalCategory C] [MonoidalClosed C]

/--
  Currying is injective: internal hom does not identify distinct morphisms.
  This is the categorical core of “no collapse of morphism content at the exponential.”
-/
theorem fixed_point_preserves_distinction (A X Y : C) :
    Function.Injective (MonoidalClosed.curry (A := A) (X := X) (Y := Y)) :=
  MonoidalClosed.curry_injective

theorem uncurry_injective_on (A X Y : C) :
    Function.Injective (MonoidalClosed.uncurry (A := A) (X := X) (Y := Y)) :=
  MonoidalClosed.uncurry_injective

/-! ## Ontological non-collapse for the representational arrow -/

variable (R : RepresentationalSystem)

theorem lawvere_wall_is_not_dissolution (fp : R.C) :
    OntologicalSlot.endo R.represent ≠ OntologicalSlot.obj fp :=
  (obj_ne_endo R fp R.represent).symm

end RepresentationalRegress
