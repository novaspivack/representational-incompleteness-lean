/-
  **Lawvere ↔ cartesian closed `Type u`.**

  The diagonal theorem in `Lawvere.lean` is stated in ordinary function language.
  Here we package the same hypothesis using **`MonoidalClosed (Type u)`**:
  internal hom, `curry`, and evaluation `ev` (via lemmas from closed monoidal categories).

  This is *not* Lawvere for an abstract CCC—the category is still `Type u`—but it
  nails the **CCC vocabulary** Mathlib actually uses for “exponentials = function
  types,” so “Lawvere-ish” becomes “Lawvere for `Type` in categorical dress.”

  **Further work (not here):** state and prove Lawvere for a general `C` with
  `[MonoidalClosed C]` + `[HasTerminal C]` + surjectivity on *global elements*
  `⊤ ⟶ B^^A`, reusing the same diagram; that requires a small API for “elements.”
-/

import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

import RepresentationalRegress.Lawvere

universe u

namespace RepresentationalRegress

open CategoryTheory MonoidalCategory MonoidalClosed

variable {A B : Type u}

/--
  Binary morphism `A ⊗ A ⟶ B` whose *curried* form is **`fun i x => s i x`**:

  on `(a₁, a₂)` it uses `s a₂ a₁` so that `curry`’s convention
  `(curry f) y = fun a' => f (a', y)` yields `(curry f) i = s i`.
-/
def lawvereBinary (s : A → A → B) : (A ⊗ A) ⟶ B :=
  fun p : A × A => s p.2 p.1

lemma lawvereBinary_apply (s : A → A → B) (a₁ a₂ : A) :
    lawvereBinary s (a₁, a₂) = s a₂ a₁ :=
  rfl

/-- `uncurry` recovers `lawvereBinary s` from the morphism `s : A ⟶ A ⟹ B`. -/
theorem uncurry_eq_lawvereBinary (s : A → A → B) :
    uncurry (s : A ⟶ (A ⟶[Type u] B)) = lawvereBinary s := by
  funext p
  rcases p with ⟨x, i⟩
  simp [uncurry_eq, types_tensorObj_def, lawvereBinary]
  rfl

/--
  `curry` turns `lawvereBinary s` into `s` itself — this is the key alignment with
  `lawvere_fixed_point_Type`’s “`s a` as a unary function.”
-/
theorem curry_lawvereBinary (s : A → A → B) : curry (lawvereBinary s) = s := by
  rw [← uncurry_eq_lawvereBinary s, curry_uncurry]

/-- The “universal enumerator” hypothesis `∀ g, ∃ a, s a = g` ↔ surjectivity of `curry`. -/
theorem lawvere_universal_iff_surjective_curry (s : A → A → B) :
    (∀ g : A → B, ∃ a : A, s a = g) ↔ Function.Surjective (curry (lawvereBinary s)) := by
  constructor
  · intro H k
    obtain ⟨a, ha⟩ := H k
    refine ⟨a, ?_⟩
    rw [curry_lawvereBinary, ha]
  · intro hsurj g
    obtain ⟨a, ha⟩ := hsurj g
    refine ⟨a, ?_⟩
    rw [← curry_lawvereBinary s, ha]

/--
  **Lawvere fixed point (Type), categorical hypothesis.**

  If `curry (lawvereBinary s)` is surjective, every endomap `f : B → B` has a fixed point.
  Same mathematics as `lawvere_fixed_point_Type`; hypothesis matches CCC bookkeeping.
-/
theorem lawvere_fixed_point_MonoidalClosedType {A B : Type u} (f : B → B) (s : A → A → B)
    (hsurj : Function.Surjective (MonoidalClosed.curry (lawvereBinary s))) :
    ∃ b : B, f b = b :=
  lawvere_fixed_point_Type f s ((lawvere_universal_iff_surjective_curry s).1 hsurj)

end RepresentationalRegress
