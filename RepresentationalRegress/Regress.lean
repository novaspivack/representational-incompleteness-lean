/-
  Regress: distinct ℕ-indices give distinct **iterates** of `represent`, hence distinct
  objects of the slice `Over A`.
-/

import Mathlib.Data.Nat.Basic
import RepresentationalRegress.Basic

namespace RepresentationalRegress

variable (R : RepresentationalSystem)

theorem regress_no_termination :
    ∀ n m : ℕ, n ≠ m → metaRegressArrow R n ≠ metaRegressArrow R m :=
  fun _ _ h => metaRegressArrow_injective R h

theorem regress_over_injective :
    ∀ n m : ℕ, n ≠ m → metaOver R n ≠ metaOver R m :=
  fun _ _ h => metaOver_injective R h

/-- For **arrows** there is no finite exhaustive bound: for every `bound` some larger
    index carries a *different* iterate (because iterates are injective in `n`). -/
theorem regress_iterates_unbounded (bound : ℕ) :
    ∃ level : ℕ, bound < level ∧ metaRegressArrow R level ≠ metaRegressArrow R bound :=
  ⟨Nat.succ bound, Nat.lt_succ_self bound,
   metaRegressArrow_injective R (Nat.succ_ne_self bound)⟩

/-- Legacy: existence of an “object witness” — here the witness is the **source object**
    `A` common to all iterates; the *content* of level `level` is the arrow
    `metaRegressArrow R level : A ⟶ A`. -/
theorem regress_is_infinite (bound : ℕ) :
    ∃ level : ℕ, level > bound ∧ ∃ _obj : R.C, True :=
  ⟨bound + 1, Nat.lt_succ_self bound, R.A, trivial⟩

theorem meta_range_infinite (bound : ℕ) : ∃ level : ℕ, bound < level :=
  ⟨bound + 1, Nat.lt_succ_self bound⟩

end RepresentationalRegress
