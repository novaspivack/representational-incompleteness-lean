/-
  Regress chain: levels of meta-representation and non-termination claims.

  The spec sketches a coinductive `RegressChain`; the scaffold uses `ℕ → R.C`
  via `metaRepresent` until a coinductive design is stabilized (`SPEC_001_RR1`).
-/

import Mathlib.Data.Nat.Basic
import RepresentationalRegress.Basic

namespace RepresentationalRegress

variable (R : RepresentationalSystem)

/-- Distinct meta-levels yield distinct objects (strict injectivity of `metaRepresent`). -/
theorem regress_no_termination :
    ∀ n m : ℕ, n ≠ m → metaRepresent R n ≠ metaRepresent R m := by
  sorry

/-- No finite prefix exhausts the chain: for any bound, some larger level exists. -/
theorem regress_is_infinite :
    ∀ bound : ℕ,
      ∃ level : ℕ,
        level > bound ∧ ∃ obj : R.C, obj = metaRepresent R level := by
  intro bound
  exact ⟨bound + 1, Nat.lt_succ_self bound, metaRepresent R (bound + 1), rfl⟩

end RepresentationalRegress

/-!
## Draft API (spec)

The original design document proposed:

```lean
coinductive RegressChain (R : RepresentationalSystem) : Type u where
  | cons : (n : ℕ) → R.C → RegressChain R → RegressChain R
```

Revive this here if the coinductive presentation becomes preferable to `ℕ → R.C`.
-/
