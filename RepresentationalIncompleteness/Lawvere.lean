/-
  Lawvere's fixed-point theorem — **`Type` instantiation**.

  In the cartesian closed category **`Type u`**, exponential objects are function
  types, and “weak point-surjectivity” of `s : A → A → B` is the hypothesis
  `∀ g : A → B, ∃ a, s a = g` (every unary function `A → B` appears as a *slice*
  `s a` of the binary map).

  This is the concrete form used in Cantor / Gödel / Turing style diagonal
  arguments. A bundled CCC statement can be recovered from
  `CategoryTheory.MonoidalClosed.Types` (`Mathlib.CategoryTheory.Monoidal.Closed.Types`).

  Reference: F. Lawvere, “Diagonal arguments and cartesian closed categories” (1969).

  For the same hypothesis in **`MonoidalClosed (Type u)`** notation (`curry` / `⊗`), see
  `RepresentationalIncompleteness.LawvereCCCType`.
-/

import Mathlib.Logic.Function.Basic

universe u

/--
  **Lawvere fixed-point (Type).**

  If every `g : A → B` is `s a` for some parameter `a : A` (“`s` is universal for
  unary functions”), then every endomap `f : B → B` has a fixed point.

  Proof: diagonalize `k a := f (s a a)` and pick `a₀` with `s a₀ = k`, then
  `s a₀ a₀ = k a₀ = f (s a₀ a₀)`.
-/
theorem lawvere_fixed_point_Type {A B : Type u} (f : B → B) (s : A → A → B)
    (hs : ∀ g : A → B, ∃ a : A, s a = g) :
    ∃ b : B, f b = b := by
  let k : A → B := fun a => f (s a a)
  obtain ⟨a₀, ha₀⟩ := hs k
  refine ⟨s a₀ a₀, ?_⟩
  simpa [k] using (congr_fun ha₀ a₀).symm

/--
  **Corollary (no universal enumerator into `A → B` for `B` with a shift).**

  If `B` admits a map `succ : B → B` **without** fixed points (for example
  `ℕ` with `Nat.succ`), then there is **no** `s : A → A → B` surjective onto
  unary functions in the sense of `lawvere_fixed_point_Type`.

  This is the usual “no surjection `A → (A → B)`” diagonal corollary.
-/
theorem lawvere_fixed_point_corollary_no_universal {A B : Type u} (succ : B → B)
    (hsucc : ∀ b : B, succ b ≠ b) (s : A → A → B)
    (hU : ∀ g : A → B, ∃ a : A, s a = g) : False := by
  obtain ⟨b, hb⟩ := lawvere_fixed_point_Type succ s hU
  exact hsucc b hb
