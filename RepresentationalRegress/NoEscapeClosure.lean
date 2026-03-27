/-
  **No-escape packaging (“horns”) around representational iteration.**

  1. **Finite-order / collision horn:** If distinct monoid powers coincide, then every power equals
     one of at most `n + d` distinguished powers (`Iterate` collision → finite index range).

  2. **Cross-object “readout of A inside B” horn:** A retraction--section pair `A ⇄ B` induces an
     idempotent `End B` composite. If that composite is not the identity, iterates cannot be
     injective beyond height one—so no infinite injective *tower* along that readout channel.

  3. **Iterate dichotomy (classical):** For every `End A`, either iterates are injective, or the
     distinct-power set is finite (bounded indexing).

  This module is intentionally **orthogonal** to `RepresentationalSystem.iter_injective`: it records
  what happens when that hypothesis fails or when a rival self-representation channel is taken.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

import RepresentationalRegress.Basic

universe u

open CategoryTheory

namespace RepresentationalRegress

namespace IterateClosure

variable {C : Type u} [Category C] {A : C}

/-- Once `e ^ (n + d) = e ^ n` with `d > 0`, shifting by `+d` stabilizes every tail `n + k`. -/
theorem End.pow_tail_periodic (e : End A) {n d : ℕ} (_hd : 0 < d) (h : e ^ (n + d) = e ^ n) :
    ∀ k : ℕ, e ^ (n + k + d) = e ^ (n + k) := by
  intro k
  induction k with
  | zero => simpa [Nat.add_zero] using h
  | succ k ih =>
    have ex1 : n + Nat.succ k + d = n + k + d + 1 := by omega
    have ex2 : n + Nat.succ k = n + k + 1 := by omega
    rw [ex1, ex2, pow_succ, pow_succ, ih]

private theorem End.pow_eq_of_ge {e : End A} {n d k : ℕ} (hd : 0 < d) (hk : n + d ≤ k)
    (h : e ^ (n + d) = e ^ n) :
    e ^ k = e ^ (k - d) := by
  have hk0 : d ≤ k := (Nat.le_add_left d n).trans hk
  have hn : n ≤ k - d := (Nat.le_sub_iff_add_le hk0).2 hk
  have hsplit : k = n + (k - d - n) + d := by omega
  have hm := End.pow_tail_periodic e hd h (k - d - n)
  rw [hsplit, hm]
  -- Close `e ^ (n + (k - d - n)) = e ^ (k - d)`; RHS may normalize via `hsplit` to `+ d - d`.
  rw [Nat.add_sub_of_le hn]
  simp_rw [Nat.sub_add_cancel hk0]

theorem End.exists_lt_of_pow_collision (e : End A) {n d : ℕ} (hd : 0 < d)
    (h : e ^ (n + d) = e ^ n) (k : ℕ) :
    ∃ i < n + d, e ^ i = e ^ k := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < n + d
    · exact ⟨k, hk, rfl⟩
    · push_neg at hk
      have hk' : n + d ≤ k := hk
      have hred : e ^ k = e ^ (k - d) := End.pow_eq_of_ge hd hk' h
      have hkpos : 0 < k := by omega
      have hlt : k - d < k := Nat.sub_lt hkpos hd
      rcases ih (k - d) hlt with ⟨i, hi, he⟩
      exact ⟨i, hi, he.trans hred.symm⟩

/-- From **non**-injective iterate indices extract a positive modulus equality `e ^ (n + d) = e ^ n`. -/
theorem End.exists_pow_collision_of_not_injective (e : End A)
    (h : ¬∀ {n m : ℕ}, n ≠ m → e ^ n ≠ e ^ m) :
    ∃ n d : ℕ, d ≠ 0 ∧ e ^ (n + d) = e ^ n := by
  classical
  push_neg at h
  rcases h with ⟨n, m, hne, heq⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨n, m - n, ?_, ?_⟩
    · exact Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hlt)
    · simpa [Nat.add_sub_of_le hlt.le] using heq.symm
  · refine ⟨m, n - m, ?_, ?_⟩
    · exact Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hgt)
    · simpa [Nat.add_sub_of_le hgt.le] using heq

/-- **Bounded distinct powers:** after the first collision, only finitely many iterate labels occur. -/
theorem End.exists_bound_of_pow_collision (e : End A) {n d : ℕ} (hd : d ≠ 0)
    (h : e ^ (n + d) = e ^ n) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ i < B, e ^ i = e ^ k :=
  ⟨n + d, fun k => End.exists_lt_of_pow_collision e (Nat.pos_of_ne_zero hd) h k⟩

/-- **Dichotomy:** unbounded injective tower vs finite repertoire of iterate morphisms. -/
theorem End.pow_iterate_dichotomy (e : End A) :
    (∃ B : ℕ, ∀ k : ℕ, ∃ i < B, e ^ i = e ^ k) ∨
      ∀ {n m : ℕ}, n ≠ m → e ^ n ≠ e ^ m := by
  classical
  by_cases h : ∀ {n m : ℕ}, n ≠ m → e ^ n ≠ e ^ m
  · exact Or.inr h
  · rcases End.exists_pow_collision_of_not_injective e h with ⟨n, d, hd, heq⟩
    exact Or.inl (End.exists_bound_of_pow_collision e hd heq)

theorem representIter_exists_bound_of_not_iter_injective (R : RepresentationalSystem.{u})
    (h : ¬∀ {n m : ℕ}, n ≠ m → representIter R n ≠ representIter R m) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ i < B, representIter R i = representIter R k := by
  let e : End R.A := End.of R.represent
  have h' : ¬∀ {n m : ℕ}, n ≠ m → e ^ n ≠ e ^ m := by
    intro hn
    apply h
    intro n m hnm
    simpa [representIter, e] using hn hnm
  rcases End.exists_pow_collision_of_not_injective e h' with ⟨n, d, hd, heq⟩
  exact End.exists_bound_of_pow_collision e hd heq

end IterateClosure

namespace CrossObjectRepresentation

variable {C : Type u} [Category C] {A B : C}

/-- Section `s : A ⟶ B` and retraction `r : B ⟶ A` with `s ≫ r = 𝟙 A`. The induced
    endomorphism `r ≫ s` on `B` is idempotent (`B → A → B` then again `B → A → B`). -/
theorem idemComp_section_retraction (s : A ⟶ B) (r : B ⟶ A) (h : s ≫ r = 𝟙 A) :
    (r ≫ s) ≫ (r ≫ s) = r ≫ s := by
  calc
    (r ≫ s) ≫ (r ≫ s) = ((r ≫ s) ≫ r) ≫ s := (Category.assoc _ _ _).symm
    _ = (r ≫ (s ≫ r)) ≫ s := by rw [Category.assoc r s r]
    _ = (r ≫ 𝟙 A) ≫ s := by rw [h]
    _ = r ≫ (𝟙 A ≫ s) := Category.assoc r (𝟙 A) s
    _ = r ≫ s := by rw [Category.id_comp]

theorem End.mul_self_section_retraction (s : A ⟶ B) (r : B ⟶ A) (h : s ≫ r = 𝟙 A) :
    End.of (r ≫ s) * End.of (r ≫ s) = End.of (r ≫ s) :=
  End.ext (idemComp_section_retraction s r h)

/-- Idempotent endomorphisms have `e ^ n = e` for every positive `n`. -/
theorem End.pow_pos_eq_self_of_mul_self (e : End B) (hid : e * e = e) :
    ∀ {n : ℕ}, 0 < n → e ^ n = e
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | 1, _ => by rw [pow_one]
  | n + 2, _ => by
      rw [pow_succ, pow_pos_eq_self_of_mul_self e hid (Nat.add_one_pos n)]
      simpa [pow_one] using hid

/-- An idempotent has `e ^ 1 = e ^ 2`, so monoid-powers **cannot** be injective on `ℕ`. -/
theorem End.not_injective_pow_of_mul_self (e : End B) (hid : e * e = e) :
    ¬∀ {n m : ℕ}, n ≠ m → e ^ n ≠ e ^ m := by
  intro hinj
  have h12 := hinj (show (1 : ℕ) ≠ 2 by decide)
  have e2 : e ^ 2 = e := by rw [pow_succ, pow_one, hid]
  rw [pow_one, e2] at h12
  exact absurd rfl h12

/-- Any retraction--section loop `r ≫ s` on `B` yields **non-injective** iterate indices (already at
    `1` vs `2`): no infinite injective ℕ-indexed tower along this readout channel. -/
theorem End.not_injective_pow_section_retraction (s : A ⟶ B) (r : B ⟶ A) (h : s ≫ r = 𝟙 A) :
    ¬∀ {n m : ℕ}, n ≠ m → (End.of (r ≫ s)) ^ n ≠ (End.of (r ≫ s)) ^ m :=
  End.not_injective_pow_of_mul_self _ (End.mul_self_section_retraction s r h)

end CrossObjectRepresentation

end RepresentationalRegress
