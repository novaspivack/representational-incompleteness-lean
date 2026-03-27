/-
  **Topological obstruction for “ℝ² charts”.**

  `EuclideanSpace ℝ (Fin 2)` is **not** compact (Heine–Borel: `univ` is unbounded), whereas any
  **compact** nonempty patch of `ℝ²` (e.g. a closed Euclidean square) has compact subtype space.
  Hence such a patch **cannot** be homeomorphic to **all** of `ℝ²`.

  This packages the invariant behind SPEC_002‘s **B-bridged** route: boundary charts sit inside
  compact models, while interior charts target a noncompact chart type homeomorphic to `ℝ²`.
  Wiring `mobiusStripBoundary` / `closedCylinderBoundaryUnion` to those models is still a
  separate quotient/chart construction — this file proves the **core** `ℝ²` obstruction.
-/

import Mathlib.Algebra.Order.Ring.Abs
import RepresentationalIncompleteness.HalfPlaneVsPlane
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section

namespace RepresentationalIncompleteness

open scoped Topology
open Set Topology Metric Bornology

theorem not_compactSpace_euclidean_two : ¬ CompactSpace R2 := by
  rw [compactSpace_iff_isBounded_univ]
  intro h_univ
  rcases (isBounded_iff_subset_closedBall (c := (0 : R2))).1 h_univ with ⟨r, hr⟩
  have hr0 : 0 ≤ r := by
    have := hr (mem_univ (0 : R2))
    simpa [mem_closedBall_zero_iff, dist_zero_right, norm_zero] using this
  set p : R2 := EuclideanSpace.single (0 : Fin 2) (r + 1)
  have hp : p ∈ Metric.closedBall (0 : R2) r := hr (mem_univ p)
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_single, Real.norm_eq_abs] at hp
  have hrpos : 0 < r + 1 := by linarith [hr0, show (0 : ℝ) < 1 by norm_num]
  rw [abs_of_pos hrpos] at hp
  linarith

/-- **Closed** axis-aligned square in `ℝ²` (as a `PiLp` product of `Icc`). -/
def euclideanClosedSquare (a b c d : ℝ) : Set R2 :=
  { v | v 0 ∈ Icc a b ∧ v 1 ∈ Icc c d }

theorem isClosed_euclideanClosedSquare (a b c d : ℝ) : IsClosed (euclideanClosedSquare a b c d) := by
  let φ : R2 → ℝ × ℝ := fun v => (v 0, v 1)
  have hφ : Continuous φ := by fun_prop
  have hpre :
      euclideanClosedSquare a b c d = φ ⁻¹' (Icc a b ×ˢ Icc c d) := by
    ext v
    simp only [euclideanClosedSquare, mem_setOf_eq, mem_preimage, φ, mem_prod, mem_Icc]
  rw [hpre]
  exact (isClosed_Icc.prod isClosed_Icc).preimage hφ

theorem isBounded_euclideanClosedSquare (a b c d : ℝ) : IsBounded (euclideanClosedSquare a b c d) := by
  set Mx : ℝ := max |a| |b|
  set My : ℝ := max |c| |d|
  set R : ℝ := Real.sqrt (Mx ^ 2 + My ^ 2)
  refine (Metric.isBounded_closedBall (x := (0 : R2)) (r := R)).subset fun v hv => ?_
  rw [euclideanClosedSquare] at hv
  rcases hv with ⟨⟨ha0, hb0⟩, ⟨hc0, hd0⟩⟩
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq,
    Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ R)]
  have hsum : (∑ i : Fin 2, ‖v i‖ ^ 2) = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  rw [hsum]
  have h_abs0 : |v 0| ≤ Mx := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hneg : -Mx ≤ -|a| := neg_le_neg_iff.2 (le_max_left _ _)
      have ha' : -|a| ≤ a := neg_abs_le a
      linarith [ha0, hneg, ha']
    · have hb' : v 0 ≤ b := hb0
      have hb'' : b ≤ |b| := le_abs_self b
      have hb''' : |b| ≤ Mx := le_max_right _ _
      linarith
  have h_abs1 : |v 1| ≤ My := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hneg : -My ≤ -|c| := neg_le_neg_iff.2 (le_max_left _ _)
      have hc' : -|c| ≤ c := neg_abs_le c
      linarith [hc0, hneg, hc']
    · have hd' : v 1 ≤ d := hd0
      have hd'' : d ≤ |d| := le_abs_self d
      have hd''' : |d| ≤ My := le_max_right _ _
      linarith
  have hMxnn : 0 ≤ Mx := le_max_of_le_left (abs_nonneg a)
  have hMynn : 0 ≤ My := le_max_of_le_left (abs_nonneg c)
  have hsq0 : (v 0) ^ 2 ≤ Mx ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hMxnn])
  have hsq1 : (v 1) ^ 2 ≤ My ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hMynn])
  have hRsq : R ^ 2 = Mx ^ 2 + My ^ 2 := by
    dsimp [R]
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  nlinarith [hRsq]

theorem isCompact_euclideanClosedSquare (a b c d : ℝ) : IsCompact (euclideanClosedSquare a b c d) :=
  isCompact_of_isClosed_isBounded (isClosed_euclideanClosedSquare a b c d)
    (isBounded_euclideanClosedSquare a b c d)

theorem euclideanClosedSquare_nonempty (a b c d : ℝ) (_h₀ : a < b) (_h₁ : c < d) :
    (euclideanClosedSquare a b c d).Nonempty := by
  set v : R2 :=
    EuclideanSpace.single (0 : Fin 2) ((a + b) / 2) + EuclideanSpace.single (1 : Fin 2) ((c + d) / 2)
  refine ⟨v, ?_⟩
  simp only [euclideanClosedSquare, mem_setOf_eq]
  have hv0 : v 0 = (a + b) / 2 := by
    dsimp only [v]
    simp only [PiLp.add_apply, EuclideanSpace.single_apply, if_neg (by decide : (0 : Fin 2) ≠ 1),
      add_zero, if_true]
  have hv1 : v 1 = (c + d) / 2 := by
    dsimp only [v]
    simp only [PiLp.add_apply, EuclideanSpace.single_apply, if_neg (by decide : (1 : Fin 2) ≠ 0),
      if_true, zero_add]
  constructor
  · rw [hv0]; exact ⟨by linarith, by linarith⟩
  · rw [hv1]; exact ⟨by linarith, by linarith⟩

theorem isEmpty_homeomorph_euclideanClosedSquare_euclidean_two {a b c d : ℝ} (_h₀ : a < b) (_h₁ : c < d) :
    IsEmpty (euclideanClosedSquare a b c d ≃ₜ R2) := by
  refine ⟨fun e => ?_⟩
  set Sq := euclideanClosedSquare a b c d
  have hSq : IsCompact Sq := isCompact_euclideanClosedSquare a b c d
  have hSqsp : CompactSpace (Subtype Sq) := isCompact_iff_compactSpace.mp hSq
  exact not_compactSpace_euclidean_two (@Homeomorph.compactSpace (Subtype Sq) R2 _ _ hSqsp e)

end RepresentationalIncompleteness

end
