/-
  **Seam `ChartableR2` packaging (SPEC_003_NF8).**

  Phase **A–B** spine living here:
  * `mobiusPlaneTrigCoordMap` agrees with fundamental-domain `mobiusFDTrigCoord` after `mobiusPlaneCoord`.
  * `mobiusFDTrigCoord '' S` rewrites to `mobiusPlaneTrigCoordMap '' (mobiusPlaneCoord '' S)`.
  * On `mobiusSeamSaturatedPatch`, planar height avoids `½` (`mobiusPlaneCoord_height_ne_half_of_mem_…`); see
    `sub_half_ne_zero_of_mem_mobiusSeamSaturatedPatch` in `MobiusSeamTrigInject`.
  * Open **images** of the plane trig map on **open** subsets of `R2` that avoid `t = ½` (`B1`).
  * **B3 (interior-sheet form):** `isOpen_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatchSheetInterior` — open trig image on
    `mobiusSeamSaturatedPatchSheetInterior` (away from `x ∈ {0,1}` in `Icc`), where `mobiusPlaneCoord '' patch` is open in `R2`.
    The **full** patch satisfies **`mobiusPlaneCoord_image_mobiusSeamSaturatedPatch_eq`** (closed-on-one-side rectangle union in `R2`)
    and **`not_isOpen_mobiusPlaneCoord_image_mobiusSeamSaturatedPatch`**, so it is **not** the domain for the plain `B1`/`IsOpen` chain.
    **Not** `mobiusFDTrigCoord '' full patch = mobiusFDTrigCoord '' sheet interior`: see **`ne_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch_sheetInterior`**. **B3 (full patch):** `isOpen_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch` (proved).

  * **C1 (sheet interior):** `chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatchSheetInterior` — `ChartableR2 ⟦p⟧`
    for `p ∈ mobiusSeamSaturatedPatchSheetInterior` under the same **geometric** windows as the saturated seam patch
    (`ε < ½`, `0 < t₀ ± δ`, etc.); no `δ < |t₀ - ½|` hypothesis (that hypothesis is for the **trig** open-image route).
    Corollaries: `chartableR2_mobiusQuotientMk_of_mem_mobiusSeamLeftPatch_of_pos`,
    `chartableR2_mobiusQuotientMk_of_mem_mobiusSeamRightPatch_of_lt_one`,
    `chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatch_of_ne_seamIccEdges`. Transport along `mobiusRel₀`:
    `chartableR2_mobiusQuotientMk_of_mobiusRel₀`, `chartableR2_mobiusQuotientMk_of_mobiusRel₀_chartable_left`
    in `MobiusChartableBoundary`.

  * **E1 prep:** `chartableR2_mobiusQuotientMk_of_mem_Ioo_square_or_seamSheetInterior`; plane criteria
    `chartableR2_mobiusQuotientMk_of_mobiusPlaneCoord_mem_image_seamSheetInterior`,
    `chartableR2_mobiusQuotientMk_of_mobiusPlaneCoord_mem_openBox_union_image_seamSheetInterior`; on **`MobiusStrip`**,
    **`chartableR2_of_mem_image_quotient_mk_*`**, including
    **`chartableR2_of_mem_image_quotient_mk_seamSaturatedPatch_ne_seamIccEdges`**.

  * **Phase D (sliding / `0 < x < 1` fiber):** **`chartableR2_mobiusQuotientMk_of_mem_sliding_strictCoordSet`** — if
    **`mobiusSeamSlidingCoord t₀ p` lies in `mobiusSeamSlidingStrictCoordSet t₀`**, then **`p` lies in `(0,1)²`**
    (**`mem_preimage_mobiusSeamSlidingStrictCoordSet_iff`**) and **`ChartableR2 ⟦p⟧`** is **`chartableR2_mobiusQuotientMk_of_Ioo_square`**.
    **`chartableR2_mobiusQuotientMk_of_sliding_strict_ball`** reduces to the same route. Covers strict-interior points including
    **`t₀ = ½`** (no **`δ < |t₀ - ½|`** trig-window hypothesis).     **`homeomorph_subtype_mobiusSeamSlidingCoord_preimage`** remains for
    **IFT ∘ sliding** composition with **`mobiusSeamLocalMapOpenPartialHomeomorph`** (still to be wired at seam normals).
    **`MobiusChartableBoundary`:** **`injective_mobiusQuotientMk_subtype_of_subset`**; this file:
    **`mobiusSeamSlidingCoordBallLeftHalf`**, **`isOpen_mobiusSeamSlidingCoordBallLeftHalf`**, **`injective_mobiusQuotientMk_subtype_of_mem_slidingCoordBallLeftHalf_radius_lt_one`**, **`mem_mobiusSeamLeftPatch_of_mem_mobiusSeamSlidingCoordBallLeftHalf`**, **`mem_mobiusSeamSlidingCoordBallLeftHalf_of_left_seam_point`**, **`chartableR2_mobiusQuotientMk_of_mem_slidingCoordBallLeftHalf_of_pos`**.

  **C4 / M-FINAL:** **`chartableR2_mobiusQuotientMk_of_interior_height`** discharges
  **`∀ p, 0 < t < 1 → ChartableR2 ⟦p⟧`**; combine with **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`**
  in **`MobiusChartableBoundary`** and **`mobiusStrip_not_homeomorphic_closedCylinder`** in this file
  (see **`ChartableR2Bridge`**). Plane-geometry caveats (**`mobiusPlaneCoord_image_mobiusSeamSaturatedPatch_eq`**, etc.)
  remain as documented in **`SPEC_003_NF8`**.
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Piecewise

import RepresentationalRegress.ChartableR2Bridge
import RepresentationalRegress.ChartableR2Neighbor
import RepresentationalRegress.MobiusChartableBoundary
import RepresentationalRegress.MobiusSeamChart
import RepresentationalRegress.MobiusSeamChartable
import RepresentationalRegress.MobiusSeamTrigInject

noncomputable section

namespace RepresentationalRegress

open scoped Topology
open Set Filter Topology EuclideanSpace PiLp Function Metric Real

/-- Spec **A1:** `mobiusPlaneTrigCoordMap` from `MobiusSeamChart` (`mobiusSeamLocalMapPure 0`) agrees with
  `mobiusFDTrigCoord` after `mobiusPlaneCoord`. -/

theorem mobiusPlaneTrigCoordMap_mobiusPlaneCoord_eq_mobiusFDTrigCoord (p : MobiusFundamentalDomain) :
    mobiusPlaneTrigCoordMap (mobiusPlaneCoord p) = mobiusFDTrigCoord p := by
  simp [mobiusPlaneTrigCoordMap, mobiusPlaneCoord, mobiusSeamLocalMapPure, mobiusFDTrigCoord,
    EuclideanSpace.single_apply, PiLp.add_apply, sub_eq_add_neg]

theorem mobiusPlaneHalfSlidingEquatorCoordMap_mobiusPlaneCoord (p : MobiusFundamentalDomain) :
    mobiusPlaneHalfSlidingEquatorCoordMap (mobiusPlaneCoord p) = mobiusFDHalfSlidingCoord p := by
  dsimp only [mobiusPlaneHalfSlidingEquatorCoordMap, mobiusFDHalfSlidingCoord, mobiusSeamSlidingCoord,
    mobiusPlaneCoord]
  congr 1
  refine PiLp.ext ?_
  intro i
  fin_cases i <;> simp [PiLp.add_apply, EuclideanSpace.single_apply, sub_eq_add_neg, add_assoc,
    add_left_comm]

theorem mobiusPlaneCoord_of_left_seam_equator {p : MobiusFundamentalDomain} (hp0 : p.1.val = 0)
    (hth : p.2.val = 1 / 2) : mobiusPlaneCoord p = mobiusPlaneLeftSeamEquatorPoint := by
  refine PiLp.ext ?_
  intro i
  fin_cases i <;> simp [mobiusPlaneCoord, mobiusPlaneLeftSeamEquatorPoint, PiLp.add_apply,
    EuclideanSpace.single_apply, hp0, hth]

theorem mobiusFDTrigCoord_image_eq_image_trigMap_planeCoord (S : Set MobiusFundamentalDomain) :
    mobiusFDTrigCoord '' S = mobiusPlaneTrigCoordMap '' (mobiusPlaneCoord '' S) := by
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨mobiusPlaneCoord p, ⟨p, hp, rfl⟩, ?_⟩
    exact mobiusPlaneTrigCoordMap_mobiusPlaneCoord_eq_mobiusFDTrigCoord p
  · rintro ⟨v, ⟨p, hp, hvp⟩, hvy⟩
    subst hvp
    refine ⟨p, hp, ?_⟩
    rw [← hvy, mobiusPlaneTrigCoordMap_mobiusPlaneCoord_eq_mobiusFDTrigCoord p]

theorem mobiusPlaneCoord_height_ne_half_of_mem_mobiusSeamSaturatedPatch {t₀ ε δ : ℝ}
    (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|) {p : MobiusFundamentalDomain}
    (hp : p ∈ mobiusSeamSaturatedPatch t₀ ε δ) :
    mobiusPlaneCoord p (1 : Fin 2) ≠ (1 / 2 : ℝ) := by
  have h := sub_half_ne_zero_of_mem_mobiusSeamSaturatedPatch hδ₂ hp
  rw [mobiusPlaneCoord_apply_one]
  intro h12
  apply h
  linarith

theorem mobiusPlaneCoord_height_ne_half_of_mem_mobiusSeamSaturatedPatchSheetInterior {t₀ ε δ : ℝ}
    (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|) {p : MobiusFundamentalDomain}
    (hp : p ∈ mobiusSeamSaturatedPatchSheetInterior t₀ ε δ) :
    mobiusPlaneCoord p (1 : Fin 2) ≠ (1 / 2 : ℝ) := by
  refine mobiusPlaneCoord_height_ne_half_of_mem_mobiusSeamSaturatedPatch (ε := ε) (δ := δ) hδ₂ ?_
  rcases hp with hpL | hpR
  · exact Or.inl hpL.2
  · exact Or.inr hpR.2

private lemma continuous_mobiusSeamR2_coord0 : Continuous fun v : R2 => v 0 :=
  @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (0 : Fin 2)

private lemma continuous_mobiusSeamR2_coord1 : Continuous fun v : R2 => v 1 :=
  @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (1 : Fin 2)

/-- Avoiding `v 1 = ½`, the trig model pushes neighborhoods (hence open sets) to open sets. -/
theorem isOpen_image_mobiusPlaneTrigCoordMap_of_forall_height_ne_half {Ω : Set R2} (hΩ : IsOpen Ω)
    (h : ∀ v ∈ Ω, v 1 ≠ (1 / 2 : ℝ)) : IsOpen (mobiusPlaneTrigCoordMap '' Ω) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases hy with ⟨v, hvΩ, hvy⟩
  have hv_ne : v 1 ≠ (1 / 2 : ℝ) := h v hvΩ
  have hΩnhds : Ω ∈ 𝓝 v := hΩ.mem_nhds hvΩ
  have hn :=
    (HasStrictFDerivAt.map_nhds_eq_of_equiv
      (hasStrictFDerivAt_mobiusPlaneTrigCoordMap_of_ne_half hv_ne))
  have hy' : mobiusPlaneTrigCoordMap '' Ω ∈ 𝓝 (mobiusPlaneTrigCoordMap v) := by
    rw [← hn, mem_map]
    exact mem_of_superset hΩnhds (subset_preimage_image _ _)
  simpa [hvy] using hy'

/-! ### Plane seam partners for `mobiusPlaneTrigCoordMap` (`SPEC_003` B3 seam) -/

/-- `v ↦ (1 + v₀, 1 - v₁)` identifies trig values with nearby plane points of negative `v₀`. -/
noncomputable def mobiusPlaneTrigSeamPartnerAdd (v : R2) : R2 :=
  EuclideanSpace.single (0 : Fin 2) (1 + v 0) + EuclideanSpace.single (1 : Fin 2) (1 - v 1)

/-- `v ↦ (v₀ - 1, 1 - v₁)` identifies trig values with nearby plane points of `v₀ > 1`. -/
noncomputable def mobiusPlaneTrigSeamPartnerSub (v : R2) : R2 :=
  EuclideanSpace.single (0 : Fin 2) (v 0 - 1) + EuclideanSpace.single (1 : Fin 2) (1 - v 1)

theorem mobiusPlaneTrigCoordMap_mobiusPlaneTrigSeamPartnerAdd (v : R2) :
    mobiusPlaneTrigCoordMap (mobiusPlaneTrigSeamPartnerAdd v) = mobiusPlaneTrigCoordMap v := by
  classical
  have hcos : Real.cos (Real.pi * (1 + v 0)) = -Real.cos (Real.pi * v 0) := by
    have hlin : Real.pi * (1 + v 0) = Real.pi * v 0 + Real.pi := by ring
    rw [hlin, Real.cos_add_pi]
  have hsin : Real.sin (Real.pi * (1 + v 0)) = -Real.sin (Real.pi * v 0) := by
    have hlin : Real.pi * (1 + v 0) = Real.pi * v 0 + Real.pi := by ring
    rw [hlin, Real.sin_add_pi]
  ext i
  dsimp [mobiusPlaneTrigCoordMap, mobiusSeamLocalMapPure, mobiusPlaneTrigSeamPartnerAdd]
  fin_cases i <;>
    simp [hcos, hsin] <;> ring

theorem mobiusPlaneTrigCoordMap_mobiusPlaneTrigSeamPartnerSub (v : R2) :
    mobiusPlaneTrigCoordMap (mobiusPlaneTrigSeamPartnerSub v) = mobiusPlaneTrigCoordMap v := by
  classical
  have hcos : Real.cos (Real.pi * (v 0 - (1 : ℝ))) = -Real.cos (Real.pi * v 0) := by
    have hlin : Real.pi * (v 0 - (1 : ℝ)) = Real.pi * v 0 - Real.pi := by ring
    rw [hlin, Real.cos_sub, Real.cos_pi, Real.sin_pi]
    ring
  have hsin : Real.sin (Real.pi * (v 0 - (1 : ℝ))) = -Real.sin (Real.pi * v 0) := by
    have hlin : Real.pi * (v 0 - (1 : ℝ)) = Real.pi * v 0 - Real.pi := by ring
    rw [hlin, Real.sin_sub, Real.cos_pi, Real.sin_pi]
    ring
  ext i
  dsimp [mobiusPlaneTrigCoordMap, mobiusSeamLocalMapPure, mobiusPlaneTrigSeamPartnerSub]
  fin_cases i <;>
    simp [hcos, hsin] <;> ring

private lemma abs_sub_coord_lt_of_mem_ball_euclideanSpace_two {u v : R2} {r : ℝ} (hr : 0 < r)
    (hu : u ∈ Metric.ball v r) (i : Fin 2) : |u i - v i| < r := by
  rw [Metric.mem_ball] at hu
  have hdsq : dist u v ^ 2 < r ^ 2 := (sq_lt_sq₀ dist_nonneg (le_of_lt hr)).2 hu
  rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_two] at hdsq
  simp_rw [Real.dist_eq, sq_abs] at hdsq
  have hi0 : (u (0 : Fin 2) - v (0 : Fin 2)) ^ 2 < r ^ 2 := by
    nlinarith [hdsq, sq_nonneg (u 1 - v 1 : ℝ)]
  have hi1 : (u (1 : Fin 2) - v (1 : Fin 2)) ^ 2 < r ^ 2 := by
    nlinarith [hdsq, sq_nonneg (u 0 - v 0 : ℝ)]
  have hi : (u i - v i) ^ 2 < r ^ 2 := by
    fin_cases i
    · exact hi0
    · exact hi1
  refine (sq_lt_sq₀ (abs_nonneg _) (le_of_lt hr)).1 ?_
  simpa [sq_abs] using hi

theorem isOpen_image_mobiusFDTrigCoord_of_isOpen_mobiusPlaneCoord_image {S : Set MobiusFundamentalDomain}
    (himg : IsOpen (mobiusPlaneCoord '' S))
    (h : ∀ ⦃p : MobiusFundamentalDomain⦄, p ∈ S → mobiusPlaneCoord p (1 : Fin 2) ≠ (1 / 2 : ℝ)) :
    IsOpen (mobiusFDTrigCoord '' S) := by
  classical
  rw [mobiusFDTrigCoord_image_eq_image_trigMap_planeCoord]
  exact isOpen_image_mobiusPlaneTrigCoordMap_of_forall_height_ne_half himg (fun v hv => by
    rcases hv with ⟨p, hp, rfl⟩
    exact h hp)

private lemma mobiusPlaneCoord_image_mobiusSeamSaturatedPatchSheetInterior_eq_aux {t₀ ε δ : ℝ}
    (hε : ε < 1 / 2) (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) :
    mobiusPlaneCoord '' (mobiusSeamSaturatedPatchSheetInterior t₀ ε δ) =
      { v : R2 | v 0 ∈ Ioo (0 : ℝ) ε ∧ v 1 ∈ Ioo (t₀ - δ) (t₀ + δ) } ∪
        { v : R2 | v 0 ∈ Ioo (1 - ε) (1 : ℝ) ∧ v 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) } := by
  classical
  have hε1 : ε < (1 : ℝ) := lt_trans hε one_half_lt_one
  have h1m : 0 < 1 - t₀ - δ := by linarith [htHi]
  have h1p : 1 - t₀ + δ < (1 : ℝ) := by linarith [htLo]
  ext v
  simp only [mem_image, mem_union, mem_setOf_eq, mem_Ioo, mobiusSeamSaturatedPatchSheetInterior,
    mem_inter_iff, mobiusSeamLeftPatch, mobiusSeamRightPatch]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨hx0, hpleft⟩ | ⟨hx1, hpright⟩
    · rcases hpleft with ⟨hxε, _ht0, _ht1, htLo', htHi'⟩
      refine Or.inl ⟨?_, ?_⟩
      · rw [mobiusPlaneCoord_apply_zero]; exact ⟨hx0, hxε⟩
      · rw [mobiusPlaneCoord_apply_one]; exact ⟨htLo', htHi'⟩
    · rcases hpright with ⟨hx1ε, _ht0, _ht1, htLo', htHi'⟩
      refine Or.inr ⟨?_, ?_⟩
      · rw [mobiusPlaneCoord_apply_zero]; exact ⟨hx1ε, hx1⟩
      · rw [mobiusPlaneCoord_apply_one]; exact ⟨htLo', htHi'⟩
  · rintro (hL | hR)
    · rcases hL with ⟨hv0, hv1⟩
      rcases hv0 with ⟨hv0L, hv0U⟩
      rcases hv1 with ⟨hv1L, hv1U⟩
      let x : Icc (0 : ℝ) 1 := ⟨v 0, ⟨le_of_lt hv0L, le_of_lt (lt_trans hv0U hε1)⟩⟩
      let y : Icc (0 : ℝ) 1 :=
        ⟨v 1, ⟨le_of_lt (lt_trans htLo hv1L), le_of_lt (lt_trans hv1U htHi)⟩⟩
      let p : MobiusFundamentalDomain := (x, y)
      have hpL : p ∈ mobiusSeamLeftPatch t₀ ε δ :=
        ⟨hv0U, lt_trans htLo hv1L, lt_trans hv1U htHi, hv1L, hv1U⟩
      have hvp : mobiusPlaneCoord p = v :=
        PiLp.ext fun i =>
          match i with
          | ⟨0, h⟩ => by
              have hi : (⟨0, h⟩ : Fin 2) = (0 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_zero, p, x]
          | ⟨1, h⟩ => by
              have hi : (⟨1, h⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_one, p, y]
      exact ⟨p, Or.inl ⟨hv0L, hpL⟩, hvp⟩
    · rcases hR with ⟨hv0, hv1⟩
      rcases hv0 with ⟨hv0L, hv0U⟩
      rcases hv1 with ⟨hv1L, hv1U⟩
      let x : Icc (0 : ℝ) 1 :=
        ⟨v 0, ⟨le_of_lt (by linarith [hv0L, hε]), le_of_lt hv0U⟩⟩
      let y : Icc (0 : ℝ) 1 :=
        ⟨v 1, ⟨le_of_lt (lt_trans h1m hv1L), le_of_lt (lt_trans hv1U h1p)⟩⟩
      let p : MobiusFundamentalDomain := (x, y)
      have hpR : p ∈ mobiusSeamRightPatch t₀ ε δ :=
        ⟨by linarith [hv0L], lt_trans h1m hv1L, lt_trans hv1U h1p, hv1L, hv1U⟩
      have hvp : mobiusPlaneCoord p = v :=
        PiLp.ext fun i =>
          match i with
          | ⟨0, h⟩ => by
              have hi : (⟨0, h⟩ : Fin 2) = (0 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_zero, p, x]
          | ⟨1, h⟩ => by
              have hi : (⟨1, h⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_one, p, y]
      exact ⟨p, Or.inr ⟨hv0U, hpR⟩, hvp⟩

/-- **Plane shadow of the full saturated seam patch** (`x` may be `0` on the left sheet or `1` on the
  right). This is a **closed-on-one-side** rectangle union in `R2`, hence **not** `IsOpen` there — the sheet
  interior uses the `Ioo`-`Ioo` cross product (`mobiusPlaneCoord_image_mobiusSeamSaturatedPatchSheetInterior_eq_aux`)
  for the open `B1` route. -/
theorem mobiusPlaneCoord_image_mobiusSeamSaturatedPatch_eq {t₀ ε δ : ℝ}
    (hε : ε < 1 / 2) (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) :
    mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ) =
      { v : R2 | v 0 ∈ Ico (0 : ℝ) ε ∧ v 1 ∈ Ioo (t₀ - δ) (t₀ + δ) } ∪
        { v : R2 | v 0 ∈ Ioc (1 - ε) (1 : ℝ) ∧ v 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) } := by
  classical
  have hε1 : ε < (1 : ℝ) := lt_trans hε one_half_lt_one
  have h1m : 0 < 1 - t₀ - δ := by linarith [htHi]
  have h1p : 1 - t₀ + δ < (1 : ℝ) := by linarith [htLo]
  have honeps : 0 < 1 - ε := sub_pos.mpr hε1
  ext v
  simp only [mem_image, mem_union, mem_setOf_eq, mem_Ico, mem_Ioc, mem_Ioo, mobiusSeamSaturatedPatch,
    mem_union, mobiusSeamLeftPatch, mobiusSeamRightPatch]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with hpL | hpR
    · rcases hpL with ⟨hxε, ht0, ht1, htLo', htHi'⟩
      refine Or.inl ⟨?_, ?_⟩
      · rw [mobiusPlaneCoord_apply_zero]
        exact ⟨p.1.property.1, hxε⟩
      · rw [mobiusPlaneCoord_apply_one]
        exact ⟨htLo', htHi'⟩
    · rcases hpR with ⟨hx1ε, ht0, ht1, htLo', htHi'⟩
      refine Or.inr ⟨?_, ?_⟩
      · rw [mobiusPlaneCoord_apply_zero]
        exact ⟨hx1ε, p.1.property.2⟩
      · rw [mobiusPlaneCoord_apply_one]
        exact ⟨htLo', htHi'⟩
  · rintro (hL | hR)
    · rcases hL with ⟨hv0, hv1⟩
      rcases hv0 with ⟨hv0Lo, hv0Hi⟩
      rcases hv1 with ⟨hv1L, hv1U⟩
      let x : Icc (0 : ℝ) 1 := ⟨v 0, ⟨hv0Lo, le_of_lt (lt_trans hv0Hi hε1)⟩⟩
      let y : Icc (0 : ℝ) 1 :=
        ⟨v 1, ⟨le_of_lt (lt_trans htLo hv1L), le_of_lt (lt_trans hv1U htHi)⟩⟩
      let p : MobiusFundamentalDomain := (x, y)
      have hpL : p ∈ mobiusSeamLeftPatch t₀ ε δ :=
        ⟨hv0Hi, lt_trans htLo hv1L, lt_trans hv1U htHi, hv1L, hv1U⟩
      have hvp : mobiusPlaneCoord p = v :=
        PiLp.ext fun i =>
          match i with
          | ⟨0, h⟩ => by
              have hi : (⟨0, h⟩ : Fin 2) = (0 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_zero, p, x]
          | ⟨1, h⟩ => by
              have hi : (⟨1, h⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_one, p, y]
      exact ⟨p, Or.inl hpL, hvp⟩
    · rcases hR with ⟨hv0, hv1⟩
      rcases hv0 with ⟨hv0Lo, hv0Hi⟩
      rcases hv1 with ⟨hv1L, hv1U⟩
      have hv0pos : 0 < v 0 := lt_trans honeps hv0Lo
      let x : Icc (0 : ℝ) 1 := ⟨v 0, ⟨le_of_lt hv0pos, hv0Hi⟩⟩
      let y : Icc (0 : ℝ) 1 :=
        ⟨v 1, ⟨le_of_lt (lt_trans h1m hv1L), le_of_lt (lt_trans hv1U h1p)⟩⟩
      let p : MobiusFundamentalDomain := (x, y)
      have hpR : p ∈ mobiusSeamRightPatch t₀ ε δ :=
        ⟨hv0Lo, lt_trans h1m hv1L, lt_trans hv1U h1p, hv1L, hv1U⟩
      have hvp : mobiusPlaneCoord p = v :=
        PiLp.ext fun i =>
          match i with
          | ⟨0, h⟩ => by
              have hi : (⟨0, h⟩ : Fin 2) = (0 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_zero, p, x]
          | ⟨1, h⟩ => by
              have hi : (⟨1, h⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
              simp_rw [hi, mobiusPlaneCoord_apply_one, p, y]
      exact ⟨p, Or.inr hpR, hvp⟩

/-- **SPEC_003 (B3 seam).** Small planar balls centered at **`(0, tₚ)`** (left sheet geometry) stay inside the
  **trig image** of the seam plane-shadow: either **directly** in the left `Ico × Ioo` rectangle, or via
  **`mobiusPlaneTrigSeamPartnerAdd`** in the right `Ioc × Ioo` rectangle. -/
private lemma mem_mobiusPlaneTrigCoordMap_image_mobiusPlaneCoord_image_seamSaturatedPatch_of_mem_ball_leftBase
    {t₀ ε δ r : ℝ} {v u : R2} {tₚ : ℝ} (_hε0 : 0 < ε) (hε : ε < 1 / 2) (_hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hv0 : v 0 = 0) (hv1 : v 1 = tₚ)
    (htp : tₚ ∈ Ioo (t₀ - δ) (t₀ + δ)) (hr0 : 0 < r)
    (hr :
      r <
        min ε
          (min (tₚ - (t₀ - δ)) ((t₀ + δ) -
            tₚ))) (hu : u ∈ Metric.ball v r) :
    mobiusPlaneTrigCoordMap u ∈
      mobiusPlaneTrigCoordMap '' (mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ)) := by
  classical
  let ηt : ℝ := min (tₚ - (t₀ - δ)) ((t₀ + δ) - tₚ)
  have hηt : 0 < ηt := by
    rcases htp with ⟨htpL, htpU⟩
    dsimp only [ηt]; refine lt_min ?_ ?_
    · linarith only [htpL]
    · linarith only [htpU]
  have hrε : r < ε := lt_of_lt_of_le hr (min_le_left _ _)
  have hrη : r < ηt := lt_of_lt_of_le hr (min_le_right _ _)
  have hball0 : |u 0 - v 0| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (0 : Fin 2)
  have hball1 : |u 1 - v 1| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (1 : Fin 2)
  rw [hv0] at hball0
  rw [hv1] at hball1
  have hη1 : ηt ≤ tₚ - (t₀ - δ) := min_le_left _ _
  have hη2 : ηt ≤ (t₀ + δ) - tₚ := min_le_right _ _
  have hplane :=
    (mobiusPlaneCoord_image_mobiusSeamSaturatedPatch_eq (t₀ := t₀) (ε := ε) (δ := δ) hε htLo htHi)
  by_cases hu0 : 0 ≤ u 0
  · have hu0abs : |u 0| < r := by simpa [abs_of_nonneg hu0, sub_eq_add_neg] using hball0
    have hu0_ltε : u 0 < ε := by
      have hu0_lt_r : u 0 < r := by
        rw [← abs_eq_self.mpr hu0]
        simpa [hv0, sub_zero] using hball0
      exact hu0_lt_r.trans hrε
    have huIco : u 0 ∈ Ico (0 : ℝ) ε := ⟨hu0, hu0_ltε⟩
    have huIoo_lo : t₀ - δ < u 1 := by
      have hl : u 1 > tₚ - r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1)]
      linarith only [hl, hη1, hrη]
    have huIoo_hi : u 1 < t₀ + δ := by
      have hl : u 1 < tₚ + r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1)]
      linarith only [hl, hη2, hrη]
    have huIoo : u 1 ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨huIoo_lo, huIoo_hi⟩
    have hu_mem : u ∈ mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ) := by
      rw [hplane]; left; exact ⟨huIco, huIoo⟩
    exact ⟨u, hu_mem, rfl⟩
  · have hu0neg : u 0 < 0 := not_le.mp hu0
    have hu0_gt_neg_r : (0 : ℝ) - r < u 0 := by
      have hball0' : |u 0| < r := by simpa [hv0, sub_zero] using hball0
      rw [abs_of_neg hu0neg] at hball0'
      linarith only [hball0']
    have hu0_gt : (0 : ℝ) - ε < u 0 := by
      have hneg : -r > -ε := neg_lt_neg_iff.mpr hrε
      linarith only [hu0_gt_neg_r, hneg]
    let w : R2 := mobiusPlaneTrigSeamPartnerAdd u
    have hwtr : mobiusPlaneTrigCoordMap w = mobiusPlaneTrigCoordMap u :=
      mobiusPlaneTrigCoordMap_mobiusPlaneTrigSeamPartnerAdd u
    have hw0 : w 0 = 1 + u 0 := by
      simp [w, mobiusPlaneTrigSeamPartnerAdd, PiLp.add_apply, EuclideanSpace.single_apply]
    have hw1 : w 1 = 1 - u 1 := by
      simp [w, mobiusPlaneTrigSeamPartnerAdd, PiLp.add_apply, EuclideanSpace.single_apply]
    have hwIoo_lo : 1 - t₀ - δ < w 1 := by
      have hs : 1 - tₚ - (1 - t₀ - δ) = t₀ + δ - tₚ := by ring
      have hl : w 1 > (1 - tₚ) - r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1), hw1]
      linarith only [hl, hη2, hrη, hs]
    have hwIoo_hi : w 1 < 1 - t₀ + δ := by
      have hs : (1 - t₀ + δ) - (1 - tₚ) = tₚ - (t₀ - δ) := by ring
      have hl : w 1 < (1 - tₚ) + r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1), hw1]
      linarith only [hl, hη1, hrη, hs]
    have hwIoo : w 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) := ⟨hwIoo_lo, hwIoo_hi⟩
    have hwIoc_lo : (1 : ℝ) - ε < w 0 := by linarith only [hw0, hu0_gt]
    have hwIoc_hi : w 0 < (1 : ℝ) := by linarith only [hw0, hu0neg]
    have hwIoc : w 0 ∈ Ioc (1 - ε) (1 : ℝ) := ⟨hwIoc_lo, hwIoc_hi.le⟩
    have hw_mem : w ∈ mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ) := by
      rw [hplane]; right; exact ⟨hwIoc, hwIoo⟩
    exact ⟨w, hw_mem, hwtr⟩

/-! ### Left-base plane ball → explicit seam lifts (for the trig chart homeomorph) -/

private lemma Ico_Ioo_of_mem_ball_leftBase_nonneg {t₀ ε δ r : ℝ} {v u : R2} {tₚ : ℝ}
    (_hε0 : 0 < ε) (_hε : ε < 1 / 2) (_hδ0 : 0 < δ) (_htLo : 0 < t₀ - δ) (_htHi : t₀ + δ < 1)
    (hv0 : v 0 = 0) (hv1 : v 1 = tₚ) (_htp : tₚ ∈ Ioo (t₀ - δ) (t₀ + δ)) (hr0 : 0 < r)
    (hr :
      r <
        min ε
          (min (tₚ - (t₀ - δ)) ((t₀ + δ) -
            tₚ))) (hu : u ∈ Metric.ball v r) (hu0 : 0 ≤ u 0) :
    u 0 ∈ Ico (0 : ℝ) ε ∧ u 1 ∈ Ioo (t₀ - δ) (t₀ + δ) := by
  classical
  let ηt : ℝ := min (tₚ - (t₀ - δ)) ((t₀ + δ) - tₚ)
  have hη1 : ηt ≤ tₚ - (t₀ - δ) := min_le_left _ _
  have hη2 : ηt ≤ (t₀ + δ) - tₚ := min_le_right _ _
  have hrε : r < ε := lt_of_lt_of_le hr (min_le_left _ _)
  have hrη : r < ηt := lt_of_lt_of_le hr (min_le_right _ _)
  have hball0 : |u 0 - v 0| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (0 : Fin 2)
  have hball1 : |u 1 - v 1| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (1 : Fin 2)
  rw [hv0] at hball0
  rw [hv1] at hball1
  have hu0abs : |u 0| < r := by simpa [abs_of_nonneg hu0, sub_eq_add_neg] using hball0
  have hu0_ltε : u 0 < ε := by
    have hu0_lt_r : u 0 < r := by
      rw [← abs_eq_self.mpr hu0]
      simpa [hv0, sub_zero] using hball0
    exact hu0_lt_r.trans hrε
  refine ⟨⟨hu0, hu0_ltε⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · have hl : u 1 > tₚ - r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1)]
    linarith only [hl, hη1, hrη]
  · have hl : u 1 < tₚ + r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1)]
    linarith only [hl, hη2, hrη]

private lemma Ioc_Ioo_partner_of_mem_ball_leftBase_neg {t₀ ε δ r : ℝ} {v u : R2} {tₚ : ℝ}
    (_hε0 : 0 < ε) (_hε : ε < 1 / 2) (_hδ0 : 0 < δ) (_htLo : 0 < t₀ - δ) (_htHi : t₀ + δ < 1)
    (hv0 : v 0 = 0) (hv1 : v 1 = tₚ) (_htp : tₚ ∈ Ioo (t₀ - δ) (t₀ + δ)) (hr0 : 0 < r)
    (hr :
      r <
        min ε
          (min (tₚ - (t₀ - δ)) ((t₀ + δ) -
            tₚ))) (hu : u ∈ Metric.ball v r) (hu0 : u 0 < 0) :
    (mobiusPlaneTrigSeamPartnerAdd u) 0 ∈ Ioc (1 - ε) (1 : ℝ) ∧
      (mobiusPlaneTrigSeamPartnerAdd u) 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) := by
  classical
  let ηt : ℝ := min (tₚ - (t₀ - δ)) ((t₀ + δ) - tₚ)
  have hη1 : ηt ≤ tₚ - (t₀ - δ) := min_le_left _ _
  have hη2 : ηt ≤ (t₀ + δ) - tₚ := min_le_right _ _
  have hrε : r < ε := lt_of_lt_of_le hr (min_le_left _ _)
  have hrη : r < ηt := lt_of_lt_of_le hr (min_le_right _ _)
  have hball0 : |u 0 - v 0| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (0 : Fin 2)
  have hball1 : |u 1 - v 1| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (1 : Fin 2)
  rw [hv0] at hball0
  rw [hv1] at hball1
  have hu0neg : u 0 < 0 := hu0
  have hu0_gt_neg_r : (0 : ℝ) - r < u 0 := by
    have hball0' : |u 0| < r := by simpa [hv0, sub_zero] using hball0
    rw [abs_of_neg hu0neg] at hball0'
    linarith only [hball0']
  have hu0_gt : (0 : ℝ) - ε < u 0 := by
    have hneg : -r > -ε := neg_lt_neg_iff.mpr hrε
    linarith only [hu0_gt_neg_r, hneg]
  let w : R2 := mobiusPlaneTrigSeamPartnerAdd u
  have hw0 : w 0 = 1 + u 0 := by
    simp [w, mobiusPlaneTrigSeamPartnerAdd, PiLp.add_apply, EuclideanSpace.single_apply]
  have hw1 : w 1 = 1 - u 1 := by
    simp [w, mobiusPlaneTrigSeamPartnerAdd, PiLp.add_apply, EuclideanSpace.single_apply]
  have hwIoo_lo : 1 - t₀ - δ < w 1 := by
    have hs : 1 - tₚ - (1 - t₀ - δ) = t₀ + δ - tₚ := by ring
    have hl : w 1 > (1 - tₚ) - r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1), hw1]
    linarith only [hl, hη2, hrη, hs]
  have hwIoo_hi : w 1 < 1 - t₀ + δ := by
    have hs : (1 - t₀ + δ) - (1 - tₚ) = tₚ - (t₀ - δ) := by ring
    have hl : w 1 < (1 - tₚ) + r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1), hw1]
    linarith only [hl, hη1, hrη, hs]
  have hwIoc_lo : (1 : ℝ) - ε < w 0 := by linarith only [hw0, hu0_gt]
  have hwIoc_hi : w 0 < (1 : ℝ) := by linarith only [hw0, hu0neg]
  refine ⟨⟨hwIoc_lo, hwIoc_hi.le⟩, ?_, ?_⟩
  · exact hwIoo_lo
  · exact hwIoo_hi

private lemma Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos {t₀ ε δ r : ℝ} {v u : R2} {tₚ : ℝ}
    (_hε0 : 0 < ε) (_hε : ε < 1 / 2) (_hδ0 : 0 < δ) (_htLo : 0 < t₀ - δ) (_htHi : t₀ + δ < 1)
    (hv0 : v 0 = 0) (hv1 : v 1 = tₚ) (htp : tₚ ∈ Ioo (t₀ - δ) (t₀ + δ)) (hr0 : 0 < r)
    (hr :
      r <
        min ε
          (min (tₚ - (t₀ - δ)) ((t₀ + δ) -
            tₚ))) (hu : u ∈ Metric.ball v r) (hu0 : u 0 ≤ 0) :
    (mobiusPlaneTrigSeamPartnerAdd u) 0 ∈ Ioc (1 - ε) (1 : ℝ) ∧
      (mobiusPlaneTrigSeamPartnerAdd u) 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) := by
  rcases le_iff_lt_or_eq.mp hu0 with hu0' | hu0'
  · exact Ioc_Ioo_partner_of_mem_ball_leftBase_neg (t₀ := t₀) (ε := ε) (δ := δ) (r := r) (v := v) (u := u)
      (tₚ := tₚ) _hε0 _hε _hδ0 _htLo _htHi hv0 hv1 htp hr0 hr hu hu0'
  have hu0z : u 0 = 0 := hu0'
  classical
  let ηt : ℝ := min (tₚ - (t₀ - δ)) ((t₀ + δ) - tₚ)
  have hη1 : ηt ≤ tₚ - (t₀ - δ) := min_le_left _ _
  have hη2 : ηt ≤ (t₀ + δ) - tₚ := min_le_right _ _
  have hrε : r < ε := lt_of_lt_of_le hr (min_le_left _ _)
  have hrη : r < ηt := lt_of_lt_of_le hr (min_le_right _ _)
  have hball1 : |u 1 - v 1| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (1 : Fin 2)
  rw [hv1] at hball1
  let w : R2 := mobiusPlaneTrigSeamPartnerAdd u
  have hw0 : w 0 = 1 + u 0 := by
    simp [w, mobiusPlaneTrigSeamPartnerAdd, PiLp.add_apply, EuclideanSpace.single_apply]
  have hw1 : w 1 = 1 - u 1 := by
    simp [w, mobiusPlaneTrigSeamPartnerAdd, PiLp.add_apply, EuclideanSpace.single_apply]
  have hwIoo_lo : 1 - t₀ - δ < w 1 := by
    have hs : 1 - tₚ - (1 - t₀ - δ) = t₀ + δ - tₚ := by ring
    have hl : w 1 > (1 - tₚ) - r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1), hw1]
    linarith only [hl, hη2, hrη, hs]
  have hwIoo_hi : w 1 < 1 - t₀ + δ := by
    have hs : (1 - t₀ + δ) - (1 - tₚ) = tₚ - (t₀ - δ) := by ring
    have hl : w 1 < (1 - tₚ) + r := by linarith [abs_lt.mp (show |u 1 - tₚ| < r from by simpa using hball1), hw1]
    linarith only [hl, hη1, hrη, hs]
  have hw0eq : w 0 = 1 := by rw [hw0, hu0z, add_zero]
  have hwIoc : w 0 ∈ Ioc (1 - ε) (1 : ℝ) := by
    rw [hw0eq]
    refine ⟨?_, le_rfl⟩
    linarith only [_hε0]
  refine ⟨hwIoc, ⟨hwIoo_lo, hwIoo_hi⟩⟩

private noncomputable def mobiusFD_of_planeIcoIoo_left {t₀ ε δ : ℝ} (hε : ε < 1) (htLo : 0 < t₀ - δ)
    (htHi : t₀ + δ < 1) (u : R2) (hIco : u 0 ∈ Ico (0 : ℝ) ε) (hIoo : u 1 ∈ Ioo (t₀ - δ) (t₀ + δ)) :
    MobiusFundamentalDomain :=
  let x : Icc (0 : ℝ) 1 :=
    ⟨u 0, ⟨hIco.1, le_of_lt (lt_trans hIco.2 hε)⟩⟩
  let y : Icc (0 : ℝ) 1 :=
    ⟨u 1, ⟨le_of_lt (lt_trans htLo hIoo.1), le_of_lt (lt_trans hIoo.2 htHi)⟩⟩
  (x, y)

private lemma mem_leftPatch_mobiusFD_of_planeIcoIoo_left {t₀ ε δ : ℝ} (hε : ε < 1) (htLo : 0 < t₀ - δ)
    (htHi : t₀ + δ < 1) (u : R2) (hIco : u 0 ∈ Ico (0 : ℝ) ε) (hIoo : u 1 ∈ Ioo (t₀ - δ) (t₀ + δ)) :
    mobiusFD_of_planeIcoIoo_left (t₀ := t₀) (ε := ε) (δ := δ) hε htLo htHi u hIco hIoo ∈
      mobiusSeamLeftPatch t₀ ε δ := by
  dsimp [mobiusFD_of_planeIcoIoo_left, mobiusSeamLeftPatch, mem_setOf_eq]
  refine ⟨hIco.2, ?_, ?_, hIoo.1, hIoo.2⟩
  · exact lt_trans htLo hIoo.1
  · exact lt_trans hIoo.2 htHi

private noncomputable def mobiusFD_of_plane_IocIoo_right {t₀ ε δ : ℝ} (hε : ε < 1) (htLo : 0 < t₀ - δ)
    (htHi : t₀ + δ < 1) (w : R2) (hIoc : w 0 ∈ Ioc (1 - ε) (1 : ℝ))
    (hIoo : w 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ)) : MobiusFundamentalDomain :=
  have hw0pos : 0 < w 0 := lt_trans (by linarith [hε] : (0 : ℝ) < 1 - ε) hIoc.1
  let x : Icc (0 : ℝ) 1 :=
    ⟨w 0, ⟨le_of_lt hw0pos, hIoc.2⟩⟩
  let y : Icc (0 : ℝ) 1 :=
    ⟨w 1,
      ⟨le_of_lt (lt_trans (by linarith [htHi] : (0 : ℝ) < 1 - t₀ - δ) hIoo.1),
        le_of_lt (lt_trans hIoo.2 (by linarith [htLo] : (1 - t₀ + δ : ℝ) < 1))⟩⟩
  (x, y)

private lemma mem_rightPatch_mobiusFD_of_plane_IocIoo_right {t₀ ε δ : ℝ} (hε : ε < 1)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (w : R2)
    (hIoc : w 0 ∈ Ioc (1 - ε) (1 : ℝ))
    (hIoo : w 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ)) :
    mobiusFD_of_plane_IocIoo_right (t₀ := t₀) (ε := ε) (δ := δ) hε htLo htHi w hIoc hIoo ∈
      mobiusSeamRightPatch t₀ ε δ := by
  rcases hIoc with ⟨hwlo, hwhi⟩
  dsimp [mobiusFD_of_plane_IocIoo_right, mobiusSeamRightPatch, mem_setOf_eq]
  refine ⟨hwlo, ?_, ?_, hIoo.1, hIoo.2⟩
  · exact lt_trans (by linarith [htHi] : (0 : ℝ) < 1 - t₀ - δ) hIoo.1
  · exact lt_trans hIoo.2 (by linarith [htLo] : (1 - t₀ + δ : ℝ) < 1)

private lemma mobiusRel₀_mobiusFD_plane_seamPartner {t₀ ε δ : ℝ} (hε : ε < 1) (htLo : 0 < t₀ - δ)
    (htHi : t₀ + δ < 1) {u : R2} (hu0 : u 0 = 0)
    (hIco : u 0 ∈ Ico (0 : ℝ) ε) (hIoo : u 1 ∈ Ioo (t₀ - δ) (t₀ + δ))
    (hIoc : (mobiusPlaneTrigSeamPartnerAdd u) 0 ∈ Ioc (1 - ε) (1 : ℝ))
    (hIoo' : (mobiusPlaneTrigSeamPartnerAdd u) 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ)) :
    mobiusRel₀
      (mobiusFD_of_planeIcoIoo_left hε htLo htHi u hIco hIoo)
      (mobiusFD_of_plane_IocIoo_right hε htLo htHi (mobiusPlaneTrigSeamPartnerAdd u) hIoc hIoo') := by
  refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
  · simp [mobiusFD_of_planeIcoIoo_left, hu0]
  · simp [mobiusFD_of_plane_IocIoo_right, mobiusPlaneTrigSeamPartnerAdd, hu0, PiLp.add_apply,
      EuclideanSpace.single_apply]
  · simp [mobiusFD_of_planeIcoIoo_left, mobiusFD_of_plane_IocIoo_right, mobiusPlaneTrigSeamPartnerAdd, hu0,
      PiLp.add_apply, EuclideanSpace.single_apply]

private lemma eq_zero_of_mem_frontier_coord0_nonneg {u : R2} (hu : u ∈ frontier {w : R2 | 0 ≤ w 0}) :
    u 0 = 0 := by
  classical
  rw [frontier, mem_diff] at hu
  rcases hu with ⟨hucl, huni⟩
  rcases lt_trichotomy (u 0) 0 with hlt | heq | hgt
  · exfalso
    have hc :
        Continuous (fun w : R2 => w 0) :=
      @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (0 : Fin 2)
    have hopen : IsOpen {w : R2 | w 0 < 0} := hc.isOpen_preimage (Iio (0 : ℝ)) isOpen_Iio
    have hmem : u ∈ {w : R2 | w 0 < 0} := hlt
    have hnU : {w : R2 | w 0 < 0} ∈ 𝓝 u := hopen.mem_nhds hmem
    rw [mem_closure_iff_nhds] at hucl
    rcases hucl _ hnU with ⟨w, hwU, hwS⟩
    simp at hwU hwS
    linarith only [hwU, hwS]
  · exact heq
  · exfalso
    have hc :
        Continuous (fun w : R2 => w 0) :=
      @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (0 : Fin 2)
    have hopen : IsOpen {w : R2 | 0 < w 0} := hc.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi
    have hmem : u ∈ {w : R2 | 0 < w 0} := hgt
    have hnU : {w : R2 | 0 < w 0} ∈ 𝓝 u := hopen.mem_nhds hmem
    have huin :
        u ∈ interior {w : R2 | 0 ≤ w 0} := by
      rw [mem_interior_iff_mem_nhds]
      refine mem_of_superset hnU ?_
      intro w hw
      simp at hw ⊢
      exact le_of_lt hw
    exact huni huin

/-- Same for a **right-sheet** basepoint **`(1, s)`** with **`s` in the `(1-t₀ ± δ)` strip**, using
  **`mobiusPlaneTrigSeamPartnerSub`** when `u₀ > 1`. -/
private lemma mem_mobiusPlaneTrigCoordMap_image_mobiusPlaneCoord_image_seamSaturatedPatch_of_mem_ball_rightBase
    {t₀ ε δ r : ℝ} {v u : R2} {s : ℝ} (_hε0 : 0 < ε) (hε : ε < 1 / 2) (_hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hv0 : v 0 = 1) (hv1 : v 1 = s)
    (hs : s ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ)) (hr0 : 0 < r)
    (hr :
      r <
        min ε
          (min (s - (1 - t₀ - δ)) ((1 - t₀ + δ) -
            s))) (hu : u ∈ Metric.ball v r) :
    mobiusPlaneTrigCoordMap u ∈
      mobiusPlaneTrigCoordMap '' (mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ)) := by
  classical
  let ηs : ℝ := min (s - (1 - t₀ - δ)) ((1 - t₀ + δ) - s)
  have hηs : 0 < ηs := by
    rcases hs with ⟨hsL, hsU⟩
    dsimp only [ηs]; refine lt_min ?_ ?_
    · linarith only [hsL]
    · linarith only [hsU]
  have hrε : r < ε := lt_of_lt_of_le hr (min_le_left _ _)
  have hrη : r < ηs := lt_of_lt_of_le hr (min_le_right _ _)
  have hball0 : |u 0 - v 0| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (0 : Fin 2)
  have hball1 : |u 1 - v 1| < r :=
    abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hr0 hu (1 : Fin 2)
  rw [hv0] at hball0
  rw [hv1] at hball1
  have hη1 : ηs ≤ s - (1 - t₀ - δ) := min_le_left _ _
  have hη2 : ηs ≤ (1 - t₀ + δ) - s := min_le_right _ _
  have hplane :=
    (mobiusPlaneCoord_image_mobiusSeamSaturatedPatch_eq (t₀ := t₀) (ε := ε) (δ := δ) hε htLo htHi)
  by_cases hu1 : u 0 ≤ 1
  · have hu0_lo : (1 : ℝ) - ε < u 0 := by
      have hl : u 0 > 1 - r := by linarith [abs_lt.mp (show |u 0 - 1| < r from by simpa using hball0)]
      linarith only [hl, hrε]
    have huIoc : u 0 ∈ Ioc (1 - ε) (1 : ℝ) := ⟨hu0_lo, hu1⟩
    have huIoo_lo : 1 - t₀ - δ < u 1 := by
      have hl : u 1 > s - r := by linarith [abs_lt.mp (show |u 1 - s| < r from by simpa using hball1)]
      linarith only [hl, hη1, hrη]
    have huIoo_hi : u 1 < 1 - t₀ + δ := by
      have hl : u 1 < s + r := by linarith [abs_lt.mp (show |u 1 - s| < r from by simpa using hball1)]
      linarith only [hl, hη2, hrη]
    have huIoo : u 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) := ⟨huIoo_lo, huIoo_hi⟩
    have hu_mem : u ∈ mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ) := by
      rw [hplane]; right; exact ⟨huIoc, huIoo⟩
    exact ⟨u, hu_mem, rfl⟩
  · have hu1' : (1 : ℝ) < u 0 := lt_of_not_ge hu1
    have hu0abs : |u 0 - 1| < r := by simpa using hball0
    have hw0_ltε : u 0 - 1 < ε := by
      have hpos : 0 < u 0 - 1 := sub_pos.mpr hu1'
      rw [abs_of_pos hpos] at hu0abs
      exact hu0abs.trans hrε
    let w : R2 := mobiusPlaneTrigSeamPartnerSub u
    have hwtr : mobiusPlaneTrigCoordMap w = mobiusPlaneTrigCoordMap u :=
      mobiusPlaneTrigCoordMap_mobiusPlaneTrigSeamPartnerSub u
    have hw0 : w 0 = u 0 - 1 := by
      simp [w, mobiusPlaneTrigSeamPartnerSub, PiLp.add_apply, EuclideanSpace.single_apply]
    have hw1 : w 1 = 1 - u 1 := by
      simp [w, mobiusPlaneTrigSeamPartnerSub, PiLp.add_apply, EuclideanSpace.single_apply]
    have hwIco : w 0 ∈ Ico (0 : ℝ) ε := by
      have hw0pos : 0 < w 0 := by linarith only [hw0, hu1']
      refine ⟨hw0pos.le, ?_⟩
      simpa [hw0] using hw0_ltε
    have hwIoo_lo : t₀ - δ < w 1 := by
      have hl : w 1 > (1 - s) - r := by
        linarith [abs_lt.mp (show |u 1 - s| < r from by simpa using hball1), hw1]
      have hm : (1 - s) - (t₀ - δ) ≥ ηs := by
        have hs2 : (1 - s) - (t₀ - δ) = (1 - t₀ + δ) - s := by ring
        rw [hs2]
        exact hη2
      linarith only [hl, hrη, hm]
    have hwIoo_hi : w 1 < t₀ + δ := by
      have hl : u 1 > s - r := by linarith [abs_lt.mp (show |u 1 - s| < r from by simpa using hball1)]
      rw [hw1]
      linarith only [hl, hη1, hrη]
    have hwIoo : w 1 ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨hwIoo_lo, hwIoo_hi⟩
    have hw_mem : w ∈ mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ) := by
      rw [hplane]; left; exact ⟨hwIco, hwIoo⟩
    exact ⟨w, hw_mem, hwtr⟩

/-- The plane shadow of the **full** saturated seam patch is **not** open in `R²`: the left sheet carries
  `x = 0` on the boundary of `Ico 0 ε`, so neighborhoods poke into `x < 0`. Matches **SPEC_003** checklist
  (B3 stays on sheet interior for the `IsOpen` / `B1` chain to `mobiusFDTrigCoord`). -/
theorem not_isOpen_mobiusPlaneCoord_image_mobiusSeamSaturatedPatch {t₀ ε δ : ℝ}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ) (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) :
    ¬ IsOpen (mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ)) := by
  classical
  have hlt1 : t₀ - δ < t₀ := by linarith only [hδ0]
  have hlt2 : t₀ < t₀ + δ := by linarith only [hδ0]
  rw [mobiusPlaneCoord_image_mobiusSeamSaturatedPatch_eq hε htLo htHi]
  let v : R2 :=
    EuclideanSpace.single (0 : Fin 2) (0 : ℝ) + EuclideanSpace.single (1 : Fin 2) t₀
  have hv0 : v 0 = 0 := by
    simp [v, PiLp.add_apply, EuclideanSpace.single_apply]
  have hv1 : v 1 = t₀ := by
    simp [v, PiLp.add_apply, EuclideanSpace.single_apply]
  have hv_mem_left :
      v ∈ { w : R2 | w 0 ∈ Ico (0 : ℝ) ε ∧ w 1 ∈ Ioo (t₀ - δ) (t₀ + δ) } := by
    refine ⟨?_, ?_⟩
    · rw [hv0]; exact ⟨le_rfl, hε0⟩
    · rw [hv1]; exact ⟨hlt1, hlt2⟩
  have hvU : v ∈
      ({ w : R2 | w 0 ∈ Ico (0 : ℝ) ε ∧ w 1 ∈ Ioo (t₀ - δ) (t₀ + δ) } ∪
        { w : R2 | w 0 ∈ Ioc (1 - ε) (1 : ℝ) ∧ w 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) }) :=
    Or.inl hv_mem_left
  rintro hO
  rcases Metric.isOpen_iff.mp hO v hvU with ⟨r, hr0, hr_ball⟩
  let w : R2 := v + EuclideanSpace.single (0 : Fin 2) (-(r / 2))
  have hw0 : w 0 = -(r / 2) := by
    simp [w, v, PiLp.add_apply, EuclideanSpace.single_apply, hv0]
  have hw1 : w 1 = t₀ := by
    simp [w, v, PiLp.add_apply, EuclideanSpace.single_apply, hv1]
  have hdist : dist w v < r := by
    rw [EuclideanSpace.dist_eq]
    have hsq : (∑ i : Fin 2, dist (w i) (v i) ^ 2) = (r / 2) ^ 2 := by
      rw [Fin.sum_univ_two]
      have h0d : dist (w 0) (v 0) = r / 2 := by
        rw [dist_eq_norm_sub]
        simp [hw0, hv0, abs_of_pos hr0]
      have h1d : dist (w 1) (v 1) = 0 := by
        rw [dist_eq_norm_sub]
        simp [hw1, hv1, sub_self, norm_zero]
      simp [h0d, h1d]
    rw [hsq, Real.sqrt_sq (half_pos hr0).le]
    linarith only [hr0]
  have hw_in_ball : w ∈ Metric.ball (α := R2) v r :=
    Metric.mem_ball.mpr hdist
  have hwU : w ∈
      ({ w : R2 | w 0 ∈ Ico (0 : ℝ) ε ∧ w 1 ∈ Ioo (t₀ - δ) (t₀ + δ) } ∪
        { w : R2 | w 0 ∈ Ioc (1 - ε) (1 : ℝ) ∧ w 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) }) :=
    hr_ball hw_in_ball
  rcases hwU with hL | hR
  · rcases hL with ⟨hwIco, _⟩
    rcases hwIco with ⟨hw0ge, _⟩
    rw [hw0] at hw0ge
    linarith only [hr0, hw0ge]
  · rcases hR with ⟨hwIoc, _⟩
    rcases hwIoc with ⟨hw0lo, _⟩
    have hone : (1 : ℝ) - ε > 1 / 2 := by linarith only [hε]
    rw [hw0] at hw0lo
    linarith only [hone, hw0lo, hr0]

theorem isOpen_mobiusPlaneCoord_image_mobiusSeamSaturatedPatchSheetInterior {t₀ ε δ : ℝ}
    (_hε0 : 0 < ε) (hε : ε < 1 / 2)
    (_hδ0 : 0 < δ) (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) :
    IsOpen (mobiusPlaneCoord '' (mobiusSeamSaturatedPatchSheetInterior t₀ ε δ)) := by
  classical
  rw [mobiusPlaneCoord_image_mobiusSeamSaturatedPatchSheetInterior_eq_aux hε htLo htHi]
  have oL0 := continuous_mobiusSeamR2_coord0.isOpen_preimage (Ioo (0 : ℝ) ε) isOpen_Ioo
  have oL1 := continuous_mobiusSeamR2_coord1.isOpen_preimage (Ioo (t₀ - δ) (t₀ + δ)) isOpen_Ioo
  have oR0 := continuous_mobiusSeamR2_coord0.isOpen_preimage (Ioo (1 - ε) (1 : ℝ)) isOpen_Ioo
  have oR1 := continuous_mobiusSeamR2_coord1.isOpen_preimage (Ioo (1 - t₀ - δ) (1 - t₀ + δ)) isOpen_Ioo
  simpa [setOf_and] using (oL0.inter oL1).union (oR0.inter oR1)

/-- **SPEC_003_NF8 (B3, interior-sheet form).** Away from the `x = 0` / `x = 1` lines in `Icc 0 1`, the
planar image of the saturated seam neighborhood is open in `R2`; with height bounded away from `½`, the
fundamental-domain trig coordinates have **open** image in `R2`.

Note: points with `x = 0` or `x = 1` in `mobiusSeamSaturatedPatch` live on the seam edges in `Icc²`; their
planar images are not interior to `mobiusPlaneCoord '' patch` in `R2`, so the **open** trig-image statement
is packaged on `mobiusSeamSaturatedPatchSheetInterior`, which is the patch used by the plane `B1` route. -/
theorem isOpen_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatchSheetInterior {t₀ ε δ : ℝ}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|) :
    IsOpen (mobiusFDTrigCoord '' (mobiusSeamSaturatedPatchSheetInterior t₀ ε δ)) :=
  isOpen_image_mobiusFDTrigCoord_of_isOpen_mobiusPlaneCoord_image
    (isOpen_mobiusPlaneCoord_image_mobiusSeamSaturatedPatchSheetInterior hε0 hε hδ0 htLo htHi)
    (fun {_} hp => mobiusPlaneCoord_height_ne_half_of_mem_mobiusSeamSaturatedPatchSheetInterior hδ₂ hp)

/-- **SPEC_003 (B3, full saturated patch).** Same `δ < |t₀ - ½|` hypothesis as the trig-injectivity
package (`injective_mobiusStripTrigCoord_on_image_quotient_mk_mobiusSeamSaturatedPatch`): every patch
point has planar height `≠ ½`, so `mobiusPlaneTrigCoordMap` is a local diffeo at each `w` in the
closed-on-one-side plane shadow; near seam lines use the left/right planar base-ball lemmas; on the
open sheet-interior rectangle use `isOpen_image_mobiusPlaneTrigCoordMap_of_forall_height_ne_half`. -/
theorem isOpen_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch {t₀ ε δ : ℝ}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|) :
    IsOpen (mobiusFDTrigCoord '' (mobiusSeamSaturatedPatch t₀ ε δ)) := by
  classical
  rw [mobiusFDTrigCoord_image_eq_image_trigMap_planeCoord]
  let P : Set R2 := mobiusPlaneCoord '' (mobiusSeamSaturatedPatch t₀ ε δ)
  let Ω : Set R2 := mobiusPlaneCoord '' (mobiusSeamSaturatedPatchSheetInterior t₀ ε δ)
  have hPeq : P =
      { v : R2 | v 0 ∈ Ico (0 : ℝ) ε ∧ v 1 ∈ Ioo (t₀ - δ) (t₀ + δ) } ∪
        { v : R2 | v 0 ∈ Ioc (1 - ε) (1 : ℝ) ∧ v 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) } :=
    mobiusPlaneCoord_image_mobiusSeamSaturatedPatch_eq hε htLo htHi
  have hΩeq : Ω =
      { v : R2 | v 0 ∈ Ioo (0 : ℝ) ε ∧ v 1 ∈ Ioo (t₀ - δ) (t₀ + δ) } ∪
        { v : R2 | v 0 ∈ Ioo (1 - ε) (1 : ℝ) ∧ v 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) } :=
    mobiusPlaneCoord_image_mobiusSeamSaturatedPatchSheetInterior_eq_aux hε htLo htHi
  have hΩo : IsOpen Ω :=
    isOpen_mobiusPlaneCoord_image_mobiusSeamSaturatedPatchSheetInterior hε0 hε hδ0 htLo htHi
  have hΩhalf :
      ∀ v ∈ Ω, v 1 ≠ (1 / 2 : ℝ) := fun v hv => by
    rcases hv with ⟨p, hp, rfl⟩
    exact mobiusPlaneCoord_height_ne_half_of_mem_mobiusSeamSaturatedPatchSheetInterior hδ₂ hp
  have hFΩ : IsOpen (mobiusPlaneTrigCoordMap '' Ω) :=
    isOpen_image_mobiusPlaneTrigCoordMap_of_forall_height_ne_half hΩo hΩhalf
  have hΩP : Ω ⊆ P := by
    rintro v ⟨p, hp, rfl⟩
    have hpS : p ∈ mobiusSeamSaturatedPatch t₀ ε δ := by
      rcases hp with hL | hR
      · exact Or.inl hL.2
      · exact Or.inr hR.2
    exact ⟨p, hpS, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases hz with ⟨w₀, hwP, hzF₀⟩
  rcases hwP with ⟨p, hp, hwp⟩
  have hw₀_eq : w₀ = mobiusPlaneCoord p := hwp.symm
  let w : R2 := mobiusPlaneCoord p
  have hzF : z = mobiusPlaneTrigCoordMap w := by
    rw [hw₀_eq] at hzF₀
    exact hzF₀.symm
  have hwP : w ∈ P := ⟨p, hp, rfl⟩
  rw [hPeq] at hwP
  rcases hwP with hwL | hwR
  · rcases hwL with ⟨hwIco, hwIoo⟩
    by_cases hw0pos : 0 < w 0
    · have hwΩ : w ∈ Ω := by
        rw [hΩeq]
        exact Or.inl ⟨⟨hw0pos, hwIco.2⟩, hwIoo⟩
      have hzmem : mobiusPlaneTrigCoordMap w ∈ mobiusPlaneTrigCoordMap '' Ω := ⟨w, hwΩ, rfl⟩
      rw [hzF]
      refine mem_of_superset (hFΩ.mem_nhds hzmem) ?_
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hΩP hx, rfl⟩
    · have hw0z : w 0 = 0 := le_antisymm (not_lt.mp hw0pos) hwIco.1
      have hw1ne : w 1 ≠ (1 / 2 : ℝ) := by
        have h := mobiusPlaneCoord_height_ne_half_of_mem_mobiusSeamSaturatedPatch hδ₂ hp
        simpa [w, mobiusPlaneCoord_apply_one p] using h
      let η : ℝ := min ε (min (w 1 - (t₀ - δ)) ((t₀ + δ) - w 1))
      have hηpos : 0 < η := by
        dsimp [η]
        refine lt_min hε0 (lt_min ?_ ?_)
        · linarith only [hwIoo.1]
        · linarith only [hwIoo.2]
      let r : ℝ := η / 2
      have hr0 : 0 < r := half_pos hηpos
      have hr_lt :
          r <
            min ε
              (min (w 1 - (t₀ - δ)) ((t₀ + δ) -
                w 1)) :=
        half_lt_self hηpos
      have hf := hasStrictFDerivAt_mobiusPlaneTrigCoordMap_of_ne_half hw1ne
      have hn := hf.map_nhds_eq_of_equiv
      have hball_mem : Metric.ball w r ∈ 𝓝 w := Metric.ball_mem_nhds w hr0
      have hsub :
          mobiusPlaneTrigCoordMap '' Metric.ball w r ⊆
            mobiusPlaneTrigCoordMap '' P := by
        rintro y ⟨u, hu, rfl⟩
        simpa [P] using
          mem_mobiusPlaneTrigCoordMap_image_mobiusPlaneCoord_image_seamSaturatedPatch_of_mem_ball_leftBase
            hε0 hε hδ0 htLo htHi (v := w) (u := u) (tₚ := w 1) hw0z rfl hwIoo hr0 hr_lt hu
      have himg_nhd : mobiusPlaneTrigCoordMap '' Metric.ball w r ∈ 𝓝 (mobiusPlaneTrigCoordMap w) := by
        rw [← hn]
        simpa [Filter.mem_map] using mem_of_superset hball_mem (subset_preimage_image _ _)
      rw [hzF]
      exact mem_of_superset himg_nhd hsub
  · rcases hwR with ⟨hwIoc, hwIoo⟩
    by_cases hw1lt : w 0 < 1
    · have hwΩ : w ∈ Ω := by
        rw [hΩeq]
        refine Or.inr ⟨?_, hwIoo⟩
        rcases hwIoc with ⟨hwlo, _⟩
        exact ⟨hwlo, hw1lt⟩
      have hzmem : mobiusPlaneTrigCoordMap w ∈ mobiusPlaneTrigCoordMap '' Ω := ⟨w, hwΩ, rfl⟩
      rw [hzF]
      refine mem_of_superset (hFΩ.mem_nhds hzmem) ?_
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hΩP hx, rfl⟩
    · have hw0one : w 0 = 1 := le_antisymm hwIoc.2 (not_lt.mp hw1lt)
      have hw1ne : w 1 ≠ (1 / 2 : ℝ) := by
        have h := mobiusPlaneCoord_height_ne_half_of_mem_mobiusSeamSaturatedPatch hδ₂ hp
        simpa [w, mobiusPlaneCoord_apply_one p] using h
      let s : ℝ := w 1
      have hs : s ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) := hwIoo
      let η : ℝ := min ε (min (s - (1 - t₀ - δ)) ((1 - t₀ + δ) - s))
      have hηpos : 0 < η := by
        dsimp [η]
        refine lt_min hε0 (lt_min ?_ ?_)
        · linarith only [hs.1]
        · linarith only [hs.2]
      let r : ℝ := η / 2
      have hr0 : 0 < r := half_pos hηpos
      have hr_lt :
          r <
            min ε
              (min (s - (1 - t₀ - δ)) ((1 - t₀ + δ) -
                s)) :=
        half_lt_self hηpos
      have hf := hasStrictFDerivAt_mobiusPlaneTrigCoordMap_of_ne_half hw1ne
      have hn := hf.map_nhds_eq_of_equiv
      have hball_mem : Metric.ball w r ∈ 𝓝 w := Metric.ball_mem_nhds w hr0
      have hsub :
          mobiusPlaneTrigCoordMap '' Metric.ball w r ⊆
            mobiusPlaneTrigCoordMap '' P := by
        rintro y ⟨u, hu, rfl⟩
        simpa [P] using
          mem_mobiusPlaneTrigCoordMap_image_mobiusPlaneCoord_image_seamSaturatedPatch_of_mem_ball_rightBase
            hε0 hε hδ0 htLo htHi (v := w) (u := u) (s := s) hw0one rfl hs hr0 hr_lt hu
      have himg_nhd : mobiusPlaneTrigCoordMap '' Metric.ball w r ∈ 𝓝 (mobiusPlaneTrigCoordMap w) := by
        rw [← hn]
        simpa [Filter.mem_map] using mem_of_superset hball_mem (subset_preimage_image _ _)
      rw [hzF]
      exact mem_of_superset himg_nhd hsub

/-- **SPEC_003_NF8 (C1).** Sheet interior near a seam height (off `x = 0,1` in `Icc`) carries an intrinsic
`R²` chart on `MobiusStrip` at the quotient class. -/
theorem chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatchSheetInterior
    {t₀ ε δ : ℝ} {p : MobiusFundamentalDomain} (_hε0 : 0 < ε) (hε : ε < 1 / 2) (_hδ0 : 0 < δ)
    (_htLo : 0 < t₀ - δ) (_htHi : t₀ + δ < 1)
    (hp : p ∈ mobiusSeamSaturatedPatchSheetInterior t₀ ε δ) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  rcases hp with hpL | hpR
  · rcases hpL with ⟨hx0, hpL⟩
    have hε1 : ε < (1 : ℝ) := lt_trans hε one_half_lt_one
    have hx1 : p.1.val < 1 := lt_trans hpL.1 hε1
    have h1 : 0 < p.1.val ∧ p.1.val < 1 := ⟨hx0, hx1⟩
    have h2 : 0 < p.2.val ∧ p.2.val < 1 := ⟨hpL.2.1, hpL.2.2.1⟩
    exact chartableR2_mobiusQuotientMk_of_Ioo_square h1 h2
  · rcases hpR with ⟨hx1, hpR⟩
    have hε1 : ε < (1 : ℝ) := lt_trans hε one_half_lt_one
    have hone_sub : 0 < 1 - ε := sub_pos.mpr hε1
    have hx0 : 0 < p.1.val := lt_trans hone_sub hpR.1
    have h1 : 0 < p.1.val ∧ p.1.val < 1 := ⟨hx0, hx1⟩
    have h2 : 0 < p.2.val ∧ p.2.val < 1 := ⟨hpR.2.1, hpR.2.2.1⟩
    exact chartableR2_mobiusQuotientMk_of_Ioo_square h1 h2

/-- **SPEC_003 (trig chart, left seam in saturated patch).** Left-patch point with **`x = 0`** (forced
  **`t ≠ ½`** by `ne_half_of_mem_mobiusSeamLeftPatch_of_delta`) uses the **strip trig coordinate** on
  **`U = π '' (mobiusSeamSaturatedPatch …)`**: open **`U`**, open trig image, small ball **`B`**, window
  **`V = (mobiusStripTrigCoord)⁻¹' B ∩ U`**, and (once the open-map step is complete) a homeomorphism
  `Subtype V ≃ₜ Subtype B ≃ₜ R²`. -/
theorem chartableR2_mobiusQuotientMk_of_mem_mobiusSeamLeftPatch_leftEdge {t₀ ε δ : ℝ}
    {p : MobiusFundamentalDomain} (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|)
    (hp : p ∈ mobiusSeamLeftPatch t₀ ε δ) (hx0 : p.1.val = 0) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  let πq := Quotient.mk mobiusSetoid
  let S := mobiusSeamSaturatedPatch t₀ ε δ
  have hpS : p ∈ S := Or.inl hp
  have hSo : IsOpen S := isOpen_mobiusSeamSaturatedPatch t₀ ε δ
  have hsat := mobiusSeamSaturatedPatch_sat hε0 hδ0 hε htLo htHi
  let U : Set MobiusStrip := πq '' S
  have hUo : IsOpen U := isOpen_mobiusQuotient_image_of_saturated S hSo hsat
  have hpU : πq p ∈ U := ⟨p, hpS, rfl⟩
  let T := mobiusFDTrigCoord '' S
  have hTo : IsOpen T :=
    isOpen_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch hε0 hε hδ0 htLo htHi hδ₂
  let y := mobiusFDTrigCoord p
  have hyT : y ∈ T := ⟨p, hpS, rfl⟩
  rcases Metric.mem_nhds_iff.mp (hTo.mem_nhds hyT) with ⟨r_big, hr_big0, hr_big_ball⟩
  let v : R2 := mobiusPlaneCoord p
  have hv0 : v 0 = 0 := by rw [mobiusPlaneCoord_apply_zero]; exact hx0
  have hv1 : v 1 = p.2.val := by rw [mobiusPlaneCoord_apply_one]
  have htp : p.2.val ∈ Ioo (t₀ - δ) (t₀ + δ) :=
    ⟨hp.2.2.2.1, hp.2.2.2.2⟩
  have hv_ne : v 1 ≠ (1 / 2 : ℝ) := by
    rw [hv1]
    exact ne_half_of_mem_mobiusSeamLeftPatch_of_delta (δ := δ) hδ₂ hp
  have hε1 : ε < (1 : ℝ) := lt_trans hε one_half_lt_one
  let η : ℝ := min ε (min (p.2.val - (t₀ - δ)) ((t₀ + δ) - p.2.val))
  have hηpos : 0 < η := by
    refine lt_min hε0 (lt_min ?_ ?_)
    · linarith only [htp.1]
    · linarith only [htp.2]
  let r_geom : ℝ := η / 2
  have hr_geom0 : 0 < r_geom := half_pos hηpos
  have hr_lt :
      r_geom <
        min ε
          (min (p.2.val - (t₀ - δ)) ((t₀ + δ) -
            p.2.val)) := by
    dsimp [η, r_geom]
    exact half_lt_self hηpos
  let τ : Set R2 := {w : R2 | 0 ≤ w 0}
  let Ball : Set R2 := Metric.ball (α := R2) v r_geom
  let Lcap : Set R2 := (Ball : Set R2) ∩ τ
  let domR : Set R2 := Ball ∩ closure τᶜ
  have mem_domR_coord_nonpos {u : R2} (hu : u ∈ domR) : u 0 ≤ 0 := by
    have hu' : u ∈ closure ({w : R2 | w 0 < 0} : Set R2) := by
      simpa [domR, τ, compl_setOf, not_le] using hu.2
    by_contra hgt
    push_neg at hgt
    have hopen : IsOpen {w : R2 | 0 < w 0} :=
      continuous_mobiusSeamR2_coord0.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi
    have hun : u ∈ {w : R2 | 0 < w 0} := hgt
    have hN : ({w : R2 | 0 < w 0} : Set R2) ∈ 𝓝 u := hopen.mem_nhds hun
    rw [mem_closure_iff_nhds] at hu'
    rcases hu' {w : R2 | 0 < w 0} hN with ⟨z, hz1, hz2⟩
    simp at hz1 hz2
    linarith
  have junkFD : MobiusFundamentalDomain := (mobiusIcc0, mobiusIcc0)
  let fL : R2 → MobiusStrip := fun u =>
    if hu : u ∈ Lcap then
      πq (mobiusFD_of_planeIcoIoo_left (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi u
        (Ico_Ioo_of_mem_ball_leftBase_nonneg (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom) (v := v)
            (u := u) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu.1 hu.2).1
        (Ico_Ioo_of_mem_ball_leftBase_nonneg (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom) (v := v)
            (u := u) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu.1 hu.2).2)
    else πq junkFD
  let fR : R2 → MobiusStrip := fun u =>
    if hu : u ∈ domR then
      have hu0 : u 0 ≤ 0 := mem_domR_coord_nonpos hu
      πq (mobiusFD_of_plane_IocIoo_right (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi
        (mobiusPlaneTrigSeamPartnerAdd u)
        (Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom)
            (v := v) (u := u) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu.1
            hu0).1
        (Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom)
            (v := v) (u := u) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu.1
            hu0).2)
    else πq junkFD
  let hf := hasStrictFDerivAt_mobiusPlaneTrigCoordMap_of_ne_half hv_ne
  let e := hf.toOpenPartialHomeomorph mobiusPlaneTrigCoordMap
  have hy_eq : y = mobiusPlaneTrigCoordMap v := by
    have : mobiusPlaneTrigCoordMap v = mobiusFDTrigCoord p :=
      mobiusPlaneTrigCoordMap_mobiusPlaneCoord_eq_mobiusFDTrigCoord p
    simp [y, v, this]
  have hy_tgt : y ∈ e.target := by
    simpa [hy_eq] using hf.image_mem_toOpenPartialHomeomorph_target (f := mobiusPlaneTrigCoordMap)
  have heY : e.symm y = v := by
    rw [hy_eq]
    simpa [hf.toOpenPartialHomeomorph_coe] using
      e.left_inv (x := v) hf.mem_toOpenPartialHomeomorph_source
  have hEv :
      ∀ᶠ w : R2 in 𝓝 y,
        w ∈ Metric.ball y r_big ∧ w ∈ e.target ∧ e.symm w ∈ Ball ∧
          mobiusPlaneTrigCoordMap (e.symm w) = w := by
    refine Filter.Eventually.and (Filter.eventually_of_mem (Metric.ball_mem_nhds y hr_big0) fun w hw => hw) ?_
    refine Filter.Eventually.and (Filter.eventually_of_mem (IsOpen.mem_nhds e.open_target hy_tgt) fun w hw => hw) ?_
    refine
      Filter.Eventually.and
        ((e.continuousAt_symm hy_tgt).tendsto.eventually_mem
          (show Metric.ball v r_geom ∈ 𝓝 (e.symm y) by simpa [heY] using Metric.ball_mem_nhds v hr_geom0)) ?_
    simpa [hy_eq] using hf.eventually_right_inverse
  obtain ⟨r_trig, hr_trig0, hr_trig⟩ :=
    (@Metric.nhds_basis_ball R2 _ y).eventually_iff.mp hEv
  let B : Set R2 := Metric.ball y r_trig
  have hB_big : B ⊆ Metric.ball y r_big := fun z hz => (hr_trig hz).1
  have hBT : B ⊆ T := fun z hz => hr_big_ball (hB_big hz)
  have hBo : IsOpen B := Metric.isOpen_ball
  have hB_tgt : B ⊆ e.target := fun z hz => (hr_trig hz).2.1
  have hB_inv : ∀ {z : R2}, z ∈ B → e.symm z ∈ Ball := by
    intro z hz
    exact (hr_trig hz).2.2.1
  have hB_rinv :
      ∀ {z : R2}, z ∈ B → mobiusPlaneTrigCoordMap (e.symm z) = z := by
    intro z hz
    exact (hr_trig hz).2.2.2
  let Vpre := mobiusStripTrigCoord ⁻¹' B
  have hVpreo : IsOpen Vpre := continuous_mobiusStripTrigCoord.isOpen_preimage B hBo
  let V : Set MobiusStrip := Vpre ∩ U
  have hVo : IsOpen V := hVpreo.inter hUo
  have hpV : πq p ∈ V := by
    constructor
    · rw [mem_preimage]
      have hid : mobiusStripTrigCoord (πq p) = mobiusFDTrigCoord p := by
        simp [πq, mobiusStripTrigCoord]
      rw [hid]
      exact Metric.mem_ball_self hr_trig0
    · exact hpU
  have hη_sub : η ≤ ε := min_le_left _ _
  have hr_geom_le :
      r_geom ≤
        min ε
          (min (p.2.val - (t₀ - δ)) ((t₀ + δ) -
            p.2.val)) := by
    simpa [η] using hr_lt.le
  have hLR_agree :
      ∀ a ∈ Ball ∩ frontier τ, fL a = fR a := by
    intro a haτ
    have ha0 : a 0 = 0 := eq_zero_of_mem_frontier_coord0_nonneg haτ.2
    have haτ_mem : a ∈ Lcap :=
      ⟨haτ.1, show 0 ≤ a 0 by rw [ha0]⟩
    have haclτc : a ∈ closure τᶜ := by
      have hfr : a ∈ closure τ ∩ closure τᶜ := by
        simpa [frontier_eq_closure_inter_closure (s := τ)] using haτ.2
      exact hfr.2
    have hadomR : a ∈ domR := ⟨haτ.1, haclτc⟩
    have hfLa :
        fL a =
          πq
            (mobiusFD_of_planeIcoIoo_left (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi a
              (Ico_Ioo_of_mem_ball_leftBase_nonneg (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom)
                  (v := v) (u := a) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0
                  hr_lt haτ.1 (show 0 ≤ a 0 by rw [ha0])).1
              (Ico_Ioo_of_mem_ball_leftBase_nonneg (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom)
                  (v := v) (u := a) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0
                  hr_lt haτ.1 (show 0 ≤ a 0 by rw [ha0])).2) := by
      classical
      dsimp [fL]
      rw [dif_pos haτ_mem]
    have hfRa :
        fR a =
          πq
            (mobiusFD_of_plane_IocIoo_right (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi
              (mobiusPlaneTrigSeamPartnerAdd a)
              (Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ)
                  (r := r_geom) (v := v) (u := a) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp
                  hr_geom0 hr_lt haτ.1 (show a 0 ≤ 0 by rw [ha0])).1
              (Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ)
                  (r := r_geom) (v := v) (u := a) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp
                  hr_geom0 hr_lt haτ.1 (show a 0 ≤ 0 by rw [ha0])).2) := by
      classical
      dsimp [fR]
      rw [dif_pos hadomR]
    rw [hfLa, hfRa]
    have hIcoIoo :=
      Ico_Ioo_of_mem_ball_leftBase_nonneg (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom) (v := v)
        (u := a) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt haτ.1
        (show 0 ≤ a 0 by rw [ha0])
    have hIocIoo :=
      Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom)
        (v := v) (u := a) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt haτ.1
        (show a 0 ≤ 0 by rw [ha0])
    refine
      Quotient.sound
        (mobiusRel₀_mobiusFD_plane_seamPartner (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi ha0
          hIcoIoo.1 hIcoIoo.2 hIocIoo.1 hIocIoo.2)
  let gL : Subtype Lcap → MobiusFundamentalDomain := fun z =>
    have hx := z.property
    have hu_ball : z.val ∈ Metric.ball v r_geom := hx.1
    have hτ : z.val ∈ τ := hx.2
    have hu0 : 0 ≤ z.val 0 := by simpa [τ, mem_setOf] using hτ
    let hi :=
      Ico_Ioo_of_mem_ball_leftBase_nonneg (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom) (v := v)
        (u := z.val) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu_ball hu0
    mobiusFD_of_planeIcoIoo_left (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi z.val hi.1 hi.2
  have hLre : Continuous gL := by
    have hfst :
        Continuous fun z : Subtype Lcap => (gL z).1.val := by
      have hmap :
          (fun z : Subtype Lcap => (gL z).1.val) = fun z : Subtype Lcap => z.val 0 := by
        funext z
        simp [gL, mobiusFD_of_planeIcoIoo_left]
      rw [hmap]
      exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 0).comp continuous_subtype_val
    have hsnd :
        Continuous fun z : Subtype Lcap => (gL z).2.val := by
      have hmap :
          (fun z : Subtype Lcap => (gL z).2.val) = fun z : Subtype Lcap => z.val 1 := by
        funext z
        simp [gL, mobiusFD_of_planeIcoIoo_left]
      rw [hmap]
      exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 1).comp continuous_subtype_val
    exact
      Continuous.prodMk (Continuous.subtype_mk hfst fun z => (gL z).1.property)
        (Continuous.subtype_mk hsnd fun z => (gL z).2.property)
  let gR : Subtype domR → MobiusFundamentalDomain := fun x =>
    have hBall : x.val ∈ Metric.ball v r_geom := x.property.1
    have hu0 : x.val 0 ≤ 0 := mem_domR_coord_nonpos x.property
    let hi :=
      Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom) (v := v)
        (u := x.val) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hBall hu0
    mobiusFD_of_plane_IocIoo_right (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi (mobiusPlaneTrigSeamPartnerAdd x.val)
      hi.1 hi.2
  have hRre : Continuous gR := by
    have hsingle (i : Fin 2) :
        Continuous fun a : ℝ => EuclideanSpace.single i a :=
      (Isometry.uniformContinuous (Isometry.of_dist_eq (EuclideanSpace.dist_single_same i))).continuous
    have hω : Continuous mobiusPlaneTrigSeamPartnerAdd := by
      dsimp [mobiusPlaneTrigSeamPartnerAdd]
      refine Continuous.add ?_ ?_
      · refine (hsingle 0).comp (continuous_const.add (@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 0))
      · refine (hsingle 1).comp (continuous_const.sub (@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 1))
    have hωdom : Continuous fun z : Subtype domR => mobiusPlaneTrigSeamPartnerAdd z.val :=
      hω.comp continuous_subtype_val
    have hfst :
        Continuous fun z : Subtype domR => (gR z).1.val := by
      have hmap :
          (fun z : Subtype domR => (gR z).1.val) =
            fun z : Subtype domR => (mobiusPlaneTrigSeamPartnerAdd z.val) 0 := by
        funext z
        simp [gR, mobiusFD_of_plane_IocIoo_right]
      rw [hmap]
      exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 0).comp hωdom
    have hsnd :
        Continuous fun z : Subtype domR => (gR z).2.val := by
      have hmap :
          (fun z : Subtype domR => (gR z).2.val) =
            fun z : Subtype domR => (mobiusPlaneTrigSeamPartnerAdd z.val) 1 := by
        funext z
        simp [gR, mobiusFD_of_plane_IocIoo_right]
      rw [hmap]
      exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 1).comp hωdom
    exact
      Continuous.prodMk (Continuous.subtype_mk hfst fun z => (gR z).1.property)
        (Continuous.subtype_mk hsnd fun z => (gR z).2.property)
  have hfLe : Lcap.restrict fL = πq ∘ gL := by
    funext ⟨x_val, hx⟩
    change fL x_val = πq (gL ⟨x_val, hx⟩)
    dsimp [fL, gL]
    rw [dif_pos hx]
  have hτcl : IsClosed τ :=
    IsClosed.preimage continuous_mobiusSeamR2_coord0 isClosed_Ici
  have hτ_eq_closure : closure τ = τ :=
    hτcl.closure_eq
  have hcontLf :
      ContinuousOn fL (Ball ∩ closure τ) := by
    simpa [Lcap, hτ_eq_closure] using
      (continuousOn_iff_continuous_restrict.2 (hfLe ▸ continuous_mobiusQuot.comp hLre))
  have hfRe : domR.restrict fR = πq ∘ gR := by
    funext ⟨x_val, hx⟩
    change fR x_val = πq (gR ⟨x_val, hx⟩)
    dsimp [fR, gR]
    rw [dif_pos hx]
  have hcontRf : ContinuousOn fR (Ball ∩ closure τᶜ) :=
    continuousOn_iff_continuous_restrict.2 (hfRe ▸ continuous_mobiusQuot.comp hRre)
  have hσ : (τ.piecewise fL fR) = (fun u => τ.piecewise fL fR u) := rfl
  have hpiece :
      τ.piecewise fL fR =
        (fun u : R2 =>
          if u ∈ τ then fL u else fR u) := by
    funext u
    by_cases h : u ∈ τ <;> simp [Set.piecewise, h]
  have hσBall : ContinuousOn (τ.piecewise fL fR) Ball := by
    rw [hpiece]
    exact
      ContinuousOn.piecewise (s := Ball) (t := τ) hLR_agree hcontLf hcontRf
  let σ := τ.piecewise fL fR
  have hσ_trig :
      ∀ {u : R2}, u ∈ Ball → mobiusStripTrigCoord (σ u) = mobiusPlaneTrigCoordMap u := by
    intro u hu
    by_cases huτ : u ∈ τ
    · have hpw : σ u = fL u := by dsimp [σ]; exact Set.piecewise_eq_of_mem τ fL fR huτ
      rw [hpw]
      have huI : u ∈ Lcap := ⟨hu, huτ⟩
      dsimp [fL]
      rw [dif_pos huI]
      let hi :=
        Ico_Ioo_of_mem_ball_leftBase_nonneg hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu
          (show 0 ≤ u 0 by simpa [τ, mem_setOf] using huτ)
      let q := mobiusFD_of_planeIcoIoo_left hε1 htLo htHi u hi.1 hi.2
      have hqμ : mobiusPlaneCoord q = u := by
        refine PiLp.ext ?_
        intro i
        fin_cases i <;>
          simp [q, mobiusPlaneCoord, mobiusFD_of_planeIcoIoo_left, PiLp.add_apply,
            EuclideanSpace.single_apply]
      calc
        mobiusStripTrigCoord (πq q) = mobiusFDTrigCoord q := by
          simp [mobiusStripTrigCoord, πq]
        _ = mobiusPlaneTrigCoordMap (mobiusPlaneCoord q) :=
          (mobiusPlaneTrigCoordMap_mobiusPlaneCoord_eq_mobiusFDTrigCoord q).symm
        _ = mobiusPlaneTrigCoordMap u := by rw [hqμ]
    · have hpw : σ u = fR u := by dsimp [σ]; exact Set.piecewise_eq_of_notMem τ fL fR huτ
      rw [hpw]
      have hu0 : u 0 < 0 := not_le.mp huτ
      have huD : u ∈ domR := ⟨hu, subset_closure (show u ∈ τᶜ by simpa [τ, compl_setOf, not_le] using hu0)⟩
      have huR : u ∈ domR := huD
      have hu0' : u 0 ≤ 0 := le_of_lt hu0
      simp [fR, huR, mobiusStripTrigCoord, πq]
      let pR :=
        mobiusFD_of_plane_IocIoo_right (t₀ := t₀) (ε := ε) (δ := δ) hε1 htLo htHi (mobiusPlaneTrigSeamPartnerAdd u)
          (Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom)
              (v := v) (u := u) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu
              hu0').1
          (Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos (t₀ := t₀) (ε := ε) (δ := δ) (r := r_geom)
              (v := v) (u := u) (tₚ := p.2.val) hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu
              hu0').2
      have hcoord : mobiusPlaneCoord pR = mobiusPlaneTrigSeamPartnerAdd u := by
        refine PiLp.ext ?_
        intro i
        fin_cases i <;>
          simp [pR, mobiusFD_of_plane_IocIoo_right, mobiusPlaneCoord, mobiusPlaneTrigSeamPartnerAdd,
            PiLp.add_apply, EuclideanSpace.single_apply]
      calc
        mobiusFDTrigCoord pR = mobiusPlaneTrigCoordMap (mobiusPlaneCoord pR) :=
          (mobiusPlaneTrigCoordMap_mobiusPlaneCoord_eq_mobiusFDTrigCoord pR).symm
        _ = mobiusPlaneTrigCoordMap (mobiusPlaneTrigSeamPartnerAdd u) := by rw [hcoord]
        _ = mobiusPlaneTrigCoordMap u := mobiusPlaneTrigCoordMap_mobiusPlaneTrigSeamPartnerAdd u
  have hσ_mem_patch :
      ∀ {u : R2}, u ∈ Ball → σ u ∈ U := by
    intro u hu
    by_cases huτ : u ∈ τ
    · have huI : u ∈ Lcap := ⟨hu, huτ⟩
      simp [σ, Set.piecewise_eq_of_mem _ _ _ huτ, fL, huI, πq]
      let hiτ :=
        Ico_Ioo_of_mem_ball_leftBase_nonneg hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu
          (show 0 ≤ u 0 by simpa [τ, mem_setOf] using huτ)
      let q := mobiusFD_of_planeIcoIoo_left hε1 htLo htHi u hiτ.1 hiτ.2
      have hqL : q ∈ mobiusSeamLeftPatch t₀ ε δ :=
        mem_leftPatch_mobiusFD_of_planeIcoIoo_left hε1 htLo htHi u hiτ.1 hiτ.2
      exact ⟨q, Or.inl hqL, rfl⟩
    · have hu0 : u 0 < 0 := not_le.mp huτ
      have huD : u ∈ domR := ⟨hu, subset_closure (show u ∈ τᶜ by simpa [τ, compl_setOf, not_le] using hu0)⟩
      have hu0' : u 0 ≤ 0 := le_of_lt hu0
      simp [σ, Set.piecewise_eq_of_notMem _ _ _ huτ, fR, huD, πq]
      let hiR :=
        Ioc_Ioo_partner_of_mem_ball_leftBase_nonpos hε0 hε hδ0 htLo htHi hv0 hv1 htp hr_geom0 hr_lt hu hu0'
      let q := mobiusFD_of_plane_IocIoo_right hε1 htLo htHi (mobiusPlaneTrigSeamPartnerAdd u) hiR.1 hiR.2
      have hqR : q ∈ mobiusSeamRightPatch t₀ ε δ :=
        mem_rightPatch_mobiusFD_of_plane_IocIoo_right hε1 htLo htHi (mobiusPlaneTrigSeamPartnerAdd u) hiR.1
          hiR.2
      exact ⟨q, Or.inr hqR, rfl⟩
  let equivVB : Equiv (Subtype B) (Subtype V) :=
    { toFun := fun w =>
        have hwball := hB_inv w.property
        have hmemV : σ (e.symm w.val) ∈ V := by
          constructor
          · rw [mem_preimage, hσ_trig hwball, hB_rinv w.property]
            exact w.property
          · exact hσ_mem_patch hwball
        ⟨σ (e.symm w.val), hmemV⟩
      invFun := fun z => ⟨mobiusStripTrigCoord z.val, z.property.1⟩
      left_inv := fun w => Subtype.ext (by
        exact (hσ_trig (hB_inv w.property)).trans (hB_rinv w.property))
      right_inv := fun z => by
        rcases z with ⟨z_val, hzV⟩
        let t := mobiusStripTrigCoord z_val
        have hzB : t ∈ B := hzV.1
        have hball := hB_inv hzB
        have hzU : z_val ∈ U := hzV.2
        have hτeq :
            mobiusStripTrigCoord (σ (e.symm t)) = mobiusStripTrigCoord z_val := by
          calc
            mobiusStripTrigCoord (σ (e.symm t)) = mobiusPlaneTrigCoordMap (e.symm t) := hσ_trig hball
            _ = t := hB_rinv hzB
            _ = mobiusStripTrigCoord z_val := rfl
        have hinj :=
          injective_mobiusStripTrigCoord_on_image_quotient_mk_mobiusSeamSaturatedPatch hε0 hε hδ0 htLo htHi
            hδ₂
        have htrig :
            (fun x : Subtype U => mobiusStripTrigCoord x) ⟨σ (e.symm t), hσ_mem_patch hball⟩ =
              (fun x : Subtype U => mobiusStripTrigCoord x) ⟨z_val, hzU⟩ := by
          simpa [Subtype.val, Function.comp_apply] using hτeq
        have hstrip : σ (e.symm t) = z_val := congrArg Subtype.val (hinj htrig)
        exact Subtype.ext hstrip
  }
  have hσcont : ContinuousOn σ Ball := hσBall
  have hemap :
      Continuous fun (w : Subtype B) => e.symm w.val :=
    e.continuousOn_symm.comp_continuous continuous_subtype_val fun w => hB_tgt w.property
  have hσemap : Continuous fun (w : Subtype B) => σ (e.symm w.val) :=
    hσcont.comp_continuous hemap fun w => hB_inv w.property
  have hcontBVinv : Continuous fun (w : Subtype B) => (equivVB w : Subtype V) :=
    Continuous.subtype_mk hσemap fun w => by
      have hwball := hB_inv w.property
      constructor
      · rw [mem_preimage, hσ_trig hwball, hB_rinv w.property]
        exact w.property
      · exact hσ_mem_patch hwball
  have hcontBVto : Continuous fun (z : Subtype V) => (equivVB.symm z : Subtype B) :=
    Continuous.subtype_mk (continuous_mobiusStripTrigCoord.comp continuous_subtype_val) fun z => z.property.1
  let ψ : Subtype V ≃ₜ Subtype B :=
    Homeomorph.mk equivVB.symm hcontBVto hcontBVinv
  let φ : Subtype V ≃ₜ R2 := ψ.trans (homeomorph_subtype_ball_R2 y hr_trig0)
  exact chartableR2_of_open_embeds_plane (Quotient.mk mobiusSetoid p) hVo hpV ⟨φ⟩

/-- For a `mobiusRel₀`-invariant function `f` that equals `mobiusPlaneCoord` on a left sub-patch
  and `seamPartnerSub ∘ mobiusPlaneCoord` on a right sub-patch, and an open saturated `S'`,
  the Quotient.lift of `f` is continuous on `πq '' S'`. -/
private lemma continuous_quotientLift_unfold_on_saturatedImage
    {f : MobiusFundamentalDomain → R2}
    (hf_rel : ∀ a b, @Setoid.r _ mobiusSetoid a b → f a = f b)
    {S' : Set MobiusFundamentalDomain}
    (hS'o : IsOpen S')
    (hS'sat : ∀ ⦃x y : MobiusFundamentalDomain⦄, x ∈ S' → mobiusRel₀ x y → y ∈ S')
    (hf_left : ∀ q, q ∈ S' → q ∈ mobiusSeamLeftPatch (1/2 : ℝ) (1/4) (1/4) → f q = mobiusPlaneCoord q)
    (hf_right : ∀ q, q ∈ S' → q ∈ mobiusSeamRightPatch (1/2 : ℝ) (1/4) (1/4) →
        f q = mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q))
    (hS'_cover : ∀ q, q ∈ S' → q ∈ mobiusSeamLeftPatch (1/2 : ℝ) (1/4) (1/4) ∨
        q ∈ mobiusSeamRightPatch (1/2 : ℝ) (1/4) (1/4)) :
    Continuous (fun z : Subtype (Quotient.mk mobiusSetoid '' S') =>
      Quotient.lift f hf_rel z.val) := by
  let πq := Quotient.mk mobiusSetoid
  let g := Quotient.lift f hf_rel
  let V := πq '' S'
  rw [continuous_def]; intro W hW; rw [isOpen_induced_iff]
  refine ⟨{z : MobiusStrip | z ∈ V ∧ g z ∈ W}, ?_, ?_⟩
  · have hsingle (i : Fin 2) : Continuous fun a : ℝ => EuclideanSpace.single i a :=
      (Isometry.uniformContinuous (Isometry.of_dist_eq (EuclideanSpace.dist_single_same i))).continuous
    have hPartnerSub : Continuous mobiusPlaneTrigSeamPartnerSub := Continuous.add
      ((hsingle 0).comp ((@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 0).sub continuous_const))
      ((hsingle 1).comp (continuous_const.sub (@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 1)))
    have hLP := isOpen_mobiusSeamLeftPatch (1/2 : ℝ) (1/4) (1/4)
    have hRP := isOpen_mobiusSeamRightPatch (1/2 : ℝ) (1/4) (1/4)
    have himg_eq : {z : MobiusStrip | z ∈ V ∧ g z ∈ W} =
        πq '' {q | q ∈ S' ∧ f q ∈ W} := by
      ext z; constructor
      · rintro ⟨⟨q, hqS', rfl⟩, hzW⟩; exact ⟨q, ⟨hqS', hzW⟩, rfl⟩
      · rintro ⟨q, ⟨hqS', hqW⟩, rfl⟩; exact ⟨⟨q, hqS', rfl⟩, hqW⟩
    rw [himg_eq]
    have hSW_eq : {q : MobiusFundamentalDomain | q ∈ S' ∧ f q ∈ W} =
        (mobiusSeamLeftPatch (1/2 : ℝ) (1/4) (1/4) ∩ S' ∩ mobiusPlaneCoord ⁻¹' W) ∪
        (mobiusSeamRightPatch (1/2 : ℝ) (1/4) (1/4) ∩ S' ∩
          (mobiusPlaneTrigSeamPartnerSub ∘ mobiusPlaneCoord) ⁻¹' W) := by
      ext q; simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_preimage, Function.comp]
      constructor
      · rintro ⟨hqS', hqW⟩
        rcases hS'_cover q hqS' with hL | hR
        · left; exact ⟨⟨hL, hqS'⟩, (hf_left q hqS' hL) ▸ hqW⟩
        · right; exact ⟨⟨hR, hqS'⟩, (hf_right q hqS' hR) ▸ hqW⟩
      · rintro (⟨⟨hL, hqS'⟩, hW'⟩ | ⟨⟨hR, hqS'⟩, hW'⟩)
        · exact ⟨hqS', (hf_left q hqS' hL) ▸ hW'⟩
        · exact ⟨hqS', (hf_right q hqS' hR) ▸ hW'⟩
    have hSW_open : IsOpen {q : MobiusFundamentalDomain | q ∈ S' ∧ f q ∈ W} := by
      rw [hSW_eq]
      exact ((hLP.inter hS'o).inter (hW.preimage continuous_mobiusPlaneCoord)).union
        ((hRP.inter hS'o).inter (hW.preimage (hPartnerSub.comp continuous_mobiusPlaneCoord)))
    have hSW_sat : ∀ ⦃x y⦄, x ∈ {q | q ∈ S' ∧ f q ∈ W} → mobiusRel₀ x y →
        y ∈ {q | q ∈ S' ∧ f q ∈ W} := by
      intro x y ⟨hxS', hxW⟩ hxy; exact ⟨hS'sat hxS' hxy, hf_rel x y hxy ▸ hxW⟩
    exact isOpen_mobiusQuotient_image_of_saturated _ hSW_open hSW_sat
  · ext ⟨z, hz⟩
    simp only [mem_preimage, Subtype.coe_mk, mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-- **SPEC_003 (Phase E, left seam equator).** Chart at `⟦(0, ½)⟧` via piecewise-linear
  unfolding on `mobiusSeamSaturatedPatch (1/2) (1/4) (1/4)`.

  The **FD unfolding map** `unfoldFD q` returns `mobiusPlaneCoord q` when `q.1 ≤ ½` and
  `mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q)` otherwise. This is `mobiusRel₀`-invariant
  (both formulas agree on `(0,t)~(1,1−t)`), hence lifts to `mobiusStripUnfold : MobiusStrip → R2`.
  Restricted to `U = π '' (mobiusSeamSaturatedPatch (1/2) (1/4) (1/4))` it is continuous and
  injective, giving a homeomorphism with the open rectangle `(−¼,¼)×(¼,¾) ≃ R²`. -/
theorem chartableR2_mobiusQuotientMk_of_left_seam_half {p : MobiusFundamentalDomain}
    (hp0 : p.1.val = 0) (hth : p.2.val = 1 / 2) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  let πq := Quotient.mk mobiusSetoid
  let t₀ : ℝ := 1 / 2
  let ε : ℝ := 1 / 4
  let δ : ℝ := 1 / 4
  have hε0 : (0 : ℝ) < ε := by norm_num
  have hε : ε < 1 / 2 := by norm_num
  have hδ0 : (0 : ℝ) < δ := by norm_num
  have htLo : (0 : ℝ) < t₀ - δ := by norm_num
  have htHi : t₀ + δ < (1 : ℝ) := by norm_num
  have hε1 : ε < (1 : ℝ) := by norm_num
  let S := mobiusSeamSaturatedPatch t₀ ε δ
  have hSo : IsOpen S := isOpen_mobiusSeamSaturatedPatch t₀ ε δ
  have hsat := mobiusSeamSaturatedPatch_sat hε0 hδ0 hε htLo htHi
  let U : Set MobiusStrip := πq '' S
  have hUo : IsOpen U := isOpen_mobiusQuotient_image_of_saturated S hSo hsat
  have hpS : p ∈ S := Or.inl ⟨by rw [hp0]; norm_num, by rw [hth]; norm_num,
    by rw [hth]; norm_num, by rw [hth]; norm_num, by rw [hth]; norm_num⟩
  have hpU : πq p ∈ U := ⟨p, hpS, rfl⟩
  -- FD-level unfolding: project left sheet to itself, right sheet to its seam partner coords
  let unfoldFD : MobiusFundamentalDomain → R2 := fun q =>
    if q.1.val ≤ 1 / 2 then mobiusPlaneCoord q
    else mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q)
  have hunfold_rel : ∀ {a b : MobiusFundamentalDomain}, mobiusRel₀ a b → unfoldFD a = unfoldFD b := by
    intro a b hr
    rcases hr with rfl | hglue
    · rfl
    · rcases hglue with ⟨ha0, hb1, hs⟩ | ⟨hb0, ha1, hs⟩
      · -- (0, t) ~ (1, 1-t)
        simp only [unfoldFD, ha0, hb1]
        norm_num
        simp [mobiusPlaneTrigSeamPartnerSub, mobiusPlaneCoord, PiLp.add_apply,
          EuclideanSpace.single_apply]
        ext i; fin_cases i <;> simp [PiLp.add_apply, EuclideanSpace.single_apply,
          ha0, hb1]; linarith [hs]
      · -- (1, t) ~ (0, 1-t)
        simp only [unfoldFD, ha1, hb0]
        norm_num
        simp [mobiusPlaneTrigSeamPartnerSub, mobiusPlaneCoord, PiLp.add_apply,
          EuclideanSpace.single_apply]
        ext i; fin_cases i <;> simp [PiLp.add_apply, EuclideanSpace.single_apply,
          ha1, hb0]; linarith [hs]
  let mobiusStripUnfold : MobiusStrip → R2 :=
    Quotient.lift unfoldFD fun a b hr => hunfold_rel hr
  have hunfold_quot (q : MobiusFundamentalDomain) :
      mobiusStripUnfold (πq q) = unfoldFD q := rfl
  -- Continuity of unfoldFD on the saturated patch S
  have hunfoldFD_contL :
      Continuous fun q : Subtype (mobiusSeamLeftPatch t₀ ε δ) => unfoldFD q.val := by
    have hle : ∀ q : Subtype (mobiusSeamLeftPatch t₀ ε δ), q.val.1.val ≤ 1 / 2 := fun q => by
      have := q.2.1; dsimp [ε] at this; linarith
    have : (fun q : Subtype (mobiusSeamLeftPatch t₀ ε δ) => unfoldFD q.val) =
        fun q => mobiusPlaneCoord q.val := by
      funext q; simp only [unfoldFD]; rw [if_pos (hle q)]
    rw [this]
    exact continuous_mobiusPlaneCoord.comp continuous_subtype_val
  have hunfoldFD_contR :
      Continuous fun q : Subtype (mobiusSeamRightPatch t₀ ε δ) => unfoldFD q.val := by
    have hgt : ∀ q : Subtype (mobiusSeamRightPatch t₀ ε δ), ¬ q.val.1.val ≤ 1 / 2 := fun q => by
      have := q.2.1; dsimp [ε] at this; push_neg; linarith
    simp only [unfoldFD]
    have : (fun q : Subtype (mobiusSeamRightPatch t₀ ε δ) => unfoldFD q.val) =
        fun q => mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q.val) := by
      funext q; simp only [unfoldFD]; rw [if_neg (hgt q)]
    rw [this]
    have hsingle (i : Fin 2) : Continuous fun a : ℝ => EuclideanSpace.single i a :=
      (Isometry.uniformContinuous (Isometry.of_dist_eq (EuclideanSpace.dist_single_same i))).continuous
    have hPartnerSub : Continuous mobiusPlaneTrigSeamPartnerSub := by
      dsimp [mobiusPlaneTrigSeamPartnerSub]
      exact Continuous.add
        ((hsingle 0).comp ((@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 0).sub continuous_const))
        ((hsingle 1).comp (continuous_const.sub (@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 1)))
    exact hPartnerSub.comp (continuous_mobiusPlaneCoord.comp continuous_subtype_val)
  -- Now build the piecewise section σ : Ball → MobiusStrip
  let τ : Set R2 := {w : R2 | 0 ≤ w 0}
  let v : R2 := mobiusPlaneCoord p
  have hv0 : v 0 = 0 := by rw [mobiusPlaneCoord_apply_zero]; exact hp0
  have hv1 : v 1 = 1 / 2 := by rw [mobiusPlaneCoord_apply_one]; exact hth
  let Ball : Set R2 := Metric.ball (α := R2) v ε
  let Lcap : Set R2 := Ball ∩ τ
  let domR : Set R2 := Ball ∩ closure τᶜ
  have mem_domR_coord_nonpos {u : R2} (hu : u ∈ domR) : u 0 ≤ 0 := by
    have hu' : u ∈ closure ({w : R2 | w 0 < 0} : Set R2) := by
      simpa [domR, τ, compl_setOf, not_le] using hu.2
    by_contra hgt; push_neg at hgt
    rw [mem_closure_iff_nhds] at hu'
    rcases hu' _ ((continuous_mobiusSeamR2_coord0.isOpen_preimage _ isOpen_Ioi).mem_nhds hgt)
      with ⟨z, hz1, hz2⟩
    simp at hz1 hz2; linarith
  have Ico_Ioo_of_nonneg {u : R2} (hu_ball : u ∈ Ball) (hu0 : 0 ≤ u 0) :
      u 0 ∈ Ico (0 : ℝ) ε ∧ u 1 ∈ Ioo (t₀ - δ) (t₀ + δ) := by
    have h0 := abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hε0 hu_ball 0
    have h1 := abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hε0 hu_ball 1
    rw [hv0] at h0; rw [hv1] at h1; simp [abs_lt] at h0 h1
    dsimp [ε, δ, t₀] at *
    exact ⟨⟨hu0, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have Ioc_Ioo_partner_of_nonpos {u : R2} (hu_ball : u ∈ Ball) (hu0 : u 0 ≤ 0) :
      (mobiusPlaneTrigSeamPartnerAdd u) 0 ∈ Ioc (1 - ε) (1 : ℝ) ∧
      (mobiusPlaneTrigSeamPartnerAdd u) 1 ∈ Ioo (1 - t₀ - δ) (1 - t₀ + δ) := by
    have h0 := abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hε0 hu_ball 0
    have h1 := abs_sub_coord_lt_of_mem_ball_euclideanSpace_two hε0 hu_ball 1
    rw [hv0] at h0; rw [hv1] at h1; simp [abs_lt] at h0 h1
    simp [mobiusPlaneTrigSeamPartnerAdd, PiLp.add_apply, EuclideanSpace.single_apply]
    dsimp [ε, δ, t₀] at *
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have junkFD : MobiusFundamentalDomain := (mobiusIcc0, mobiusIcc0)
  let fL : R2 → MobiusStrip := fun u =>
    if hu : u ∈ Lcap then
      πq (mobiusFD_of_planeIcoIoo_left hε1 htLo htHi u
        (Ico_Ioo_of_nonneg hu.1 hu.2).1 (Ico_Ioo_of_nonneg hu.1 hu.2).2)
    else πq junkFD
  let fR : R2 → MobiusStrip := fun u =>
    if hu : u ∈ domR then
      πq (mobiusFD_of_plane_IocIoo_right hε1 htLo htHi (mobiusPlaneTrigSeamPartnerAdd u)
        (Ioc_Ioo_partner_of_nonpos hu.1 (mem_domR_coord_nonpos hu)).1
        (Ioc_Ioo_partner_of_nonpos hu.1 (mem_domR_coord_nonpos hu)).2)
    else πq junkFD
  have hLR_agree : ∀ a ∈ Ball ∩ frontier τ, fL a = fR a := by
    intro a haτ
    have ha0 : a 0 = 0 := eq_zero_of_mem_frontier_coord0_nonneg haτ.2
    have haL : a ∈ Lcap := ⟨haτ.1, show 0 ≤ a 0 by rw [ha0]⟩
    have haR : a ∈ domR := ⟨haτ.1, (by
      simpa [frontier_eq_closure_inter_closure] using haτ.2 : a ∈ closure τ ∩ closure τᶜ).2⟩
    dsimp [fL, fR]; rw [dif_pos haL, dif_pos haR]
    exact Quotient.sound
      (mobiusRel₀_mobiusFD_plane_seamPartner hε1 htLo htHi ha0
        (Ico_Ioo_of_nonneg haτ.1 (by rw [ha0])).1 (Ico_Ioo_of_nonneg haτ.1 (by rw [ha0])).2
        (Ioc_Ioo_partner_of_nonpos haτ.1 (by rw [ha0])).1 (Ioc_Ioo_partner_of_nonpos haτ.1 (by rw [ha0])).2)
  let gL : Subtype Lcap → MobiusFundamentalDomain := fun z =>
    mobiusFD_of_planeIcoIoo_left hε1 htLo htHi z.val
      (Ico_Ioo_of_nonneg z.2.1 z.2.2).1 (Ico_Ioo_of_nonneg z.2.1 z.2.2).2
  have hLre : Continuous gL := by
    have hfst : Continuous fun z : Subtype Lcap => (gL z).1.val := by
      have hmap : (fun z : Subtype Lcap => (gL z).1.val) = fun z => z.val 0 := by
        funext z; simp [gL, mobiusFD_of_planeIcoIoo_left]
      rw [hmap]
      exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 0).comp continuous_subtype_val
    have hsnd : Continuous fun z : Subtype Lcap => (gL z).2.val := by
      have hmap : (fun z : Subtype Lcap => (gL z).2.val) = fun z => z.val 1 := by
        funext z; simp [gL, mobiusFD_of_planeIcoIoo_left]
      rw [hmap]
      exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 1).comp continuous_subtype_val
    exact Continuous.prodMk (Continuous.subtype_mk hfst fun z => (gL z).1.property)
      (Continuous.subtype_mk hsnd fun z => (gL z).2.property)
  let gR : Subtype domR → MobiusFundamentalDomain := fun x =>
    mobiusFD_of_plane_IocIoo_right hε1 htLo htHi (mobiusPlaneTrigSeamPartnerAdd x.val)
      (Ioc_Ioo_partner_of_nonpos x.2.1 (mem_domR_coord_nonpos x.2)).1
      (Ioc_Ioo_partner_of_nonpos x.2.1 (mem_domR_coord_nonpos x.2)).2
  have hRre : Continuous gR := by
    have hsingle (i : Fin 2) : Continuous fun a : ℝ => EuclideanSpace.single i a :=
      (Isometry.uniformContinuous (Isometry.of_dist_eq (EuclideanSpace.dist_single_same i))).continuous
    have hω : Continuous fun z : Subtype domR => mobiusPlaneTrigSeamPartnerAdd z.val := by
      exact Continuous.add
        ((hsingle 0).comp (continuous_const.add ((@PiLp.continuous_apply 2 _ (fun _ => ℝ) _ 0).comp continuous_subtype_val)))
        ((hsingle 1).comp (continuous_const.sub ((@PiLp.continuous_apply 2 _ (fun _ => ℝ) _ 1).comp continuous_subtype_val)))
    have hfst : Continuous fun z : Subtype domR => (gR z).1.val := by
      have hmap : (fun z : Subtype domR => (gR z).1.val) =
          fun z => (mobiusPlaneTrigSeamPartnerAdd z.val) 0 := by
        funext z; simp [gR, mobiusFD_of_plane_IocIoo_right]
      rw [hmap]; exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 0).comp hω
    have hsnd : Continuous fun z : Subtype domR => (gR z).2.val := by
      have hmap : (fun z : Subtype domR => (gR z).2.val) =
          fun z => (mobiusPlaneTrigSeamPartnerAdd z.val) 1 := by
        funext z; simp [gR, mobiusFD_of_plane_IocIoo_right]
      rw [hmap]; exact (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 1).comp hω
    exact Continuous.prodMk (Continuous.subtype_mk hfst fun z => (gR z).1.property)
      (Continuous.subtype_mk hsnd fun z => (gR z).2.property)
  have hτcl : IsClosed τ := IsClosed.preimage continuous_mobiusSeamR2_coord0 isClosed_Ici
  have hcontLf : ContinuousOn fL (Ball ∩ closure τ) := by
    simpa [Lcap, hτcl.closure_eq] using continuousOn_iff_continuous_restrict.2
      (show Continuous (Lcap.restrict fL) by
        convert continuous_mobiusQuot.comp hLre using 1
        funext ⟨x_val, hx⟩; dsimp [fL, gL]; rw [dif_pos hx])
  have hcontRf : ContinuousOn fR (Ball ∩ closure τᶜ) :=
    continuousOn_iff_continuous_restrict.2
      (show Continuous (domR.restrict fR) by
        convert continuous_mobiusQuot.comp hRre using 1
        funext ⟨x_val, hx⟩; dsimp [fR, gR]; rw [dif_pos hx])
  let σ := τ.piecewise fL fR
  have hσBall : ContinuousOn σ Ball :=
    ContinuousOn.piecewise (s := Ball) (t := τ) hLR_agree hcontLf hcontRf
  -- σ maps Ball into U
  have hσ_mem_U : ∀ {u : R2}, u ∈ Ball → σ u ∈ U := by
    intro u hu
    by_cases huτ : u ∈ τ
    · have huI : u ∈ Lcap := ⟨hu, huτ⟩
      have hpw : σ u = fL u := Set.piecewise_eq_of_mem τ fL fR huτ
      rw [hpw]; dsimp [fL]; rw [dif_pos huI]
      exact ⟨_, Or.inl (mem_leftPatch_mobiusFD_of_planeIcoIoo_left hε1 htLo htHi u
        (Ico_Ioo_of_nonneg hu huτ).1 (Ico_Ioo_of_nonneg hu huτ).2), rfl⟩
    · have hu0 : u 0 < 0 := not_le.mp huτ
      have huD : u ∈ domR :=
        ⟨hu, subset_closure (show u ∈ τᶜ by simpa [τ, compl_setOf, not_le] using hu0)⟩
      have hpw : σ u = fR u := Set.piecewise_eq_of_notMem τ fL fR huτ
      rw [hpw]; dsimp [fR]; rw [dif_pos huD]
      exact ⟨_, Or.inr (mem_rightPatch_mobiusFD_of_plane_IocIoo_right hε1 htLo htHi _
        (Ioc_Ioo_partner_of_nonpos hu hu0.le).1 (Ioc_Ioo_partner_of_nonpos hu hu0.le).2), rfl⟩
  -- left_inv: mobiusStripUnfold ∘ σ = id on Ball
  have hσ_left_inv : ∀ {u : R2}, u ∈ Ball → mobiusStripUnfold (σ u) = u := by
    intro u hu
    by_cases huτ : u ∈ τ
    · have huI : u ∈ Lcap := ⟨hu, huτ⟩
      have hpw : σ u = fL u := Set.piecewise_eq_of_mem τ fL fR huτ
      rw [hpw]; dsimp [fL]; rw [dif_pos huI]
      rw [hunfold_quot]
      let q := mobiusFD_of_planeIcoIoo_left hε1 htLo htHi u
        (Ico_Ioo_of_nonneg hu huτ).1 (Ico_Ioo_of_nonneg hu huτ).2
      have hqx : q.1.val = u 0 := by simp [q, mobiusFD_of_planeIcoIoo_left]
      have hqx_le : q.1.val ≤ 1 / 2 := by
        rw [hqx]; have := (Ico_Ioo_of_nonneg hu huτ).1.2; dsimp [ε] at this; linarith
      have hqμ : mobiusPlaneCoord q = u := by
        refine PiLp.ext fun i => ?_
        fin_cases i <;> simp [q, mobiusPlaneCoord, mobiusFD_of_planeIcoIoo_left,
          PiLp.add_apply, EuclideanSpace.single_apply]
      show unfoldFD q = u
      rw [show unfoldFD q = mobiusPlaneCoord q from if_pos hqx_le]; exact hqμ
    · have hu0 : u 0 < 0 := not_le.mp huτ
      have huD : u ∈ domR :=
        ⟨hu, subset_closure (show u ∈ τᶜ by simpa [τ, compl_setOf, not_le] using hu0)⟩
      have hpw : σ u = fR u := Set.piecewise_eq_of_notMem τ fL fR huτ
      rw [hpw]; dsimp [fR]; rw [dif_pos huD]
      rw [hunfold_quot]
      let pR := mobiusFD_of_plane_IocIoo_right hε1 htLo htHi (mobiusPlaneTrigSeamPartnerAdd u)
        (Ioc_Ioo_partner_of_nonpos hu hu0.le).1 (Ioc_Ioo_partner_of_nonpos hu hu0.le).2
      have hpRx : pR.1.val = (mobiusPlaneTrigSeamPartnerAdd u) 0 := by
        simp [pR, mobiusFD_of_plane_IocIoo_right]
      have hpRx_gt : ¬ pR.1.val ≤ 1 / 2 := by
        rw [hpRx]
        have := (Ioc_Ioo_partner_of_nonpos hu hu0.le).1.1; dsimp [ε] at this
        linarith
      have hpRμ : mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord pR) = u := by
        refine PiLp.ext fun i => ?_
        fin_cases i <;> simp [pR, mobiusPlaneTrigSeamPartnerSub, mobiusPlaneCoord,
          mobiusFD_of_plane_IocIoo_right, mobiusPlaneTrigSeamPartnerAdd,
          PiLp.add_apply, EuclideanSpace.single_apply]
      show unfoldFD pR = u
      rw [show unfoldFD pR = mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord pR) from if_neg hpRx_gt]
      exact hpRμ
  -- right_inv: σ ∘ mobiusStripUnfold = id on S-representatives
  have hσ_right_inv : ∀ {q_fd : MobiusFundamentalDomain}, q_fd ∈ S →
      unfoldFD q_fd ∈ Ball → σ (unfoldFD q_fd) = πq q_fd := by
    intro q_fd hqS hqBall
    rcases hqS with hL | hR
    · -- left patch
      have hqx_le : q_fd.1.val ≤ 1 / 2 := by
        have := hL.1; dsimp [ε] at this; linarith
      have hunf : unfoldFD q_fd = mobiusPlaneCoord q_fd := if_pos hqx_le
      rw [hunf] at hqBall ⊢
      have huτ : mobiusPlaneCoord q_fd ∈ τ := by
        simp only [τ, mem_setOf_eq, mobiusPlaneCoord_apply_zero]
        exact q_fd.1.2.1
      have hpw : σ (mobiusPlaneCoord q_fd) = fL (mobiusPlaneCoord q_fd) :=
        Set.piecewise_eq_of_mem τ fL fR huτ
      rw [hpw]; dsimp [fL]; rw [dif_pos (show mobiusPlaneCoord q_fd ∈ Lcap from ⟨hqBall, huτ⟩)]
      congr 1
      exact Prod.ext
        (Subtype.ext (by simp [mobiusFD_of_planeIcoIoo_left, mobiusPlaneCoord_apply_zero]))
        (Subtype.ext (by simp [mobiusFD_of_planeIcoIoo_left, mobiusPlaneCoord_apply_one]))
    · -- right patch: unfoldFD = seamPartnerSub ∘ planeCoord
      have hqx_gt : ¬ q_fd.1.val ≤ 1 / 2 := by
        have := hR.1; dsimp [ε] at this; linarith
      have hunf : unfoldFD q_fd = mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd) :=
        if_neg hqx_gt
      rw [hunf] at hqBall ⊢
      have hcoord0 : (mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd)) 0 =
          q_fd.1.val - 1 := by
        simp [mobiusPlaneTrigSeamPartnerSub, mobiusPlaneCoord_apply_zero, PiLp.add_apply,
          EuclideanSpace.single_apply]
      have hcoord1 : (mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd)) 1 =
          1 - q_fd.2.val := by
        simp [mobiusPlaneTrigSeamPartnerSub, mobiusPlaneCoord_apply_one, PiLp.add_apply,
          EuclideanSpace.single_apply]
      by_cases hx1 : q_fd.1.val = 1
      · -- boundary case: q_fd.1 = 1, so coord0 = 0, σ dispatches to fL
        have hcoord0_eq : (mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd)) 0 = 0 := by
          rw [hcoord0, hx1]; ring
        have huτ : mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd) ∈ τ := by
          simp only [τ, mem_setOf_eq]; rw [hcoord0]; linarith [q_fd.1.2.2]
        have hpw : σ (mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd)) =
            fL (mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd)) :=
          Set.piecewise_eq_of_mem τ fL fR huτ
        rw [hpw]; dsimp [fL]
        rw [dif_pos (show mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd) ∈ Lcap from ⟨hqBall, huτ⟩)]
        -- fL gives πq(mobiusFD_of_planeIcoIoo_left ... (0, 1-t) ...) which is ⟦(0, 1-t)⟧
        -- q_fd = (1, t) where t ∈ (1/4, 3/4), so (0, 1-t) ~ (1, t) via mobiusRel₀
        apply Quotient.sound
        refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · simp [mobiusFD_of_planeIcoIoo_left, hcoord0_eq]
        · exact hx1
        · simp [mobiusFD_of_planeIcoIoo_left, mobiusPlaneTrigSeamPartnerSub,
            mobiusPlaneCoord_apply_one, hx1, PiLp.add_apply, EuclideanSpace.single_apply]
      · -- interior case: q_fd.1 < 1, so coord0 < 0, σ dispatches to fR
        have hx1_lt : q_fd.1.val < 1 := lt_of_le_of_ne q_fd.1.2.2 hx1
        have huτ : ¬ mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd) ∈ τ := by
          simp only [τ, mem_setOf_eq, not_le, hcoord0]; linarith
        have hpw : σ (mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd)) =
            fR (mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd)) :=
          Set.piecewise_eq_of_notMem τ fL fR huτ
        rw [hpw]
        have huD : mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd) ∈ domR :=
          ⟨hqBall, subset_closure (show mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q_fd) ∈ τᶜ by
            simpa [τ, compl_setOf, not_le, hcoord0] using show q_fd.1.val - 1 < 0 by linarith)⟩
        dsimp [fR]; rw [dif_pos huD]
        congr 1
        -- Show the two FD points are equal componentwise
        apply Prod.ext <;> apply Subtype.ext
        · simp [mobiusFD_of_plane_IocIoo_right, mobiusPlaneTrigSeamPartnerAdd,
            mobiusPlaneTrigSeamPartnerSub, mobiusPlaneCoord_apply_zero,
            PiLp.add_apply, EuclideanSpace.single_apply]
        · simp [mobiusFD_of_plane_IocIoo_right, mobiusPlaneTrigSeamPartnerAdd,
            mobiusPlaneTrigSeamPartnerSub, mobiusPlaneCoord_apply_one,
            PiLp.add_apply, EuclideanSpace.single_apply]
  -- S' = sub-patch whose unfoldFD-image lands in Ball
  let S' : Set MobiusFundamentalDomain := {q ∈ S | unfoldFD q ∈ Ball}
  -- S' is open: on each sub-patch, unfoldFD is continuous, so preimage of Ball (open) is open
  have hS'o : IsOpen S' := by
    have hLP := isOpen_mobiusSeamLeftPatch t₀ ε δ
    have hRP := isOpen_mobiusSeamRightPatch t₀ ε δ
    have hBallOpen : IsOpen Ball := Metric.isOpen_ball
    have hL_pre : IsOpen {q : MobiusFundamentalDomain | q ∈ mobiusSeamLeftPatch t₀ ε δ ∧
        mobiusPlaneCoord q ∈ Ball} := by
      have : {q : MobiusFundamentalDomain | q ∈ mobiusSeamLeftPatch t₀ ε δ ∧
          mobiusPlaneCoord q ∈ Ball} =
          mobiusSeamLeftPatch t₀ ε δ ∩ mobiusPlaneCoord ⁻¹' Ball := by ext; simp [and_comm]
      rw [this]; exact hLP.inter (hBallOpen.preimage continuous_mobiusPlaneCoord)
    have hR_pre : IsOpen {q : MobiusFundamentalDomain | q ∈ mobiusSeamRightPatch t₀ ε δ ∧
        mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q) ∈ Ball} := by
      have hsingle (i : Fin 2) : Continuous fun a : ℝ => EuclideanSpace.single i a :=
        (Isometry.uniformContinuous (Isometry.of_dist_eq (EuclideanSpace.dist_single_same i))).continuous
      have hPartnerSub : Continuous mobiusPlaneTrigSeamPartnerSub := by
        dsimp [mobiusPlaneTrigSeamPartnerSub]
        exact Continuous.add
          ((hsingle 0).comp ((@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 0).sub continuous_const))
          ((hsingle 1).comp (continuous_const.sub (@PiLp.continuous_apply 2 (Fin 2) (fun _ => ℝ) _ 1)))
      have : {q : MobiusFundamentalDomain | q ∈ mobiusSeamRightPatch t₀ ε δ ∧
          mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q) ∈ Ball} =
          mobiusSeamRightPatch t₀ ε δ ∩ (mobiusPlaneTrigSeamPartnerSub ∘ mobiusPlaneCoord) ⁻¹' Ball := by
        ext; simp [and_comm, Function.comp]
      rw [this]; exact hRP.inter (hBallOpen.preimage (hPartnerSub.comp continuous_mobiusPlaneCoord))
    -- S' = left preimage ∪ right preimage
    suffices h : S' = {q | q ∈ mobiusSeamLeftPatch t₀ ε δ ∧ mobiusPlaneCoord q ∈ Ball} ∪
        {q | q ∈ mobiusSeamRightPatch t₀ ε δ ∧
          mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q) ∈ Ball} from h ▸ hL_pre.union hR_pre
    ext q; constructor
    · rintro ⟨hqS, hqB⟩
      rcases hqS with hL | hR
      · left; refine ⟨hL, ?_⟩
        have hle : q.1.val ≤ 1 / 2 := by have := hL.1; dsimp [ε] at this; linarith
        have : unfoldFD q = mobiusPlaneCoord q := if_pos hle
        rwa [this] at hqB
      · right; refine ⟨hR, ?_⟩
        have hgt : ¬ q.1.val ≤ 1 / 2 := by have := hR.1; dsimp [ε] at this; linarith
        have : unfoldFD q = mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q) := if_neg hgt
        rwa [this] at hqB
    · rintro (⟨hL, hB⟩ | ⟨hR, hB⟩)
      · refine ⟨Or.inl hL, ?_⟩
        have hle : q.1.val ≤ 1 / 2 := by have := hL.1; dsimp [ε] at this; linarith
        show unfoldFD q ∈ Ball
        rw [show unfoldFD q = mobiusPlaneCoord q from if_pos hle]; exact hB
      · refine ⟨Or.inr hR, ?_⟩
        have hgt : ¬ q.1.val ≤ 1 / 2 := by have := hR.1; dsimp [ε] at this; linarith
        show unfoldFD q ∈ Ball
        rw [show unfoldFD q = mobiusPlaneTrigSeamPartnerSub (mobiusPlaneCoord q) from if_neg hgt]
        exact hB
  -- S' is saturated: unfoldFD is mobiusRel₀-invariant, so Ball membership transfers
  have hS'sat : ∀ ⦃x y : MobiusFundamentalDomain⦄, x ∈ S' → mobiusRel₀ x y → y ∈ S' := by
    intro x y ⟨hxS, hxB⟩ hxy
    exact ⟨hsat hxS hxy, hunfold_rel hxy ▸ hxB⟩
  let V : Set MobiusStrip := πq '' S'
  have hVo : IsOpen V := isOpen_mobiusQuotient_image_of_saturated S' hS'o hS'sat
  -- p ∈ S' (unfoldFD p = v, center of Ball)
  have hunfold_p : unfoldFD p = v := by
    have hle : p.1.val ≤ 1 / 2 := by rw [hp0]; norm_num
    simp [unfoldFD, if_pos hle]
    refine PiLp.ext fun i => ?_
    fin_cases i <;> simp [mobiusPlaneCoord, v, PiLp.add_apply, EuclideanSpace.single_apply, hp0, hth]
  have hpS' : p ∈ S' := ⟨hpS, by rw [hunfold_p]; exact Metric.mem_ball_self hε0⟩
  have hpV : πq p ∈ V := ⟨p, hpS', rfl⟩
  -- unfoldFD maps S' into Ball (by definition of S')
  have hunfold_in_Ball : ∀ {q_fd : MobiusFundamentalDomain}, q_fd ∈ S' → unfoldFD q_fd ∈ Ball :=
    fun hq => hq.2
  have hunfold_mem_Ball_of_mem_V : ∀ {z : MobiusStrip}, z ∈ V → mobiusStripUnfold z ∈ Ball := by
    intro z hz; rcases hz with ⟨q_fd, hqS', rfl⟩
    rw [hunfold_quot]; exact hunfold_in_Ball hqS'
  -- σ maps Ball into V: for u ∈ Ball, σ(u) ∈ U and mobiusStripUnfold(σ(u)) = u ∈ Ball
  have hσ_mem_V : ∀ {u : R2}, u ∈ Ball → σ u ∈ V := by
    intro u hu
    rcases hσ_mem_U hu with ⟨q_fd, hqS, hq_eq⟩
    refine ⟨q_fd, ⟨hqS, ?_⟩, hq_eq⟩
    -- Need: unfoldFD q_fd ∈ Ball. We know mobiusStripUnfold(σ u) = u and σ u = πq q_fd
    have h := hσ_left_inv hu
    rw [← hq_eq] at h
    change unfoldFD q_fd = u at h
    rw [h]; exact hu
  let equivBV : Equiv (Subtype Ball) (Subtype V) :=
    { toFun := fun w => ⟨σ w.val, hσ_mem_V w.2⟩
      invFun := fun z => ⟨mobiusStripUnfold z.val, hunfold_mem_Ball_of_mem_V z.2⟩
      left_inv := fun w => Subtype.ext (hσ_left_inv w.2)
      right_inv := fun z => by
        rcases z with ⟨z_val, hz⟩
        rcases hz with ⟨q_fd, hqS', rfl⟩
        apply Subtype.ext
        show σ (mobiusStripUnfold (πq q_fd)) = πq q_fd
        change σ (unfoldFD q_fd) = πq q_fd
        exact hσ_right_inv hqS'.1 (hunfold_in_Ball hqS') }
  have hcontBV : Continuous equivBV :=
    Continuous.subtype_mk (hσBall.comp_continuous continuous_subtype_val fun w => w.2) _
  have hcontVB : Continuous equivBV.symm := by
    apply Continuous.subtype_mk
    show Continuous fun z : Subtype V => mobiusStripUnfold z.val
    exact continuous_quotientLift_unfold_on_saturatedImage
      (fun a b h => hunfold_rel h) hS'o hS'sat
      (fun q hqS' hL => by
        have hle : q.1.val ≤ 1 / 2 := by
          have := hL.1; show q.1.val ≤ 1 / 2; linarith
        exact if_pos hle)
      (fun q hqS' hR => by
        have hgt : ¬ q.1.val ≤ 1 / 2 := by
          have := hR.1; push_neg; linarith
        exact if_neg hgt)
      (fun q hqS' => by
        rcases hqS'.1 with hL | hR
        · exact Or.inl hL
        · exact Or.inr hR)
  let ψ : Subtype V ≃ₜ Subtype Ball := Homeomorph.mk equivBV.symm hcontVB hcontBV
  let φ : Subtype V ≃ₜ R2 := ψ.trans (homeomorph_subtype_ball_R2 v hε0)
  exact chartableR2_of_open_embeds_plane (πq p) hVo hpV ⟨φ⟩

/-- **SPEC_003 (Phase E, left seam, t ≠ ½).** Parameters: `t₀ = t`, `ε = 1/4`,
  `δ = min(|t - ½|/2, min(t, 1 - t) / 2)`. The point `(0, t)` lies in `mobiusSeamLeftPatch t₀ ε δ ⊆
  mobiusSeamSaturatedPatch`. -/
theorem chartableR2_mobiusQuotientMk_of_left_seam_ne_half {p : MobiusFundamentalDomain}
    (hp0 : p.1.val = 0) (ht0 : 0 < p.2.val) (ht1 : p.2.val < 1) (ht_ne : p.2.val ≠ 1 / 2) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  let t₀ : ℝ := p.2.val
  let ε : ℝ := 1 / 4
  let δ : ℝ := min (|t₀ - 1 / 2| / 2) (min t₀ (1 - t₀) / 2)
  have ht0_sub : t₀ - 1 / 2 ≠ 0 := sub_ne_zero.mpr ht_ne
  have hε0 : 0 < ε := by norm_num
  have hε : ε < 1 / 2 := by norm_num
  have hδ0 : 0 < δ := by
    dsimp [δ]
    refine lt_min_iff.mpr ⟨?_, ?_⟩
    · exact half_pos (abs_pos.mpr ht0_sub)
    · exact half_pos (lt_min_iff.mpr ⟨ht0, sub_pos.mpr ht1⟩)
  have hδ_le_half_t0 : δ ≤ t₀ / 2 := by
    have h := min_le_right (|t₀ - 1 / 2| / 2) (min t₀ (1 - t₀) / 2)
    have hm : min t₀ (1 - t₀) ≤ t₀ := min_le_left t₀ (1 - t₀)
    have h' : min t₀ (1 - t₀) / 2 ≤ t₀ / 2 := by nlinarith only [hm]
    linarith only [h, h']
  have hδ_le_half_one_sub : δ ≤ (1 - t₀) / 2 := by
    have h := min_le_right (|t₀ - 1 / 2| / 2) (min t₀ (1 - t₀) / 2)
    have hm : min t₀ (1 - t₀) ≤ 1 - t₀ := min_le_right t₀ (1 - t₀)
    have h' : min t₀ (1 - t₀) / 2 ≤ (1 - t₀) / 2 := by nlinarith only [hm]
    linarith only [h, h']
  have htLo : 0 < t₀ - δ := by linarith only [hδ_le_half_t0, ht0]
  have htHi : t₀ + δ < 1 := by linarith only [hδ_le_half_one_sub, ht1]
  have hδ₂ : δ < |t₀ - (1 / 2 : ℝ)| := by
    have hlt : |t₀ - (1 / 2 : ℝ)| / 2 < |t₀ - (1 / 2 : ℝ)| :=
      half_lt_self (abs_pos.mpr ht0_sub)
    exact lt_of_le_of_lt (min_le_left _ _) hlt
  have hpL : p ∈ mobiusSeamLeftPatch t₀ ε δ := by
    rw [mobiusSeamLeftPatch, mem_setOf_eq]
    refine ⟨?_, ht0, ht1, ?_, ?_⟩
    · rw [hp0]; norm_num
    · linarith only [hδ0]
    · linarith only [hδ0]
  exact chartableR2_mobiusQuotientMk_of_mem_mobiusSeamLeftPatch_leftEdge hε0 hε hδ0 htLo htHi hδ₂ hpL hp0

theorem chartableR2_mobiusQuotientMk_of_left_seam {p : MobiusFundamentalDomain}
    (hp0 : p.1.val = 0) (ht0 : 0 < p.2.val) (ht1 : p.2.val < 1) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  by_cases hth : p.2.val = 1 / 2
  · exact chartableR2_mobiusQuotientMk_of_left_seam_half hp0 hth
  · exact chartableR2_mobiusQuotientMk_of_left_seam_ne_half hp0 ht0 ht1 hth

/-- **SPEC_003 (Phase E).** On the **right seam** `x = 1` with `0 < t < 1`, the glue partner has
  `x = 0` and `0 < 1 - t < 1`, so `⟦q⟧ = ⟦p⟧` and the left-seam result applies. -/
theorem chartableR2_mobiusQuotientMk_of_right_seam {p : MobiusFundamentalDomain}
    (hp1 : p.1.val = 1) (ht0 : 0 < p.2.val) (ht1 : p.2.val < 1) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  let q : MobiusFundamentalDomain := (mobiusIcc0, mobiusFlipHeight p.2)
  have hq0 : q.1.val = 0 := mobiusIcc0_val
  have hqt_val : q.2.val = 1 - p.2.val := by simp [q, mobiusFlipHeight_val]
  have hqt0 : 0 < q.2.val := by rw [hqt_val]; linarith
  have hqt1 : q.2.val < 1 := by rw [hqt_val]; linarith
  have hrel : mobiusRel₀ p q := by
    refine Or.inr (Or.inr ⟨hq0, hp1, ?_⟩)
    show p.2.val + q.2.val = 1
    rw [hqt_val]; ring
  exact chartableR2_mobiusQuotientMk_of_mobiusRel₀ hrel
    (chartableR2_mobiusQuotientMk_of_left_seam hq0 hqt0 hqt1)

/-- **SPEC_003 (C1 + seam edges, trig branch).** On the **full** saturated seam patch with
  `δ < |t₀ - ½|`, `ChartableR2 ⟦p⟧` for ALL `p` (including `x ∈ {0,1}` off the equator).

  Uses: `U = π '' S` open (saturation); `mobiusStripTrigCoord` injective on `Subtype U`;
  image `T = mobiusFDTrigCoord '' S` open; ball `B ⊆ T`; pull back `V = trig⁻¹' B ∩ U`;
  `Subtype V ≃ₜ Subtype B ≃ₜ R²`.

  **Note.** `(0, ½)` cannot lie in `mobiusSeamSaturatedPatch` under `δ < |t₀ - ½|` (contradiction on the
  height window), so equator `chartableR2_mobiusQuotientMk_of_left_seam_half` is not used here. -/
theorem chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatch {t₀ ε δ : ℝ}
    {p : MobiusFundamentalDomain} (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|)
    (hp : p ∈ mobiusSeamSaturatedPatch t₀ ε δ) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  rcases hp with hpL | hpR
  · by_cases hxpos : 0 < p.1.val
    · exact chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatchSheetInterior hε0 hε hδ0 htLo htHi
        (Or.inl ⟨hxpos, hpL⟩)
    · have hx0 : p.1.val = 0 := le_antisymm (not_lt.mp hxpos) p.1.property.1
      exact chartableR2_mobiusQuotientMk_of_mem_mobiusSeamLeftPatch_leftEdge hε0 hε hδ0 htLo htHi hδ₂ hpL hx0
  · by_cases hx1 : p.1.val < 1
    · exact chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatchSheetInterior hε0 hε hδ0 htLo htHi
        (Or.inr ⟨hx1, hpR⟩)
    · have hx1' : p.1.val = 1 := le_antisymm p.1.property.2 (not_lt.mp hx1)
      exact chartableR2_mobiusQuotientMk_of_right_seam hx1' hpR.2.1 hpR.2.2.1

/-- **SPEC_003 (E1).** Every fundamental-domain representative with `0 < t < 1` maps to a `ChartableR2`
  quotient class. Together with `mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`,
  this closes Möbius **C4**. -/
theorem chartableR2_mobiusQuotientMk_of_interior_height {p : MobiusFundamentalDomain}
    (ht : 0 < p.2.val ∧ p.2.val < 1) : ChartableR2 (Quotient.mk mobiusSetoid p) := by
  by_cases h0 : p.1.val = 0
  · exact chartableR2_mobiusQuotientMk_of_left_seam h0 ht.1 ht.2
  · by_cases h1 : p.1.val = 1
    · exact chartableR2_mobiusQuotientMk_of_right_seam h1 ht.1 ht.2
    · exact chartableR2_mobiusQuotientMk_of_Ioo_square
        ⟨lt_of_le_of_ne p.1.property.1 (Ne.symm h0),
         lt_of_le_of_ne p.1.property.2 h1⟩ ht

/-- **M-FINAL (SPEC_002).** The Möbius strip is not homeomorphic to the closed cylinder. -/
theorem mobiusStrip_not_homeomorphic_closedCylinder :
    IsEmpty (MobiusStrip ≃ₜ ClosedCylinder) :=
  mobiusStrip_not_homeomorphic_closedCylinder_of_forall_off_edge_chartable fun _ hp =>
    chartableR2_mobiusQuotientMk_of_interior_height hp

end RepresentationalRegress

end
