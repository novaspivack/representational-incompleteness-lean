/-
  **Trig-coordinate injectivity** on saturated seam patches (away from the equator `t = ½`).

  If `p, q` lie in `mobiusSeamSaturatedPatch t₀ ε δ` with `δ < |t₀ - ½|` then heights never meet
  `w = t - ½ = 0`. In that situation, `mobiusFDTrigCoord p = mobiusFDTrigCoord q` implies `mobiusRel₀ p q`.

  **Quotient / strip:** `injective_mobiusStripTrigCoord_on_image_quotient_mk_mobiusSeamSaturatedPatch` —
  the lifted coordinate `mobiusStripTrigCoord` is injective on the open saturated quotient window
  `π '' (mobiusSeamSaturatedPatch …)` (same `δ` hypothesis).

  **Image identity:** `image_mobiusStripTrigCoord_quotient_mk_image_mobiusSeamSaturatedPatch` rewrites
  `mobiusStripTrigCoord '' (π '' patch)` to `mobiusFDTrigCoord '' patch`. **Not** equal to the sheet-interior
  image: see `ne_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch_sheetInterior` in **`MobiusSeamChartableR2`**.
  Proving **`IsOpen`** for `mobiusFDTrigCoord ''` (full saturated patch) is still the missing step toward
  seam-edge **`ChartableR2`**.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

import RepresentationalRegress.MobiusSeamChart
import RepresentationalRegress.MobiusSeamChartable

noncomputable section

namespace RepresentationalRegress

open scoped Topology
open Set Real Function

/-! ### Angle–algebra helpers -/

private lemma eq_of_coe_pi_mul_angle {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hA : (Real.pi * x : Real.Angle) = (Real.pi * y : Real.Angle)) : x = y := by
  rcases Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hA with ⟨k, hk⟩
  have hk' : x - y = 2 * (k : ℝ) := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    linear_combination hk
  have hk1 : -1 ≤ x - y := by linarith [hx.1, hy.2]
  have hk2 : x - y ≤ 1 := by linarith [hx.2, hy.1]
  rw [hk'] at hk1 hk2
  have hkZ : k = 0 := by
    have hk1Z : (-1 : ℤ) ≤ 2 * k := by
      have h : (-1 : ℝ) ≤ (2 : ℝ) * (k : ℝ) := by simpa using hk1
      norm_cast at h ⊢
    have hk2Z : 2 * k ≤ (1 : ℤ) := by
      have h : (2 : ℝ) * (k : ℝ) ≤ (1 : ℝ) := by simpa using hk2
      norm_cast at h ⊢
    omega
  subst hkZ
  simp at hk'
  linarith

private lemma eq_glue_edges_of_coe_pi_add_pi {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1)
    (hA : (Real.pi * x : Real.Angle) = (Real.pi * y : Real.Angle) + (Real.pi : Real.Angle)) :
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  have hA' : (Real.pi * x : Real.Angle) = (Real.pi * (y + 1) : Real.Angle) := by
    simpa [mul_add, Real.Angle.coe_add] using hA
  rcases Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hA' with ⟨k, hk⟩
  have hk' : x - (y + 1) = 2 * (k : ℝ) := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    linear_combination hk
  have hbd : -2 ≤ x - (y + 1) := by linarith [hx.1, hy.2]
  have hbd2 : x - (y + 1) ≤ 0 := by linarith [hx.2, hy.1]
  rw [hk'] at hbd hbd2
  have hk01 : k = 0 ∨ k = -1 := by
    have hk1Z : (-1 : ℤ) ≤ k := by
      have h : (-1 : ℝ) ≤ (k : ℝ) := by nlinarith [hbd]
      norm_cast at h ⊢
    have hk2Z : k ≤ (0 : ℤ) := by
      have h : (k : ℝ) ≤ (0 : ℝ) := by nlinarith [hbd2]
      norm_cast at h ⊢
    omega
  rcases hk01 with hk0 | hk1
  · rw [hk0, Int.cast_zero, mul_zero] at hk'
    right
    refine And.intro ?_ ?_
    · linarith [hk', hx.1, hx.2, hy.1, hy.2]
    · linarith [hk', hx.1, hx.2, hy.1, hy.2]
  · rw [hk1, Int.cast_neg, Int.cast_one] at hk'
    simp at hk'
    left
    refine And.intro ?_ ?_
    · linarith [hk', hx.1, hx.2, hy.1, hy.2]
    · linarith [hk', hx.1, hx.2, hy.1, hy.2]

private lemma sub_half_ne_zero_of_window_left {t₀ δ r : ℝ} (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|)
    (hrLo : t₀ - δ < r) (hrHi : r < t₀ + δ) : r - (1 / 2 : ℝ) ≠ 0 := by
  intro hrw
  have hr12 : r = (1 / 2 : ℝ) := by linarith
  subst hr12
  have hrt : |t₀ - (1 / 2 : ℝ)| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hrLo, hrHi]
  linarith [hrt, hδ₂]

private lemma sub_half_ne_zero_of_window_right {t₀ δ r : ℝ} (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|)
    (hrLo : 1 - t₀ - δ < r) (hrHi : r < 1 - t₀ + δ) : r - (1 / 2 : ℝ) ≠ 0 := by
  intro hrw
  have hr12 : r = (1 / 2 : ℝ) := by linarith
  subst hr12
  have hmid : 1 - t₀ - δ < 1 / 2 := by linarith [hrLo]
  have hmid2 : (1 / 2 : ℝ) < 1 - t₀ + δ := by linarith [hrHi]
  have hrt : |t₀ - (1 / 2 : ℝ)| < δ := by
    rw [show |t₀ - (1 / 2 : ℝ)| = |(1 - t₀) - (1 / 2 : ℝ)| by
        rw [show (1 - t₀) - (1 / 2 : ℝ) = (1 / 2 : ℝ) - t₀ by ring, abs_sub_comm]]
    rw [abs_lt]
    constructor <;> linarith [hmid, hmid2]
  linarith [hrt, hδ₂]

/-! ### Main injectivity -/

theorem sub_half_ne_zero_of_mem_mobiusSeamSaturatedPatch {t₀ ε δ : ℝ} (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|)
    {p : MobiusFundamentalDomain} (hp : p ∈ mobiusSeamSaturatedPatch t₀ ε δ) :
    p.2.val - (1 / 2 : ℝ) ≠ 0 := by
  rcases hp with hpL | hpR
  · exact sub_half_ne_zero_of_window_left hδ₂ hpL.2.2.2.1 hpL.2.2.2.2
  · exact sub_half_ne_zero_of_window_right hδ₂ hpR.2.2.2.1 hpR.2.2.2.2

theorem mobiusRel₀_of_eq_mobiusFDTrigCoord_of_seamPatch {t₀ ε δ : ℝ} {p q : MobiusFundamentalDomain}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|)
    (hp : p ∈ mobiusSeamSaturatedPatch t₀ ε δ) (hq : q ∈ mobiusSeamSaturatedPatch t₀ ε δ)
    (H : mobiusFDTrigCoord p = mobiusFDTrigCoord q) : mobiusRel₀ p q := by
  classical
  have _patchParams : 0 < ε ∧ 0 < δ ∧ 0 < t₀ - δ ∧ t₀ + δ < 1 :=
    ⟨hε0, hδ0, htLo, htHi⟩
  let xp := p.1.val
  let xq := q.1.val
  let tp := p.2.val
  let tq := q.2.val
  let wp := tp - (1 / 2 : ℝ)
  let wq := tq - (1 / 2 : ℝ)
  have hwp : wp ≠ 0 := by
    rcases hp with hpL | hpR
    · exact sub_half_ne_zero_of_window_left hδ₂ hpL.2.2.2.1 hpL.2.2.2.2
    · exact sub_half_ne_zero_of_window_right hδ₂ hpR.2.2.2.1 hpR.2.2.2.2
  have hwq : wq ≠ 0 := by
    rcases hq with hqL | hqR
    · exact sub_half_ne_zero_of_window_left hδ₂ hqL.2.2.2.1 hqL.2.2.2.2
    · exact sub_half_ne_zero_of_window_right hδ₂ hqR.2.2.2.1 hqR.2.2.2.2
  have hcp :
      wp * Real.cos (Real.pi * xp) = wq * Real.cos (Real.pi * xq) := by
    simpa [wp, wq, xp, xq, mobiusFDTrigCoord, EuclideanSpace.single_apply, Fin.sum_univ_two,
      mul_assoc] using congrArg (fun v : R2 => v 0) H
  have hsp :
      wp * Real.sin (Real.pi * xp) = wq * Real.sin (Real.pi * xq) := by
    simpa [wp, wq, xp, xq, mobiusFDTrigCoord, EuclideanSpace.single_apply, Fin.sum_univ_two,
      mul_assoc] using congrArg (fun v : R2 => v 1) H
  have hcos2 : wp ^ 2 = wq ^ 2 := by
    have h1 : (wp * Real.cos (Real.pi * xp)) ^ 2 + (wp * Real.sin (Real.pi * xp)) ^ 2 = wp ^ 2 := by
      calc
        (wp * Real.cos (Real.pi * xp)) ^ 2 + (wp * Real.sin (Real.pi * xp)) ^ 2
            = wp ^ 2 * Real.cos (Real.pi * xp) ^ 2 + wp ^ 2 * Real.sin (Real.pi * xp) ^ 2 := by ring
        _ = wp ^ 2 * (Real.cos (Real.pi * xp) ^ 2 + Real.sin (Real.pi * xp) ^ 2) := by ring
        _ = wp ^ 2 := by simp [Real.cos_sq_add_sin_sq]
    have h2 : (wq * Real.cos (Real.pi * xq)) ^ 2 + (wq * Real.sin (Real.pi * xq)) ^ 2 = wq ^ 2 := by
      calc
        (wq * Real.cos (Real.pi * xq)) ^ 2 + (wq * Real.sin (Real.pi * xq)) ^ 2
            = wq ^ 2 * Real.cos (Real.pi * xq) ^ 2 + wq ^ 2 * Real.sin (Real.pi * xq) ^ 2 := by ring
        _ = wq ^ 2 * (Real.cos (Real.pi * xq) ^ 2 + Real.sin (Real.pi * xq) ^ 2) := by ring
        _ = wq ^ 2 := by simp [Real.cos_sq_add_sin_sq]
    have h3 : (wp * Real.cos (Real.pi * xp)) ^ 2 + (wp * Real.sin (Real.pi * xp)) ^ 2 =
        (wq * Real.cos (Real.pi * xq)) ^ 2 + (wq * Real.sin (Real.pi * xq)) ^ 2 := by
      rw [hcp, hsp]
    linarith [h1, h2, h3]
  have hsq : wp = wq ∨ wp = -wq := sq_eq_sq_iff_eq_or_eq_neg.mp hcos2
  rcases hsq with hwEq | hwNeg
  · have hcp' : Real.cos (Real.pi * xp) = Real.cos (Real.pi * xq) := by
      rw [hwEq] at hcp
      exact (mul_right_inj' hwq).mp hcp
    have hsp' : Real.sin (Real.pi * xp) = Real.sin (Real.pi * xq) := by
      rw [hwEq] at hsp
      exact (mul_right_inj' hwq).mp hsp
    have hA : (Real.pi * xp : Real.Angle) = (Real.pi * xq : Real.Angle) :=
      Real.Angle.cos_sin_inj hcp' hsp'
    have hx01 : 0 ≤ xp ∧ xp ≤ 1 :=
      And.intro p.1.property.1 p.1.property.2
    have hx02 : 0 ≤ xq ∧ xq ≤ 1 :=
      And.intro q.1.property.1 q.1.property.2
    have hxx : xp = xq := eq_of_coe_pi_mul_angle hx01 hx02 hA
    have htt : tp = tq := by linarith [hwEq, hxx]
    rcases hp with hpL | hpR <;> rcases hq with hqL | hqR
    · exact Or.inl (by
        refine Prod.ext ?_ ?_
        · exact Subtype.ext hxx
        · exact Subtype.ext htt)
    · exfalso
      have hL : xp < ε := hpL.1
      have hR : 1 - ε < xq := hqR.1
      rw [← hxx] at hR
      linarith [hL, hR, hε]
    · exfalso
      have hR : 1 - ε < xp := hpR.1
      have hL : xq < ε := hqL.1
      rw [← hxx] at hL
      linarith [hL, hR, hε]
    · exact Or.inl (by
        refine Prod.ext ?_ ?_
        · exact Subtype.ext hxx
        · exact Subtype.ext htt)
  · have ht_sum : tp + tq = 1 := by
      simp [wp, wq, sub_eq_iff_eq_add] at hwNeg
      linarith
    have hcp'' : Real.cos (Real.pi * xp) = -Real.cos (Real.pi * xq) := by
      have hcp' := hcp
      rw [hwNeg] at hcp'
      have hn2 : wq * Real.cos (Real.pi * xp) = wq * (-Real.cos (Real.pi * xq)) := by
        calc
          wq * Real.cos (Real.pi * xp) = -((-wq) * Real.cos (Real.pi * xp)) := by ring
          _ = -(wq * Real.cos (Real.pi * xq)) := by rw [hcp']
          _ = wq * (-Real.cos (Real.pi * xq)) := by ring
      exact (mul_right_inj' hwq).1 hn2
    have hsp'' : Real.sin (Real.pi * xp) = -Real.sin (Real.pi * xq) := by
      have hsp' := hsp
      rw [hwNeg] at hsp'
      have hn2 : wq * Real.sin (Real.pi * xp) = wq * (-Real.sin (Real.pi * xq)) := by
        calc
          wq * Real.sin (Real.pi * xp) = -((-wq) * Real.sin (Real.pi * xp)) := by ring
          _ = -(wq * Real.sin (Real.pi * xq)) := by rw [hsp']
          _ = wq * (-Real.sin (Real.pi * xq)) := by ring
      exact (mul_right_inj' hwq).1 hn2
    have hcp''' : Real.cos (Real.pi * xp) = Real.cos (Real.pi * xq + Real.pi) := by
      simpa [Real.cos_add_pi] using hcp''
    have hsp''' : Real.sin (Real.pi * xp) = Real.sin (Real.pi * xq + Real.pi) := by
      simpa [Real.sin_add_pi] using hsp''
    have hA :
        (Real.pi * xp : Real.Angle) =
          (Real.pi * xq : Real.Angle) + (Real.pi : Real.Angle) :=
      Real.Angle.cos_sin_inj hcp''' hsp'''
    have hxp01 : 0 ≤ xp ∧ xp ≤ 1 := And.intro p.1.property.1 p.1.property.2
    have hxq01 : 0 ≤ xq ∧ xq ≤ 1 := And.intro q.1.property.1 q.1.property.2
    rcases eq_glue_edges_of_coe_pi_add_pi hxp01 hxq01 hA with ⟨hx0, hx1⟩ | ⟨hx1, hx0⟩
    · refine Or.inr (Or.inl ⟨hx0, hx1, ht_sum⟩)
    · refine Or.inr (Or.inr ⟨hx0, hx1, ht_sum⟩)

theorem onPatch_mobiusFDTrigCoord_eq_iff_mobiusRel₀ {t₀ ε δ : ℝ} {p q : MobiusFundamentalDomain}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ)
    (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1) (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|)
    (hp : p ∈ mobiusSeamSaturatedPatch t₀ ε δ) (hq : q ∈ mobiusSeamSaturatedPatch t₀ ε δ) :
    mobiusFDTrigCoord p = mobiusFDTrigCoord q ↔ mobiusRel₀ p q :=
  Iff.intro (fun h => mobiusRel₀_of_eq_mobiusFDTrigCoord_of_seamPatch hε0 hε hδ0 htLo htHi hδ₂ hp hq h)
    fun h => by simpa using mobiusFDTrigCoord_eq_of_mobiusRel₀ h

/-- **SPEC_003 (trig chart spine).** On the **open** quotient window `π '' (mobiusSeamSaturatedPatch …)`,
  `mobiusStripTrigCoord` is **injective** (under the same `δ < |t₀ - ½|` hypothesis as `onPatch`). A
  topological-openness / `ChartableR2` packaging from this injective coordinate map is still separate. -/
theorem injective_mobiusStripTrigCoord_on_image_quotient_mk_mobiusSeamSaturatedPatch {t₀ ε δ : ℝ}
    (hε0 : 0 < ε) (hε : ε < 1 / 2) (hδ0 : 0 < δ) (htLo : 0 < t₀ - δ) (htHi : t₀ + δ < 1)
    (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|) :
    Injective fun x :
        Subtype
          ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) ''
            (mobiusSeamSaturatedPatch t₀ ε δ)) =>
      mobiusStripTrigCoord x.val := by
  classical
  rintro ⟨a_val, ha⟩ ⟨b_val, hb⟩ htrig
  rcases ha with ⟨pa, hpa, rfl⟩
  rcases hb with ⟨pb, hpb, rfl⟩
  have hfd : mobiusFDTrigCoord pa = mobiusFDTrigCoord pb := by simpa [mobiusStripTrigCoord] using htrig
  have hrel : mobiusRel₀ pa pb :=
    (onPatch_mobiusFDTrigCoord_eq_iff_mobiusRel₀ hε0 hε hδ0 htLo htHi hδ₂ hpa hpb).1 hfd
  exact Subtype.ext (Quotient.sound hrel)

/-- Trig coordinates on the **open** saturated quotient window agree set-theoretically with FD trig on the
  patch (any lift hits the same target value). A convenient reduction: **`IsOpen (mobiusStripTrigCoord '' π '' S)`**
  iff **`IsOpen (mobiusFDTrigCoord '' S)`** for `S = mobiusSeamSaturatedPatch …`. -/
theorem image_mobiusStripTrigCoord_quotient_mk_image_mobiusSeamSaturatedPatch (t₀ ε δ : ℝ) :
    mobiusStripTrigCoord ''
        ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) ''
          (mobiusSeamSaturatedPatch t₀ ε δ)) =
      mobiusFDTrigCoord '' (mobiusSeamSaturatedPatch t₀ ε δ) := by
  classical
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, hp, by simp [mobiusStripTrigCoord]⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Quotient.mk mobiusSetoid p, ?_, by simp [mobiusStripTrigCoord]⟩
    exact ⟨p, hp, rfl⟩

end RepresentationalRegress

end
