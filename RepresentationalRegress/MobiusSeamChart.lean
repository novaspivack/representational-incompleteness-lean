/-
  **Vertical seam charts** on `MobiusStrip` (`x = 0`/`1` with `0 < t < 1`) for the intrinsic
  `ChartableR2` predicate.

  **`mobiusSeamSlidingCoord t₀ p`** packages `(x, t - t₀)` as `R²` (continuous in `p`). On the **strict**
  plane window **`mobiusSeamSlidingStrictCoordSet t₀`** (`0 < x < 1`, `0 < t < 1` in FD), sliding coordinates
  are a **homeomorphism** to **`Subtype V`** when **`V ⊆` that window** (**`homeomorph_subtype_mobiusSeamSlidingCoord_preimage`**).

  Local model on `R²` (coordinates `u₀ ~ x`, `u₁ ~ t - t₀` around a seam height `t₀`):
  * `f₁ = w cos(πu₀)` with `w = u₁ + (t₀ - ½)`
  * `f₂ = w sin(πu₀)` plus optional `u₀(1-u₀)` so that the Jacobian at `u = 0` is nonsingular even
    when `t₀ = ½`.

  When `π (t₀ - ½) + 1 = 0` (unique height `t₀ ∈ (0, 1)`), we disable the corrective term; then
  `det Df = -π (t₀ - ½) ≠ 0`.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.ENNReal.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Constructions

import RepresentationalRegress.ChartableR2Neighbor
import RepresentationalRegress.CylinderMobius

noncomputable section

namespace RepresentationalRegress

open scoped Topology ENNReal
open EuclideanSpace Real Module Topology Filter Set PiLp Metric
open Complex (I)

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Fundamental-domain “trig” coordinates `(t-½)(cos πx, sin πx)` — constant on `mobiusRel₀`. -/
noncomputable def mobiusFDTrigCoord (p : MobiusFundamentalDomain) : R2 :=
  let x := p.1.val
  let t := p.2.val
  let w := t - (1 / 2 : ℝ)
  EuclideanSpace.single (0 : Fin 2) (w * Real.cos (Real.pi * x)) +
    EuclideanSpace.single (1 : Fin 2) (w * Real.sin (Real.pi * x))

theorem mobiusFDTrigCoord_eq_of_mobiusRel₀ {p q : MobiusFundamentalDomain}
    (h : mobiusRel₀ p q) : mobiusFDTrigCoord p = mobiusFDTrigCoord q := by
  rcases h with rfl | hglue
  · rfl
  · rcases hglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
    · -- (0, t) ∼ (1, 1-t)
      have hxp : p.1.val = 0 := hp0
      have hxq : q.1.val = 1 := hq1
      have hw : (q.2.val - (1 / 2 : ℝ)) = -(p.2.val - (1 / 2 : ℝ)) := by linarith [hs]
      ext i
      fin_cases i
      · simp [mobiusFDTrigCoord, hxp, hxq, hw, mul_assoc, Real.cos_zero, Real.cos_pi, Real.sin_zero,
          Real.sin_pi]
        linarith [hw]
      · simp [mobiusFDTrigCoord, hxp, hxq, hw, mul_assoc, Real.cos_zero, Real.cos_pi, Real.sin_zero,
          Real.sin_pi]
    · -- (1, t) ∼ (0, 1-t)
      have hxp : p.1.val = 1 := hp1
      have hxq : q.1.val = 0 := hq0
      have hw : (q.2.val - (1 / 2 : ℝ)) = -(p.2.val - (1 / 2 : ℝ)) := by linarith [hs]
      ext i
      fin_cases i
      · simp [mobiusFDTrigCoord, hxp, hxq, hw, mul_assoc, Real.cos_zero, Real.cos_pi, Real.sin_zero,
          Real.sin_pi]
        linarith [hw]
      · simp [mobiusFDTrigCoord, hxp, hxq, hw, mul_assoc, Real.cos_zero, Real.cos_pi, Real.sin_zero,
          Real.sin_pi]

noncomputable abbrev mobiusStripTrigCoord : MobiusStrip → R2 :=
  Quotient.lift mobiusFDTrigCoord fun _ _ hr => mobiusFDTrigCoord_eq_of_mobiusRel₀ hr

theorem continuous_mobiusFDTrigCoord : Continuous mobiusFDTrigCoord := by
  have h0 :
      (fun p : MobiusFundamentalDomain => mobiusFDTrigCoord p 0) =
        fun p => (p.2.val - (1 / 2 : ℝ)) * Real.cos (Real.pi * p.1.val) := by
    funext p; simp [mobiusFDTrigCoord, EuclideanSpace.single_apply]
  have h1 :
      (fun p : MobiusFundamentalDomain => mobiusFDTrigCoord p 1) =
        fun p => (p.2.val - (1 / 2 : ℝ)) * Real.sin (Real.pi * p.1.val) := by
    funext p; simp [mobiusFDTrigCoord, EuclideanSpace.single_apply]
  rw [← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).comp_continuous_iff]
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp [← h0, ← h1, Function.comp] <;> continuity

theorem continuous_mobiusStripTrigCoord : Continuous mobiusStripTrigCoord :=
  Continuous.quotient_lift continuous_mobiusFDTrigCoord fun _ _ h =>
    mobiusFDTrigCoord_eq_of_mobiusRel₀ h

/-! ### Sliding coordinates at seam height (`u₀ = x`, `u₁ = t - t₀`) -/

/-- **Sliding `R²` coordinates** at seam height `t₀`: first component is `p.1.val`, second is `p.2.val - t₀`.
  Matches the **`u`** variables in `mobiusSeamLocalMap*` / SPEC_003 Phase D. -/
noncomputable def mobiusSeamSlidingCoord (t₀ : ℝ) (p : MobiusFundamentalDomain) : R2 :=
  EuclideanSpace.single (0 : Fin 2) p.1.val + EuclideanSpace.single (1 : Fin 2) (p.2.val - t₀)

theorem mobiusSeamSlidingCoord_zero (t₀ : ℝ) {p : MobiusFundamentalDomain}
    (hx : p.1.val = 0) (ht : p.2.val = t₀) : mobiusSeamSlidingCoord t₀ p = 0 := by
  ext i
  fin_cases i <;> simp [mobiusSeamSlidingCoord, hx, ht, PiLp.zero_apply, sub_self,
    EuclideanSpace.single_apply]

theorem continuous_mobiusSeamSlidingCoord (t₀ : ℝ) : Continuous (mobiusSeamSlidingCoord t₀) := by
  rw [← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).comp_continuous_iff]
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;>
    simp [mobiusSeamSlidingCoord, EuclideanSpace.single_apply, Function.comp] <;> continuity

/-- **Strict** plane subset where sliding coordinates decode to a **square-interior** point (`0 < x < 1`,
`0 < t < 1` for `t = u₁ + t₀`). -/
def mobiusSeamSlidingStrictCoordSet (t₀ : ℝ) : Set R2 :=
  { v | 0 < v 0 ∧ v 0 < 1 ∧ 0 < v 1 + t₀ ∧ v 1 + t₀ < 1 }

private lemma continuous_mobiusSeamSliding_coord0 : Continuous fun v : R2 => v 0 :=
  @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (0 : Fin 2)

private lemma continuous_mobiusSeamSliding_coord1 : Continuous fun v : R2 => v 1 :=
  @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (1 : Fin 2)

theorem isOpen_mobiusSeamSlidingStrictCoordSet (t₀ : ℝ) :
    IsOpen (mobiusSeamSlidingStrictCoordSet t₀) := by
  have h01 : IsOpen { v : R2 | 0 < v 0 ∧ v 0 < 1 } :=
    (continuous_mobiusSeamSliding_coord0.isOpen_preimage (Ioi 0) isOpen_Ioi).inter
      (continuous_mobiusSeamSliding_coord0.isOpen_preimage (Iio 1) isOpen_Iio)
  have hadd : Continuous fun v : R2 => v 1 + t₀ :=
    continuous_mobiusSeamSliding_coord1.add continuous_const
  have hI : IsOpen { v : R2 | 0 < v 1 + t₀ ∧ v 1 + t₀ < 1 } :=
    (hadd.isOpen_preimage (Ioi 0) isOpen_Ioi).inter (hadd.isOpen_preimage (Iio 1) isOpen_Iio)
  have hset :
      (mobiusSeamSlidingStrictCoordSet t₀) =
        { v : R2 | 0 < v 0 ∧ v 0 < 1 } ∩ { v : R2 | 0 < v 1 + t₀ ∧ v 1 + t₀ < 1 } := by
    ext v; simp [mobiusSeamSlidingStrictCoordSet, and_assoc]
  rw [hset]
  exact h01.inter hI

theorem mobiusSeamSlidingCoord_apply_zero (t₀ : ℝ) (p : MobiusFundamentalDomain) :
    (mobiusSeamSlidingCoord t₀ p) 0 = p.1.val := by
  simp [mobiusSeamSlidingCoord, EuclideanSpace.single_apply, PiLp.add_apply]

theorem mobiusSeamSlidingCoord_apply_one (t₀ : ℝ) (p : MobiusFundamentalDomain) :
    (mobiusSeamSlidingCoord t₀ p) 1 = p.2.val - t₀ := by
  simp [mobiusSeamSlidingCoord, EuclideanSpace.single_apply, PiLp.add_apply, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc]

/-- Sliding coordinates **`(x, t - t₀)`** separate **`x`** and **`t`**, hence are **globally injective** on
  the fundamental domain. -/
theorem injective_mobiusSeamSlidingCoord (t₀ : ℝ) : Function.Injective (mobiusSeamSlidingCoord t₀) := by
  intro p q h
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    simpa [mobiusSeamSlidingCoord, EuclideanSpace.single_apply, PiLp.add_apply] using
      congrArg (fun v : R2 => v 0) h
  · refine Subtype.ext ?_
    have ht := congrArg (fun v : R2 => v 1) h
    simp [mobiusSeamSlidingCoord, EuclideanSpace.single_apply, PiLp.add_apply] at ht
    linarith only [ht]

private theorem slidingCoord_abs_coord0_le_norm_aux (v : R2) (h0 : 0 ≤ v 0) : |v 0| ≤ ‖v‖ := by
  have habsv0 : |v 0| = v 0 := abs_of_nonneg h0
  have hsq : (v 0) ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [Fin.sum_univ_two]
    have hL0 : ‖v.ofLp 0‖ = |v 0| := by simp [Real.norm_eq_abs]
    have hL1 : ‖v.ofLp 1‖ = |v 1| := by simp [Real.norm_eq_abs]
    rw [hL0, hL1, sq_abs, sq_abs]
    nlinarith [sq_nonneg (v 1)]
  rw [habsv0]
  rw [← Real.sqrt_sq h0, ← Real.sqrt_sq (norm_nonneg v)]
  exact Real.sqrt_le_sqrt hsq

/-- **`|x| ≤ ‖mobiusSeamSlidingCoord t₀ p‖`** (first sliding coordinate vs **L²** norm). -/
theorem abs_coord0_le_norm_mobiusSeamSlidingCoord (t₀ : ℝ) (p : MobiusFundamentalDomain) :
    |p.1.val| ≤ ‖mobiusSeamSlidingCoord t₀ p‖ := by
  let v := mobiusSeamSlidingCoord t₀ p
  have hv0 : v 0 = p.1.val := mobiusSeamSlidingCoord_apply_zero t₀ p
  have h0 : 0 ≤ v 0 := by rw [hv0]; exact p.1.property.1
  simpa [v, hv0] using slidingCoord_abs_coord0_le_norm_aux v h0

/-- **`|t - t₀| ≤ ‖mobiusSeamSlidingCoord t₀ p‖`** (second sliding coordinate vs **L²** norm). -/
theorem abs_coord1_sub_le_norm_mobiusSeamSlidingCoord (t₀ : ℝ) (p : MobiusFundamentalDomain) :
    |p.2.val - t₀| ≤ ‖mobiusSeamSlidingCoord t₀ p‖ := by
  let v := mobiusSeamSlidingCoord t₀ p
  have hv1 : v 1 = p.2.val - t₀ := mobiusSeamSlidingCoord_apply_one t₀ p
  have hns : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [Fin.sum_univ_two]
    have hL0 : ‖v.ofLp 0‖ = |v 0| := by simp [Real.norm_eq_abs]
    have hL1 : ‖v.ofLp 1‖ = |v 1| := by simp [Real.norm_eq_abs]
    rw [hL0, hL1, sq_abs, sq_abs]
  have hsq : (v 1) ^ 2 ≤ ‖v‖ ^ 2 := by linarith [hns, sq_nonneg (v 0)]
  have habs : |v 1| ^ 2 = (v 1) ^ 2 := by rw [sq_abs]
  rw [← hv1, ← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), habs]
  linarith [hsq]

theorem mem_preimage_mobiusSeamSlidingStrictCoordSet_iff (t₀ : ℝ) (p : MobiusFundamentalDomain) :
    p ∈ mobiusSeamSlidingCoord t₀ ⁻¹' mobiusSeamSlidingStrictCoordSet t₀ ↔
      0 < p.1.val ∧ p.1.val < 1 ∧ 0 < p.2.val ∧ p.2.val < 1 := by
  simp only [mem_preimage, mobiusSeamSlidingStrictCoordSet, mem_setOf_eq, mobiusSeamSlidingCoord_apply_zero,
    mobiusSeamSlidingCoord_apply_one]
  constructor
  · intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
    · exact h1
    · exact h2
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h3
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h4
  · rintro ⟨hx1, hx2, ht1, ht2⟩
    refine And.intro hx1 (And.intro hx2 (And.intro ?_ ?_))
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using ht1
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using ht2

/-- Decode sliding `R²` coordinates to a fundamental-domain point (square **interior**). -/
noncomputable def mobiusFDOfSlidingStrict (t₀ : ℝ) (v : R2)
    (h : 0 < v 0 ∧ v 0 < 1 ∧ 0 < v 1 + t₀ ∧ v 1 + t₀ < 1) : MobiusFundamentalDomain :=
  (⟨v 0, le_of_lt h.1, le_of_lt h.2.1⟩,
   ⟨v 1 + t₀, le_of_lt h.2.2.1, le_of_lt h.2.2.2⟩)

theorem mobiusSeamSlidingCoord_mobiusFDOfSlidingStrict (t₀ : ℝ) (v : R2)
    (h : 0 < v 0 ∧ v 0 < 1 ∧ 0 < v 1 + t₀ ∧ v 1 + t₀ < 1) :
    mobiusSeamSlidingCoord t₀ (mobiusFDOfSlidingStrict t₀ v h) = v := by
  ext i
  fin_cases i <;> simp [mobiusSeamSlidingCoord, mobiusFDOfSlidingStrict, EuclideanSpace.single_apply,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem mobiusFDOfSlidingStrict_mobiusSeamSlidingCoord (t₀ : ℝ) (p : MobiusFundamentalDomain)
    (hx : 0 < p.1.val ∧ p.1.val < 1) (ht : 0 < p.2.val ∧ p.2.val < 1) :
    mobiusFDOfSlidingStrict t₀ (mobiusSeamSlidingCoord t₀ p)
        ⟨by simpa [mobiusSeamSlidingCoord_apply_zero t₀ p] using hx.1,
          by simpa [mobiusSeamSlidingCoord_apply_zero t₀ p] using hx.2,
          by simpa [mobiusSeamSlidingCoord_apply_one t₀ p, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
            using ht.1,
          by simpa [mobiusSeamSlidingCoord_apply_one t₀ p, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
            using ht.2⟩ = p := by
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    simp [mobiusFDOfSlidingStrict, mobiusSeamSlidingCoord_apply_zero t₀ p]
  · refine Subtype.ext ?_
    simp [mobiusFDOfSlidingStrict, mobiusSeamSlidingCoord_apply_one t₀ p, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc]

/-- Fundamental-domain point from **`w : Subtype V`** when **`V ⊆ mobiusSeamSlidingStrictCoordSet t₀`**.

  Matches the **`Continuous.prodMk`⋯`subtype_mk`** spine used for continuity (**definitionally** the product of the two coordinates). -/
noncomputable def mobiusFDFromSlidingSubtype {t₀ : ℝ} {V : Set R2} (hV : V ⊆ mobiusSeamSlidingStrictCoordSet t₀)
    (w : Subtype V) : MobiusFundamentalDomain :=
  (⟨w.val 0, le_of_lt (hV w.property).1, le_of_lt (hV w.property).2.1⟩,
    ⟨w.val 1 + t₀, le_of_lt (hV w.property).2.2.1, le_of_lt (hV w.property).2.2.2⟩)

theorem mobiusFDFromSlidingSubtype_eq_mobiusFDOfSlidingStrict {t₀ : ℝ} {V : Set R2} (hV : V ⊆ mobiusSeamSlidingStrictCoordSet t₀)
    (w : Subtype V) :
    mobiusFDFromSlidingSubtype hV w =
      mobiusFDOfSlidingStrict t₀ w.val
        ⟨(hV w.property).1, (hV w.property).2.1, (hV w.property).2.2.1, (hV w.property).2.2.2⟩ := by
  simp [mobiusFDFromSlidingSubtype, mobiusFDOfSlidingStrict]

theorem continuous_mobiusFDFromSlidingSubtype {t₀ : ℝ} {V : Set R2} (hV : V ⊆ mobiusSeamSlidingStrictCoordSet t₀) :
    Continuous (mobiusFDFromSlidingSubtype hV) :=
  Continuous.prodMk
    (Continuous.subtype_mk (continuous_mobiusSeamSliding_coord0.comp continuous_subtype_val) fun w =>
      And.intro (le_of_lt (hV w.property).1) (le_of_lt (hV w.property).2.1))
    (Continuous.subtype_mk
      ((continuous_mobiusSeamSliding_coord1.comp continuous_subtype_val).add continuous_const) fun w =>
        And.intro (le_of_lt (hV w.property).2.2.1) (le_of_lt (hV w.property).2.2.2))

theorem mobiusSeamSlidingCoord_mobiusFDFromSlidingSubtype {t₀ : ℝ} {V : Set R2} (hV : V ⊆ mobiusSeamSlidingStrictCoordSet t₀)
    (w : Subtype V) :
    mobiusSeamSlidingCoord t₀ (mobiusFDFromSlidingSubtype hV w) = w.val := by
  simpa [mobiusFDFromSlidingSubtype_eq_mobiusFDOfSlidingStrict hV w] using
    mobiusSeamSlidingCoord_mobiusFDOfSlidingStrict t₀ w.val
      ⟨(hV w.property).1, (hV w.property).2.1, (hV w.property).2.2.1, (hV w.property).2.2.2⟩

/-- Equivalence **`σ⁻¹' V ≃ V`** for **`V ⊆` strict sliding region** (set-level inverse to `σ`). -/
noncomputable def equiv_subtype_mobiusSeamSlidingCoord_preimage {t₀ : ℝ} {V : Set R2}
    (hV : V ⊆ mobiusSeamSlidingStrictCoordSet t₀) :
    Subtype (mobiusSeamSlidingCoord t₀ ⁻¹' V) ≃ Subtype V where
  toFun p :=
    ⟨mobiusSeamSlidingCoord t₀ p.val, mem_preimage.1 p.property⟩
  invFun w :=
    ⟨mobiusFDFromSlidingSubtype hV w,
      (mem_preimage (f := mobiusSeamSlidingCoord t₀) (s := V)).mpr <| by
        rw [mobiusSeamSlidingCoord_mobiusFDFromSlidingSubtype hV w]
        exact w.property⟩
  left_inv := by
    rintro ⟨p, hp⟩
    have hvco := hV (mem_preimage.1 hp)
    have hxp : 0 < p.1.val ∧ p.1.val < 1 :=
      ⟨by simpa [mobiusSeamSlidingStrictCoordSet, mobiusSeamSlidingCoord_apply_zero t₀ p] using hvco.1,
        by simpa [mobiusSeamSlidingStrictCoordSet, mobiusSeamSlidingCoord_apply_zero t₀ p] using hvco.2.1⟩
    have htp : 0 < p.2.val ∧ p.2.val < 1 :=
      ⟨by simpa [mobiusSeamSlidingStrictCoordSet, mobiusSeamSlidingCoord_apply_one t₀ p, sub_eq_add_neg,
            add_assoc, add_comm, add_left_comm] using hvco.2.2.1,
        by simpa [mobiusSeamSlidingStrictCoordSet, mobiusSeamSlidingCoord_apply_one t₀ p, sub_eq_add_neg,
            add_assoc, add_comm, add_left_comm] using hvco.2.2.2⟩
    exact Subtype.ext (mobiusFDOfSlidingStrict_mobiusSeamSlidingCoord t₀ p hxp htp)
  right_inv := by
    rintro ⟨v, hv⟩
    have hst := hV hv
    apply Subtype.ext
    exact mobiusSeamSlidingCoord_mobiusFDOfSlidingStrict t₀ v
      ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2⟩

/-- Homeomorphism **`Subtype (σ⁻¹' V) ≃ₜ Subtype V`** for open (or arbitrary) `V` in the strict region. -/
noncomputable def homeomorph_subtype_mobiusSeamSlidingCoord_preimage {t₀ : ℝ} {V : Set R2}
    (hV : V ⊆ mobiusSeamSlidingStrictCoordSet t₀) :
    Subtype (mobiusSeamSlidingCoord t₀ ⁻¹' V) ≃ₜ Subtype V :=
  Homeomorph.mk
    (equiv_subtype_mobiusSeamSlidingCoord_preimage hV)
    (Continuous.subtype_mk ((continuous_mobiusSeamSlidingCoord t₀).comp continuous_subtype_val)
      fun p => mem_preimage.1 p.property)
    (Continuous.subtype_mk (continuous_mobiusFDFromSlidingSubtype hV) fun w => by
        refine (mem_preimage (f := mobiusSeamSlidingCoord t₀) (s := V)).mpr ?_
        rw [mobiusSeamSlidingCoord_mobiusFDFromSlidingSubtype hV w]
        exact w.property)

/-! ### Local seam flattening map `f : R² → R²` (IFT input) -/

@[simp] private theorem R2_PiLp_proj_apply (u : R2) (i : Fin 2) :
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i u = u i :=
  rfl

@[simp] private theorem R2_continuousLinearEquiv_apply (u : R2) (i : Fin 2) :
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ) u i = u i :=
  rfl

@[simp] private theorem R2_ofLp_apply (u : R2) (i : Fin 2) : u.ofLp i = u i :=
  rfl

/-- Augmented flattening map (quadratic correction in the second coordinate). -/
noncomputable def mobiusSeamLocalMapAug (t₀ : ℝ) (u : R2) : R2 :=
  let u₀ := u 0
  let u₁ := u 1
  let w := u₁ + (t₀ - (1 / 2 : ℝ))
  EuclideanSpace.single (0 : Fin 2) (w * Real.cos (Real.pi * u₀)) +
    EuclideanSpace.single (1 : Fin 2) (w * Real.sin (Real.pi * u₀) + u₀ * (1 - u₀))

/-- **Seam bookkeeping (equator / IFT chart).** On the augmented branch at **`t₀ = ½`**, the composed map
  `mobiusSeamLocalMapAug ½ ∘ mobiusSeamSlidingCoord ½` is **`mobiusRel₀`-invariant**, hence descends to
  `MobiusStrip`. On **`x ∈ {0,1}`** the correction `u₀(1-u₀)` vanishes, so this agrees with
  `mobiusFDTrigCoord`; the invariance is the same trigonometry as `mobiusFDTrigCoord_eq_of_mobiusRel₀`. -/
theorem mobiusSeamLocalMapAug_half_sliding_eq_of_mobiusRel₀ {p q : MobiusFundamentalDomain}
    (h : mobiusRel₀ p q) :
    mobiusSeamLocalMapAug (1 / 2 : ℝ) (mobiusSeamSlidingCoord (1 / 2 : ℝ) p) =
      mobiusSeamLocalMapAug (1 / 2 : ℝ) (mobiusSeamSlidingCoord (1 / 2 : ℝ) q) := by
  rcases h with rfl | hglue
  · rfl
  · rcases hglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
    · -- `(0, t) ~ (1, 1 - t)`
      let tp := p.2.val
      let tq := q.2.val
      have htq : tq = 1 - tp := by linarith [hs]
      have hp0' : p.1.val = 0 := hp0
      have hq1' : q.1.val = 1 := hq1
      ext i
      fin_cases i
      · -- first coordinate
        simp [mobiusSeamLocalMapAug, mobiusSeamSlidingCoord, PiLp.add_apply, EuclideanSpace.single_apply,
          hp0', hq1', htq, Real.cos_zero, Real.cos_pi, Real.sin_zero, Real.sin_pi]
        ring_nf
        linarith
      · -- second coordinate
        simp [mobiusSeamLocalMapAug, mobiusSeamSlidingCoord, PiLp.add_apply, EuclideanSpace.single_apply,
          hp0', hq1', htq, Real.cos_zero, Real.cos_pi, Real.sin_zero, Real.sin_pi]
    · -- `(1, t) ~ (0, 1 - t)`
      let tp := p.2.val
      let tq := q.2.val
      have htq : tq = 1 - tp := by linarith [hs]
      have hp1' : p.1.val = 1 := hp1
      have hq0' : q.1.val = 0 := hq0
      ext i
      fin_cases i
      · simp [mobiusSeamLocalMapAug, mobiusSeamSlidingCoord, PiLp.add_apply, EuclideanSpace.single_apply,
          hp1', hq0', htq, Real.cos_zero, Real.cos_pi, Real.sin_zero, Real.sin_pi]
        ring_nf
        linarith
      · simp [mobiusSeamLocalMapAug, mobiusSeamSlidingCoord, PiLp.add_apply, EuclideanSpace.single_apply,
          hp1', hq0', htq, Real.cos_zero, Real.cos_pi, Real.sin_zero, Real.sin_pi]

/-- Pure trigonometric branch (needed when `π(t₀-½)+1 = 0`). -/
noncomputable def mobiusSeamLocalMapPure (t₀ : ℝ) (u : R2) : R2 :=
  let u₀ := u 0
  let u₁ := u 1
  let w := u₁ + (t₀ - (1 / 2 : ℝ))
  EuclideanSpace.single (0 : Fin 2) (w * Real.cos (Real.pi * u₀)) +
    EuclideanSpace.single (1 : Fin 2) (w * Real.sin (Real.pi * u₀))

/-- Branchwise local model at seam height `t₀` (fixed classically). -/
noncomputable def mobiusSeamLocalMap (t₀ : ℝ) (u : R2) : R2 :=
  if _ : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0 then mobiusSeamLocalMapPure t₀ u
  else mobiusSeamLocalMapAug t₀ u

theorem mobiusSeamLocalMap_eq_aug_of (t₀ : ℝ)
    (h : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 ≠ 0) :
    mobiusSeamLocalMap t₀ = mobiusSeamLocalMapAug t₀ := by
  funext u
  unfold mobiusSeamLocalMap
  split_ifs with hif
  · exfalso; exact h hif
  · rfl

theorem mobiusSeamLocalMap_half_eq_aug :
    mobiusSeamLocalMap (1 / 2 : ℝ) = mobiusSeamLocalMapAug (1 / 2 : ℝ) :=
  mobiusSeamLocalMap_eq_aug_of (1 / 2 : ℝ) (by norm_num)

theorem mobiusSeamLocalMap_half_sliding_eq_of_mobiusRel₀ {p q : MobiusFundamentalDomain}
    (h : mobiusRel₀ p q) :
    mobiusSeamLocalMap (1 / 2 : ℝ) (mobiusSeamSlidingCoord (1 / 2 : ℝ) p) =
      mobiusSeamLocalMap (1 / 2 : ℝ) (mobiusSeamSlidingCoord (1 / 2 : ℝ) q) := by
  simp_rw [mobiusSeamLocalMap_half_eq_aug]
  exact mobiusSeamLocalMapAug_half_sliding_eq_of_mobiusRel₀ h

theorem mobiusSeamLocalMap_eq_pure_of (t₀ : ℝ)
    (h : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0) :
    mobiusSeamLocalMap t₀ = mobiusSeamLocalMapPure t₀ := by
  funext u
  unfold mobiusSeamLocalMap
  split_ifs <;> try contradiction
  · rfl

theorem contDiff_mobiusSeamLocalMapAug (t₀ : ℝ) :
    ContDiff ℝ ⊤ (mobiusSeamLocalMapAug t₀) := by
  haveI := fact_one_le_two_ennreal
  refine (contDiff_piLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)).2 ?_
  intro i
  fin_cases i <;> simp [mobiusSeamLocalMapAug] <;> fun_prop

theorem contDiff_mobiusSeamLocalMapPure (t₀ : ℝ) :
    ContDiff ℝ ⊤ (mobiusSeamLocalMapPure t₀) := by
  haveI := fact_one_le_two_ennreal
  refine (contDiff_piLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)).2 ?_
  intro i
  fin_cases i <;> simp [mobiusSeamLocalMapPure] <;> fun_prop

theorem contDiff_mobiusSeamLocalMap (t₀ : ℝ) :
    ContDiff ℝ ⊤ (mobiusSeamLocalMap t₀) := by
  classical
  by_cases h : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0
  · rw [mobiusSeamLocalMap_eq_pure_of t₀ h]; exact contDiff_mobiusSeamLocalMapPure t₀
  · rw [mobiusSeamLocalMap_eq_aug_of t₀ h]; exact contDiff_mobiusSeamLocalMapAug t₀

theorem continuous_mobiusSeamLocalMap (t₀ : ℝ) : Continuous (mobiusSeamLocalMap t₀) :=
  (contDiff_mobiusSeamLocalMap t₀).continuous

/-- Fréchet derivative operators at `u = 0` (see `hasFDerivAt_mobiusSeamLocalMap*` lemmas). -/
noncomputable def mobiusSeamAugFderivAux (w₀ : ℝ) : R2 →L[ℝ] R2 :=
  let iso : R2 ≃L[ℝ] (Fin 2 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun i : Fin 2 =>
      match i with
      | 0 => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
      | 1 => (Real.pi * w₀ + 1) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  iso.symm.toContinuousLinearMap.comp Dπ

noncomputable def mobiusSeamPureFderivAux (w₀ : ℝ) : R2 →L[ℝ] R2 :=
  let iso : R2 ≃L[ℝ] (Fin 2 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun i : Fin 2 =>
      match i with
      | 0 => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
      | 1 => (Real.pi * w₀) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  iso.symm.toContinuousLinearMap.comp Dπ

private theorem hasFDerivAt_coord0_mobiusSeamAug (t₀ : ℝ) :
    HasFDerivAt (fun u : R2 => (mobiusSeamLocalMapAug t₀ u).ofLp 0)
      (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 1) 0 := by
  let πproj := Real.pi • PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 0
  have hπ_eq : (fun u : R2 => Real.pi * u.ofLp 0) = πproj := by
    funext u
    simp [πproj, ContinuousLinearMap.smul_apply, R2_PiLp_proj_apply, R2_ofLp_apply]
  have hπ : HasFDerivAt (fun u : R2 => Real.pi * u.ofLp 0) πproj 0 := by
    rw [hπ_eq]
    exact πproj.hasFDerivAt
  have hinner := hπ.cos
  simpa [mobiusSeamLocalMapAug, Real.sin_zero, Real.cos_zero, PiLp.zero_apply, neg_zero, zero_smul,
    one_smul, R2_ofLp_apply, EuclideanSpace.single_apply, Fin.sum_univ_two, WithLp.ofLp_add,
    WithLp.ofLp_smul, PiLp.smul_apply] using
    (HasFDerivAt.mul
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) (0 : R2) 1).add
        (hasFDerivAt_const (t₀ - (1 / 2 : ℝ)) (0 : R2))) hinner)

private theorem hasFDerivAt_coord1_mobiusSeamAug (t₀ w₀ : ℝ) (hw₀ : w₀ = t₀ - (1 / 2 : ℝ)) :
    HasFDerivAt (fun u : R2 => (mobiusSeamLocalMapAug t₀ u).ofLp 1)
      ((Real.pi * w₀ + 1) • PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 0) 0 := by
  subst hw₀
  let πproj := Real.pi • PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 0
  have hπ_eq : (fun u : R2 => Real.pi * u.ofLp 0) = πproj := by
    funext u
    simp [πproj, ContinuousLinearMap.smul_apply, R2_PiLp_proj_apply, R2_ofLp_apply]
  have hπ : HasFDerivAt (fun u : R2 => Real.pi * u.ofLp 0) πproj 0 := by
    rw [hπ_eq]
    exact πproj.hasFDerivAt
  have hsincomp := hπ.sin
  have hmul :=
    HasFDerivAt.mul
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) (0 : R2) 1).add
        (hasFDerivAt_const (t₀ - (1 / 2 : ℝ)) (0 : R2))) hsincomp
  have hquad :=
    HasFDerivAt.mul (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) (0 : R2) 0)
      ((hasFDerivAt_const (1 : ℝ) (0 : R2)).sub
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) (0 : R2) 0))
  convert hmul.add hquad using 1
  · ext u
    simp [mobiusSeamLocalMapAug, R2_ofLp_apply, EuclideanSpace.single_apply, Fin.sum_univ_two,
      WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.smul_apply, mul_comm, mul_add, add_mul, sub_eq_add_neg]
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [πproj, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_smul,
      R2_PiLp_proj_apply]
    ring_nf

theorem hasFDerivAt_mobiusSeamLocalMapAug_zero (t₀ : ℝ) :
    HasFDerivAt (mobiusSeamLocalMapAug t₀) (mobiusSeamAugFderivAux (t₀ - (1 / 2 : ℝ))) 0 := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let w₀ := t₀ - (1 / 2 : ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun i1 : Fin 2 =>
      match i1 with
      | 0 => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
      | 1 => (Real.pi * w₀ + 1) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  have harrow : HasFDerivAt (fun u : R2 => iso (mobiusSeamLocalMapAug t₀ u)) Dπ 0 := by
    have hΦ :
        (fun u : R2 => iso (mobiusSeamLocalMapAug t₀ u)) =
          (fun u : R2 => (fun i : Fin 2 => (mobiusSeamLocalMapAug t₀ u).ofLp i)) := by
      funext u i
      rw [R2_continuousLinearEquiv_apply (mobiusSeamLocalMapAug t₀ u) i,
        ← R2_ofLp_apply (mobiusSeamLocalMapAug t₀ u) i]
    rw [hΦ]
    have hDer0 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 ∘L Dπ =
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply]
    have hDer1 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 ∘L Dπ =
          (Real.pi * w₀ + 1) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply]
    refine hasFDerivAt_pi'' ?_
    intro i
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨i, hi⟩
      interval_cases i <;> simp [Fin.ext_iff]
    rcases hi with (rfl | rfl)
    · rw [hDer0]; exact hasFDerivAt_coord0_mobiusSeamAug t₀
    · rw [hDer1]; exact hasFDerivAt_coord1_mobiusSeamAug t₀ w₀ rfl
  have hD :
      (iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamAugFderivAux w₀) = Dπ := by
    refine ContinuousLinearMap.ext fun x => ?_
    funext i
    simp only [ContinuousLinearMap.comp_apply, mobiusSeamAugFderivAux,
      PiLp.continuousLinearEquiv_apply, ContinuousLinearEquiv.apply_symm_apply, Dπ,
      ContinuousLinearMap.pi_apply, PiLp.proj, ContinuousLinearMap.smul_apply]
    fin_cases i <;> rfl
  have harrow' :
      HasFDerivAt (fun u : R2 => iso (mobiusSeamLocalMapAug t₀ u))
        ((iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamAugFderivAux w₀)) 0 := by
    simpa [hD] using harrow
  -- `w₀` is `let`-bound so unfold it for the theorem statement’s `(t₀ - ½)`.
  simpa [Function.comp_def, w₀] using iso.comp_hasFDerivAt_iff.1 harrow'

private theorem hasFDerivAt_coord0_mobiusSeamPure (t₀ : ℝ) :
    HasFDerivAt (fun u : R2 => (mobiusSeamLocalMapPure t₀ u).ofLp 0)
      (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 1) 0 := by
  let πproj := Real.pi • PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 0
  have hπ_eq : (fun u : R2 => Real.pi * u.ofLp 0) = πproj := by
    funext u
    simp [πproj, ContinuousLinearMap.smul_apply, R2_PiLp_proj_apply, R2_ofLp_apply]
  have hπ : HasFDerivAt (fun u : R2 => Real.pi * u.ofLp 0) πproj 0 := by
    rw [hπ_eq]
    exact πproj.hasFDerivAt
  have hinner := hπ.cos
  simpa [mobiusSeamLocalMapPure, Real.sin_zero, Real.cos_zero, PiLp.zero_apply, neg_zero, zero_smul,
    one_smul, R2_ofLp_apply, EuclideanSpace.single_apply, Fin.sum_univ_two, WithLp.ofLp_add,
    WithLp.ofLp_smul, PiLp.smul_apply] using
    (HasFDerivAt.mul
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) (0 : R2) 1).add
        (hasFDerivAt_const (t₀ - (1 / 2 : ℝ)) (0 : R2))) hinner)

private theorem hasFDerivAt_coord1_mobiusSeamPure (t₀ w₀ : ℝ) (hw₀ : w₀ = t₀ - (1 / 2 : ℝ)) :
    HasFDerivAt (fun u : R2 => (mobiusSeamLocalMapPure t₀ u).ofLp 1)
      ((Real.pi * w₀) • PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 0) 0 := by
  subst hw₀
  let πproj := Real.pi • PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 2 => ℝ) 0
  have hπ_eq : (fun u : R2 => Real.pi * u.ofLp 0) = πproj := by
    funext u
    simp [πproj, ContinuousLinearMap.smul_apply, R2_PiLp_proj_apply, R2_ofLp_apply]
  have hπ : HasFDerivAt (fun u : R2 => Real.pi * u.ofLp 0) πproj 0 := by
    rw [hπ_eq]
    exact πproj.hasFDerivAt
  have hsincomp := hπ.sin
  convert
    HasFDerivAt.mul
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) (0 : R2) 1).add
        (hasFDerivAt_const (t₀ - (1 / 2 : ℝ)) (0 : R2))) hsincomp using 1
  · ext u
    simp [mobiusSeamLocalMapPure, R2_ofLp_apply, EuclideanSpace.single_apply, Fin.sum_univ_two,
      WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.smul_apply, mul_comm, mul_add, add_mul, sub_eq_add_neg]
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [πproj, ContinuousLinearMap.smul_apply, R2_PiLp_proj_apply]
    ring

theorem hasFDerivAt_mobiusSeamLocalMapPure_zero (t₀ : ℝ) :
    HasFDerivAt (mobiusSeamLocalMapPure t₀) (mobiusSeamPureFderivAux (t₀ - (1 / 2 : ℝ))) 0 := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let w₀ := t₀ - (1 / 2 : ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun i1 : Fin 2 =>
      match i1 with
      | 0 => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
      | 1 => (Real.pi * w₀) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  have harrow : HasFDerivAt (fun u : R2 => iso (mobiusSeamLocalMapPure t₀ u)) Dπ 0 := by
    have hΦ :
        (fun u : R2 => iso (mobiusSeamLocalMapPure t₀ u)) =
          (fun u : R2 => (fun i : Fin 2 => (mobiusSeamLocalMapPure t₀ u).ofLp i)) := by
      funext u i
      rw [R2_continuousLinearEquiv_apply (mobiusSeamLocalMapPure t₀ u) i,
        ← R2_ofLp_apply (mobiusSeamLocalMapPure t₀ u) i]
    rw [hΦ]
    have hDer0 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 ∘L Dπ =
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply]
    have hDer1 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 ∘L Dπ =
          (Real.pi * w₀) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply]
    refine hasFDerivAt_pi'' ?_
    intro i
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨i, hi⟩
      interval_cases i <;> simp [Fin.ext_iff]
    rcases hi with (rfl | rfl)
    · rw [hDer0]; exact hasFDerivAt_coord0_mobiusSeamPure t₀
    · rw [hDer1]; exact hasFDerivAt_coord1_mobiusSeamPure t₀ w₀ rfl
  have hD :
      (iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamPureFderivAux w₀) = Dπ := by
    refine ContinuousLinearMap.ext fun x => ?_
    funext i
    simp only [ContinuousLinearMap.comp_apply, mobiusSeamPureFderivAux,
      PiLp.continuousLinearEquiv_apply, ContinuousLinearEquiv.apply_symm_apply, Dπ,
      ContinuousLinearMap.pi_apply, PiLp.proj, ContinuousLinearMap.smul_apply]
    fin_cases i <;> rfl
  have harrow' :
      HasFDerivAt (fun u : R2 => iso (mobiusSeamLocalMapPure t₀ u))
        ((iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamPureFderivAux w₀)) 0 := by
    simpa [hD] using harrow
  simpa [Function.comp_def, w₀] using iso.comp_hasFDerivAt_iff.1 harrow'

/-! ### General-point derivative for the pure trig model (`w = u₁ + (t₀ - ½)` can vary) -/

/-- Jacobian as a map `R² → (Fin 2 → ℝ)` used in `mobiusSeamPureFderivAt`. -/
noncomputable def mobiusSeamPureFderivPi (t₀ : ℝ) (u : R2) : R2 →L[ℝ] (Fin 2 → ℝ) :=
  let w := u 1 + (t₀ - (1 / 2 : ℝ))
  let θ := Real.pi * u 0
  ContinuousLinearMap.pi fun i =>
    match i with
    | 0 =>
      (-Real.pi * w * Real.sin θ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.cos θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
    | 1 =>
      (Real.pi * w * Real.cos θ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.sin θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1

/-- Fréchet derivative of `mobiusSeamLocalMapPure t₀` at an arbitrary base point `u : R2`. -/
noncomputable def mobiusSeamPureFderivAt (t₀ : ℝ) (u : R2) : R2 →L[ℝ] R2 :=
  let iso : R2 ≃L[ℝ] (Fin 2 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  iso.symm.toContinuousLinearMap.comp (mobiusSeamPureFderivPi t₀ u)

private theorem hasFDerivAt_coord0_mobiusSeamPureAt (t₀ : ℝ) (u : R2) :
    HasFDerivAt (fun v : R2 => (mobiusSeamLocalMapPure t₀ v).ofLp 0)
      ((-Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) * Real.sin (Real.pi * u 0)) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.cos (Real.pi * u 0) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) u := by
  let c : ℝ := t₀ - (1 / 2 : ℝ)
  let θ : ℝ := Real.pi * u 0
  let w : ℝ := u 1 + c
  have hw :
      HasFDerivAt ((fun v : R2 => v.ofLp 1) + fun _ : R2 => c)
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) u := by
    simpa [add_zero] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) u 1).add
        (hasFDerivAt_const c u)
  have hπcoord :
      HasFDerivAt (fun v : R2 => Real.pi * v.ofLp 0)
        (Real.pi • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) u := by
    simpa [ContinuousLinearMap.smul_apply, PiLp.smul_apply] using
      (Real.pi • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt
  have hcos :
      HasFDerivAt (fun v : R2 => Real.cos (Real.pi * v.ofLp 0))
        ((-Real.sin θ) • (Real.pi • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)) u :=
    hπcoord.cos
  convert HasFDerivAt.mul hw hcos using 1
  · funext v
    simp [mobiusSeamLocalMapPure, c, θ, w, R2_ofLp_apply, EuclideanSpace.single_apply,
      Fin.sum_univ_two, WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.add_apply, PiLp.smul_apply]
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [θ, w, smul_add, smul_smul, mul_assoc, PiLp.proj_apply, R2_PiLp_proj_apply]
    ring

private theorem hasFDerivAt_coord1_mobiusSeamPureAt (t₀ : ℝ) (u : R2) :
    HasFDerivAt (fun v : R2 => (mobiusSeamLocalMapPure t₀ v).ofLp 1)
      ((Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) * Real.cos (Real.pi * u 0)) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.sin (Real.pi * u 0) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) u := by
  let c : ℝ := t₀ - (1 / 2 : ℝ)
  let θ : ℝ := Real.pi * u 0
  let w : ℝ := u 1 + c
  have hw :
      HasFDerivAt ((fun v : R2 => v.ofLp 1) + fun _ : R2 => c)
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) u := by
    simpa [add_zero] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) u 1).add
        (hasFDerivAt_const c u)
  have hπcoord :
      HasFDerivAt (fun v : R2 => Real.pi * v.ofLp 0)
        (Real.pi • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) u := by
    simpa [ContinuousLinearMap.smul_apply, PiLp.smul_apply] using
      (Real.pi • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt
  have hsin :
      HasFDerivAt (fun v : R2 => Real.sin (Real.pi * v.ofLp 0))
        (Real.cos θ • (Real.pi • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)) u :=
    hπcoord.sin
  convert HasFDerivAt.mul hw hsin using 1
  · funext v
    simp [mobiusSeamLocalMapPure, c, θ, w, R2_ofLp_apply, EuclideanSpace.single_apply,
      Fin.sum_univ_two, WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.add_apply, PiLp.smul_apply]
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [θ, w, smul_add, smul_smul, mul_assoc, PiLp.proj_apply, R2_PiLp_proj_apply]
    ring

theorem hasFDerivAt_mobiusSeamLocalMapPure (t₀ : ℝ) (u : R2) :
    HasFDerivAt (mobiusSeamLocalMapPure t₀) (mobiusSeamPureFderivAt t₀ u) u := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) := mobiusSeamPureFderivPi t₀ u
  have harrow : HasFDerivAt (fun v : R2 => iso (mobiusSeamLocalMapPure t₀ v)) Dπ u := by
    let w := u 1 + (t₀ - (1 / 2 : ℝ))
    let θ := Real.pi * u 0
    have hΦ :
        (fun v : R2 => iso (mobiusSeamLocalMapPure t₀ v)) =
          (fun v : R2 => (fun i : Fin 2 => (mobiusSeamLocalMapPure t₀ v).ofLp i)) := by
      funext v i
      rw [R2_continuousLinearEquiv_apply (mobiusSeamLocalMapPure t₀ v) i,
        ← R2_ofLp_apply (mobiusSeamLocalMapPure t₀ v) i]
    rw [hΦ]
    have hDer0 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 ∘L Dπ =
          (-Real.pi * w * Real.sin θ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
            Real.cos θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, mobiusSeamPureFderivPi, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, PiLp.proj_apply, R2_PiLp_proj_apply, w, θ]
    have hDer1 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 ∘L Dπ =
          (Real.pi * w * Real.cos θ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
            Real.sin θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, mobiusSeamPureFderivPi, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, PiLp.proj_apply, R2_PiLp_proj_apply, w, θ]
    refine hasFDerivAt_pi'' ?_
    intro i
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨i, hi⟩
      interval_cases i <;> simp [Fin.ext_iff]
    rcases hi with (rfl | rfl)
    · rw [hDer0]; exact hasFDerivAt_coord0_mobiusSeamPureAt t₀ u
    · rw [hDer1]; exact hasFDerivAt_coord1_mobiusSeamPureAt t₀ u
  have hD : (iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamPureFderivAt t₀ u) = Dπ := rfl
  have harrow' :
      HasFDerivAt (fun v : R2 => iso (mobiusSeamLocalMapPure t₀ v))
        ((iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamPureFderivAt t₀ u)) u := by
    simpa [hD] using harrow
  simpa [Function.comp_def] using iso.comp_hasFDerivAt_iff.1 harrow'

private theorem injective_mobiusSeamPureFderivAt (t₀ : ℝ) (u : R2)
    (hw : u 1 + (t₀ - (1 / 2 : ℝ)) ≠ 0) :
    Function.Injective (mobiusSeamPureFderivAt t₀ u) := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let w := u 1 + (t₀ - (1 / 2 : ℝ))
  let θ := Real.pi * u 0
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) := mobiusSeamPureFderivPi t₀ u
  refine (LinearMap.ker_eq_bot (f := (mobiusSeamPureFderivAt t₀ u).toLinearMap)).mp ?_
  refine (Submodule.eq_bot_iff _).2 ?_
  intro v hv
  have hv0 : mobiusSeamPureFderivAt t₀ u v = 0 :=
    (LinearMap.mem_ker (f := (mobiusSeamPureFderivAt t₀ u).toLinearMap)).1 hv
  have hσ : iso.symm (Dπ v) = 0 := by
    simpa [mobiusSeamPureFderivAt, ContinuousLinearMap.comp_apply, Dπ, w, θ] using hv0
  have hDπ : Dπ v = 0 := by
    rw [← ContinuousLinearEquiv.apply_symm_apply iso (Dπ v), hσ, map_zero]
  have eq0 : (-Real.pi * w * Real.sin θ) * v 0 + Real.cos θ * v 1 = 0 := by
    simpa [Dπ, mobiusSeamPureFderivPi, ContinuousLinearMap.pi_apply, PiLp.proj,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, R2_PiLp_proj_apply, w, θ]
      using congrArg (fun z => z 0) hDπ
  have eq1 : (Real.pi * w * Real.cos θ) * v 0 + Real.sin θ * v 1 = 0 := by
    simpa [Dπ, mobiusSeamPureFderivPi, ContinuousLinearMap.pi_apply, PiLp.proj,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, R2_PiLp_proj_apply, w, θ]
      using congrArg (fun z => z 1) hDπ
  have hπ0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hwπ : Real.pi * w ≠ 0 := mul_ne_zero hπ0 hw
  have hv0' : v 0 = 0 := by
    have hcomb :
        Real.sin θ * ((-Real.pi * w * Real.sin θ) * v 0 + Real.cos θ * v 1) +
          (-Real.cos θ) * ((Real.pi * w * Real.cos θ) * v 0 + Real.sin θ * v 1) = 0 := by
      rw [eq0, eq1]
      ring
    have hvanish : (-Real.pi * w) * v 0 = 0 := by
      have hstep :
          (-Real.pi * w * (Real.sin θ ^ 2 + Real.cos θ ^ 2)) * v 0 =
            Real.sin θ * ((-Real.pi * w * Real.sin θ) * v 0 + Real.cos θ * v 1) +
              (-Real.cos θ) * ((Real.pi * w * Real.cos θ) * v 0 + Real.sin θ * v 1) := by
        ring_nf
      calc
        (-Real.pi * w) * v 0 = (-Real.pi * w * (Real.sin θ ^ 2 + Real.cos θ ^ 2)) * v 0 := by
          simp [Real.sin_sq_add_cos_sq θ]
        _ = 0 := by rw [hstep, hcomb]
    rcases (mul_eq_zero.mp hvanish) with hp | hz
    · have hp' : Real.pi * w = 0 := by
        simpa [neg_mul, neg_eq_zero] using hp
      exact False.elim (hwπ hp')
    · exact hz
  have hv1' : v 1 = 0 := by
    rw [hv0'] at eq0 eq1
    simp only [mul_zero, zero_add] at eq0 eq1
    rcases (mul_eq_zero.mp eq0) with hc | hv₁
    · rcases (mul_eq_zero.mp eq1) with hs | hv₁'
      · exfalso
        have ident := Real.cos_sq_add_sin_sq θ
        simp [hc, hs] at ident
      · exact hv₁'
    · exact hv₁
  ext i
  fin_cases i <;> simp [hv0', hv1']

/-- Invertible derivative of `mobiusSeamLocalMapPure t₀` at `u` when `u₁ + (t₀ - ½) ≠ 0`. -/
noncomputable def mobiusSeamPureFderivContinuousLinearEquivAt (t₀ : ℝ) (u : R2)
    (hw : u 1 + (t₀ - (1 / 2 : ℝ)) ≠ 0) :
    R2 ≃L[ℝ] R2 :=
  (LinearEquiv.ofInjectiveEndo (mobiusSeamPureFderivAt t₀ u).toLinearMap
      (injective_mobiusSeamPureFderivAt t₀ u hw)).toContinuousLinearEquiv

theorem hasFDerivAt_mobiusSeamLocalMapPure_continuousLinearEquivAt (t₀ : ℝ) (u : R2)
    (hw : u 1 + (t₀ - (1 / 2 : ℝ)) ≠ 0) :
    HasFDerivAt (mobiusSeamLocalMapPure t₀)
      (mobiusSeamPureFderivContinuousLinearEquivAt t₀ u hw : R2 →L[ℝ] R2) u :=
  hasFDerivAt_mobiusSeamLocalMapPure t₀ u

/-- **Strict** derivative with an invertible `≃L` (IFT input) at `u`. -/
theorem hasStrictFDerivAt_mobiusSeamLocalMapPure_of_ne (t₀ : ℝ) (u : R2)
    (hw : u 1 + (t₀ - (1 / 2 : ℝ)) ≠ 0) :
    HasStrictFDerivAt (mobiusSeamLocalMapPure t₀)
      (mobiusSeamPureFderivContinuousLinearEquivAt t₀ u hw : R2 →L[ℝ] R2) u := by
  have hf₁ : ContDiffAt ℝ 1 (mobiusSeamLocalMapPure t₀) u :=
    ContDiffAt.of_le (ContDiff.contDiffAt (contDiff_mobiusSeamLocalMapPure t₀) (x := u)) le_top
  simpa using
    hf₁.hasStrictFDerivAt' (hasFDerivAt_mobiusSeamLocalMapPure_continuousLinearEquivAt t₀ u hw)
      one_ne_zero

/-- Push-forward of neighborhoods under the pure seam map at a **nonsingular** height `w ≠ 0`. -/
theorem map_nhds_mobiusSeamLocalMapPure (t₀ : ℝ) (u : R2)
    (hw : u 1 + (t₀ - (1 / 2 : ℝ)) ≠ 0) :
    map (mobiusSeamLocalMapPure t₀) (𝓝 u) = 𝓝 (mobiusSeamLocalMapPure t₀ u) :=
  HasStrictFDerivAt.map_nhds_eq_of_equiv (hasStrictFDerivAt_mobiusSeamLocalMapPure_of_ne t₀ u hw)

noncomputable abbrev mobiusPlaneTrigCoordMap : R2 → R2 :=
  mobiusSeamLocalMapPure 0

theorem hasStrictFDerivAt_mobiusPlaneTrigCoordMap_of_ne_half {v : R2} (hv : v 1 ≠ (1 / 2 : ℝ)) :
    HasStrictFDerivAt mobiusPlaneTrigCoordMap
      (mobiusSeamPureFderivContinuousLinearEquivAt 0 v
        (by intro h; apply hv; linarith) :
        R2 →L[ℝ] R2) v :=
  hasStrictFDerivAt_mobiusSeamLocalMapPure_of_ne 0 v (by intro h; apply hv; linarith)

theorem map_nhds_mobiusPlaneTrigCoordMap {v : R2} (hv : v 1 ≠ (1 / 2 : ℝ)) :
    map mobiusPlaneTrigCoordMap (𝓝 v) = 𝓝 (mobiusPlaneTrigCoordMap v) :=
  HasStrictFDerivAt.map_nhds_eq_of_equiv (hasStrictFDerivAt_mobiusPlaneTrigCoordMap_of_ne_half hv)

/-! ### General-point derivative for the augmented seam model (`mobiusSeamLocalMapAug`) -/

/-- Coordinate representation of `fderiv (mobiusSeamLocalMapAug t₀) u` as `R² → (Fin 2 → ℝ)`. -/
noncomputable def mobiusSeamAugFderivPiAt (t₀ : ℝ) (u : R2) : R2 →L[ℝ] (Fin 2 → ℝ) :=
  let w := u 1 + (t₀ - (1 / 2 : ℝ))
  let θ := Real.pi * u 0
  ContinuousLinearMap.pi fun i =>
    match i with
    | 0 =>
      (-Real.pi * w * Real.sin θ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.cos θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
    | 1 =>
      (Real.pi * w * Real.cos θ + (1 - 2 * u 0)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.sin θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1

/-- Fréchet derivative of `mobiusSeamLocalMapAug t₀` at an arbitrary base point `u`. -/
noncomputable def mobiusSeamAugFderivAt (t₀ : ℝ) (u : R2) : R2 →L[ℝ] R2 :=
  let iso : R2 ≃L[ℝ] (Fin 2 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  iso.symm.toContinuousLinearMap.comp (mobiusSeamAugFderivPiAt t₀ u)

private theorem hasFDerivAt_coord0_mobiusSeamAugAt (t₀ : ℝ) (u : R2) :
    HasFDerivAt (fun v : R2 => (mobiusSeamLocalMapAug t₀ v).ofLp 0)
      ((-Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) * Real.sin (Real.pi * u 0)) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.cos (Real.pi * u 0) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) u := by
  simpa [mobiusSeamLocalMapAug, mobiusSeamLocalMapPure] using hasFDerivAt_coord0_mobiusSeamPureAt t₀ u

private theorem hasFDerivAt_coord1_mobiusSeamAugAt (t₀ : ℝ) (u : R2) :
    HasFDerivAt (fun v : R2 => (mobiusSeamLocalMapAug t₀ v).ofLp 1)
      ((Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) * Real.cos (Real.pi * u 0) + (1 - 2 * u 0)) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
        Real.sin (Real.pi * u 0) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) u := by
  let c : ℝ := t₀ - (1 / 2 : ℝ)
  let θ : ℝ := Real.pi * u 0
  let w : ℝ := u 1 + c
  have hpure :
      HasFDerivAt (fun v : R2 => (mobiusSeamLocalMapPure t₀ v).ofLp 1)
        ((Real.pi * w * Real.cos θ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
          Real.sin θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) u :=
    hasFDerivAt_coord1_mobiusSeamPureAt t₀ u
  have hquad :
      HasFDerivAt (fun v : R2 => v.ofLp 0 * (1 - v.ofLp 0))
        ((1 - 2 * u 0) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) u := by
    have :=
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ) u 0).mul
        ((hasFDerivAt_const (1 : ℝ) u).sub (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2)
          (E := fun _ : Fin 2 => ℝ) u 0))
    convert this using 1
    · refine ContinuousLinearMap.ext fun z => ?_
      simp [PiLp.proj_apply, R2_PiLp_proj_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
      ring
  convert hpure.add hquad using 1
  · funext v
    simp [mobiusSeamLocalMapAug, mobiusSeamLocalMapPure, c, θ, w, R2_ofLp_apply,
      EuclideanSpace.single_apply, Fin.sum_univ_two, WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.add_apply,
      PiLp.smul_apply]
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [smul_add, PiLp.proj_apply, R2_PiLp_proj_apply, ContinuousLinearMap.add_apply]
    ring

theorem hasFDerivAt_mobiusSeamLocalMapAug (t₀ : ℝ) (u : R2) :
    HasFDerivAt (mobiusSeamLocalMapAug t₀) (mobiusSeamAugFderivAt t₀ u) u := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) := mobiusSeamAugFderivPiAt t₀ u
  have harrow : HasFDerivAt (fun v : R2 => iso (mobiusSeamLocalMapAug t₀ v)) Dπ u := by
    let w := u 1 + (t₀ - (1 / 2 : ℝ))
    let θ := Real.pi * u 0
    have hΦ :
        (fun v : R2 => iso (mobiusSeamLocalMapAug t₀ v)) =
          (fun v : R2 => (fun i : Fin 2 => (mobiusSeamLocalMapAug t₀ v).ofLp i)) := by
      funext v i
      rw [R2_continuousLinearEquiv_apply (mobiusSeamLocalMapAug t₀ v) i,
        ← R2_ofLp_apply (mobiusSeamLocalMapAug t₀ v) i]
    rw [hΦ]
    have hDer0 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 ∘L Dπ =
          (-Real.pi * w * Real.sin θ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
            Real.cos θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, mobiusSeamAugFderivPiAt, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, PiLp.proj_apply, R2_PiLp_proj_apply, w, θ]
    have hDer1 :
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 ∘L Dπ =
          (Real.pi * w * Real.cos θ + (1 - 2 * u 0)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 +
            Real.sin θ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 := by
      refine ContinuousLinearMap.ext fun z => ?_
      simp [Dπ, mobiusSeamAugFderivPiAt, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, PiLp.proj_apply, R2_PiLp_proj_apply, w, θ]
    refine hasFDerivAt_pi'' ?_
    intro i
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨i, hi⟩
      interval_cases i <;> simp [Fin.ext_iff]
    rcases hi with (rfl | rfl)
    · rw [hDer0]; exact hasFDerivAt_coord0_mobiusSeamAugAt t₀ u
    · rw [hDer1]; exact hasFDerivAt_coord1_mobiusSeamAugAt t₀ u
  have hD : (iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamAugFderivAt t₀ u) = Dπ := rfl
  have harrow' :
      HasFDerivAt (fun v : R2 => iso (mobiusSeamLocalMapAug t₀ v))
        ((iso : R2 →L[ℝ] (Fin 2 → ℝ)).comp (mobiusSeamAugFderivAt t₀ u)) u := by
    simpa [hD] using harrow
  simpa [Function.comp_def] using iso.comp_hasFDerivAt_iff.1 harrow'

private theorem injective_mobiusSeamAugFderivAt_kernel (t₀ : ℝ) (u : R2)
    (hdet :
      Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) + (1 - 2 * u 0) * Real.cos (Real.pi * u 0) ≠ 0) :
    Function.Injective (mobiusSeamAugFderivAt t₀ u) := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let w := u 1 + (t₀ - (1 / 2 : ℝ))
  let θ := Real.pi * u 0
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) := mobiusSeamAugFderivPiAt t₀ u
  refine (LinearMap.ker_eq_bot (f := (mobiusSeamAugFderivAt t₀ u).toLinearMap)).mp ?_
  refine (Submodule.eq_bot_iff _).2 ?_
  intro v hv
  have hv0 : mobiusSeamAugFderivAt t₀ u v = 0 :=
    (LinearMap.mem_ker (f := (mobiusSeamAugFderivAt t₀ u).toLinearMap)).1 hv
  have hσ : iso.symm (Dπ v) = 0 := by
    simpa [mobiusSeamAugFderivAt, ContinuousLinearMap.comp_apply, Dπ, w, θ] using hv0
  have hDπ : Dπ v = 0 := by
    rw [← ContinuousLinearEquiv.apply_symm_apply iso (Dπ v), hσ, map_zero]
  have eq0 : (-Real.pi * w * Real.sin θ) * v 0 + Real.cos θ * v 1 = 0 := by
    simpa [Dπ, mobiusSeamAugFderivPiAt, ContinuousLinearMap.pi_apply, PiLp.proj,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, R2_PiLp_proj_apply, w, θ]
      using congrArg (fun z => z 0) hDπ
  have eq1 : (Real.pi * w * Real.cos θ + (1 - 2 * u 0)) * v 0 + Real.sin θ * v 1 = 0 := by
    simpa [Dπ, mobiusSeamAugFderivPiAt, ContinuousLinearMap.pi_apply, PiLp.proj,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, R2_PiLp_proj_apply, w, θ]
      using congrArg (fun z => z 1) hDπ
  have hv0' : v 0 = 0 := by
    have hexp :
        Real.cos θ * ((Real.pi * w * Real.cos θ + (1 - 2 * u 0)) * v 0 + Real.sin θ * v 1)
            - Real.sin θ * ((-Real.pi * w * Real.sin θ) * v 0 + Real.cos θ * v 1)
            = (Real.pi * w + (1 - 2 * u 0) * Real.cos θ) * v 0 := by
      rw [show
            Real.cos θ * ((Real.pi * w * Real.cos θ + (1 - 2 * u 0)) * v 0 + Real.sin θ * v 1)
                - Real.sin θ * ((-Real.pi * w * Real.sin θ) * v 0 + Real.cos θ * v 1)
              = (Real.pi * w * (Real.cos θ ^ 2 + Real.sin θ ^ 2) + (1 - 2 * u 0) * Real.cos θ) * v 0 by
            ring]
      rw [Real.cos_sq_add_sin_sq θ]
      ring
    have hzero :
        Real.cos θ * ((Real.pi * w * Real.cos θ + (1 - 2 * u 0)) * v 0 + Real.sin θ * v 1)
            - Real.sin θ * ((-Real.pi * w * Real.sin θ) * v 0 + Real.cos θ * v 1) = 0 := by
      rw [eq1, eq0]
      ring
    have hvc : (Real.pi * w + (1 - 2 * u 0) * Real.cos θ) * v 0 = 0 :=
      hexp.symm.trans hzero
    rcases (mul_eq_zero.mp hvc) with h | hz
    · exact False.elim (hdet h)
    · exact hz
  have hv1' : v 1 = 0 := by
    rw [hv0'] at eq0 eq1
    simp only [mul_zero, zero_add] at eq0 eq1
    calc
      v 1 = v 1 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by rw [Real.cos_sq_add_sin_sq θ]; ring
      _ = Real.cos θ * (Real.cos θ * v 1) + Real.sin θ * (Real.sin θ * v 1) := by ring
      _ = 0 := by rw [eq0, eq1]; ring
  ext i
  fin_cases i <;> simp [hv0', hv1']

/-- Invertible Fréchet derivative of `mobiusSeamLocalMapAug t₀` at `u` under
`π w + (1 - 2 u₀) cos(π u₀) ≠ 0` with `w = u₁ + (t₀ - ½)`. -/
noncomputable def mobiusSeamAugFderivContinuousLinearEquivAt (t₀ : ℝ) (u : R2)
    (hdet :
      Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) + (1 - 2 * u 0) * Real.cos (Real.pi * u 0) ≠ 0) :
    R2 ≃L[ℝ] R2 :=
  (LinearEquiv.ofInjectiveEndo (mobiusSeamAugFderivAt t₀ u).toLinearMap
      (injective_mobiusSeamAugFderivAt_kernel t₀ u hdet)).toContinuousLinearEquiv

theorem hasFDerivAt_mobiusSeamLocalMapAug_continuousLinearEquivAt (t₀ : ℝ) (u : R2)
    (hdet :
      Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) + (1 - 2 * u 0) * Real.cos (Real.pi * u 0) ≠ 0) :
    HasFDerivAt (mobiusSeamLocalMapAug t₀)
      (mobiusSeamAugFderivContinuousLinearEquivAt t₀ u hdet : R2 →L[ℝ] R2) u :=
  hasFDerivAt_mobiusSeamLocalMapAug t₀ u

theorem hasStrictFDerivAt_mobiusSeamLocalMapAug_of_det_ne (t₀ : ℝ) (u : R2)
    (hdet :
      Real.pi * (u 1 + (t₀ - (1 / 2 : ℝ))) + (1 - 2 * u 0) * Real.cos (Real.pi * u 0) ≠ 0) :
    HasStrictFDerivAt (mobiusSeamLocalMapAug t₀)
      (mobiusSeamAugFderivContinuousLinearEquivAt t₀ u hdet : R2 →L[ℝ] R2) u := by
  have hf₁ : ContDiffAt ℝ 1 (mobiusSeamLocalMapAug t₀) u :=
    ContDiffAt.of_le (ContDiff.contDiffAt (contDiff_mobiusSeamLocalMapAug t₀) (x := u)) le_top
  simpa using
    hf₁.hasStrictFDerivAt' (hasFDerivAt_mobiusSeamLocalMapAug_continuousLinearEquivAt t₀ u hdet)
      one_ne_zero

theorem hasFDerivAt_mobiusSeamLocalMap_zero (t₀ : ℝ) :
    HasFDerivAt (mobiusSeamLocalMap t₀)
      (if _ : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0 then
        mobiusSeamPureFderivAux (t₀ - (1 / 2 : ℝ))
      else mobiusSeamAugFderivAux (t₀ - (1 / 2 : ℝ))) 0 := by
  classical
  by_cases h : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0
  · simp only [h, mobiusSeamLocalMap_eq_pure_of t₀ h]; exact hasFDerivAt_mobiusSeamLocalMapPure_zero t₀
  · simp only [h, mobiusSeamLocalMap_eq_aug_of t₀ h]; exact hasFDerivAt_mobiusSeamLocalMapAug_zero t₀

/-! ### Invertible derivative (`≃L`) for the inverse function theorem -/

private theorem injective_mobiusSeamAugFderivAux (w₀ : ℝ) (h : Real.pi * w₀ + 1 ≠ 0) :
    Function.Injective (mobiusSeamAugFderivAux w₀) := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun i1 : Fin 2 =>
      match i1 with
      | 0 => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
      | 1 => (Real.pi * w₀ + 1) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  refine (LinearMap.ker_eq_bot (R := ℝ) (M := R2)
    (f := (mobiusSeamAugFderivAux w₀).toLinearMap)).mp ?_
  refine (Submodule.eq_bot_iff _).2 ?_
  intro v hv
  have hv0 : mobiusSeamAugFderivAux w₀ v = 0 :=
    (LinearMap.mem_ker (f := (mobiusSeamAugFderivAux w₀).toLinearMap)).1 hv
  have hσ : iso.symm (Dπ v) = 0 := by
    simpa [mobiusSeamAugFderivAux, ContinuousLinearMap.comp_apply] using hv0
  have hDπ : Dπ v = 0 := by
    rw [← ContinuousLinearEquiv.apply_symm_apply iso (Dπ v), hσ, map_zero]
  have h01 : (Dπ v) (0 : Fin 2) = 0 := congrArg (fun z => z 0) hDπ
  have h11 : (Dπ v) (1 : Fin 2) = 0 := congrArg (fun z => z 1) hDπ
  simp only [Dπ, ContinuousLinearMap.pi_apply, PiLp.proj, ContinuousLinearMap.smul_apply] at h01 h11
  have hv1 : v (1 : Fin 2) = 0 := by simpa [R2_PiLp_proj_apply] using h01
  have hv0' : v (0 : Fin 2) = 0 := by
    rcases (mul_eq_zero.mp h11) with hπ | hproj
    · exact False.elim (h hπ)
    · simpa [R2_PiLp_proj_apply] using hproj
  ext i
  fin_cases i <;> assumption

private theorem injective_mobiusSeamPureFderivAux (w₀ : ℝ) (h : Real.pi * w₀ ≠ 0) :
    Function.Injective (mobiusSeamPureFderivAux w₀) := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun i1 : Fin 2 =>
      match i1 with
      | 0 => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
      | 1 => (Real.pi * w₀) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  refine (LinearMap.ker_eq_bot (R := ℝ) (M := R2)
    (f := (mobiusSeamPureFderivAux w₀).toLinearMap)).mp ?_
  refine (Submodule.eq_bot_iff _).2 ?_
  intro v hv
  have hv0 : mobiusSeamPureFderivAux w₀ v = 0 :=
    (LinearMap.mem_ker (f := (mobiusSeamPureFderivAux w₀).toLinearMap)).1 hv
  have hσ : iso.symm (Dπ v) = 0 := by
    simpa [mobiusSeamPureFderivAux, ContinuousLinearMap.comp_apply] using hv0
  have hDπ : Dπ v = 0 := by
    rw [← ContinuousLinearEquiv.apply_symm_apply iso (Dπ v), hσ, map_zero]
  have h01 : (Dπ v) (0 : Fin 2) = 0 := congrArg (fun z => z 0) hDπ
  have h11 : (Dπ v) (1 : Fin 2) = 0 := congrArg (fun z => z 1) hDπ
  simp only [Dπ, ContinuousLinearMap.pi_apply, PiLp.proj, ContinuousLinearMap.smul_apply] at h01 h11
  have hv1 : v (1 : Fin 2) = 0 := by simpa [R2_PiLp_proj_apply] using h01
  have hv0' : v (0 : Fin 2) = 0 := by
    rcases (mul_eq_zero.mp h11) with hπ | hproj
    · exact False.elim (h hπ)
    · simpa [R2_PiLp_proj_apply] using hproj
  ext i
  fin_cases i <;> assumption

/-- Invertible (₂×₂) derivative in the augmented (`π w₀ + 1 ≠ 0`) branch. -/
noncomputable def mobiusSeamAugFderivContinuousLinearEquiv (w₀ : ℝ) (h : Real.pi * w₀ + 1 ≠ 0) :
    R2 ≃L[ℝ] R2 :=
  (LinearEquiv.ofInjectiveEndo (mobiusSeamAugFderivAux w₀).toLinearMap
      (injective_mobiusSeamAugFderivAux w₀ h)).toContinuousLinearEquiv

/-- Invertible derivative in the pure (`π w₀ + 1 = 0`) branch; requires `π w₀ ≠ 0` (e.g. `w₀ = -1/π`). -/
noncomputable def mobiusSeamPureFderivContinuousLinearEquiv (w₀ : ℝ) (h : Real.pi * w₀ ≠ 0) :
    R2 ≃L[ℝ] R2 :=
  (LinearEquiv.ofInjectiveEndo (mobiusSeamPureFderivAux w₀).toLinearMap
      (injective_mobiusSeamPureFderivAux w₀ h)).toContinuousLinearEquiv

theorem hasFDerivAt_mobiusSeamLocalMapAug_zero_equiv (t₀ : ℝ)
    (hne : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 ≠ 0) :
    HasFDerivAt (mobiusSeamLocalMapAug t₀)
      (mobiusSeamAugFderivContinuousLinearEquiv (t₀ - (1 / 2 : ℝ)) hne : R2 →L[ℝ] R2) 0 :=
  hasFDerivAt_mobiusSeamLocalMapAug_zero t₀

/-- At the unique seam height where `π(t₀ - ½) + 1 = 0`, the pure flattening map still has
invertible linearization since `π (t₀ - ½) ≠ 0`. -/
theorem hasFDerivAt_mobiusSeamLocalMapPure_zero_equiv (t₀ : ℝ)
    (hpi1 : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0) :
    HasFDerivAt (mobiusSeamLocalMapPure t₀)
      (mobiusSeamPureFderivContinuousLinearEquiv (t₀ - (1 / 2 : ℝ))
          (by intro hπw; have := congrArg (fun x => x + (1 : ℝ)) hpi1; linarith [hπw]) :
        R2 →L[ℝ] R2) 0 :=
  hasFDerivAt_mobiusSeamLocalMapPure_zero t₀

theorem hasFDerivAt_mobiusSeamLocalMap_zero_equiv (t₀ : ℝ) :
    HasFDerivAt (mobiusSeamLocalMap t₀)
      (if h1 : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0 then
        (mobiusSeamPureFderivContinuousLinearEquiv (t₀ - (1 / 2 : ℝ))
            (by intro hπw; have := congrArg (fun x => x + (1 : ℝ)) h1; linarith [hπw]) :
          R2 →L[ℝ] R2)
      else
        (mobiusSeamAugFderivContinuousLinearEquiv (t₀ - (1 / 2 : ℝ)) h1 : R2 →L[ℝ] R2)) 0 := by
  classical
  by_cases h1 : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0
  · simp only [dif_pos h1, mobiusSeamLocalMap_eq_pure_of t₀ h1]
    exact hasFDerivAt_mobiusSeamLocalMapPure_zero_equiv t₀ h1
  · simp only [dif_neg h1, mobiusSeamLocalMap_eq_aug_of t₀ h1]
    exact hasFDerivAt_mobiusSeamLocalMapAug_zero_equiv t₀ h1

theorem hasFDerivAt_mobiusSeamLocalMap_zero_pureBranch (t₀ : ℝ)
    (h1 : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0) :
    HasFDerivAt (mobiusSeamLocalMap t₀)
      (mobiusSeamPureFderivContinuousLinearEquiv (t₀ - (1 / 2 : ℝ))
          (by intro hπw; have := congrArg (fun x => x + (1 : ℝ)) h1; linarith [hπw]) :
        R2 →L[ℝ] R2) 0 := by
  simpa [mobiusSeamLocalMap_eq_pure_of t₀ h1] using hasFDerivAt_mobiusSeamLocalMapPure_zero_equiv t₀ h1

theorem hasFDerivAt_mobiusSeamLocalMap_zero_augBranch (t₀ : ℝ)
    (h1 : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 ≠ 0) :
    HasFDerivAt (mobiusSeamLocalMap t₀)
      (mobiusSeamAugFderivContinuousLinearEquiv (t₀ - (1 / 2 : ℝ)) h1 : R2 →L[ℝ] R2) 0 := by
  simpa [mobiusSeamLocalMap_eq_aug_of t₀ h1] using hasFDerivAt_mobiusSeamLocalMapAug_zero_equiv t₀ h1

/-! ### `OpenPartialHomeomorph` from the inverse function theorem (source ⊂ `R²`, `toFun = f`)

  The **quotient** `ChartableR2` step on `MobiusStrip` still requires gluing this local model to
  fundamental-domain / `Quotient.mk` opens; saturated seam neighborhoods **pair** two FD points, so the
  injective `Subtype W → Quotient` pattern from `mobiusQuotientMk_subtype_homeomorph` does not apply
  verbatim — use this partial homeomorphism plus a **section** (e.g. chart from the `x`–small half only)
  or an explicit factorization through `mobiusStripTrigCoord`. -/

/-- `C¹` at `0` suffices for Mathlib’s `ContDiffAt.toOpenPartialHomeomorph`. -/
private theorem contDiffAt_one_mobiusSeamLocalMap_zero (t₀ : ℝ) :
    ContDiffAt ℝ 1 (mobiusSeamLocalMap t₀) 0 :=
  ContDiff.contDiffAt ((contDiff_mobiusSeamLocalMap t₀).of_le le_top) (x := 0)

/-- Local `C¹` diffeomorphism `R² ⇝ R²` extending `mobiusSeamLocalMap t₀` near `0`. -/
noncomputable def mobiusSeamLocalMapOpenPartialHomeomorph (t₀ : ℝ) : OpenPartialHomeomorph R2 R2 :=
  open Classical in
  if h1 : Real.pi * (t₀ - (1 / 2 : ℝ)) + 1 = 0 then
    (contDiffAt_one_mobiusSeamLocalMap_zero t₀).toOpenPartialHomeomorph (mobiusSeamLocalMap t₀)
      (hasFDerivAt_mobiusSeamLocalMap_zero_pureBranch t₀ h1) one_ne_zero
  else
    (contDiffAt_one_mobiusSeamLocalMap_zero t₀).toOpenPartialHomeomorph (mobiusSeamLocalMap t₀)
      (hasFDerivAt_mobiusSeamLocalMap_zero_augBranch t₀ h1) one_ne_zero

theorem zero_mem_mobiusSeamLocalMapOpenPartialHomeomorph_source (t₀ : ℝ) :
    (0 : R2) ∈ (mobiusSeamLocalMapOpenPartialHomeomorph t₀).source := by
  classical
  unfold mobiusSeamLocalMapOpenPartialHomeomorph
  split_ifs with h1 <;>
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ one_ne_zero

theorem mobiusSeamLocalMapOpenPartialHomeomorph_toFun (t₀ : ℝ) :
    (mobiusSeamLocalMapOpenPartialHomeomorph t₀).toFun = mobiusSeamLocalMap t₀ := by
  classical
  unfold mobiusSeamLocalMapOpenPartialHomeomorph
  split_ifs <;> exact ContDiffAt.toOpenPartialHomeomorph_coe _ _ one_ne_zero

theorem image_zero_mem_mobiusSeamLocalMapOpenPartialHomeomorph_target (t₀ : ℝ) :
    mobiusSeamLocalMap t₀ 0 ∈ (mobiusSeamLocalMapOpenPartialHomeomorph t₀).target := by
  classical
  unfold mobiusSeamLocalMapOpenPartialHomeomorph
  split_ifs with h1 <;>
    exact ContDiffAt.image_mem_toOpenPartialHomeomorph_target _ _ one_ne_zero

/-- Some Euclidean **ball around `0`** lies in the **IFT source** of `mobiusSeamLocalMapOpenPartialHomeomorph t₀`. -/
theorem exists_pos_radius_ball_subset_mobiusSeamLocalMapOpenPartialHomeomorph_source (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : R2) ε ⊆ (mobiusSeamLocalMapOpenPartialHomeomorph t₀).source := by
  classical
  have hn :=
    (mobiusSeamLocalMapOpenPartialHomeomorph t₀).open_source.mem_nhds
      (zero_mem_mobiusSeamLocalMapOpenPartialHomeomorph_source t₀)
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  exact ⟨ε, hε, hball⟩

/-! ### Half-sliding FD coordinate (equator chart) -/

/-- **Sliding plane map at `t₀ = ½`**: `mobiusSeamLocalMap (1/2) ∘ mobiusSeamSlidingCoord (1/2)`,
  constant on `mobiusRel₀` by `mobiusSeamLocalMap_half_sliding_eq_of_mobiusRel₀`. -/
noncomputable def mobiusFDHalfSlidingCoord (p : MobiusFundamentalDomain) : R2 :=
  mobiusSeamLocalMap (1 / 2 : ℝ) (mobiusSeamSlidingCoord (1 / 2 : ℝ) p)

theorem mobiusFDHalfSlidingCoord_eq_of_mobiusRel₀ {p q : MobiusFundamentalDomain}
    (h : mobiusRel₀ p q) :
    mobiusFDHalfSlidingCoord p = mobiusFDHalfSlidingCoord q :=
  mobiusSeamLocalMap_half_sliding_eq_of_mobiusRel₀ h

noncomputable abbrev mobiusStripHalfSlidingCoord : MobiusStrip → R2 :=
  Quotient.lift mobiusFDHalfSlidingCoord fun _ _ hr =>
    mobiusFDHalfSlidingCoord_eq_of_mobiusRel₀ hr

theorem continuous_mobiusFDHalfSlidingCoord : Continuous mobiusFDHalfSlidingCoord :=
  (continuous_mobiusSeamLocalMap _).comp (continuous_mobiusSeamSlidingCoord _)

theorem continuous_mobiusStripHalfSlidingCoord : Continuous mobiusStripHalfSlidingCoord :=
  Continuous.quotient_lift continuous_mobiusFDHalfSlidingCoord fun _ _ h =>
    mobiusFDHalfSlidingCoord_eq_of_mobiusRel₀ h

theorem mobiusStripHalfSlidingCoord_quot (p : MobiusFundamentalDomain) :
    mobiusStripHalfSlidingCoord (Quotient.mk mobiusSetoid p) = mobiusFDHalfSlidingCoord p :=
  rfl

/-- The half-sliding map **`H u := mobiusSeamLocalMap (1/2) u`** has an invertible strict derivative
  at any `u` with `u 1 + (1/2 - 1/2) ≠ 0`, i.e. `u 1 ≠ 0` for the aug branch. But at `u = 0`
  (i.e. the seam normal `σ = 0` at `(x, t) = (0, ½)`), the aug branch still applies (π·0 + 1 ≠ 0),
  giving a nonsingular linearization. -/
theorem hasStrictFDerivAt_mobiusSeamLocalMap_half_zero :
    HasStrictFDerivAt (mobiusSeamLocalMap (1 / 2 : ℝ))
      (mobiusSeamAugFderivContinuousLinearEquiv (0 : ℝ) (by norm_num) : R2 →L[ℝ] R2) 0 := by
  have hcd : ContDiffAt ℝ ⊤ (mobiusSeamLocalMap (1 / 2 : ℝ)) 0 :=
    ContDiff.contDiffAt (contDiff_mobiusSeamLocalMap _)
  refine hcd.hasStrictFDerivAt' ?_ (by norm_cast)
  simpa using hasFDerivAt_mobiusSeamLocalMap_zero_augBranch (1 / 2 : ℝ) (by norm_num)

/-! ### Plane formulation of equator half-sliding (left seam basepoint `(0, ½)`) -/

/-- **Plane chart germs for `t = ½`:** translate the planar second coordinate by `−½` (so seam height
  becomes `0` in the sliding plane), then apply `mobiusSeamLocalMap (1/2)`. -/
noncomputable def mobiusPlaneHalfSlidingEquatorCoordMap (w : R2) : R2 :=
  mobiusSeamLocalMap (1 / 2 : ℝ) (w - EuclideanSpace.single (1 : Fin 2) (1 / 2 : ℝ))

noncomputable def mobiusPlaneLeftSeamEquatorPoint : R2 :=
  EuclideanSpace.single (0 : Fin 2) (0 : ℝ) + EuclideanSpace.single (1 : Fin 2) (1 / 2 : ℝ)

theorem mobiusPlaneLeftSeamEquatorPoint_apply0 : mobiusPlaneLeftSeamEquatorPoint 0 = 0 := by
  simp [mobiusPlaneLeftSeamEquatorPoint, PiLp.add_apply, EuclideanSpace.single_apply]

theorem mobiusPlaneLeftSeamEquatorPoint_apply1 : mobiusPlaneLeftSeamEquatorPoint 1 = 1 / 2 := by
  simp [mobiusPlaneLeftSeamEquatorPoint, PiLp.add_apply, EuclideanSpace.single_apply]

/-- Shifted by `w ↦ w - (0, ½)` the half-sliding plane map has a nonsingular derivative at the left
  seam equator point (composition of translation with `hasStrictFDerivAt` at `0`). -/
theorem hasStrictFDerivAt_mobiusPlaneHalfSlidingEquatorCoordMap_leftSeamEquator :
    HasStrictFDerivAt mobiusPlaneHalfSlidingEquatorCoordMap
      (mobiusSeamAugFderivContinuousLinearEquiv (0 : ℝ) (by norm_num) : R2 →L[ℝ] R2)
      mobiusPlaneLeftSeamEquatorPoint := by
  classical
  let c : R2 := EuclideanSpace.single (1 : Fin 2) (1 / 2 : ℝ)
  have hfT :
      HasStrictFDerivAt (fun w : R2 => w - c) (ContinuousLinearMap.id ℝ R2)
        mobiusPlaneLeftSeamEquatorPoint := by simpa [c] using hasStrictFDerivAt_sub_const (𝕜 := ℝ) (F := R2) c
  have hfc : mobiusPlaneLeftSeamEquatorPoint - c = (0 : R2) := by
    ext i
    fin_cases i <;> simp [c, mobiusPlaneLeftSeamEquatorPoint, PiLp.sub_apply, PiLp.add_apply,
      EuclideanSpace.single_apply]
  have hg :
      HasStrictFDerivAt (mobiusSeamLocalMap (1 / 2 : ℝ))
        (mobiusSeamAugFderivContinuousLinearEquiv (0 : ℝ) (by norm_num) : R2 →L[ℝ] R2)
        (mobiusPlaneLeftSeamEquatorPoint - c) := by simpa [hfc] using hasStrictFDerivAt_mobiusSeamLocalMap_half_zero
  have hmain :=
    HasStrictFDerivAt.comp (f := fun w : R2 => w - c) (x := mobiusPlaneLeftSeamEquatorPoint) hg hfT
  have hfun :
      (fun x => mobiusSeamLocalMap (1 / 2 : ℝ) (x - c)) = mobiusPlaneHalfSlidingEquatorCoordMap := by
    funext w
    simp [mobiusPlaneHalfSlidingEquatorCoordMap, c]
  simpa [← hfun] using hmain

theorem map_nhds_mobiusSeamLocalMap_half_zero :
    map (mobiusSeamLocalMap (1 / 2 : ℝ)) (𝓝 (0 : R2)) =
      𝓝 (mobiusSeamLocalMap (1 / 2 : ℝ) 0) :=
  HasStrictFDerivAt.map_nhds_eq_of_equiv hasStrictFDerivAt_mobiusSeamLocalMap_half_zero

/-- Any **open** set `Ω ⊆ R2` on which the `w₁ + 0 ≠ 0` (i.e. `u 1 ≠ 0` for `t₀ = ½`) hypothesis
  holds has open image under `mobiusSeamLocalMapPure (1/2)`. But for the equator chart we need open
  images from **`mobiusSeamLocalMap (1/2)` at basepoints in `Ball`**; we use the full IFT via
  `mobiusSeamLocalMapOpenPartialHomeomorph (1/2)` which provides a local homeomorphism. -/
theorem isOpen_image_mobiusSeamLocalMap_half_of_subset_source {Ω : Set R2} (hΩ : IsOpen Ω)
    (hΩsrc : Ω ⊆ (mobiusSeamLocalMapOpenPartialHomeomorph (1 / 2 : ℝ)).source) :
    IsOpen (mobiusSeamLocalMap (1 / 2 : ℝ) '' Ω) := by
  rw [← mobiusSeamLocalMapOpenPartialHomeomorph_toFun (1 / 2 : ℝ)]
  exact (mobiusSeamLocalMapOpenPartialHomeomorph (1 / 2 : ℝ)).isOpen_image_of_subset_source hΩ hΩsrc

/-! ### Right base point and IFT at `(1, 0)` for the equator right-arm chart -/

/-- The point `(1, 0)` in `R2` (right base point for the equator right-arm). -/
noncomputable def mobiusSeamRightBasePoint : R2 :=
  EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (0 : ℝ)

@[simp]
theorem mobiusSeamRightBasePoint_coord0 : mobiusSeamRightBasePoint 0 = 1 := by
  simp [mobiusSeamRightBasePoint, PiLp.add_apply, EuclideanSpace.single_apply]

@[simp]
theorem mobiusSeamRightBasePoint_coord1 : mobiusSeamRightBasePoint 1 = 0 := by
  simp [mobiusSeamRightBasePoint, PiLp.add_apply, EuclideanSpace.single_apply]

/-- `mobiusFDHalfSlidingCoord` at `(1, ½)` equals `mobiusSeamLocalMapAug ½ (1, 0)`. -/
theorem mobiusFDHalfSlidingCoord_rightSeamEquator :
    let q : MobiusFundamentalDomain := (mobiusIcc1, ⟨1 / 2, by norm_num, by norm_num⟩)
    mobiusFDHalfSlidingCoord q =
      mobiusSeamLocalMapAug (1 / 2 : ℝ) mobiusSeamRightBasePoint := by
  simp only [mobiusFDHalfSlidingCoord, mobiusSeamLocalMap_half_eq_aug, mobiusSeamSlidingCoord,
    mobiusSeamRightBasePoint, mobiusIcc1_val, EuclideanSpace.single_apply, PiLp.add_apply,
    mobiusIcc1]
  simp [EuclideanSpace.single_apply, PiLp.add_apply]

/-- The neg-swap CLEquiv: `(v0, v1) ↦ (-v1, -v0)`. Jacobian of `mobiusSeamLocalMapAug ½` at `(1,0)`. -/
private noncomputable def mobiusSeamAugRightCLEquiv : R2 ≃L[ℝ] R2 :=
  let iso : R2 ≃L[ℝ] (Fin 2 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let Dπ : R2 →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun i =>
      match i with
      | 0 => -(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1)
      | 1 => -(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)
  let negSwapCLM : R2 →L[ℝ] R2 := iso.symm.toContinuousLinearMap.comp Dπ
  (LinearEquiv.ofInjectiveEndo negSwapCLM.toLinearMap (by
    intro v w hvw
    -- hvw : negSwapCLM v = negSwapCLM w, i.e., (-v1, -v0) = (-w1, -w0)
    have heq : Dπ v = Dπ w := by
      have := congrArg iso (show iso.symm (Dπ v) = iso.symm (Dπ w) by
        simpa [negSwapCLM, ContinuousLinearMap.comp_apply] using hvw)
      simpa using this
    have h0 : (Dπ v) 0 = (Dπ w) 0 := by rw [heq]
    have h1 : (Dπ v) 1 = (Dπ w) 1 := by rw [heq]
    simp [Dπ, ContinuousLinearMap.pi_apply, PiLp.proj, ContinuousLinearMap.neg_apply,
      R2_PiLp_proj_apply] at h0 h1
    ext i; fin_cases i <;> [simpa using h1; simpa using h0]
    )).toContinuousLinearEquiv

-- Helper: HasFDerivAt for coord0 of the aug map at (1,0)
private theorem hasFDerivAt_mobiusSeamLocalMapAug_half_coord0_rightBase :
    HasFDerivAt (fun w : R2 => (mobiusSeamLocalMapAug (1 / 2 : ℝ) w) 0)
      (-(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1)) mobiusSeamRightBasePoint := by
  -- coord0 w = w 1 * cos(π * w 0). D at (1,0): cos(π)*proj_1 = -proj_1
  have h : HasFDerivAt (fun w : R2 => w 1 * Real.cos (Real.pi * w 0))
      (-(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1)) mobiusSeamRightBasePoint := by
    have := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)
        mobiusSeamRightBasePoint 1).mul
      (((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)
          mobiusSeamRightBasePoint 0).const_mul Real.pi).cos)
    simp only [mobiusSeamRightBasePoint, PiLp.add_apply, EuclideanSpace.single_apply,
      Real.cos_pi, Real.sin_pi, neg_mul, one_mul, smul_neg, smul_zero, neg_zero,
      mul_zero, zero_mul, add_zero] at this
    convert this using 1
    ext v; simp [PiLp.proj, ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, R2_PiLp_proj_apply]
  have : (fun w : R2 => (mobiusSeamLocalMapAug (1 / 2 : ℝ) w) 0) =
      fun w : R2 => w 1 * Real.cos (Real.pi * w 0) := by
    funext w; simp [mobiusSeamLocalMapAug, R2_ofLp_apply, EuclideanSpace.single_apply, PiLp.add_apply]
  rwa [this]

private theorem hasFDerivAt_mobiusSeamLocalMapAug_half_coord1_rightBase :
    HasFDerivAt (fun w : R2 => (mobiusSeamLocalMapAug (1 / 2 : ℝ) w) 1)
      (-(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)) mobiusSeamRightBasePoint := by
  -- coord1 w = w 1 * sin(π * w 0) + w 0 * (1 - w 0). D at (1,0): 0 + (1-2)*proj_0 = -proj_0
  have h : HasFDerivAt (fun w : R2 => w 1 * Real.sin (Real.pi * w 0) + w 0 * (1 - w 0))
      (-(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)) mobiusSeamRightBasePoint := by
    have hsin := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)
        mobiusSeamRightBasePoint 1).mul
      (((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)
          mobiusSeamRightBasePoint 0).const_mul Real.pi).sin)
    have hquad := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)
        mobiusSeamRightBasePoint 0).mul
      ((hasFDerivAt_const (1 : ℝ) mobiusSeamRightBasePoint).sub
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 => ℝ)
          mobiusSeamRightBasePoint 0))
    have hfull := hsin.add hquad
    simp only [mobiusSeamRightBasePoint, PiLp.add_apply, EuclideanSpace.single_apply,
      Real.cos_pi, Real.sin_pi, smul_zero, zero_smul, zero_mul, mul_zero, add_zero, zero_add,
      neg_mul, one_mul, sub_self, smul_neg, neg_zero, mul_one] at hfull
    convert hfull using 1
    ext v; simp [PiLp.proj, ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      R2_PiLp_proj_apply]
  have : (fun w : R2 => (mobiusSeamLocalMapAug (1 / 2 : ℝ) w) 1) =
      fun w : R2 => w 1 * Real.sin (Real.pi * w 0) + w 0 * (1 - w 0) := by
    funext w; simp [mobiusSeamLocalMapAug, R2_ofLp_apply, EuclideanSpace.single_apply, PiLp.add_apply]
  rwa [this]

private theorem hasFDerivAt_mobiusSeamLocalMapAug_half_rightBasePoint :
    HasFDerivAt (mobiusSeamLocalMapAug (1 / 2 : ℝ))
      (mobiusSeamAugRightCLEquiv : R2 →L[ℝ] R2) mobiusSeamRightBasePoint := by
  let iso := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  -- The full map = iso.symm ∘ (coord0, coord1)
  have hΦ : (fun w : R2 => mobiusSeamLocalMapAug (1 / 2 : ℝ) w) =
      fun w : R2 => iso.symm (fun i : Fin 2 => (mobiusSeamLocalMapAug (1 / 2 : ℝ) w).ofLp i) := by
    funext w; ext i; simp [iso, R2_continuousLinearEquiv_apply, R2_ofLp_apply]
  -- Change goal to use the eta-expanded form
  show HasFDerivAt (fun w : R2 => mobiusSeamLocalMapAug (1 / 2 : ℝ) w)
      (mobiusSeamAugRightCLEquiv : R2 →L[ℝ] R2) mobiusSeamRightBasePoint
  rw [hΦ]
  have harrow : HasFDerivAt
      (fun w : R2 => (fun i : Fin 2 => (mobiusSeamLocalMapAug (1 / 2 : ℝ) w).ofLp i))
      (ContinuousLinearMap.pi fun i => match i with
        | 0 => -(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1)
        | 1 => -(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)) mobiusSeamRightBasePoint := by
    apply hasFDerivAt_pi''
    intro i; fin_cases i
    · norm_cast; exact hasFDerivAt_mobiusSeamLocalMapAug_half_coord0_rightBase
    · norm_cast; exact hasFDerivAt_mobiusSeamLocalMapAug_half_coord1_rightBase
  -- iso.symm.hasFDerivAt.comp gives the HasFDerivAt for the full function
  -- Now show the result CLMap equals mobiusSeamAugRightCLEquiv
  have hcomposed := iso.symm.hasFDerivAt.comp mobiusSeamRightBasePoint harrow
  -- hcomposed : HasFDerivAt (iso.symm ∘ ...) (iso.symm.toContinuousLinearMap.comp negSwap) pt
  -- Need to show this CLMap = mobiusSeamAugRightCLEquiv
  -- Check that fderiv = mobiusSeamAugRightCLEquiv
  refine hcomposed.congr_fderiv ?_
  -- Goal: iso.symm.toContinuousLinearMap.comp (negSwap) = mobiusSeamAugRightCLEquiv
  -- Both are iso.symm ∘ negSwap by construction
  rfl

private theorem hasStrictFDerivAt_mobiusSeamLocalMapAug_half_rightBasePoint :
    HasStrictFDerivAt (mobiusSeamLocalMapAug (1 / 2 : ℝ))
      (mobiusSeamAugRightCLEquiv : R2 →L[ℝ] R2) mobiusSeamRightBasePoint := by
  have hcd : ContDiffAt ℝ 1 (mobiusSeamLocalMapAug (1 / 2 : ℝ)) mobiusSeamRightBasePoint :=
    ContDiffAt.of_le (ContDiff.contDiffAt (contDiff_mobiusSeamLocalMapAug _)) le_top
  simpa using hcd.hasStrictFDerivAt' hasFDerivAt_mobiusSeamLocalMapAug_half_rightBasePoint one_ne_zero

/-- IFT partial homeomorphism for `mobiusSeamLocalMapAug ½` near `(1, 0)`. -/
noncomputable def mobiusSeamAugRightPartialHomeomorph : OpenPartialHomeomorph R2 R2 :=
  hasStrictFDerivAt_mobiusSeamLocalMapAug_half_rightBasePoint.toOpenPartialHomeomorph
    (mobiusSeamLocalMapAug (1 / 2 : ℝ))

theorem mobiusSeamRightBasePoint_mem_augRightSource :
    mobiusSeamRightBasePoint ∈ mobiusSeamAugRightPartialHomeomorph.source :=
  hasStrictFDerivAt_mobiusSeamLocalMapAug_half_rightBasePoint.mem_toOpenPartialHomeomorph_source

theorem mobiusSeamAugRightPartialHomeomorph_toFun :
    mobiusSeamAugRightPartialHomeomorph.toFun = mobiusSeamLocalMapAug (1 / 2 : ℝ) :=
  hasStrictFDerivAt_mobiusSeamLocalMapAug_half_rightBasePoint.toOpenPartialHomeomorph_coe

theorem mobiusSeamRightBaseImage_mem_augRightTarget :
    mobiusSeamLocalMapAug (1 / 2 : ℝ) mobiusSeamRightBasePoint ∈
      mobiusSeamAugRightPartialHomeomorph.target :=
  hasStrictFDerivAt_mobiusSeamLocalMapAug_half_rightBasePoint.image_mem_toOpenPartialHomeomorph_target

theorem exists_pos_radius_ball_subset_mobiusSeamAugRightTarget :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (mobiusSeamLocalMapAug (1 / 2 : ℝ) mobiusSeamRightBasePoint) r ⊆
        mobiusSeamAugRightPartialHomeomorph.target := by
  rcases Metric.mem_nhds_iff.mp
    (mobiusSeamAugRightPartialHomeomorph.open_target.mem_nhds
      mobiusSeamRightBaseImage_mem_augRightTarget) with ⟨r, hr, hball⟩
  exact ⟨r, hr, hball⟩

/-- Some Euclidean ball around **`mobiusSeamRightBasePoint`** lies in the **IFT source** of
  `mobiusSeamAugRightPartialHomeomorph` (equator / right-arm chart). -/
theorem exists_pos_radius_ball_subset_mobiusSeamAugRightPartialHomeomorph_source :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball mobiusSeamRightBasePoint ε ⊆ mobiusSeamAugRightPartialHomeomorph.source := by
  classical
  have hn :=
    mobiusSeamAugRightPartialHomeomorph.open_source.mem_nhds mobiusSeamRightBasePoint_mem_augRightSource
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  exact ⟨ε, hε, hball⟩

/-- For `z` in the **augmented right-arm IFT target**, translate back to `R²` at the **left seam
  equator basepoint** `(0, ½)` so that **`mobiusPlaneHalfSlidingEquatorCoordMap`** recovers `z`.

  This is the plane-side identity behind the équateur **right branch** (lift
  `v ↦ mobiusPlaneLeftSeamEquatorPoint + (mobiusSeamAugRightPartialHomeomorph.symm (G v))`, not
  `mobiusPlaneTrigSeamPartnerAdd` / `mobiusFD_of_plane_IocIoo_right` from the trig chart): `G`
  satisfies `G (v₀) = aug ((v₀) - (0,½))`, and `symm` inverts `aug` on the target. -/
theorem mobiusPlaneHalfSlidingEquatorCoordMap_leftSeamEquator_add_augRight_symm {z : R2}
    (hz : z ∈ mobiusSeamAugRightPartialHomeomorph.target) :
    mobiusPlaneHalfSlidingEquatorCoordMap
      (mobiusPlaneLeftSeamEquatorPoint + mobiusSeamAugRightPartialHomeomorph.symm z) = z := by
  classical
  let e := mobiusSeamAugRightPartialHomeomorph
  let s := e.symm z
  have hmain : mobiusSeamLocalMapAug (1 / 2 : ℝ) s = z := by
    rw [← congrFun mobiusSeamAugRightPartialHomeomorph_toFun s]
    exact e.right_inv hz
  have hbase :
      mobiusPlaneLeftSeamEquatorPoint = EuclideanSpace.single (1 : Fin 2) (1 / 2 : ℝ) := by
    ext i
    fin_cases i <;>
      simp [mobiusPlaneLeftSeamEquatorPoint, PiLp.add_apply, EuclideanSpace.single_apply]
  have hsub :
      mobiusPlaneLeftSeamEquatorPoint + s - EuclideanSpace.single (1 : Fin 2) (1 / 2 : ℝ) = s := by
    rw [hbase]; abel
  calc
    mobiusPlaneHalfSlidingEquatorCoordMap (mobiusPlaneLeftSeamEquatorPoint + e.symm z) =
        mobiusSeamLocalMap (1 / 2 : ℝ)
          (mobiusPlaneLeftSeamEquatorPoint + s - EuclideanSpace.single (1 : Fin 2) (1 / 2 : ℝ)) := rfl
    _ = mobiusSeamLocalMap (1 / 2 : ℝ) s := by rw [hsub]
    _ = mobiusSeamLocalMapAug (1 / 2 : ℝ) s := by rw [mobiusSeamLocalMap_half_eq_aug]
    _ = z := hmain

end RepresentationalRegress

end
