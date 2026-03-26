/-
  Toward `¬ Nonempty (MobiusStrip ≃ₜ ClosedCylinder)` (SPEC_002 P1-1).

  **Route W (winding), Steps 1–4 proved here:**
  * Steps 1–3: `mobiusStripToAddCircle`, `mobiusBoundaryLoop`, composition = `2 •` after rescale,
    `mobiusStripToAddCircle_comp_mobiusBoundaryLoop_not_injective`.
  * Algebraic: `two_zsmul_not_injective_addCircle_twoPi`, `two_zsmul_not_injective_addCircle_two`,
    `equivAddCircle_symm_map_zsmul`, `mobiusAddCircleRescale_symm_map_two_zsmul`.
  * Step 4: `cylinderToAddCircle`, `cylinderBoundaryLoop`, `cylinderToAddCircle_comp_cylinderBoundaryLoop`,
    `injective_cylinderToAddCircle_comp_cylinderBoundaryLoop`.

  **Still missing for P1-1:** transport under a hypothetical global homeomorphism (SPEC_002 steps 5–6)
  **or** a boundary bridge + `MobiusCylinderBoundaryContrast` contradiction. See `SPEC_002` master list.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Piecewise

import RepresentationalRegress.CylinderBoundary
import RepresentationalRegress.CylinderMobius

noncomputable section

open scoped Topology
open Real Set
open AddCircle

namespace RepresentationalRegress

abbrev mobiusCirclePeriod : ℝ := 2 * π

lemma mobiusCirclePeriod_pos : 0 < mobiusCirclePeriod :=
  mul_pos (by norm_num) pi_pos

lemma mobiusCirclePeriodNeZero : mobiusCirclePeriod ≠ 0 :=
  ne_of_gt mobiusCirclePeriod_pos

lemma homeomorphAddCircle_self {p : ℝ} (hp : p ≠ 0) :
    homeomorphAddCircle p p hp hp = Homeomorph.refl (AddCircle p) := by
  refine Homeomorph.ext ?_
  intro x
  refine QuotientAddGroup.induction_on x fun w => ?_
  simp only [homeomorphAddCircle_apply_mk]
  rw [show (Homeomorph.refl (AddCircle p)) ↑w = Equiv.refl (AddCircle p) ↑w from rfl, Equiv.refl_apply]
  rw [QuotientAddGroup.eq]
  refine ⟨0, ?_⟩
  simp [inv_mul_cancel₀ hp, add_comm]

lemma homeomorphCircle_at_period :
    homeomorphCircle mobiusCirclePeriodNeZero = homeomorphCircle' := by
  rw [homeomorphCircle, homeomorphAddCircle_self mobiusCirclePeriodNeZero]
  refine Homeomorph.ext ?_
  intro z
  simp only [Homeomorph.trans_apply]
  rfl

lemma equivAddCircle_symm_map_zsmul (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (n : ℤ) (w : AddCircle q) :
    (equivAddCircle p q hp hq).symm (n • w) =
      n • (equivAddCircle p q hp hq).symm w := by
  refine QuotientAddGroup.induction_on w fun w => ?_
  have hl :
      (equivAddCircle p q hp hq).symm (n • (↑w : AddCircle q)) =
        ↑((n : ℤ) • w * (q⁻¹ * p)) := by
    rw [(AddCircle.coe_zsmul (n := n) (x := w) (p := q)).symm, equivAddCircle_symm_apply_mk]
  have hr :
      n • ((equivAddCircle p q hp hq).symm (↑w : AddCircle q)) =
        ↑((n : ℤ) • (w * (q⁻¹ * p))) := by
    rw [equivAddCircle_symm_apply_mk, ← AddCircle.coe_zsmul (n := n) (x := w * (q⁻¹ * p)) (p := p)]
  rw [hl, hr]
  congr 1
  simp [zsmul_eq_mul]
  ring

theorem two_zsmul_not_injective_addCircle_twoPi :
    ¬ Function.Injective (fun z : AddCircle (2 * π) => (2 : ℤ) • z) := by
  intro h
  have ne_cosets : (↑(π / 2) : AddCircle (2 * π)) ≠ ↑(3 * π / 2) := by
    intro e
    rw [QuotientAddGroup.eq] at e
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp e
    rw [zsmul_eq_mul] at hz
    have hπ : π ≠ 0 := pi_ne_zero
    have rhs_eq : -(π / 2 : ℝ) + 3 * π / 2 = π := by ring
    rw [rhs_eq] at hz
    have hz2 : (z : ℝ) * 2 = 1 := (mul_right_inj' hπ).1 (by linarith [hz])
    norm_cast at hz2
    omega
  have ha : (2 : ℤ) • (↑(π / 2) : AddCircle (2 * π)) = (↑π : AddCircle (2 * π)) := by
    rw [← AddCircle.coe_zsmul (n := (2 : ℤ)) (x := (π / 2 : ℝ))]
    congr 1
    simp only [zsmul_eq_mul]
    ring
  have hb : (2 : ℤ) • (↑(3 * π / 2) : AddCircle (2 * π)) = (↑(3 * π) : AddCircle (2 * π)) := by
    rw [← AddCircle.coe_zsmul (n := (2 : ℤ)) (x := (3 * π / 2 : ℝ))]
    congr 1
    simp only [zsmul_eq_mul]
    ring
  have hmid : (↑π : AddCircle (2 * π)) = (↑(3 * π) : AddCircle (2 * π)) := by
    rw [QuotientAddGroup.eq]
    refine ⟨(1 : ℤ), ?_⟩
    simpa [zsmul_eq_mul] using (show (1 : ℝ) * (2 * π) = -π + 3 * π by ring)
  have eq_smul :
      (2 : ℤ) • (↑(π / 2) : AddCircle (2 * π)) = (2 : ℤ) • (↑(3 * π / 2) : AddCircle (2 * π)) :=
    ha.trans (hmid.trans hb.symm)
  exact ne_cosets (h eq_smul)

theorem two_zsmul_not_injective_addCircle_two :
    ¬ Function.Injective (fun z : AddCircle (2 : ℝ) => (2 : ℤ) • z) := by
  intro h2
  let e := equivAddCircle (2 : ℝ) mobiusCirclePeriod two_ne_zero mobiusCirclePeriodNeZero
  have hπ :
      ¬ Function.Injective (fun w : AddCircle mobiusCirclePeriod => (2 : ℤ) • w) :=
    two_zsmul_not_injective_addCircle_twoPi
  refine hπ ?_
  intro w₁ w₂ he
  have hs : (2 : ℤ) • e.symm w₁ = (2 : ℤ) • e.symm w₂ :=
    (equivAddCircle_symm_map_zsmul (2 : ℝ) mobiusCirclePeriod two_ne_zero mobiusCirclePeriodNeZero
          (2 : ℤ) w₁).symm.trans
      ((congrArg (⇑e.symm) he).trans
        (equivAddCircle_symm_map_zsmul (2 : ℝ) mobiusCirclePeriod two_ne_zero
          mobiusCirclePeriodNeZero (2 : ℤ) w₂))
  exact EquivLike.injective e.symm (h2 hs)

/-! ### Step 1: core circle map -/

noncomputable def mobiusStripToAddCircleFun (p : MobiusFundamentalDomain) : AddCircle mobiusCirclePeriod :=
  ↑((2 * π) * (p.1.val : ℝ))

theorem mobiusStripToAddCircleFun_congr {p q : MobiusFundamentalDomain} (h : mobiusRel₀ p q) :
    mobiusStripToAddCircleFun p = mobiusStripToAddCircleFun q := by
  dsimp [mobiusStripToAddCircleFun]
  rcases h with rfl | h
  · rfl
  · rcases h with ⟨hp0, hq1, _⟩ | ⟨hq0, hp1, _⟩
    · rw [hp0, hq1, mul_zero, mul_one]
      rw [AddCircle.coe_period (p := mobiusCirclePeriod), ← AddCircle.coe_zero]
    · rw [hp1, hq0, mul_one, mul_zero]
      rw [AddCircle.coe_period (p := mobiusCirclePeriod), ← AddCircle.coe_zero]

theorem continuous_mobiusStripToAddCircleFun : Continuous mobiusStripToAddCircleFun := by
  unfold mobiusStripToAddCircleFun
  refine (AddCircle.continuous_mk' (p := mobiusCirclePeriod)).comp ?_
  refine Continuous.comp (continuous_const_mul (2 * π)) ?_
  refine Continuous.comp continuous_subtype_val continuous_fst

noncomputable def mobiusStripToAddCircle : MobiusStrip → AddCircle mobiusCirclePeriod :=
  Quotient.lift mobiusStripToAddCircleFun fun _ _ h => mobiusStripToAddCircleFun_congr h

@[simp]
theorem mobiusStripToAddCircle_mk (p : MobiusFundamentalDomain) :
    mobiusStripToAddCircle (Quotient.mk mobiusSetoid p) = mobiusStripToAddCircleFun p :=
  rfl

theorem continuous_mobiusStripToAddCircle : Continuous mobiusStripToAddCircle :=
  Continuous.quotient_lift continuous_mobiusStripToAddCircleFun fun _ _ h =>
    mobiusStripToAddCircleFun_congr h

/-! ### Step 2: boundary loop -/

noncomputable def mobiusBoundaryLoopBotAux (t : ℝ) : MobiusStrip :=
  Quotient.mk mobiusSetoid
    (⟨⟨min (max t 0) 1,
        ⟨le_min (le_max_right t 0) zero_le_one, min_le_right (max t 0) 1⟩⟩, mobiusIcc0⟩)

noncomputable def mobiusBoundaryLoopTopAux (t : ℝ) : MobiusStrip :=
  let r := min (max t 1) 2
  let u := r - 1
  Quotient.mk mobiusSetoid
    (⟨⟨u,
        ⟨by
          have hr : 1 ≤ r := by
            by_cases h : max t 1 ≤ 2
            · simp [r, min_eq_left h]
            · have h2m : 2 ≤ max t 1 := le_of_lt (lt_of_not_ge h)
              simp [r, min_eq_right h2m]
          linarith,
        by
          have hr : r ≤ 2 := min_le_right _ _
          linarith⟩⟩,
        mobiusIcc1⟩)

theorem mobiusBoundaryLoop_seam_agree :
    mobiusBoundaryLoopBotAux 1 = mobiusBoundaryLoopTopAux 1 := by
  simp [mobiusBoundaryLoopBotAux, mobiusBoundaryLoopTopAux]
  refine Quotient.sound (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
  simp [mobiusIcc0_val, mobiusIcc1_val]

noncomputable def mobiusBoundaryLoopSeg (t : ℝ) : MobiusStrip :=
  if _ : t ≤ (1 : ℝ) then mobiusBoundaryLoopBotAux t else mobiusBoundaryLoopTopAux t

theorem continuous_mobiusBoundaryLoopBotAux : Continuous mobiusBoundaryLoopBotAux := by
  unfold mobiusBoundaryLoopBotAux
  refine continuous_quotient_mk'.comp (Continuous.prodMk ?_ continuous_const)
  refine Continuous.subtype_mk ?_ fun t => by
    exact ⟨le_min (le_max_right t 0) zero_le_one, min_le_right (max t 0) 1⟩
  exact Continuous.min (Continuous.max continuous_id continuous_const) continuous_const

theorem continuous_mobiusBoundaryLoopTopAux : Continuous mobiusBoundaryLoopTopAux := by
  unfold mobiusBoundaryLoopTopAux
  refine continuous_quotient_mk'.comp (Continuous.prodMk ?_ continuous_const)
  refine Continuous.subtype_mk ?_ fun t => by
    have _hr2 : 1 ≤ min (max t 1) 2 :=
      le_min (le_max_right t 1) (by norm_num : (1 : ℝ) ≤ 2)
    have hr : min (max t 1) 2 ≤ 2 := min_le_right _ _
    have hu0 : 0 ≤ min (max t 1) 2 - 1 := by linarith
    have hu1 : min (max t 1) 2 - 1 ≤ 1 := by linarith
    exact ⟨hu0, hu1⟩
  exact Continuous.sub (Continuous.min (Continuous.max continuous_id continuous_const)
      continuous_const) continuous_const

theorem continuous_mobiusBoundaryLoopSeg : Continuous mobiusBoundaryLoopSeg := by
  have hp :
      ∀ t ∈ frontier { x : ℝ | x ≤ 1 },
        mobiusBoundaryLoopBotAux t = mobiusBoundaryLoopTopAux t := by
    intro t ht
    rw [show ({x : ℝ | x ≤ 1} : Set ℝ) = Iic (1 : ℝ) from rfl] at ht
    have ht1 : t ∈ ({1} : Set ℝ) := by simpa [frontier_Iic (a := (1 : ℝ))] using ht
    obtain rfl := mem_singleton_iff.mp ht1
    exact mobiusBoundaryLoop_seam_agree
  exact Continuous.if hp continuous_mobiusBoundaryLoopBotAux continuous_mobiusBoundaryLoopTopAux

noncomputable def mobiusBoundaryLoopFun (s : ℝ) : MobiusStrip :=
  mobiusBoundaryLoopSeg (min (max s 0) 2)

theorem mobiusBoundaryLoopFun_period : mobiusBoundaryLoopFun 0 = mobiusBoundaryLoopFun 2 := by
  let p00 : MobiusFundamentalDomain := (mobiusIcc0, mobiusIcc0)
  let p11 : MobiusFundamentalDomain := (mobiusIcc1, mobiusIcc1)
  have hL : mobiusBoundaryLoopFun 0 = Quotient.mk mobiusSetoid p00 := by
    simp [mobiusBoundaryLoopFun, mobiusBoundaryLoopSeg, mobiusBoundaryLoopBotAux, p00]
    refine congrArg (Quotient.mk mobiusSetoid) ?_
    refine Prod.ext ?_ rfl
    refine Subtype.ext ?_
    norm_num
  have hR : mobiusBoundaryLoopFun 2 = Quotient.mk mobiusSetoid p11 := by
    simp [mobiusBoundaryLoopFun, mobiusBoundaryLoopSeg, mobiusBoundaryLoopTopAux, p11]
    refine congrArg (Quotient.mk mobiusSetoid) ?_
    refine Prod.ext ?_ rfl
    refine Subtype.ext ?_
    norm_num
  rw [hL, hR]
  refine Quotient.sound (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
  · rfl
  · rfl
  · simp [p00, p11, mobiusIcc0_val, mobiusIcc1_val]

theorem continuous_mobiusBoundaryLoopFun : Continuous mobiusBoundaryLoopFun :=
  continuous_mobiusBoundaryLoopSeg.comp (by fun_prop : Continuous fun s : ℝ => min (max s 0) 2)

theorem continuousOn_mobiusBoundaryLoopFun_Icc : ContinuousOn mobiusBoundaryLoopFun (Icc (0 : ℝ) 2) :=
  continuous_mobiusBoundaryLoopFun.continuousOn

noncomputable def mobiusBoundaryLoop : AddCircle (2 : ℝ) → MobiusStrip :=
  haveI : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩
  AddCircle.liftIco (p := (2 : ℝ)) 0 mobiusBoundaryLoopFun

theorem continuous_mobiusBoundaryLoop : Continuous mobiusBoundaryLoop :=
  haveI : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩
  AddCircle.liftIco_zero_continuous mobiusBoundaryLoopFun_period continuousOn_mobiusBoundaryLoopFun_Icc

/-! ### Step 3: composition -/

noncomputable def mobiusAddCircleRescale : AddCircle (2 : ℝ) ≃ₜ AddCircle mobiusCirclePeriod :=
  homeomorphAddCircle (2 : ℝ) mobiusCirclePeriod two_ne_zero mobiusCirclePeriodNeZero

lemma Ico_mem_clamp_identity {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 2) : min (max x 0) 2 = x := by
  rcases hx with ⟨hx0, hx2⟩
  simp [max_eq_left hx0, min_eq_left (le_of_lt hx2)]

theorem mobiusStripToAddCircle_comp_mobiusBoundaryLoopFun {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 2) :
    mobiusStripToAddCircle (mobiusBoundaryLoopFun x) =
      (2 : ℤ) • (mobiusAddCircleRescale ↑x) := by
  have hxE := Ico_mem_clamp_identity hx
  rcases hx with ⟨hx0, hx2lt⟩
  have hx2 : x ≤ 2 := le_of_lt hx2lt
  by_cases h1 : x ≤ 1
  · -- `x ∈ Icc 0 1`
    dsimp [mobiusBoundaryLoopFun, mobiusBoundaryLoopSeg, mobiusBoundaryLoopBotAux]
    simp only [hxE, h1, if_pos, mobiusStripToAddCircle_mk, mobiusStripToAddCircleFun]
    have hm : min (max x 0) 1 = x := by
      simp [max_eq_left hx0, h1]
    simp only [hm]
    have rescale_x :
        mobiusAddCircleRescale (↑x : AddCircle (2 : ℝ)) =
          ↑(x * ((2 : ℝ)⁻¹ * mobiusCirclePeriod)) := by
      simp only [mobiusAddCircleRescale, homeomorphAddCircle_apply_mk]
    rw [rescale_x]
    rw [← AddCircle.coe_zsmul (n := (2 : ℤ)) (x := x * ((2 : ℝ)⁻¹ * mobiusCirclePeriod))]
    congr 1
    simp only [mobiusCirclePeriod, zsmul_eq_mul, Int.cast_two]
    ring
  · -- `x ∈ Ioc 1 2`
    dsimp [mobiusBoundaryLoopFun, mobiusBoundaryLoopSeg, mobiusBoundaryLoopTopAux]
    simp_rw [hxE]
    rw [if_neg h1]
    simp only [mobiusStripToAddCircle_mk, mobiusStripToAddCircleFun]
    have hr_formula : min (max x 1) 2 = x := by
      have h1lt : 1 < x := not_le.mp h1
      rw [max_eq_left (le_of_lt h1lt), min_eq_left hx2]
    simp only [hr_formula]
    have rescale_x :
        mobiusAddCircleRescale (↑x : AddCircle (2 : ℝ)) =
          ↑(x * ((2 : ℝ)⁻¹ * mobiusCirclePeriod)) := by
      simp only [mobiusAddCircleRescale, homeomorphAddCircle_apply_mk]
    rw [rescale_x]
    rw [← AddCircle.coe_zsmul (n := (2 : ℤ)) (x := x * ((2 : ℝ)⁻¹ * mobiusCirclePeriod))]
    rw [QuotientAddGroup.eq]
    simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
    refine ⟨(1 : ℤ), ?_⟩
    ring_nf

theorem mobiusStripToAddCircle_comp_mobiusBoundaryLoop (z : AddCircle (2 : ℝ)) :
    mobiusStripToAddCircle (mobiusBoundaryLoop z) = (2 : ℤ) • mobiusAddCircleRescale z := by
  haveI : Fact ((0 : ℝ) < (2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ico (p := (2 : ℝ)) z
  have hx' : x ∈ Ico (0 : ℝ) (0 + (2 : ℝ)) := by rwa [zero_add]
  rw [mobiusBoundaryLoop, AddCircle.liftIco_coe_apply (p := (2 : ℝ)) (a := 0) hx']
  exact mobiusStripToAddCircle_comp_mobiusBoundaryLoopFun hx

theorem mobiusStripToAddCircle_comp_mobiusBoundaryLoop_not_injective :
    ¬ Function.Injective (mobiusStripToAddCircle ∘ mobiusBoundaryLoop) := by
  intro hinj
  let e := mobiusAddCircleRescale
  have hEq : (fun w : AddCircle mobiusCirclePeriod => (2 : ℤ) • w) =
      (mobiusStripToAddCircle ∘ mobiusBoundaryLoop) ∘ ⇑e.symm := by
    funext w
    calc
      (2 : ℤ) • w = (2 : ℤ) • (e (e.symm w)) := by
        congr 1
        exact (e.apply_symm_apply w).symm
      _ = mobiusStripToAddCircle (mobiusBoundaryLoop (e.symm w)) :=
        (mobiusStripToAddCircle_comp_mobiusBoundaryLoop (e.symm w)).symm
  have hsm : Function.Injective (fun w : AddCircle mobiusCirclePeriod => (2 : ℤ) • w) := by
    rw [hEq]
    exact hinj.comp e.symm.injective
  exact two_zsmul_not_injective_addCircle_twoPi hsm

lemma mobiusAddCircleRescale_symm_map_two_zsmul (z : AddCircle mobiusCirclePeriod) :
    mobiusAddCircleRescale.symm ((2 : ℤ) • z) = (2 : ℤ) • (mobiusAddCircleRescale.symm z) :=
  equivAddCircle_symm_map_zsmul (2 : ℝ) mobiusCirclePeriod two_ne_zero mobiusCirclePeriodNeZero
    (2 : ℤ) z

/-! ### Step 4 (Route W): cylinder-side circle maps -/

noncomputable def cylinderToAddCircle : ClosedCylinder → AddCircle mobiusCirclePeriod :=
  (homeomorphCircle mobiusCirclePeriodNeZero).symm ∘ Prod.fst

noncomputable def cylinderBoundaryLoop : AddCircle (2 : ℝ) → ClosedCylinder :=
  closedCylinderBotCoords ∘ homeomorphCircle two_ne_zero

theorem continuous_cylinderToAddCircle : Continuous cylinderToAddCircle :=
  Continuous.comp (homeomorphCircle mobiusCirclePeriodNeZero).symm.continuous continuous_fst

theorem continuous_cylinderBoundaryLoop : Continuous cylinderBoundaryLoop :=
  Continuous.comp continuous_closedCylinderBotCoords (homeomorphCircle two_ne_zero).continuous

theorem cylinderToAddCircle_comp_cylinderBoundaryLoop :
    cylinderToAddCircle ∘ cylinderBoundaryLoop = mobiusAddCircleRescale := by
  funext z
  simp only [Function.comp_apply, cylinderToAddCircle, cylinderBoundaryLoop, closedCylinderBotCoords,
    homeomorphCircle_at_period]
  simp only [homeomorphCircle, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, mobiusAddCircleRescale]

theorem injective_cylinderToAddCircle_comp_cylinderBoundaryLoop :
    Function.Injective (cylinderToAddCircle ∘ cylinderBoundaryLoop) := by
  simpa [cylinderToAddCircle_comp_cylinderBoundaryLoop] using Homeomorph.injective mobiusAddCircleRescale

end RepresentationalRegress

end
