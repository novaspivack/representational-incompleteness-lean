/-
  `ℂ \\ {0}` is not simply connected (universal cover `exp` + path lifting).

  Corollary: the punctured open unit ball (as a subtype of `ℂ`) is not simply connected.
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Path

noncomputable section

namespace RepresentationalRegress

open scoped unitInterval
open Topology Complex IsCoveringMap unitInterval ContinuousMap Set

abbrev ℂNeZero :=
  {z : ℂ // z ≠ 0}

noncomputable def complexCovering : ℂ → ℂNeZero :=
  fun z ↦ ⟨exp z, exp_ne_zero z⟩

lemma complexCovering_isCoveringMap : IsCoveringMap complexCovering :=
  Complex.isCoveringMap_exp

@[simp] lemma complexCovering_apply (z : ℂ) : (complexCovering z).val = exp z := rfl

noncomputable def halfPlaneNeZero : ℂNeZero :=
  ⟨(1 / 2 : ℂ), by norm_num⟩

lemma complexCovering_log_half :
    complexCovering (log (1 / 2 : ℂ)) = halfPlaneNeZero := by
  ext1
  rw [complexCovering_apply, Complex.exp_log (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  rfl

lemma I_coe_one : (↑(1 : I) : ℝ) = 1 := rfl

lemma puncturedBallLoop_underlying_cont :
    Continuous fun t : I => (1 / 2 : ℂ) * exp ((↑t : ℝ) * (2 * Real.pi * Complex.I)) := by
  fun_prop

noncomputable def puncturedBallLoop : C(I, ℂNeZero) where
  toFun t :=
    ⟨(1 / 2 : ℂ) * exp ((↑t : ℝ) * (2 * Real.pi * Complex.I)),
      mul_ne_zero (by norm_num) (exp_ne_zero _)⟩
  continuous_toFun :=
    Continuous.subtype_mk puncturedBallLoop_underlying_cont
      (fun _ => mul_ne_zero (by norm_num) (exp_ne_zero _))

noncomputable def puncturedBallConst : C(I, ℂNeZero) :=
  ⟨(fun _ ↦ halfPlaneNeZero), continuous_const⟩

lemma puncturedBallLoop_zero : puncturedBallLoop 0 = halfPlaneNeZero := by
  refine Subtype.ext ?_
  simp [puncturedBallLoop, halfPlaneNeZero, Complex.exp_zero]

lemma puncturedBallLoop_one : puncturedBallLoop 1 = halfPlaneNeZero := by
  refine Subtype.ext ?_
  simp [puncturedBallLoop, halfPlaneNeZero, Complex.exp_two_pi_mul_I]

lemma puncturedBallConst_zero : puncturedBallConst 0 = halfPlaneNeZero := rfl
lemma puncturedBallConst_one : puncturedBallConst 1 = halfPlaneNeZero := rfl

lemma puncturedBallConst_eq :
    puncturedBallConst = ContinuousMap.const I halfPlaneNeZero := by
  ext1 t
  rcases t with ⟨_, _, _⟩
  rfl

lemma norm_exp_circle (θ : ℝ) : ‖exp (θ * (2 * Real.pi * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [mul_assoc]

lemma puncturedBallLoop_mem_ball (t : I) :
    (puncturedBallLoop t).val ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, puncturedBallLoop, ContinuousMap.coe_mk]
  rw [norm_mul, norm_exp_circle]
  have hn : ‖(1 / 2 : ℂ)‖ = (2 : ℝ)⁻¹ := by simp
  rw [hn]
  norm_num

noncomputable def puncturedBallLoopLift : C(I, ℂ) :=
  ⟨(fun t : I ↦ log (1 / 2 : ℂ) + (↑t : ℝ) * (2 * Real.pi * Complex.I)), by continuity⟩

lemma puncturedBallLoopLift_lifts :
    complexCovering ∘ ⇑puncturedBallLoopLift = ⇑puncturedBallLoop := by
  funext t
  simp only [Function.comp_apply, puncturedBallLoopLift, puncturedBallLoop, ContinuousMap.coe_mk]
  refine Subtype.ext ?_
  simp only [complexCovering_apply, Complex.exp_add,
    Complex.exp_log (by norm_num : (1 / 2 : ℂ) ≠ 0)]

lemma puncturedBallLoopLift_zero : puncturedBallLoopLift 0 = log (1 / 2 : ℂ) := by
  simp [puncturedBallLoopLift]

lemma puncturedBallLoopLift_one :
    puncturedBallLoopLift 1 = log (1 / 2 : ℂ) + (2 * Real.pi * Complex.I) := by
  simp [puncturedBallLoopLift]

lemma puncturedBallLoop_lift_eq_liftPath :
    complexCovering_isCoveringMap.liftPath puncturedBallLoop (log (1 / 2 : ℂ))
        (by rw [puncturedBallLoop_zero]; exact complexCovering_log_half.symm) = puncturedBallLoopLift :=
  Eq.symm <|
    (complexCovering_isCoveringMap.eq_liftPath_iff' (γ := puncturedBallLoop)
        (e := log (1 / 2 : ℂ))
        (γ_0 := by rw [puncturedBallLoop_zero]; exact complexCovering_log_half.symm)).mpr
      ⟨funext fun t => congr_fun puncturedBallLoopLift_lifts t, puncturedBallLoopLift_zero⟩

lemma puncturedBallLoop_liftPath_one_applied :
    (complexCovering_isCoveringMap.liftPath puncturedBallLoop (log (1 / 2 : ℂ))
        (by rw [puncturedBallLoop_zero]; exact complexCovering_log_half.symm) : I → ℂ) 1 =
      log (1 / 2 : ℂ) + (2 * Real.pi * Complex.I) := by
  rw [puncturedBallLoop_lift_eq_liftPath]
  exact puncturedBallLoopLift_one

lemma puncturedBallConst_liftPath_one_applied :
    (complexCovering_isCoveringMap.liftPath puncturedBallConst (log (1 / 2 : ℂ))
        (by rw [puncturedBallConst_zero]; exact complexCovering_log_half.symm) : I → ℂ) 1 =
      log (1 / 2 : ℂ) := by
  have h :=
    congrArg (fun F : C(I, ℂ) => F 1)
      (complexCovering_isCoveringMap.liftPath_const complexCovering_log_half.symm)
  convert h using 1

theorem puncturedBall_loop_not_homotopic_const :
    ¬ HomotopicRel puncturedBallLoop puncturedBallConst {0, 1} := by
  intro h
  have Heq :=
    complexCovering_isCoveringMap.liftPath_apply_one_eq_of_homotopicRel h (log (1 / 2 : ℂ))
      (by rw [puncturedBallLoop_zero]; exact complexCovering_log_half.symm)
      (by rw [puncturedBallConst_zero]; exact complexCovering_log_half.symm)
  rw [puncturedBallLoop_liftPath_one_applied, puncturedBallConst_liftPath_one_applied] at Heq
  have him := congrArg Complex.im Heq
  have him_im_spin : (2 * Real.pi * Complex.I).im = 2 * Real.pi := by simp
  rw [Complex.add_im, him_im_spin] at him
  have hπ : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  linarith

/-!### Same winding loop with radius `c ∈ (0,1) ∩ ℝ` (for shrinking toward `0` in `ℂ`) -/

noncomputable def halfPlaneNeZeroOfReal (c : ℝ) (hc : 0 < c) : ℂNeZero :=
  ⟨(c : ℂ), by exact_mod_cast ne_of_gt hc⟩

lemma halfPlaneNeZeroOfReal_pos (c : ℝ) (hc : 0 < c) :
    (halfPlaneNeZeroOfReal c hc).val = (c : ℂ) := rfl

lemma complexCovering_log_real {c : ℝ} (hc : 0 < c) :
    complexCovering (log (c : ℂ)) = halfPlaneNeZeroOfReal c hc := by
  ext1
  rw [complexCovering_apply, Complex.exp_log (by exact_mod_cast ne_of_gt hc)]
  rfl

lemma puncturedBallLoopOfReal_underlying_cont (c : ℝ) :
    Continuous fun t : I =>
      (c : ℂ) * exp ((↑t : ℝ) * (2 * Real.pi * Complex.I)) := by
  fun_prop

noncomputable def puncturedBallLoopOfReal (c : ℝ) (hc0 : 0 < c) (_ : c < 1) : C(I, ℂNeZero) where
  toFun t :=
    ⟨(c : ℂ) * exp ((↑t : ℝ) * (2 * Real.pi * Complex.I)),
      mul_ne_zero (by norm_cast; linarith only [hc0]) (exp_ne_zero _)⟩
  continuous_toFun :=
    Continuous.subtype_mk (puncturedBallLoopOfReal_underlying_cont c)
      (fun _ => mul_ne_zero (by norm_cast; linarith only [hc0]) (exp_ne_zero _))

noncomputable def puncturedBallConstOfReal (c : ℝ) (hc0 : 0 < c) (_ : c < 1) : C(I, ℂNeZero) :=
  ⟨(fun _ ↦ halfPlaneNeZeroOfReal c hc0), continuous_const⟩

lemma puncturedBallLoopOfReal_zero (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    puncturedBallLoopOfReal c hc0 hc1 0 = halfPlaneNeZeroOfReal c hc0 := by
  refine Subtype.ext ?_
  simp [puncturedBallLoopOfReal, halfPlaneNeZeroOfReal, Complex.exp_zero]

lemma puncturedBallLoopOfReal_one (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    puncturedBallLoopOfReal c hc0 hc1 1 = halfPlaneNeZeroOfReal c hc0 := by
  refine Subtype.ext ?_
  simp [puncturedBallLoopOfReal, halfPlaneNeZeroOfReal, Complex.exp_two_pi_mul_I]

lemma puncturedBallConstOfReal_zero (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    puncturedBallConstOfReal c hc0 hc1 0 = halfPlaneNeZeroOfReal c hc0 := rfl

lemma puncturedBallConstOfReal_one (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    puncturedBallConstOfReal c hc0 hc1 1 = halfPlaneNeZeroOfReal c hc0 := rfl

lemma puncturedBallLoopOfReal_mem_ball (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (t : I) :
    (puncturedBallLoopOfReal c hc0 hc1 t).val ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, puncturedBallLoopOfReal, ContinuousMap.coe_mk]
  rw [norm_mul, norm_exp_circle]
  have hn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  rw [hn, mul_one]
  exact hc1

noncomputable def puncturedBallLoopLiftOfReal (c : ℝ) : C(I, ℂ) :=
  ⟨(fun t : I ↦ log (c : ℂ) + (↑t : ℝ) * (2 * Real.pi * Complex.I)), by continuity⟩

lemma puncturedBallLoopLiftOfReal_lifts (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    complexCovering ∘ ⇑(puncturedBallLoopLiftOfReal c) = ⇑(puncturedBallLoopOfReal c hc0 hc1) := by
  funext t
  simp only [Function.comp_apply, puncturedBallLoopLiftOfReal, puncturedBallLoopOfReal,
    ContinuousMap.coe_mk]
  refine Subtype.ext ?_
  simp only [complexCovering_apply]
  rw [Complex.exp_add, Complex.exp_log (by exact_mod_cast ne_of_gt hc0)]

lemma puncturedBallLoopLiftOfReal_zero (c : ℝ) : (puncturedBallLoopLiftOfReal c) 0 = log (c : ℂ) := by
  simp [puncturedBallLoopLiftOfReal]

lemma puncturedBallLoopLiftOfReal_one (c : ℝ) :
    (puncturedBallLoopLiftOfReal c) 1 = log (c : ℂ) + (2 * Real.pi * Complex.I) := by
  simp [puncturedBallLoopLiftOfReal]

lemma puncturedBallLoopOfReal_lift_eq_liftPath (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    complexCovering_isCoveringMap.liftPath (puncturedBallLoopOfReal c hc0 hc1) (log (c : ℂ))
        (by rw [puncturedBallLoopOfReal_zero]; exact (complexCovering_log_real hc0).symm) =
      puncturedBallLoopLiftOfReal c :=
  Eq.symm <|
    (complexCovering_isCoveringMap.eq_liftPath_iff'
      (γ := puncturedBallLoopOfReal c hc0 hc1) (e := log (c : ℂ))
      (γ_0 := by rw [puncturedBallLoopOfReal_zero]; exact (complexCovering_log_real hc0).symm)).mpr
      ⟨funext fun t => congr_fun (puncturedBallLoopLiftOfReal_lifts c hc0 hc1) t,
        puncturedBallLoopLiftOfReal_zero c⟩

lemma puncturedBallLoopOfReal_liftPath_one_applied (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (complexCovering_isCoveringMap.liftPath (puncturedBallLoopOfReal c hc0 hc1) (log (c : ℂ))
        (by rw [puncturedBallLoopOfReal_zero]; exact (complexCovering_log_real hc0).symm) : I → ℂ) 1 =
      log (c : ℂ) + (2 * Real.pi * Complex.I) := by
  rw [puncturedBallLoopOfReal_lift_eq_liftPath]
  exact puncturedBallLoopLiftOfReal_one c

lemma puncturedBallConstOfReal_liftPath_one_applied (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (complexCovering_isCoveringMap.liftPath (puncturedBallConstOfReal c hc0 hc1) (log (c : ℂ))
        (by rw [puncturedBallConstOfReal_zero]; exact (complexCovering_log_real hc0).symm) : I → ℂ) 1 =
      log (c : ℂ) := by
  have h :=
    congrArg (fun F : C(I, ℂ) => F 1)
      (complexCovering_isCoveringMap.liftPath_const (complexCovering_log_real hc0).symm)
  convert h using 1

theorem puncturedBall_loopOfReal_not_homotopic_const (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ HomotopicRel (puncturedBallLoopOfReal c hc0 hc1) (puncturedBallConstOfReal c hc0 hc1) {0, 1} := by
  intro h
  have Heq :=
    complexCovering_isCoveringMap.liftPath_apply_one_eq_of_homotopicRel h (log (c : ℂ))
      (by rw [puncturedBallLoopOfReal_zero]; exact (complexCovering_log_real hc0).symm)
      (by rw [puncturedBallConstOfReal_zero]; exact (complexCovering_log_real hc0).symm)
  rw [puncturedBallLoopOfReal_liftPath_one_applied, puncturedBallConstOfReal_liftPath_one_applied] at Heq
  have him := congrArg Complex.im Heq
  have him_im_spin : (2 * Real.pi * Complex.I).im = 2 * Real.pi := by simp
  rw [Complex.add_im, him_im_spin] at him
  have hπ : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  linarith

theorem notSimplyConnected_complex_ne_zero : ¬ SimplyConnectedSpace ℂNeZero := by
  intro h
  haveI : SimplyConnectedSpace ℂNeZero := h
  let pLoop := Path.mk puncturedBallLoop puncturedBallLoop_zero puncturedBallLoop_one
  let pConst := Path.mk puncturedBallConst puncturedBallConst_zero puncturedBallConst_one
  exact puncturedBall_loop_not_homotopic_const (SimplyConnectedSpace.paths_homotopic pLoop pConst)

/-- Punctured open unit ball as a subtype of `ℂ`. -/
abbrev PuncturedOpenUnitBall :=
  {z : ℂ // z ≠ 0 ∧ z ∈ Metric.ball (0 : ℂ) 1}

lemma loopInPuncturedOpenBall_aux (t : I) :
    (puncturedBallLoop t).val ≠ 0 ∧ (puncturedBallLoop t).val ∈ Metric.ball (0 : ℂ) 1 :=
  And.intro (puncturedBallLoop t).2 (puncturedBallLoop_mem_ball t)

noncomputable def loopInPuncturedOpenBall : C(I, PuncturedOpenUnitBall) where
  toFun t := ⟨(puncturedBallLoop t).val, loopInPuncturedOpenBall_aux t⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_subtype_val.comp puncturedBallLoop.continuous_toFun)
      loopInPuncturedOpenBall_aux

lemma half_in_unit_ball : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  norm_num

lemma constInPuncturedOpenBall_aux :
    (1 / 2 : ℂ) ≠ 0 ∧ (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 :=
  And.intro (by norm_num) half_in_unit_ball

noncomputable def constInPuncturedOpenBall : C(I, PuncturedOpenUnitBall) :=
  ContinuousMap.const I ⟨(1 / 2 : ℂ), constInPuncturedOpenBall_aux⟩

noncomputable def puncturedOpenUnitBallIncl : C(PuncturedOpenUnitBall, ℂNeZero) where
  toFun z := ⟨z.val, z.prop.1⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val fun z => z.prop.1

lemma incl_comp_loop :
    puncturedOpenUnitBallIncl.comp loopInPuncturedOpenBall = puncturedBallLoop := by
  ext1 t
  rfl

lemma incl_comp_constMap :
    puncturedOpenUnitBallIncl.comp constInPuncturedOpenBall = puncturedBallConst := by
  ext1 t
  simp [puncturedOpenUnitBallIncl, constInPuncturedOpenBall, puncturedBallConst, halfPlaneNeZero]

theorem notSimplyConnected_punctured_open_unit_ball :
    ¬ SimplyConnectedSpace PuncturedOpenUnitBall := by
  intro h
  haveI : SimplyConnectedSpace PuncturedOpenUnitBall := h
  let x₀ : PuncturedOpenUnitBall := loopInPuncturedOpenBall 0
  have hx₁ : loopInPuncturedOpenBall 1 = x₀ := by
    refine Subtype.ext ?_
    simp [x₀, loopInPuncturedOpenBall, puncturedBallLoop_one, puncturedBallLoop_zero, halfPlaneNeZero]
  have hs0 : constInPuncturedOpenBall 0 = x₀ := by
    refine Subtype.ext ?_
    simp [x₀, constInPuncturedOpenBall, loopInPuncturedOpenBall, puncturedBallLoop_zero, halfPlaneNeZero]
  have hxC : constInPuncturedOpenBall 1 = x₀ := by
    refine Subtype.ext ?_
    simp [x₀, constInPuncturedOpenBall, loopInPuncturedOpenBall, puncturedBallLoop_zero, halfPlaneNeZero]
  let pL := Path.mk loopInPuncturedOpenBall rfl hx₁
  let pC := Path.mk constInPuncturedOpenBall hs0 hxC
  have hmt := SimplyConnectedSpace.paths_homotopic pL pC
  have Hpush := HomotopicRel.comp_continuousMap hmt puncturedOpenUnitBallIncl
  rw [incl_comp_loop, incl_comp_constMap] at Hpush
  exact puncturedBall_loop_not_homotopic_const Hpush

/-!### Punctured **any** open neighborhood of `0` in `ℂ` -/

/-- A punctured open neighborhood of `0` in `ℂ` (subtype). -/
abbrev PuncturedOpenNeighAtZeroComplex (U : Set ℂ) :=
  {z : ℂ // z ∈ U \ {(0 : ℂ)}}

lemma exists_pos_ball_subset_open_nhds_zero_complex {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : ℂ) ε ⊆ U :=
  Metric.mem_nhds_iff.mp (IsOpen.mem_nhds hU h0)

lemma puncturedBallLoopOfReal_mem_ball_eps (c ε : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hce : c < ε)
    (t : I) : (puncturedBallLoopOfReal c hc0 hc1 t).val ∈ Metric.ball (0 : ℂ) ε := by
  rw [mem_ball_zero_iff, puncturedBallLoopOfReal, ContinuousMap.coe_mk, norm_mul, norm_exp_circle]
  have hn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  rw [hn, mul_one]
  exact hce

lemma loopInPuncturedOpenNeighComplex_aux {U : Set ℂ} {ε c : ℝ} (hball : Metric.ball (0 : ℂ) ε ⊆ U)
    (hc0 : 0 < c) (hc1 : c < 1) (hcε : c < ε) (t : I) :
    (puncturedBallLoopOfReal c hc0 hc1 t).val ∈ U \ {(0 : ℂ)} := by
  have hb : (puncturedBallLoopOfReal c hc0 hc1 t).val ∈ Metric.ball (0 : ℂ) ε :=
    puncturedBallLoopOfReal_mem_ball_eps c ε hc0 hc1 hcε t
  exact ⟨hball hb, (puncturedBallLoopOfReal c hc0 hc1 t).2⟩

noncomputable def loopInPuncturedOpenNeighComplex (U : Set ℂ) {ε c : ℝ} (hball : Metric.ball (0 : ℂ) ε ⊆ U)
    (hc0 : 0 < c) (hc1 : c < 1) (hcε : c < ε) : C(I, PuncturedOpenNeighAtZeroComplex U) where
  toFun t := ⟨(puncturedBallLoopOfReal c hc0 hc1 t).val,
    loopInPuncturedOpenNeighComplex_aux hball hc0 hc1 hcε t⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_subtype_val.comp (puncturedBallLoopOfReal c hc0 hc1).continuous_toFun)
      (loopInPuncturedOpenNeighComplex_aux hball hc0 hc1 hcε)

lemma constInPuncturedOpenNeighComplex_aux {U : Set ℂ} {ε c : ℝ} (hball : Metric.ball (0 : ℂ) ε ⊆ U)
    (hcε : c < ε) (hc0 : 0 < c) : (c : ℂ) ≠ 0 ∧ (c : ℂ) ∈ U := by
  refine And.intro ?_ ?_
  · exact_mod_cast ne_of_gt hc0
  · refine hball ?_
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    exact hcε

lemma constInPuncturedOpenNeighComplex_mem {U : Set ℂ} {ε c : ℝ} (hball : Metric.ball (0 : ℂ) ε ⊆ U)
    (hcε : c < ε) (hc0 : 0 < c) : (c : ℂ) ∈ U \ {(0 : ℂ)} := by
  rcases constInPuncturedOpenNeighComplex_aux hball hcε hc0 with ⟨hne, hmem⟩
  refine And.intro hmem (notMem_singleton_iff.mpr hne)

noncomputable def constInPuncturedOpenNeighComplex (U : Set ℂ) {ε c : ℝ} (hball : Metric.ball (0 : ℂ) ε ⊆ U)
    (hcε : c < ε) (hc0 : 0 < c) (_hc1 : c < 1) : C(I, PuncturedOpenNeighAtZeroComplex U) :=
  ContinuousMap.const I ⟨(c : ℂ), constInPuncturedOpenNeighComplex_mem hball hcε hc0⟩

noncomputable def puncturedOpenNeighComplexIncl (U : Set ℂ) : C(PuncturedOpenNeighAtZeroComplex U, ℂNeZero) where
  toFun z := ⟨z.val, by rcases z.property with ⟨_, hz⟩; simpa using notMem_singleton_iff.mp hz⟩
  continuous_toFun :=
    Continuous.subtype_mk continuous_subtype_val fun z => by
      rcases z.property with ⟨_, hz⟩
      simpa using notMem_singleton_iff.mp hz

lemma inclNeigh_comp_loop (U : Set ℂ) {ε c : ℝ} (hball : Metric.ball (0 : ℂ) ε ⊆ U) (hc0 : 0 < c)
    (hc1 : c < 1) (hcε : c < ε) :
    (puncturedOpenNeighComplexIncl U).comp (loopInPuncturedOpenNeighComplex U hball hc0 hc1 hcε) =
      puncturedBallLoopOfReal c hc0 hc1 :=
  ContinuousMap.ext fun t => Subtype.ext (by
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, puncturedOpenNeighComplexIncl,
      loopInPuncturedOpenNeighComplex, puncturedBallLoopOfReal])

lemma inclNeigh_comp_const (U : Set ℂ) {ε c : ℝ} (hball : Metric.ball (0 : ℂ) ε ⊆ U) (hcε : c < ε)
    (hc0 : 0 < c) (hc1 : c < 1) :
    (puncturedOpenNeighComplexIncl U).comp (constInPuncturedOpenNeighComplex U hball hcε hc0 hc1) =
      puncturedBallConstOfReal c hc0 hc1 :=
  ContinuousMap.ext fun t => Subtype.ext (by
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, puncturedOpenNeighComplexIncl,
      constInPuncturedOpenNeighComplex, puncturedBallConstOfReal, ContinuousMap.const_apply,
      halfPlaneNeZeroOfReal_pos])

theorem notSimplyConnected_punctured_open_neighborhood_zero_complex (U : Set ℂ) (hU : IsOpen U)
    (h0 : (0 : ℂ) ∈ U) : ¬ SimplyConnectedSpace (PuncturedOpenNeighAtZeroComplex U) := by
  classical
  rcases exists_pos_ball_subset_open_nhds_zero_complex hU h0 with ⟨ε, hε, hball⟩
  let c : ℝ := min (ε / 2) (1 / 3)
  have hc0 : 0 < c := lt_min (half_pos hε) (by norm_num)
  have hcε : c < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hc1 : c < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  intro h
  haveI : SimplyConnectedSpace (PuncturedOpenNeighAtZeroComplex U) := h
  let γ := loopInPuncturedOpenNeighComplex U hball hc0 hc1 hcε
  let γC := constInPuncturedOpenNeighComplex U hball hcε hc0 hc1
  let x₀ := γ 0
  have hx₁ : γ 1 = x₀ := by
    refine Subtype.ext ?_
    simp [x₀, γ, loopInPuncturedOpenNeighComplex, puncturedBallLoopOfReal_one,
      puncturedBallLoopOfReal_zero, halfPlaneNeZeroOfReal]
  have hs0 : γC 0 = x₀ := by
    refine Subtype.ext ?_
    simp [x₀, γC, γ, constInPuncturedOpenNeighComplex, loopInPuncturedOpenNeighComplex,
      puncturedBallLoopOfReal_zero, halfPlaneNeZeroOfReal]
  have hxC : γC 1 = x₀ := by
    refine Subtype.ext ?_
    simp [x₀, γC, γ, constInPuncturedOpenNeighComplex, loopInPuncturedOpenNeighComplex,
      puncturedBallLoopOfReal_zero, halfPlaneNeZeroOfReal]
  let pL := Path.mk γ rfl hx₁
  let pC := Path.mk γC hs0 hxC
  have hmt := SimplyConnectedSpace.paths_homotopic pL pC
  have Hpush := HomotopicRel.comp_continuousMap hmt (puncturedOpenNeighComplexIncl U)
  rw [inclNeigh_comp_loop U hball hc0 hc1 hcε, inclNeigh_comp_const U hball hcε hc0 hc1] at Hpush
  exact puncturedBall_loopOfReal_not_homotopic_const c hc0 hc1 Hpush

end RepresentationalRegress

end
