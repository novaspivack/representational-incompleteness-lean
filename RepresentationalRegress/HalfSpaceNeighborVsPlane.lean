/-
  **Half-space neighborhood vs plane (local `SPEC_002` model).**

  If `V ⊆ H2` is **open** in `EuclideanHalfSpace 2` and contains the boundary point `0`, then
  `Subtype V` is **not** homeomorphic to `ℝ²`: shrink `V` to a small Euclidean ball in the
  underlying plane, puncture at `0`, and compare with a punctured open patch in `ℝ²`
  (not simply connected).
-/

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Separation.Basic

import RepresentationalRegress.HalfPlaneVsPlane

noncomputable section

namespace RepresentationalRegress

open scoped Manifold Topology
open Set Metric Topology EuclideanSpace

/-- The closed half-plane `{x : R2 | 0 ≤ x 0}` (same carrier as `H2`). -/
def halfspaceR2 : Set R2 :=
  { x | 0 ≤ x 0 }

/-- Points in the closed half-plane, nonzero, of norm `< ε` (subset of `R2`). -/
def puncturedHalfBallR2 (ε : ℝ) : Set R2 :=
  { v | 0 ≤ v 0 ∧ v ≠ 0 ∧ ‖v‖ < ε }

noncomputable def puncturedHalfBallCenter (ε : ℝ) (_hε : 0 < ε) : R2 :=
  EuclideanSpace.single (0 : Fin 2) (ε / 4)

lemma puncturedHalfBallCenter_mem (ε : ℝ) (hε : 0 < ε) :
    puncturedHalfBallCenter ε hε ∈ puncturedHalfBallR2 ε := by
  refine And.intro (by
    simp only [puncturedHalfBallCenter, EuclideanSpace.single_apply]; positivity) (And.intro ?_ ?_)
  · intro h0
    have h10 := congrArg (fun w : R2 => w 0) h0
    simp [puncturedHalfBallCenter, EuclideanSpace.single_apply] at h10
    linarith [hε]
  · rw [EuclideanSpace.norm_eq]
    have hterm :
        (∑ i : Fin 2, ‖puncturedHalfBallCenter ε hε i‖ ^ 2) = (ε / 4) ^ 2 := by
      simp [puncturedHalfBallCenter, EuclideanSpace.single_apply, Real.norm_eq_abs]
    rw [hterm, Real.sqrt_sq (by positivity)]
    nlinarith [hε]

lemma starConvex_puncturedHalfBallR2 (ε : ℝ) (hε : 0 < ε) :
    StarConvex ℝ (puncturedHalfBallCenter ε hε) (puncturedHalfBallR2 ε) := by
  let c := puncturedHalfBallCenter ε hε
  intro y hy a b ha hb hab
  obtain ⟨hy0, hyNE, hyn⟩ := hy
  have hc0' : c (0 : Fin 2) = ε / 4 := by
    simp [c, puncturedHalfBallCenter, EuclideanSpace.single_apply]
  have hn_c : ‖c‖ < ε := (puncturedHalfBallCenter_mem ε hε).2.2
  refine And.intro ?_ (And.intro ?_ ?_)
  · simp only [PiLp.smul_apply, PiLp.add_apply]
    rw [hc0']
    exact add_nonneg (mul_nonneg ha (by positivity : (0 : ℝ) ≤ ε / 4)) (mul_nonneg hb hy0)
  · rintro h0
    have hcoord0 :
        a * c (0 : Fin 2) + b * y (0 : Fin 2) = 0 := by
      simpa [PiLp.add_apply, PiLp.smul_apply] using congrArg (fun w : R2 => w 0) h0
    rw [hc0'] at hcoord0
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith [hb0, hab]
      subst hb0 ha1
      norm_num at hcoord0
      linarith [hcoord0, hε]
    · by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith [ha0, hab]
        subst ha0 hb1
        have hy0' : y = 0 := by
          simpa [PiLp.add_apply, PiLp.smul_apply, zero_smul, one_smul] using h0
        exact hyNE hy0'
      · have hbpos : 0 < b := (Ne.symm hb0).lt_of_le hb
        have hapos : 0 < a := (Ne.symm ha0).lt_of_le ha
        have hm : 0 ≤ b * y 0 := mul_nonneg hb hy0
        have hsum : 0 < a * (ε / 4) + b * y 0 :=
          lt_of_lt_of_le (mul_pos hapos (by positivity : (0 : ℝ) < ε / 4))
            (le_add_of_nonneg_right hm)
        linarith [hcoord0, hsum]
  · have hn1 : ‖a • c‖ = a * ‖c‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    have hn2 : ‖b • y‖ = b * ‖y‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have hle : ‖a • c + b • y‖ ≤ a * ‖c‖ + b * ‖y‖ := by
      calc
        ‖a • c + b • y‖ ≤ ‖a • c‖ + ‖b • y‖ := norm_add_le _ _
        _ = a * ‖c‖ + b * ‖y‖ := by rw [hn1, hn2]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith [ha0, hab]
      subst ha0 hb1
      simpa [one_smul, zero_smul, add_zero] using hyn
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith [hb0, hab]
        subst hb0 ha1
        simpa [one_smul, zero_smul, zero_add] using hn_c
      · have hapos : 0 < a := (Ne.symm ha0).lt_of_le ha
        have hbpos : 0 < b := (Ne.symm hb0).lt_of_le hb
        have hlt : a * ‖c‖ + b * ‖y‖ < ε := by
          have hc2 : a * ‖c‖ < a * ε := mul_lt_mul_of_pos_left hn_c hapos
          have hy2 : b * ‖y‖ < b * ε := mul_lt_mul_of_pos_left hyn hbpos
          calc
            a * ‖c‖ + b * ‖y‖ < a * ε + b * ε := add_lt_add hc2 hy2
            _ = ε := by rw [← add_mul, hab, one_mul]
        exact lt_of_le_of_lt hle hlt

lemma puncturedHalfBallR2_nonempty (ε : ℝ) (hε : 0 < ε) : (puncturedHalfBallR2 ε).Nonempty :=
  ⟨_, puncturedHalfBallCenter_mem ε hε⟩

lemma exists_rnBall_nhds_subset_halfspace_open {V : Set H2} (hV : IsOpen V) (h0 : (0 : H2) ∈ V) :
    ∃ ε > 0, ∀ h : H2, ‖(h.val : R2)‖ < ε → h ∈ V := by
  rcases (IsInducing.subtypeVal (t := halfspaceR2)).isOpen_iff.mp hV with ⟨O, hO, hVO⟩
  have h0O : (0 : R2) ∈ O := by
    have h' : (0 : H2) ∈ Subtype.val ⁻¹' O :=
      (Set.ext_iff.mp hVO.symm (0 : H2)).1 h0
    exact mem_preimage.mp h'
  rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds hO h0O) with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro h hh
  have hval : h.val ∈ Metric.ball (0 : R2) ε := by simpa [mem_ball_zero_iff] using hh
  have hvalO : h.val ∈ O := hball hval
  rw [← hVO]
  exact mem_preimage.mpr hvalO

abbrev PuncturedHalfBallR2 (ε : ℝ) :=
  { v : R2 // v ∈ puncturedHalfBallR2 ε }

abbrev PuncturedRNBallInV (V : Set H2) (_h0 : (0 : H2) ∈ V) (ε : ℝ) :=
  { w : Subtype V // ‖(w.val.val : R2)‖ < ε ∧ w.val ≠ (0 : H2) }

noncomputable def puncturedRNBallInVHomeoPuncturedHalfBallR2 {V : Set H2} {h0 : (0 : H2) ∈ V}
    {ε : ℝ} (_hε : 0 < ε) (hball : ∀ h : H2, ‖(h.val : R2)‖ < ε → h ∈ V) :
    PuncturedRNBallInV V h0 ε ≃ₜ PuncturedHalfBallR2 ε where
  toFun w :=
    ⟨w.val.val.val,
      And.intro w.val.val.property
        (And.intro (by
          intro hz
          apply w.property.2
          refine EuclideanHalfSpace.ext w.val.val (0 : H2) hz) w.property.1)⟩
  invFun v :=
    let hH : H2 := ⟨v.val, v.property.1⟩
    have hmemV : hH ∈ V := by
      refine hball hH ?_
      simpa [hH, mem_ball_zero_iff] using v.property.2.2
    let w : Subtype V := ⟨hH, hmemV⟩
    ⟨w,
      And.intro (by simpa [mem_ball_zero_iff] using v.property.2.2) (by
        intro heq
        apply v.property.2.1
        simpa [hH] using congrArg (fun x : H2 => (x.val : R2)) heq)⟩
  left_inv w := by ext1; rfl
  right_inv v := by ext1; rfl
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
      (by
        intro w
        dsimp only [puncturedHalfBallR2]
        exact And.intro w.val.val.property
          (And.intro (fun hz => w.property.2 (EuclideanHalfSpace.ext w.val.val (0 : H2) hz))
            w.property.1))
  continuous_invFun := by
    let g : PuncturedHalfBallR2 ε → Subtype V := fun (x : PuncturedHalfBallR2 ε) =>
      ⟨⟨x.val, x.property.1⟩,
        hball ⟨x.val, x.property.1⟩ (by simpa [mem_ball_zero_iff] using x.property.2.2)⟩
    have hg' : Continuous g := by
      have hinner :
          Continuous (fun (x : PuncturedHalfBallR2 ε) => (⟨x.val, x.property.1⟩ : H2)) :=
        Continuous.subtype_mk
          (continuous_subtype_val : Continuous (Subtype.val : PuncturedHalfBallR2 ε → R2))
          (by intro (x : PuncturedHalfBallR2 ε); exact x.property.1)
      exact Continuous.subtype_mk hinner fun (x : PuncturedHalfBallR2 ε) =>
        hball ⟨x.val, x.property.1⟩ (by simpa [mem_ball_zero_iff] using x.property.2.2)
    refine Continuous.subtype_mk hg' fun (x : PuncturedHalfBallR2 ε) =>
      And.intro (by simpa [mem_ball_zero_iff] using x.property.2.2) (by
        intro heq
        apply x.property.2.1
        simpa [g, Subtype.val] using congrArg (fun h : H2 => (h.val : R2)) heq)

theorem isEmpty_homeomorph_subtype_openH2_zero_nbhd_R2 {V : Set H2} (hV : IsOpen V)
    (h0 : (0 : H2) ∈ V) : IsEmpty (Subtype V ≃ₜ R2) := by
  classical
  refine ⟨fun e => ?_⟩
  rcases exists_rnBall_nhds_subset_halfspace_open hV h0 with ⟨ε, hε, hball⟩
  let z0 : Subtype V := ⟨(0 : H2), h0⟩
  let p : R2 := e z0
  let S : Set (Subtype V) := { w : Subtype V | ‖(w.val.val : R2)‖ < ε }
  have hS_open : IsOpen (S : Set (Subtype V)) := by
    have hf : Continuous (fun w : Subtype V => (w.val.val : R2)) :=
      (continuous_subtype_val : Continuous (Subtype.val : H2 → R2)).comp
        (continuous_subtype_val : Continuous (Subtype.val : Subtype V → H2))
    have hn := continuous_norm.comp hf
    simpa [S, preimage, mem_setOf_eq] using IsOpen.preimage hn isOpen_Iio
  have hz0S : z0 ∈ S := by
    simp [S, z0, Set.mem_setOf_eq]
    change ‖(0 : R2)‖ < ε
    rw [norm_zero]
    exact hε
  let Sv : Set (Subtype V) :=
    { w : Subtype V | ‖(w.val.val : R2)‖ < ε ∧ w.val ≠ (0 : H2) }
  have hSv_eq : Sv = S \ {z0} := by
    ext w
    constructor
    · rintro ⟨hnorm, hval⟩
      refine ⟨hnorm, ?_⟩
      intro heq
      apply hval
      simpa [z0] using congrArg Subtype.val heq
    · rintro ⟨hnorm, hne⟩
      refine ⟨hnorm, ?_⟩
      intro hv0
      exact hne (Subtype.ext hv0)
  have hSv_open : IsOpen (Sv : Set (Subtype V)) := by
    have hp : IsOpen ({(0 : R2)}ᶜ : Set R2) := isOpen_compl_singleton
    have hf : Continuous (fun w : Subtype V => (w.val.val : R2)) :=
      (continuous_subtype_val : Continuous (Subtype.val : H2 → R2)).comp continuous_subtype_val
    have hpre : IsOpen ((fun w : Subtype V => (w.val.val : R2)) ⁻¹' ({(0 : R2)}ᶜ)) :=
      hp.preimage hf
    simpa [Sv, S, preimage, mem_setOf_eq, ne_eq, Subtype.ext_iff, EuclideanHalfSpace.ext_iff] using
      hS_open.inter hpre
  have hhdiff : ⇑e '' Sv = ⇑e '' S \ {p} := by
    rw [hSv_eq, Set.image_diff (Homeomorph.injective e) S {z0}, Set.image_singleton]
  have hSe : IsOpen (⇑e '' S : Set R2) := e.isOpenMap S hS_open
  let W : Set R2 := ⇑e '' S \ {p}
  have htW : IsOpen (W : Set R2) := hSe.sdiff isClosed_singleton
  let U : Set R2 := (translateMinus p) '' (e '' S)
  have hU_open : IsOpen (U : Set R2) := (translateMinus p).isOpenMap _ hSe
  have h0U : (0 : R2) ∈ U := by
    refine ⟨p, ⟨z0, hz0S, rfl⟩, ?_⟩
    simp [translateMinus, p]
  have htrans_image : (translateMinus p) '' W = U \ {(0 : R2)} := by
    have := Set.image_diff (Homeomorph.injective (translateMinus p)) (e '' S) {p}
    simpa [U, W, translateMinus, sub_eq_zero, p, Set.image_singleton] using this
  have φ :
      Subtype Sv ≃ₜ PuncturedOpenNeighAtZeroR2 U :=
    (Homeomorph.image e Sv).trans
      ((Homeomorph.setCongr hhdiff).trans
        ((Homeomorph.image (translateMinus p) W).trans (Homeomorph.setCongr htrans_image)))
  have ψ := puncturedRNBallInVHomeoPuncturedHalfBallR2 (h0 := h0) hε hball
  have sc_punct :
      SimplyConnectedSpace (PuncturedOpenNeighAtZeroR2 U) := by
    letI : ContractibleSpace (↥(puncturedHalfBallR2 ε)) :=
      StarConvex.contractibleSpace (starConvex_puncturedHalfBallR2 ε hε)
        (puncturedHalfBallR2_nonempty ε hε)
    haveI : SimplyConnectedSpace (↥(puncturedHalfBallR2 ε)) := SimplyConnectedSpace.ofContractible _
    haveI sc_Sv : SimplyConnectedSpace (Subtype Sv) :=
      ψ.toHomotopyEquiv.simplyConnectedSpace
    exact φ.symm.toHomotopyEquiv.simplyConnectedSpace
  exact notSimplyConnected_punctured_open_neighborhood_zero_R2 hU_open h0U sc_punct

end RepresentationalRegress

end
