/-
  `EuclideanHalfSpace 2` is **not** homeomorphic to `EuclideanSpace ℝ (Fin 2)` (≈ `ℝ²`).

  Sketch: `E² \\ {0}` on the half-space side is star-convex, hence contractible / simply connected.
  But `ℝ² \\ {p}` is not simply connected for any `p` (via `ℂNeZero`). Any `φ : H2 ≃ₜ E²`
  restricts to `H2\\{0} ≃ E²\\{φ 0}`, contradicting homotopy invariance of simple connectivity.
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import RepresentationalIncompleteness.HalfLineVsLine
import RepresentationalIncompleteness.PuncturedPlaneNotSimplyConnected

noncomputable section

namespace RepresentationalIncompleteness

open scoped Manifold Topology
open EuclideanSpace Set Complex Filter

abbrev R2 := EuclideanSpace ℝ (Fin 2)
abbrev H2 := EuclideanHalfSpace 2

def openHalfPlaneNeZeroSet : Set R2 :=
  { v | 0 ≤ v 0 ∧ v ≠ 0 }

noncomputable def openHalfPlaneNeZeroCenter : R2 :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

lemma openHalfPlaneNeZeroCenter_mem :
    openHalfPlaneNeZeroCenter ∈ openHalfPlaneNeZeroSet := by
  refine And.intro ?_ ?_
  · simp [openHalfPlaneNeZeroCenter, EuclideanSpace.single_apply]
  · intro h0
    have h10 : openHalfPlaneNeZeroCenter (0 : Fin 2) = (0 : ℝ) := by
      simpa [openHalfPlaneNeZeroCenter, EuclideanSpace.single_apply] using
        congrArg (fun w : R2 => w 0) h0
    simp [openHalfPlaneNeZeroCenter, EuclideanSpace.single_apply] at h10

lemma starConvex_openHalfPlaneNeZeroSet :
    StarConvex ℝ openHalfPlaneNeZeroCenter openHalfPlaneNeZeroSet := by
  intro y hy a b ha hb hab
  refine And.intro ?_ ?_
  · simp only [openHalfPlaneNeZeroSet, mem_setOf_eq] at hy ⊢
    have hc0 : openHalfPlaneNeZeroCenter 0 = 1 := by
      simp [openHalfPlaneNeZeroCenter, EuclideanSpace.single_apply]
    simp only [PiLp.smul_apply, PiLp.add_apply, hc0]
    have hy0 : 0 ≤ y 0 := hy.1
    exact add_nonneg (mul_nonneg ha zero_le_one) (mul_nonneg hb hy0)
  · intro h0
    obtain ⟨hy1, hyNE⟩ := hy
    have hcoord0 :
        a * openHalfPlaneNeZeroCenter (0 : Fin 2) + b * y (0 : Fin 2) = 0 := by
      simpa [PiLp.add_apply, PiLp.smul_apply, openHalfPlaneNeZeroCenter, EuclideanSpace.single_apply,
        mul_one] using congrArg (fun w : R2 => w 0) h0
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith [hb0, hab]
      subst hb0 ha1
      norm_num [openHalfPlaneNeZeroCenter, EuclideanSpace.single_apply] at hcoord0
    · by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith [ha0, hab]
        subst ha0 hb1
        have hy0 : y = 0 := by
          simpa [PiLp.add_apply, PiLp.smul_apply, zero_smul, one_smul] using h0
        exact hyNE hy0
      · have hbpos : 0 < b := (Ne.symm hb0).lt_of_le hb
        have hapos : 0 < a := (Ne.symm ha0).lt_of_le ha
        have hy0 : 0 ≤ y 0 := hy1
        have hm : 0 ≤ b * y 0 := mul_nonneg hb hy0
        have hsum : 0 < a + b * y 0 :=
          lt_of_lt_of_le hapos (le_add_of_nonneg_right hm)
        have hcoord0' : a + b * y 0 = 0 := by
          simpa [openHalfPlaneNeZeroCenter, EuclideanSpace.single_apply] using hcoord0
        linarith [hcoord0', hsum]

lemma openHalfPlaneNeZeroSet_nonempty : openHalfPlaneNeZeroSet.Nonempty :=
  ⟨openHalfPlaneNeZeroCenter, openHalfPlaneNeZeroCenter_mem⟩

instance contractibleSpace_openHalfPlaneNeZeroSet :
    ContractibleSpace { v : R2 // v ∈ openHalfPlaneNeZeroSet } :=
  starConvex_openHalfPlaneNeZeroSet.contractibleSpace openHalfPlaneNeZeroSet_nonempty

instance simplyConnectedSpace_openHalfPlaneNeZeroSet :
    SimplyConnectedSpace { v : R2 // v ∈ openHalfPlaneNeZeroSet } :=
  SimplyConnectedSpace.ofContractible _

abbrev PuncturedE2 :=
  { v : R2 // v ≠ 0 }

abbrev H2NeZero :=
  { h : H2 // h ≠ 0 }

/-!### `ℂ ≃ₜ R2` and punctured spaces -/

noncomputable def euclidFinTwoHomeoProd : R2 ≃ₜ ℝ × ℝ :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).toHomeomorph.trans
    (euclideanFinOneHomeoReal.prodCongr euclideanFinOneHomeoReal)

noncomputable def complexHomeoE2 : ℂ ≃ₜ R2 :=
  equivRealProdCLM.toHomeomorph.trans euclidFinTwoHomeoProd.symm

lemma euclideanFinOneHomeoReal_zero :
    euclideanFinOneHomeoReal (0 : EuclideanSpace ℝ (Fin 1)) = 0 := by
  simp [euclideanFinOneHomeoReal]

lemma euclidFinTwoHomeoProd_zero : euclidFinTwoHomeoProd (0 : R2) = (0, 0) := by
  simp [euclidFinTwoHomeoProd, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
    ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.map_zero, Prod.map,
    euclideanFinOneHomeoReal_zero]

lemma complexHomeoE2_zero : complexHomeoE2 0 = 0 := by
  rw [complexHomeoE2, Homeomorph.trans_apply]
  have hε : equivRealProdCLM.toHomeomorph 0 = euclidFinTwoHomeoProd 0 := by
    rw [ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.map_zero, euclidFinTwoHomeoProd_zero]
    rfl
  rw [hε, euclidFinTwoHomeoProd.symm_apply_apply]

lemma continuous_complexHomeoE2 : Continuous complexHomeoE2 := complexHomeoE2.continuous

lemma tendsto_norm_complexHomeoE2_nhds_zero :
    Tendsto (fun z : ℂ => ‖complexHomeoE2 z‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
  simpa [complexHomeoE2_zero, norm_zero] using
    (continuous_norm.comp complexHomeoE2.continuous).tendsto (0 : ℂ)

noncomputable def complexNeZeroHomeoPuncturedE2 : ℂNeZero ≃ₜ PuncturedE2 :=
  Homeomorph.subtype complexHomeoE2 (by
    intro z
    rw [← complexHomeoE2_zero]
    exact (complexHomeoE2.injective.ne_iff (x := z) (y := 0)).symm)

theorem notSimplyConnected_punctured_E2 : ¬ SimplyConnectedSpace PuncturedE2 := by
  intro h
  haveI : SimplyConnectedSpace PuncturedE2 := h
  haveI : SimplyConnectedSpace ℂNeZero :=
    complexNeZeroHomeoPuncturedE2.toHomotopyEquiv.simplyConnectedSpace
  exact notSimplyConnected_complex_ne_zero ‹_›

/-!### `H2 \\ {0}` as a punctured half-plane -/

noncomputable def puncturedHalfPlaneHomeoH2NeZero :
    { v : R2 // v ∈ openHalfPlaneNeZeroSet } ≃ₜ H2NeZero where
  toFun w :=
    ⟨⟨w.val, w.property.1⟩, by
      rintro hw
      have : (w.val : R2) = (0 : R2) := congrArg Subtype.val hw
      exact w.property.2 this⟩
  invFun h :=
    ⟨h.val.val, And.intro h.val.property (by
      intro h0
      refine h.property ?_
      have heq : (h.val : H2) = (0 : H2) :=
        @EuclideanHalfSpace.ext 2 inferInstance _ _ (by simpa using h0)
      exact heq)⟩
  left_inv w := by ext1; rfl
  right_inv h := by ext1; rfl
  continuous_toFun := by
    let g : { v : R2 // v ∈ openHalfPlaneNeZeroSet } → H2 := fun w => ⟨w.val, w.property.1⟩
    have hg : Continuous g :=
      Continuous.subtype_mk (continuous_subtype_val : Continuous (Subtype.val : _ → R2))
        fun w => w.property.1
    refine Continuous.subtype_mk hg fun w => by
      intro hw
      have hz : w.val = (0 : R2) := by simpa [g] using congrArg Subtype.val hw
      exact w.property.2 hz
  continuous_invFun := by
    have hf : Continuous fun h : H2NeZero => (h.val.val : R2) :=
      (continuous_subtype_val : Continuous (Subtype.val : H2 → R2)).comp
        (continuous_subtype_val : Continuous (Subtype.val : H2NeZero → H2))
    exact Continuous.subtype_mk hf fun h => And.intro h.val.property
      (by
        intro hz
        have heq : (h.val : H2) = (0 : H2) :=
          @EuclideanHalfSpace.ext 2 inferInstance _ _ (by simpa using hz)
        exact h.property heq)

instance simplyConnectedSpace_H2_ne_zero : SimplyConnectedSpace H2NeZero :=
  puncturedHalfPlaneHomeoH2NeZero.symm.toHomotopyEquiv.simplyConnectedSpace

/-!### Translation identifies punctured plane at `q` with punctured plane at `0` -/

noncomputable def translateMinus (q : R2) : R2 ≃ₜ R2 where
  toFun v := v - q
  invFun v := v + q
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := continuous_id.sub continuous_const
  continuous_invFun := continuous_id.add continuous_const

noncomputable def puncturedTranslate (q : R2) : { v : R2 // v ≠ q } ≃ₜ PuncturedE2 :=
  Homeomorph.subtype (translateMinus q) (by
    intro v
    simp [translateMinus, sub_eq_zero])

/-!### Any punctured open neighborhood of `0` in `R2` -/

abbrev PuncturedOpenNeighAtZeroR2 (U : Set R2) :=
  { x : R2 // x ∈ U \ {(0 : R2)} }

lemma complex_preimage_U_diff_zero_eq_image_symm (U : Set R2) :
    (complexHomeoE2 ⁻¹' U : Set ℂ) \ {(0 : ℂ)} = complexHomeoE2.symm '' (U \ {(0 : R2)}) := by
  ext z
  simp only [mem_diff, mem_preimage, mem_singleton_iff, mem_image]
  constructor
  · rintro ⟨hzU, hz0⟩
    refine ⟨complexHomeoE2 z, ?_, (complexHomeoE2.symm_apply_apply z).symm⟩
    refine And.intro hzU ?_
    intro hce
    apply hz0
    have h' : complexHomeoE2 z = complexHomeoE2 (0 : ℂ) := by rw [hce, complexHomeoE2_zero]
    exact (Homeomorph.injective complexHomeoE2) h'
  · rintro ⟨x, ⟨hxU, hx0⟩, hzq⟩
    subst hzq
    refine And.intro ?_ ?_
    · simpa [mem_preimage, Homeomorph.apply_symm_apply] using hxU
    · intro hz
      apply hx0
      calc
        x = complexHomeoE2 (complexHomeoE2.symm x) := (complexHomeoE2.apply_symm_apply x).symm
        _ = complexHomeoE2 0 := by rw [hz]
        _ = 0 := complexHomeoE2_zero

noncomputable def homeoPuncturedNeighR2OfComplex (U : Set R2) :
    PuncturedOpenNeighAtZeroR2 U ≃ₜ PuncturedOpenNeighAtZeroComplex (complexHomeoE2 ⁻¹' U) :=
  (Homeomorph.image (complexHomeoE2.symm) (U \ {(0 : R2)})).trans
    (Homeomorph.setCongr (complex_preimage_U_diff_zero_eq_image_symm U).symm)

theorem notSimplyConnected_punctured_open_neighborhood_zero_R2 {U : Set R2} (hU : IsOpen U)
    (h0 : (0 : R2) ∈ U) : ¬ SimplyConnectedSpace (PuncturedOpenNeighAtZeroR2 U) := by
  classical
  intro hs
  haveI : SimplyConnectedSpace (PuncturedOpenNeighAtZeroR2 U) := hs
  have hUc : IsOpen (complexHomeoE2 ⁻¹' U) :=
    hU.preimage complexHomeoE2.continuous
  have h0c : (0 : ℂ) ∈ complexHomeoE2 ⁻¹' U := by
    simpa [complexHomeoE2_zero] using h0
  haveI scC : SimplyConnectedSpace (PuncturedOpenNeighAtZeroComplex (complexHomeoE2 ⁻¹' U)) :=
    (Homeomorph.toHomotopyEquiv (homeoPuncturedNeighR2OfComplex U).symm).simplyConnectedSpace
  exact notSimplyConnected_punctured_open_neighborhood_zero_complex _ hUc h0c scC

/-!### Main result -/

theorem euclideanHalfSpace2_not_homeomorphic_euclidean2 : IsEmpty (H2 ≃ₜ R2) := by
  refine ⟨fun φ => ?_⟩
  let q := φ (0 : H2)
  let ψ : H2NeZero ≃ₜ { v : R2 // v ≠ q } :=
    Homeomorph.subtype φ (by
      intro x
      rw [show q = φ (0 : H2) from rfl]
      exact (φ.injective.ne_iff (x := x) (y := (0 : H2))).symm)
  haveI hcod : SimplyConnectedSpace { v : R2 // v ≠ q } :=
    ψ.symm.toHomotopyEquiv.simplyConnectedSpace
  have hE : SimplyConnectedSpace PuncturedE2 :=
    (puncturedTranslate q).symm.toHomotopyEquiv.simplyConnectedSpace
  exact notSimplyConnected_punctured_E2 hE

end RepresentationalIncompleteness

end
