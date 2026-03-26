/-
  `EuclideanHalfSpace 1` (closed ray) is not homeomorphic to `ℝ` (and hence not to
  `EuclideanSpace ℝ (Fin 1)`): deleting the boundary endpoint leaves a connected punctured set,
  while ℝ minus a point is never connected.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open scoped Topology
open Set Topology

namespace RepresentationalRegress

abbrev RealHalfLine :=
  EuclideanHalfSpace 1

theorem ne_zero_iff_pos {z : RealHalfLine} : z ≠ 0 ↔ 0 < z.val 0 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le z.2 with heq | hlt
    · refine (h ?_).elim
      have hz0 : z.val 0 = 0 := heq.symm
      have heqv : z.val = 0 := PiLp.ext (fun i : Fin 1 => by
        fin_cases i
        simpa using hz0)
      exact @EuclideanHalfSpace.ext 1 inferInstance z (0 : RealHalfLine) heqv
    · simpa [Fin.forall_fin_one] using hlt
  · intro hlt h0
    subst h0
    have hz0 : (0 : RealHalfLine).val 0 = 0 := rfl
    rw [hz0] at hlt
    linarith

noncomputable def halfLineComplZeroHomeomorph_Ioi :
    ({z : RealHalfLine | z ≠ 0} : Set RealHalfLine) ≃ₜ Ioi (0 : ℝ) where
  toFun w := ⟨w.val.val 0, ne_zero_iff_pos.mp w.property⟩
  invFun y :=
    ⟨⟨EuclideanSpace.single (0 : Fin 1) y.val, by
      simpa [EuclideanSpace.single_apply] using y.property.le⟩,
      ne_zero_iff_pos.mpr y.property⟩
  left_inv w := by
    refine Subtype.ext ?_
    refine @EuclideanHalfSpace.ext 1 inferInstance _ _ (PiLp.ext ?_)
    intro i
    fin_cases i
    simp [EuclideanSpace.single_apply]
  right_inv y := by
    ext1
    simp [EuclideanSpace.single_apply]
  continuous_toFun := by
    refine continuous_induced_rng.mpr ?_
    exact (PiLp.continuous_apply (p := 2) (fun _ : Fin 1 => ℝ) 0).comp <|
      continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun :=
    continuous_induced_rng.mpr <|
      Continuous.subtype_mk
        ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 1 => ℝ)).comp <|
          continuous_pi_iff.mpr fun (i : Fin 1) => by
            fin_cases i
            simpa using continuous_subtype_val)
        fun y => by simpa [EuclideanSpace.single_apply] using y.property.le

theorem isConnected_halfLine_compl_zero :
    IsConnected ({z : RealHalfLine | z ≠ 0} : Set RealHalfLine) := by
  have hci : IsConnected (Ioi (0 : ℝ)) := isConnected_Ioi
  haveI : ConnectedSpace {y : ℝ // y ∈ Ioi (0 : ℝ)} := isConnected_iff_connectedSpace.mp hci
  let f : {y : ℝ // y ∈ Ioi (0 : ℝ)} → RealHalfLine := fun y =>
    (halfLineComplZeroHomeomorph_Ioi.symm y).val
  have hf : Continuous f :=
    continuous_subtype_val.comp halfLineComplZeroHomeomorph_Ioi.symm.continuous
  have hrange : f '' univ = {z : RealHalfLine | z ≠ 0} := by
    ext z
    simp only [RealHalfLine, mem_image, mem_setOf_eq, mem_univ]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (halfLineComplZeroHomeomorph_Ioi.symm y).property
    · intro hz
      refine ⟨halfLineComplZeroHomeomorph_Ioi ⟨z, hz⟩, trivial, ?_⟩
      dsimp [f]
      exact congrArg Subtype.val (halfLineComplZeroHomeomorph_Ioi.left_inv ⟨z, hz⟩)
  rw [← hrange]
  exact (isConnected_univ (α := {y : ℝ // y ∈ Ioi (0 : ℝ)})).image f hf.continuousOn

theorem real_compl_singleton_not_preconnected (c : ℝ) :
    ¬ IsPreconnected ({x : ℝ | x ≠ c} : Set ℝ) := by
  have hs : ({x : ℝ | x ≠ c} : Set ℝ) = Iio c ∪ Ioi c := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro h
      rcases lt_trichotomy x c with hlt | rfl | hgt <;> simp_all
    · rintro (h | h) <;> intro hce <;> linarith
  rw [hs]
  intro h
  rcases h.subset_or_subset isOpen_Iio isOpen_Ioi Iio_disjoint_Ioi_same Subset.rfl with
    hsub | hsub
  · have hm : c + 1 ∈ Iio c ∪ Ioi c := Or.inr (mem_Ioi.mpr (lt_add_one c))
    have hmem : c + 1 ∈ Iio c := hsub hm
    simp only [mem_Iio] at hmem
    linarith [hmem, lt_add_one c]
  · have hm : c - 1 ∈ Iio c ∪ Ioi c := Or.inl (mem_Iio.mpr (sub_one_lt c))
    have hmem : c - 1 ∈ Ioi c := hsub hm
    simp only [mem_Ioi] at hmem
    linarith

theorem real_compl_singleton_not_connected (c : ℝ) :
    ¬ IsConnected ({x : ℝ | x ≠ c} : Set ℝ) := fun h =>
  real_compl_singleton_not_preconnected c h.2

theorem Homeomorph.image_compl_singleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (x0 : X) :
    φ '' {x : X | x ≠ x0} = {y : Y | y ≠ φ x0} := by
  ext y
  simp only [mem_image, mem_setOf_eq, ne_eq]
  constructor
  · rintro ⟨x, hxne, rfl⟩
    exact fun hc => hxne (φ.injective hc)
  · intro hyne
    refine ⟨φ.symm y, fun heq => ?_, φ.apply_symm_apply y⟩
    apply hyne
    calc
      y = φ (φ.symm y) := (φ.apply_symm_apply y).symm
      _ = φ x0 := congr_arg φ heq

theorem euclideanHalfSpace1_not_homeomorphic_real : IsEmpty (RealHalfLine ≃ₜ ℝ) := by
  refine ⟨fun h => ?_⟩
  have hS : IsConnected ({z : RealHalfLine | z ≠ 0} : Set RealHalfLine) :=
    isConnected_halfLine_compl_zero
  have hS' : IsConnected (h '' {z : RealHalfLine | z ≠ 0}) :=
    (h.isConnected_image (s := {z | z ≠ 0})).mpr hS
  rw [Homeomorph.image_compl_singleton h 0] at hS'
  exact real_compl_singleton_not_connected (h 0) hS'

/-! ### `EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ` (via `PiLp` projections) -/

noncomputable def euclideanFinOneHomeoReal : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ where
  toFun v := v 0
  invFun r := EuclideanSpace.single (0 : Fin 1) r
  left_inv v := by
    refine PiLp.ext ?_
    intro i
    fin_cases i
    simp
  right_inv r := by simp [EuclideanSpace.single_apply]
  continuous_toFun := PiLp.continuous_apply (p := 2) (β := fun _ : Fin 1 => ℝ) 0
  continuous_invFun := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 1 => ℝ)).comp ?_
    refine continuous_pi_iff.mpr ?_
    intro i
    fin_cases i
    simp
    exact continuous_id

theorem euclideanHalfSpace1_not_homeomorphic_euclidean1 :
    IsEmpty (RealHalfLine ≃ₜ EuclideanSpace ℝ (Fin 1)) := by
  refine ⟨fun φ => ?_⟩
  exact euclideanHalfSpace1_not_homeomorphic_real.false <| φ.trans euclideanFinOneHomeoReal

end RepresentationalRegress

end
