/-
  Closed cylinder `Circle × Icc 0 1` in the `Geometry.Manifold` sense: **boundary** as a disjoint
  union of two faces, each **connected**.

  This is the Mathlib-backed step toward the philosophical “two boundary circles vs one” contrast
  with the Möbius strip. **New:** `not_isPreconnected_closedCylinderBoundaryUnion` /
  `not_isConnected_closedCylinderBoundaryUnion` (the union of the two faces is disconnected), to
  pair with connected `mobiusStripBoundary` once a homeomorphism boundary bridge is proved.

  Main inputs: `boundary_product` (`Geometry.Manifold.Instances.Real`) and connectivity of
  `Circle` via surjectivity of `Circle.exp` (`Analysis.SpecialFunctions.Complex.Circle`).
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Set.Prod
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Connected.Basic

noncomputable section

open scoped Manifold

open Set Function
open Topology

namespace RepresentationalRegress

/-- Closed cylinder `S¹ × [0, 1]` with the product manifold structure (`𝓡 1` on the circle,
`𝓡∂ 1` on the interval). -/
abbrev ClosedCylinder : Type :=
  Circle × Icc (0 : ℝ) 1

/-- The bottom face `S¹ × {0}` as a subset of the closed cylinder. -/
def closedCylinderBotFace : Set ClosedCylinder :=
  univ ×ˢ {⊥}

/-- The top face `S¹ × {1}` as a subset of the closed cylinder. -/
def closedCylinderTopFace : Set ClosedCylinder :=
  univ ×ˢ {⊤}

/-- Coordinates on the bottom boundary circle. -/
def closedCylinderBotCoords : Circle → ClosedCylinder :=
  fun c ↦ (c, ⊥)

/-- Coordinates on the top boundary circle. -/
def closedCylinderTopCoords : Circle → ClosedCylinder :=
  fun c ↦ (c, ⊤)

theorem continuous_closedCylinderBotCoords : Continuous closedCylinderBotCoords :=
  continuous_id.prodMk continuous_const

theorem continuous_closedCylinderTopCoords : Continuous closedCylinderTopCoords :=
  continuous_id.prodMk continuous_const

theorem range_closedCylinderBotCoords : range closedCylinderBotCoords = closedCylinderBotFace := by
  ext ⟨c, p⟩
  simp only [closedCylinderBotCoords, closedCylinderBotFace, mem_range, mem_prod, mem_univ,
    mem_singleton_iff]
  constructor
  · rintro ⟨c', h⟩
    rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    simp
  · rintro ⟨_, hp⟩
    subst hp
    exact ⟨c, rfl⟩

theorem range_closedCylinderTopCoords : range closedCylinderTopCoords = closedCylinderTopFace := by
  ext ⟨c, p⟩
  simp only [closedCylinderTopCoords, closedCylinderTopFace, mem_range, mem_prod, mem_univ,
    mem_singleton_iff]
  constructor
  · rintro ⟨c', h⟩
    rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    simp
  · rintro ⟨_, hp⟩
    subst hp
    exact ⟨c, rfl⟩

theorem bot_ne_top_Icc01 : (⊥ : Icc (0 : ℝ) 1) ≠ (⊤ : Icc (0 : ℝ) 1) := by
  intro h
  have := congr_arg Subtype.val h
  simp at this

lemma circleExp_surjective : Surjective Circle.exp := fun z ↦
  let ⟨x, _, hx⟩ := Circle.surjOn_exp_neg_pi_pi (mem_univ z)
  ⟨x, hx⟩

lemma isConnected_univ_circle : IsConnected (univ : Set Circle) := by
  rw [← Surjective.range_eq circleExp_surjective, ← image_univ]
  exact isConnected_univ.image Circle.exp Circle.exp.continuous.continuousOn

theorem isConnected_closedCylinderBotFace : IsConnected closedCylinderBotFace := by
  rw [← range_closedCylinderBotCoords, ← image_univ]
  exact isConnected_univ_circle.image _ continuous_closedCylinderBotCoords.continuousOn

theorem isConnected_closedCylinderTopFace : IsConnected closedCylinderTopFace := by
  rw [← range_closedCylinderTopCoords, ← image_univ]
  exact isConnected_univ_circle.image _ continuous_closedCylinderTopCoords.continuousOn

theorem closedCylinder_boundary :
    ((𝓡 1).prod (𝓡∂ 1)).boundary (ClosedCylinder) = univ ×ˢ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  simpa [ClosedCylinder] using boundary_product (M := Circle) (I := 𝓡 1)

theorem icc01_bot_top_union : ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) = {⊥} ∪ {⊤} :=
  rfl

theorem closedCylinder_boundary_eq_union :
    ((𝓡 1).prod (𝓡∂ 1)).boundary ClosedCylinder = closedCylinderBotFace ∪ closedCylinderTopFace := by
  rw [closedCylinder_boundary, closedCylinderBotFace, closedCylinderTopFace, icc01_bot_top_union,
    prod_union]

theorem closedCylinder_boundary_faces_disjoint :
    Disjoint closedCylinderBotFace closedCylinderTopFace := by
  rw [disjoint_iff_inter_eq_empty]
  ext ⟨c, p⟩
  simp only [closedCylinderBotFace, closedCylinderTopFace, mem_inter_iff, mem_prod, mem_univ,
    true_and, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
  rintro hp hq
  exact bot_ne_top_Icc01 (hp.symm.trans hq)

/-- The manifold boundary edges `S¹×{0} ⊔ S¹×{1}` as one subset of the cylinder. -/
abbrev closedCylinderBoundaryUnion : Set ClosedCylinder :=
  closedCylinderBotFace ∪ closedCylinderTopFace

theorem closedCylinderBoundaryUnion_nonempty : closedCylinderBoundaryUnion.Nonempty :=
  ⟨(Circle.exp (0 : ℝ), (⊥ : Icc (0 : ℝ) 1)), Or.inl ⟨mem_univ _, rfl⟩⟩

theorem mem_closedCylinderBoundaryUnion_iff (x : ClosedCylinder) :
    x ∈ closedCylinderBoundaryUnion ↔ x.2 = ⊥ ∨ x.2 = ⊤ := by
  constructor
  · intro h
    rcases h with hB | hT
    · rcases hB with ⟨_, hp⟩
      left
      simpa [mem_singleton_iff] using hp
    · rcases hT with ⟨_, hp⟩
      right
      simpa [mem_singleton_iff] using hp
  · rintro (h | h)
    · cases x
      simp_all
      exact Or.inl ⟨mem_univ _, rfl⟩
    · cases x
      simp_all
      exact Or.inr ⟨mem_univ _, rfl⟩

theorem not_isPreconnected_closedCylinderBoundaryUnion :
    ¬ IsPreconnected closedCylinderBoundaryUnion := by
  intro hp
  let U : Set ClosedCylinder :=
    (univ : Set Circle) ×ˢ (Subtype.val ⁻¹' Iio (1 / 2 : ℝ) : Set (Icc (0 : ℝ) 1))
  let V : Set ClosedCylinder :=
    (univ : Set Circle) ×ˢ (Subtype.val ⁻¹' Ioi (1 / 2 : ℝ) : Set (Icc (0 : ℝ) 1))
  have hU : IsOpen U :=
    isOpen_univ.prod (Continuous.isOpen_preimage continuous_subtype_val _ isOpen_Iio)
  have hV : IsOpen V :=
    isOpen_univ.prod (Continuous.isOpen_preimage continuous_subtype_val _ isOpen_Ioi)
  have hCov : closedCylinderBoundaryUnion ⊆ U ∪ V := by
    rintro ⟨c, p⟩ hp
    rcases hp with hpB | hpT
    · rcases hpB with ⟨_, hp⟩
      rw [mem_singleton_iff] at hp
      subst hp
      left
      refine ⟨trivial, ?_⟩
      norm_num
    · rcases hpT with ⟨_, hp⟩
      rw [mem_singleton_iff] at hp
      subst hp
      right
      refine ⟨trivial, ?_⟩
      norm_num
  have hUE : (closedCylinderBoundaryUnion ∩ U).Nonempty := by
    refine ⟨(Circle.exp (0 : ℝ), ⊥), ?_, ?_⟩
    · exact Or.inl ⟨mem_univ _, rfl⟩
    · exact ⟨mem_univ _, by norm_num⟩
  have hVE : (closedCylinderBoundaryUnion ∩ V).Nonempty := by
    refine ⟨(Circle.exp (0 : ℝ), ⊤), ?_, ?_⟩
    · exact Or.inr ⟨mem_univ _, rfl⟩
    · exact ⟨mem_univ _, by norm_num⟩
  have hUV : U ∩ V = ∅ :=
    eq_empty_of_forall_notMem (by
      rintro ⟨c, p⟩ h
      simp only [mem_inter_iff, U, V, mem_prod, mem_univ, true_and, mem_preimage, mem_Iio,
        mem_Ioi] at h
      linarith [h.left, h.right])
  have hInt : (closedCylinderBoundaryUnion ∩ (U ∩ V) : Set ClosedCylinder) = ∅ := by
    rw [hUV, inter_empty]
  exact (not_nonempty_iff_eq_empty.2 hInt) (hp U V hU hV hCov hUE hVE)

theorem not_isConnected_closedCylinderBoundaryUnion : ¬ IsConnected closedCylinderBoundaryUnion :=
  fun h => not_isPreconnected_closedCylinderBoundaryUnion h.2

end RepresentationalRegress

end
