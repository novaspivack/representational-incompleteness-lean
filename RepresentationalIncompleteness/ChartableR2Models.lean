/-
  **Intrinsic `ChartableR2` on the cylinder model (C1/C3 spine).**

  Interior points of the product manifold use a small ball in an `extChartAt` target; composing
  with translations, `unitBallBall`, and `Homeomorph.unitBall` yields `Subtype U ≃ₜ R2`.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

import RepresentationalIncompleteness.ChartableR2Neighbor
import RepresentationalIncompleteness.CylinderBoundary
import RepresentationalIncompleteness.HalfPlaneVsPlane

noncomputable section

namespace RepresentationalIncompleteness

open scoped Manifold Topology
open Set Metric Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Two-dimensional model vector spaces are homeomorphic to `R2`. -/
noncomputable def homeomorph_euclideanSpace_finTwo (hE : finrank ℝ E = 2) : E ≃ₜ R2 :=
  (ContinuousLinearEquiv.ofFinrankEq (by
      rw [hE, finrank_euclideanSpace, Fintype.card_fin])).toHomeomorph

lemma finrank_modelProd_circle_Icc :
    finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2 := by
  classical
  simp [Module.finrank_prod, finrank_euclideanSpace]

/-- `extChartAt`, restricted over a ball contained in the extended target. -/
noncomputable def homeomorph_subtype_extChartAt_ball (x : M) {ε : ℝ} (_hε : 0 < ε)
    (hball : Metric.ball (extChartAt I x x) ε ⊆ (extChartAt I x).target) :
    let B : Set E := Metric.ball (extChartAt I x x) ε
    let U : Set M := (chartAt H x).source ∩ extChartAt I x ⁻¹' B
    Subtype U ≃ₜ Subtype B :=
  let e := extChartAt I x
  let z := e x
  let B := Metric.ball z ε
  let U := (chartAt H x).source ∩ e ⁻¹' B
  have hBU : ∀ u : Subtype U, e u.val ∈ B := fun u => u.2.2
  have hUs : ∀ u : Subtype U, u.val ∈ e.source := fun u => by
    rw [extChartAt_source I]
    exact u.2.1
  have hB_tgt : ∀ b : Subtype B, b.val ∈ e.target := fun b => hball b.property
  have hBmem : ∀ b : Subtype B, e.symm b.val ∈ U := fun b => by
    refine And.intro ?_ ?_
    · rw [← extChartAt_source I]
      exact e.map_target (hB_tgt b)
    · rw [mem_preimage, e.right_inv (hB_tgt b)]
      exact b.property
  have hmonoU : U ⊆ e.source := by
    rw [extChartAt_source I]
    exact inter_subset_left
  have hcf : Continuous (U.restrict e) :=
    continuousOn_iff_continuous_restrict.1
      ((continuousOn_extChartAt x).mono hmonoU)
  have hci : Continuous (B.restrict e.symm) :=
    continuousOn_iff_continuous_restrict.1
      ((continuousOn_extChartAt_symm x).mono hball)
  { toEquiv :=
      Equiv.mk
        (fun u => ⟨e u.val, hBU u⟩)
        (fun b => ⟨e.symm b.val, hBmem b⟩)
        (fun u => Subtype.ext (e.left_inv (hUs u)))
        (fun b => Subtype.ext (e.right_inv (hB_tgt b)))
    continuous_toFun := Continuous.subtype_mk hcf hBU
    continuous_invFun := Continuous.subtype_mk hci hBmem }

/-- Interior point of a `2`-dimensional manifold model ⇒ `ChartableR2`. -/
theorem chartableR2_of_isInteriorPoint_finTwo {x : M} (hx : I.IsInteriorPoint x)
    (hE : finrank ℝ E = 2) : ChartableR2 x := by
  classical
  let e := extChartAt I x
  let z := e x
  have hz : z ∈ interior e.target :=
    (ModelWithCorners.isInteriorPoint_iff (I := I) (M := M)).1 hx
  have ht : e.target ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  rcases Metric.mem_nhds_iff.mp ht with ⟨ε, hε, hball⟩
  let B : Set E := Metric.ball z ε
  let U : Set M := (chartAt H x).source ∩ e ⁻¹' B
  have hUo : IsOpen U := isOpen_extChartAt_preimage x Metric.isOpen_ball
  have hxU : x ∈ U :=
    ⟨mem_chart_source H x, by simp [B, z, mem_ball, hε]⟩
  let φ₀ : Subtype U ≃ₜ Subtype B :=
    homeomorph_subtype_extChartAt_ball (I := I) (M := M) (H := H) x hε hball
  have him :
      (IsometryEquiv.vaddConst (P := E) z).symm.toHomeomorph '' B = ball (0 : E) ε := by
    simpa [B, z] using
      (IsometryEquiv.image_ball ((IsometryEquiv.vaddConst (P := E) z).symm) z ε : _)
  let φ₁ : Subtype B ≃ₜ Subtype (ball (0 : E) ε) :=
    (Homeomorph.image ((IsometryEquiv.vaddConst (P := E) z).symm.toHomeomorph) B).trans
      (Homeomorph.setCongr him)
  let φ₂ : Subtype (ball (0 : E) ε) ≃ₜ Subtype (ball (0 : E) 1) :=
    (OpenPartialHomeomorph.unitBallBall (0 : E) ε hε).toHomeomorphSourceTarget.symm
  let φ₃ : Subtype (ball (0 : E) 1) ≃ₜ E := (Homeomorph.unitBall (E := E)).symm
  let φ₄ : E ≃ₜ R2 := homeomorph_euclideanSpace_finTwo hE
  let ψ : Subtype U ≃ₜ R2 := φ₀.trans (φ₁.trans (φ₂.trans (φ₃.trans φ₄)))
  exact chartableR2_of_open_embeds_plane x hUo hxU ⟨ψ⟩

/-! ### Closed cylinder -/

theorem isInteriorPoint_closedCylinder_iff {p : ClosedCylinder} :
    letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
    ((𝓡 1).prod (𝓡∂ 1)).IsInteriorPoint p ↔ 0 < p.2.val ∧ p.2.val < 1 := by
  classical
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  constructor
  · intro hp
    have hin :
        p ∈ ((𝓡 1).prod (𝓡∂ 1)).interior (Circle × Icc (0 : ℝ) 1) := by
      change p ∈ ((𝓡 1).prod (𝓡∂ 1)).interior ClosedCylinder
      exact mem_setOf.mpr hp
    simp_rw [ModelWithCorners.interior_prod (I := 𝓡 1) (J := 𝓡∂ 1) (M := Circle) (N := Icc (0 : ℝ) 1),
      ModelWithCorners.interior_eq_univ, univ_prod, mem_preimage, ModelWithCorners.interior,
      mem_setOf_eq] at hin
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc p.2.property with hp | hp | hmid
    · have hpBot : p.2 = ⊥ := SetCoe.ext hp
      rw [hpBot] at hin
      exact False.elim <|
        (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := 𝓡∂ 1) (M := Icc (0 : ℝ) 1) (⊥ : Icc (0 : ℝ) 1)).1
          hin (Icc_isBoundaryPoint_bot (x := (0 : ℝ)) (y := (1 : ℝ)))
    · have hpTop : p.2 = ⊤ := SetCoe.ext hp
      rw [hpTop] at hin
      exact False.elim <|
        (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := 𝓡∂ 1) (M := Icc (0 : ℝ) 1) (⊤ : Icc (0 : ℝ) 1)).1
          hin (Icc_isBoundaryPoint_top (x := (0 : ℝ)) (y := (1 : ℝ)))
    · exact ⟨hmid.1, hmid.2⟩
  · intro hp
    have hp2 : (𝓡∂ 1).IsInteriorPoint p.2 := Icc_isInteriorPoint_interior hp
    have hmem :
        p ∈ ((𝓡 1).prod (𝓡∂ 1)).interior (Circle × Icc (0 : ℝ) 1) := by
      rw [ModelWithCorners.interior_prod (I := 𝓡 1) (J := 𝓡∂ 1) (M := Circle) (N := Icc (0 : ℝ) 1),
        ModelWithCorners.interior_eq_univ, univ_prod, mem_preimage, ModelWithCorners.interior,
        mem_setOf_eq]
      exact hp2
    simpa [ClosedCylinder, ModelWithCorners.interior, mem_setOf_eq] using hmem

theorem chartableR2_closedCylinder_of_Ioo {x : ClosedCylinder} (h : 0 < x.2.val ∧ x.2.val < 1) :
    ChartableR2 x := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hx : ((𝓡 1).prod (𝓡∂ 1)).IsInteriorPoint x :=
    (isInteriorPoint_closedCylinder_iff).2 h
  exact chartableR2_of_isInteriorPoint_finTwo (M := ClosedCylinder) hx finrank_modelProd_circle_Icc

theorem closedCylinder_boundaryUnion_iff_Ioo (x : ClosedCylinder) :
    x ∈ closedCylinderBoundaryUnion ↔ ¬ (0 < x.2.val ∧ x.2.val < 1) := by
  rw [mem_closedCylinderBoundaryUnion_iff]
  constructor
  · rintro (h2 | h2)
    · rintro ⟨h0, _⟩
      rw [h2] at h0
      simp at h0
    · rintro ⟨_, h1⟩
      rw [h2] at h1
      simp at h1
  · intro hn
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc x.2.property with hp | hp | hio
    · exact Or.inl (SetCoe.ext hp)
    · exact Or.inr (SetCoe.ext hp)
    · exact False.elim (hn ⟨hio.1, hio.2⟩)

-- Möbius: planar open cell in `MobiusChartableBoundary` (`chartableR2_mobiusQuotientMk_of_planeOpenBox` / `Ioo_square`).
-- Seam + boundary C4 and unconditional M-FINAL: still to wire (see `REMAINING_QUEUE`).

end RepresentationalIncompleteness

end
