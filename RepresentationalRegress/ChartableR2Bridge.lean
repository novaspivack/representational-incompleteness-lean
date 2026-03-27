/-
  **Intrinsic “ℝ² chart” predicate (open neighborhood ≃ₜ `R2`).**

  A global homeomorphism preserves existence of such charts. Together with lemmas identifying
  `mobiusStripBoundary` / `closedCylinderBoundaryUnion` with the complement of this predicate
  (cylinder side is proved; Möbius **`mobiusStripBoundary → ¬ ChartableR2`** in `MobiusChartableBoundary`;
  full **`↔`** reduces via   **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`** to
  **`∀ p, 0 < p.2 ∧ p.2 < 1 → ChartableR2 ⟦p⟧`**, now discharged in **`MobiusSeamChartableR2`** by
  **`chartableR2_mobiusQuotientMk_of_interior_height`**. The unconditional theorem
  **`mobiusStrip_not_homeomorphic_closedCylinder`** is also in **`MobiusSeamChartableR2`**.

  This file proves **`ChartableR2`** invariance and the **conditional** packaging
  **`mobiusStrip_not_homeomorphic_closedCylinder_of_*`**; the fully instantiated M-FINAL lives in **`MobiusSeamChartableR2`**.
-/

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic

import RepresentationalRegress.ChartableR2Neighbor
import RepresentationalRegress.CylinderBoundary
import RepresentationalRegress.CylinderChartableBoundary
import RepresentationalRegress.CylinderMobius
import RepresentationalRegress.MobiusChartableBoundary
import RepresentationalRegress.MobiusCylinderBoundaryContrast

noncomputable section

namespace RepresentationalRegress

open scoped Topology
open Topology
open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homeomorphisms preserve `ChartableR2`. -/
theorem Homeomorph.chartableR2_iff (e : X ≃ₜ Y) (x : X) :
    ChartableR2 x ↔ ChartableR2 (e x) := by
  constructor
  · rintro ⟨U, hUo, hxU, ⟨φ⟩⟩
    set V : Set Y := e '' U
    refine ⟨V, ?_, ?_, ?_⟩
    · exact e.isOpenMap U hUo
    · exact mem_image_of_mem e hxU
    · let ψ : Subtype (e '' U) ≃ₜ Subtype U := (Homeomorph.image e U).symm
      exact ⟨ψ.trans φ⟩
  · rintro ⟨U, hUo, hxU, ⟨φ⟩⟩
    set W : Set X := e ⁻¹' U
    refine ⟨W, ?_, ?_, ?_⟩
    · exact continuous_def.mp e.continuous U hUo
    · simpa [W, mem_preimage] using hxU
    · have hUV : e.symm '' U = e ⁻¹' U := congrFun e.image_symm U
      let ψ : Subtype (e ⁻¹' U) ≃ₜ Subtype U :=
        (Homeomorph.setCongr hUV.symm).trans (Homeomorph.image e.symm U).symm
      exact ⟨ψ.trans φ⟩

/-- Boundary points in the Möbius model ↔ non-chartable points, once that lemma is available. -/
theorem mobiusStrip_homeomorph_boundary_iff_closedCylinderBoundaryUnion
    (h : MobiusStrip ≃ₜ ClosedCylinder) (x : MobiusStrip)
    (hM : ∀ x : MobiusStrip, x ∈ mobiusStripBoundary ↔ ¬ ChartableR2 x)
    (hC : ∀ x : ClosedCylinder, x ∈ closedCylinderBoundaryUnion ↔ ¬ ChartableR2 x) :
    x ∈ mobiusStripBoundary ↔ h x ∈ closedCylinderBoundaryUnion := by
  rw [hM, hC, Homeomorph.chartableR2_iff h x]

/-- **Conditional M-FINAL** from `ChartableR2` boundary characterizations on both spaces. -/
theorem mobiusStrip_not_homeomorphic_closedCylinder_of_chartable_boundary
    (hM : ∀ x : MobiusStrip, x ∈ mobiusStripBoundary ↔ ¬ ChartableR2 x)
    (hC : ∀ x : ClosedCylinder, x ∈ closedCylinderBoundaryUnion ↔ ¬ ChartableR2 x) :
    IsEmpty (MobiusStrip ≃ₜ ClosedCylinder) := by
  classical
  refine ⟨fun h => ?_⟩
  have hbij := fun x => mobiusStrip_homeomorph_boundary_iff_closedCylinderBoundaryUnion h x hM hC
  have hsub : (Subtype mobiusStripBoundary) ≃ₜ (Subtype closedCylinderBoundaryUnion) :=
    h.subtype hbij
  exact mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion.false hsub

/-- Same as `mobiusStrip_not_homeomorphic_closedCylinder_of_chartable_boundary` with the cylinder side
discharged by `closedCylinder_boundaryUnion_iff_not_chartableR2`. -/
theorem mobiusStrip_not_homeomorphic_closedCylinder_of_mobius_boundary_chartable
    (hM : ∀ x : MobiusStrip, x ∈ mobiusStripBoundary ↔ ¬ ChartableR2 x) :
    IsEmpty (MobiusStrip ≃ₜ ClosedCylinder) :=
  mobiusStrip_not_homeomorphic_closedCylinder_of_chartable_boundary hM
    closedCylinder_boundaryUnion_iff_not_chartableR2

/-- **M-FINAL from height–interior `ChartableR2`** once **`∀ p, 0 < p.2 ∧ p.2 < 1 → ChartableR2 ⟦p⟧`**
  is proved (see **`chartableR2_mobiusQuotientMk_of_interior_height`** in **`MobiusSeamChartableR2`**). -/
theorem mobiusStrip_not_homeomorphic_closedCylinder_of_forall_off_edge_chartable
    (h :
      ∀ p : MobiusFundamentalDomain, 0 < p.2.val ∧ p.2.val < 1 →
        ChartableR2 (Quotient.mk mobiusSetoid p)) :
    IsEmpty (MobiusStrip ≃ₜ ClosedCylinder) :=
  mobiusStrip_not_homeomorphic_closedCylinder_of_mobius_boundary_chartable
    (mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable h)

end RepresentationalRegress

end
