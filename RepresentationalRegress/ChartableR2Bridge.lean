/-
  **Intrinsic “ℝ² chart” predicate (open neighborhood ≃ₜ `R2`).**

  A global homeomorphism preserves existence of such charts. Together with lemmas identifying
  `mobiusStripBoundary` / `closedCylinderBoundaryUnion` with the complement of this predicate
  (still to be proved — see SPEC_002), this yields `Homeomorph.subtype` and contradicts
  `mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`.

  This file proves the **invariance** and the **conditional** Möbius vs cylinder conclusion.
-/

import Mathlib.Topology.Homeomorph.Lemmas

import RepresentationalRegress.CylinderBoundary
import RepresentationalRegress.CylinderMobius
import RepresentationalRegress.HalfPlaneVsPlane
import RepresentationalRegress.MobiusCylinderBoundaryContrast

noncomputable section

namespace RepresentationalRegress

open scoped Topology
open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- There is an **open** neighborhood of `x` homeomorphic to the plane `R2`. -/
def ChartableR2 (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Nonempty (Subtype U ≃ₜ R2)

theorem chartableR2_of_open_embeds_plane (x : X) {U : Set X} (hUo : IsOpen U) (hx : x ∈ U)
    (h : Nonempty (Subtype U ≃ₜ R2)) : ChartableR2 x :=
  ⟨U, hUo, hx, h⟩

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

end RepresentationalRegress

end
