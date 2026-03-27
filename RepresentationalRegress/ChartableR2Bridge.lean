/-
  **`ChartableR2` invariance under homeomorphism and the generic boundary-contrast obstruction.**

  **Generic theorem (`not_homeomorphic_of_chartableR2_boundary_contrast`):** if two topological spaces
  each have a "boundary" predicate that is equivalent to `¬ ChartableR2`, and the resulting boundary
  **subspaces** are not homeomorphic, then the ambient spaces are not homeomorphic. This is the
  universal engine behind **M-FINAL** and any future pair separated by `ChartableR2`-detected boundary
  topology. See `MobiusSeamChartableR2` for the unconditional instantiation.

  Concrete Möbius / cylinder packaging (`mobiusStrip_not_homeomorphic_closedCylinder_of_*`) delegates
  to the generic theorem with `mobiusStripBoundary` / `closedCylinderBoundaryUnion` and
  `mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`.
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

-- ═══════════════════════════════════════════════════════════════════
-- Generic obstruction: any two spaces whose ChartableR2-detected
-- boundaries are topologically incompatible cannot be homeomorphic.
-- ═══════════════════════════════════════════════════════════════════

/-- A homeomorphism maps points in a `¬ ChartableR2`-characterized "boundary" of `X` to those of `Y`. -/
theorem homeomorph_boundary_iff_of_chartableR2 {bX : Set X} {bY : Set Y}
    (e : X ≃ₜ Y)
    (hX : ∀ x, x ∈ bX ↔ ¬ ChartableR2 x)
    (hY : ∀ y, y ∈ bY ↔ ¬ ChartableR2 y)
    (x : X) : x ∈ bX ↔ e x ∈ bY := by
  rw [hX, hY, Homeomorph.chartableR2_iff e x]

/-- **Generic boundary-contrast obstruction.** If `X` and `Y` each have a predicate characterizing
  "boundary = complement of `ChartableR2`", and the resulting boundary subspaces are **not**
  homeomorphic, then the ambient spaces are not homeomorphic.

  This is the universal engine: to prove `IsEmpty (X ≃ₜ Y)`, supply:
  * `bX`, `bY` — boundary predicates;
  * `hX`, `hY` — each is `↔ ¬ ChartableR2`;
  * `hincompat` — `IsEmpty (Subtype bX ≃ₜ Subtype bY)`.

  **M-FINAL** and any future surface pair separated by boundary topology are one-line corollaries. -/
theorem not_homeomorphic_of_chartableR2_boundary_contrast
    {bX : Set X} {bY : Set Y}
    (hX : ∀ x, x ∈ bX ↔ ¬ ChartableR2 x)
    (hY : ∀ y, y ∈ bY ↔ ¬ ChartableR2 y)
    (hincompat : IsEmpty (Subtype bX ≃ₜ Subtype bY)) :
    IsEmpty (X ≃ₜ Y) :=
  ⟨fun e => hincompat.false (e.subtype (homeomorph_boundary_iff_of_chartableR2 e hX hY))⟩

theorem ChartableR2BoundaryModel.not_homeomorphic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (MX : ChartableR2BoundaryModel X) (MY : ChartableR2BoundaryModel Y)
    (h : IsEmpty (Subtype MX.boundary ≃ₜ Subtype MY.boundary)) :
    IsEmpty (X ≃ₜ Y) :=
  not_homeomorphic_of_chartableR2_boundary_contrast MX.boundary_iff_not_chartableR2
    MY.boundary_iff_not_chartableR2 h

-- ═══════════════════════════════════════════════════════════════════
-- Concrete Möbius / cylinder packaging (corollaries of the generic theorem)
-- ═══════════════════════════════════════════════════════════════════

/-- Boundary points in the Möbius model ↔ non-chartable points, once that lemma is available. -/
theorem mobiusStrip_homeomorph_boundary_iff_closedCylinderBoundaryUnion
    (h : MobiusStrip ≃ₜ ClosedCylinder) (x : MobiusStrip)
    (hM : ∀ x : MobiusStrip, x ∈ mobiusStripBoundary ↔ ¬ ChartableR2 x)
    (hC : ∀ x : ClosedCylinder, x ∈ closedCylinderBoundaryUnion ↔ ¬ ChartableR2 x) :
    x ∈ mobiusStripBoundary ↔ h x ∈ closedCylinderBoundaryUnion :=
  homeomorph_boundary_iff_of_chartableR2 h hM hC x

/-- **Conditional M-FINAL** from `ChartableR2` boundary characterizations on both spaces.
  Corollary of `not_homeomorphic_of_chartableR2_boundary_contrast`. -/
theorem mobiusStrip_not_homeomorphic_closedCylinder_of_chartable_boundary
    (hM : ∀ x : MobiusStrip, x ∈ mobiusStripBoundary ↔ ¬ ChartableR2 x)
    (hC : ∀ x : ClosedCylinder, x ∈ closedCylinderBoundaryUnion ↔ ¬ ChartableR2 x) :
    IsEmpty (MobiusStrip ≃ₜ ClosedCylinder) :=
  not_homeomorphic_of_chartableR2_boundary_contrast hM hC
    mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion

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
