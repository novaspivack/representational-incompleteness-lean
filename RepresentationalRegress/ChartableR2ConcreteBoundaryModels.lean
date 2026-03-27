/-
  **Concrete `ChartableR2BoundaryModel` instances** (Möbius strip, closed cylinder) and
  **conditional schematic lemmas** for future models (e.g. von Neumann / measurement chains).

  No axioms: QM-style applications assume explicit topological data and discharge the same
  hypotheses this library proved for `MobiusStrip` / `ClosedCylinder`.
-/

import Mathlib.Topology.Homeomorph.Defs

import RepresentationalRegress.ChartableR2Neighbor
import RepresentationalRegress.ChartableR2Bridge
import RepresentationalRegress.CylinderChartableBoundary
import RepresentationalRegress.CylinderMobius
import RepresentationalRegress.MobiusCylinderBoundaryContrast
import RepresentationalRegress.MobiusSeamChartableR2

noncomputable section

namespace RepresentationalRegress

open scoped Topology

/-- Möbius strip with **C4** boundary sensor from interior-height charts (`SPEC_003`). -/
noncomputable def mobiusStripChartableR2BoundaryModel : ChartableR2BoundaryModel MobiusStrip where
  boundary := mobiusStripBoundary
  boundary_iff_not_chartableR2 :=
    mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable fun _ hp =>
      chartableR2_mobiusQuotientMk_of_interior_height hp

/-- Closed cylinder with proved **C4** biconditional (`CylinderChartableBoundary`). -/
noncomputable def closedCylinderChartableR2BoundaryModel : ChartableR2BoundaryModel ClosedCylinder where
  boundary := closedCylinderBoundaryUnion
  boundary_iff_not_chartableR2 := closedCylinder_boundaryUnion_iff_not_chartableR2

theorem mobiusStrip_closedCylinder_boundary_models_not_homeomorphic :
    IsEmpty (MobiusStrip ≃ₜ ClosedCylinder) :=
  ChartableR2BoundaryModel.not_homeomorphic mobiusStripChartableR2BoundaryModel
    closedCylinderChartableR2BoundaryModel
    mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion

/-!
## Conditional “measurement chain” / QM schematic

Suppose a future formalization provides a topological space `ObserverChain` (apparatus +
environment readouts), a boundary subset `obsBoundary` that satisfies the same **ChartableR2**
biconditional as the models here, and a proved **boundary subspace incompatibility** with the
Möbius boundary band. Then `ObserverChain` is not homeomorphic to `MobiusStrip`. No commitment
to Hilbert space, operators, or interpretational branches — only the obstruction template.
-/

theorem conditional_observer_chain_not_homeomorphic_mobiusStrip
    {ObserverChain : Type*} [TopologicalSpace ObserverChain]
    (obsBoundary : Set ObserverChain)
    (hObs : ∀ x : ObserverChain, x ∈ obsBoundary ↔ ¬ ChartableR2 x)
    (hInc : IsEmpty (Subtype obsBoundary ≃ₜ Subtype mobiusStripBoundary)) :
    IsEmpty (ObserverChain ≃ₜ MobiusStrip) :=
  ChartableR2BoundaryModel.not_homeomorphic ⟨obsBoundary, hObs⟩ mobiusStripChartableR2BoundaryModel
    hInc

theorem conditional_observer_chain_not_homeomorphic_mobiusStrip_of_model_boundary
    {ObserverChain : Type*} [TopologicalSpace ObserverChain]
    (MObs : ChartableR2BoundaryModel ObserverChain)
    (hInc : IsEmpty (Subtype MObs.boundary ≃ₜ Subtype mobiusStripBoundary)) :
    IsEmpty (ObserverChain ≃ₜ MobiusStrip) :=
  ChartableR2BoundaryModel.not_homeomorphic MObs mobiusStripChartableR2BoundaryModel hInc

/--
  **Bundled hypotheses** for a schematic “observer / measurement / readout chain” model
  (paper gloss: von Neumann chain). **No axioms** — when a future formalization proves each
  field, `not_homeomorphic_mobiusStrip` applies `conditional_observer_chain_not_homeomorphic_mobiusStrip`.
-/
structure QuantumObserverChainHypothesis (Obs : Type*) [TopologicalSpace Obs] where
  obsBoundary : Set Obs
  boundary_iff_not_chartableR2 : ∀ x : Obs, x ∈ obsBoundary ↔ ¬ ChartableR2 x
  boundary_not_homeomorphic_mobiusBand :
    IsEmpty (Subtype obsBoundary ≃ₜ Subtype mobiusStripBoundary)

theorem QuantumObserverChainHypothesis.not_homeomorphic_mobiusStrip
    {Obs : Type*} [TopologicalSpace Obs] (H : QuantumObserverChainHypothesis Obs) :
    IsEmpty (Obs ≃ₜ MobiusStrip) :=
  conditional_observer_chain_not_homeomorphic_mobiusStrip H.obsBoundary
    H.boundary_iff_not_chartableR2 H.boundary_not_homeomorphic_mobiusBand

def QuantumObserverChainHypothesis.chartableR2Model {Obs : Type*} [TopologicalSpace Obs]
    (H : QuantumObserverChainHypothesis Obs) : ChartableR2BoundaryModel Obs :=
  ⟨H.obsBoundary, H.boundary_iff_not_chartableR2⟩

end RepresentationalRegress

end
