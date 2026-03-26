/-
  **Boundary subspaces (Route B contrast):** the Möbius strip’s boundary band (one circle after
  glueing) is **connected** as a subspace; the closed cylinder’s two-face boundary union is **not**
  connected (`CylinderBoundary`). Hence these **subtype** spaces cannot be homeomorphic.

  **Not yet a full:** `¬ Nonempty (MobiusStrip ≃ₜ ClosedCylinder)` — that needs a lemma that any
  `h : MobiusStrip ≃ₜ ClosedCylinder` restricts/induces a homeomorphism between the named boundary
  subspaces (manifold or intrinsic-topology bridge; see SPEC_002).
-/

import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs

import RepresentationalRegress.CylinderBoundary
import RepresentationalRegress.CylinderMobius

noncomputable section

open scoped Topology

namespace RepresentationalRegress

open Function Set

theorem mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion :
    IsEmpty ((Subtype mobiusStripBoundary) ≃ₜ (Subtype closedCylinderBoundaryUnion)) := by
  classical
  refine ⟨fun h => ?_⟩
  have hX : ConnectedSpace (Subtype mobiusStripBoundary) :=
    isConnected_iff_connectedSpace.mp isConnected_mobiusStripBoundary
  have hY : ConnectedSpace (Subtype closedCylinderBoundaryUnion) :=
    h.surjective.connectedSpace h.continuous
  have hcon : IsConnected (closedCylinderBoundaryUnion : Set ClosedCylinder) :=
    isConnected_iff_connectedSpace.mpr hY
  exact not_isConnected_closedCylinderBoundaryUnion hcon

end RepresentationalRegress

end
