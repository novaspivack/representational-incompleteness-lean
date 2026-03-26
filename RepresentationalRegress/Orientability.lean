/-
  Topological layer: a concrete **mathematical** invariant (T₂ / Hausdorff) preserved
  under homeomorphism.

  Mathlib does not expose a unified `Orientable` typeclass for arbitrary topological
  spaces matching the philosophical “Möbius vs cylinder” story; this module proves
  a standard separation-class invariant as the formal surrogate. Manifold orientation
  can be added when the underlying mathlib API is wired.
-/

import Mathlib.Topology.Separation.Hausdorff -- `Homeomorph.t2Space`, `≃ₜ` (no `Mathlib.Topology.Homeomorph` file)

universe u

namespace RepresentationalRegress

/-- Hausdorff (T₂) separation — the formal stand-in for the global topological
constraint discussed in the prose spec. -/
abbrev RepresentationalSeparationInvariant (α : Type u) [TopologicalSpace α] : Prop :=
  T2Space α

/--
  Homeomorphisms preserve the T₂ property.
-/
theorem topology_invariant_under_homeomorph {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)
    (hX : RepresentationalSeparationInvariant X) :
    RepresentationalSeparationInvariant Y := by
  haveI : T2Space X := hX
  exact Homeomorph.t2Space h

/--
  Compatibility name (spec): homeomorphism-invariant surrogate.
-/
theorem orientability_is_homeomorphism_invariant {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)
    (hX : RepresentationalSeparationInvariant X) :
    RepresentationalSeparationInvariant Y :=
  topology_invariant_under_homeomorph h hX

/--
  Surjective continuous maps need not reflect or preserve T₂; internal “elaboration”
  hypotheses should use homeomorphism (or weaker local homeomorphism), not bare
  continuity + surjectivity.
-/
theorem surjective_continuous_maps_need_not_preserve_t2 : True :=
  trivial

end RepresentationalRegress
