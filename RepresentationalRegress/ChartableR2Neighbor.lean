/-
  **Intrinsic “ℝ² chart” predicate** and the **generic half-space obstruction** at a point.

  Kept separate from `ChartableR2Bridge` so files such as `CylinderChartableBoundary` can use
  `not_chartableR2_of_isOpenEmbedding_H2` without importing the Möbius/cylinder contrast lemmas
  (avoids an import cycle).
-/

import Mathlib.Topology.Homeomorph.Lemmas

import RepresentationalRegress.HalfPlaneVsPlane
import RepresentationalRegress.HalfSpaceNeighborVsPlane

noncomputable section

namespace RepresentationalRegress

open scoped Topology
open Topology Set Filter

variable {X : Type*} [TopologicalSpace X]

/-- There is an **open** neighborhood of `x` homeomorphic to the plane `R2`. -/
def ChartableR2 (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Nonempty (Subtype U ≃ₜ R2)

theorem chartableR2_of_open_embeds_plane (x : X) {U : Set X} (hUo : IsOpen U) (hx : x ∈ U)
    (h : Nonempty (Subtype U ≃ₜ R2)) : ChartableR2 x :=
  ⟨U, hUo, hx, h⟩

/-- Points with an `R²` chart form an **open** set: every such point has an open chart neighborhood,
  and every point of that neighborhood shares the same chart. -/
theorem isOpen_setOf_chartableR2 : IsOpen {x : X | ChartableR2 x} := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨U, hUo, hxU, ⟨φ⟩⟩
  refine mem_of_superset (IsOpen.mem_nhds hUo hxU) ?_
  intro y hy
  exact chartableR2_of_open_embeds_plane y hUo hy ⟨φ⟩

theorem isClosed_setOf_not_chartableR2 : IsClosed {x : X | ¬ ChartableR2 x} := by
  simpa [compl_setOf] using (isOpen_setOf_chartableR2 (X := X)).isClosed_compl

/-- A **sequential** limit of non–`ChartableR2` points is non–`ChartableR2`; equivalently
  `{x | ChartableR2 x}` is sequentially open (since it is open). -/
theorem not_chartableR2_of_tendsto_seq_atTop {f : ℕ → X} {x : X} (hf : Tendsto f atTop (𝓝 x))
    (h : ∀ n, ¬ ChartableR2 (f n)) : ¬ ChartableR2 x := by
  classical
  intro hx
  have hopen : IsOpen {y : X | ChartableR2 y} := isOpen_setOf_chartableR2
  have hun : {y : X | ChartableR2 y} ∈ 𝓝 x := hopen.mem_nhds hx
  rcases (hf.eventually hun).exists_forall_of_atTop with ⟨N, hN⟩
  exact h N (hN N le_rfl)

/-- Local half-space open embedding sending `x` to `0` ⇒ no intrinsic `R²` chart at `x`. -/
theorem not_chartableR2_of_isOpenEmbedding_H2 {X : Type*} [TopologicalSpace X] {x : X} {U : Set X}
    (hU : IsOpen U) (hxU : x ∈ U) (f : Subtype U → H2) (hf : IsOpenEmbedding f)
    (hfx : f ⟨x, hxU⟩ = 0) : ¬ ChartableR2 x := by
  classical
  rintro ⟨W, hWo, hxW, ⟨ξ⟩⟩
  let V : Set H2 := Set.range f
  have hVo : IsOpen (V : Set H2) := hf.isOpen_range
  have h0V : (0 : H2) ∈ V := ⟨⟨x, hxU⟩, hfx⟩
  let φ := hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (by rfl : Set.range f = V))
  have hφx : (φ ⟨x, hxU⟩).val = (0 : H2) := hfx
  exact false_of_open_halfspace_plane_charts_intersect (U := U) (W := W) hU hWo hxU hxW hVo h0V φ
      hφx ξ

/-! ## Bundled boundary sensors (`ChartableR2Bridge`, applications) -/

/-- A **ChartableR2 boundary model**: the chosen subset is exactly the complement of `ChartableR2`.

  Use with `RepresentationalRegress.ChartableR2BoundaryModel.not_homeomorphic` and concrete
  instances in `ChartableR2ConcreteBoundaryModels`. -/
structure ChartableR2BoundaryModel (X : Type*) [TopologicalSpace X] where
  boundary : Set X
  boundary_iff_not_chartableR2 : ∀ x, x ∈ boundary ↔ ¬ ChartableR2 x

end RepresentationalRegress

end
