/-
  Cylinder **boundary** points are **not** `ChartableR2`: compose the manifold product chart
  (restricted to its source) with a fixed `ModelProd (E¹) (H¹) ≃ₜ H²` coordinate swap.
  This yields cylinder **C4:** `closedCylinderBoundaryUnion ↔ ¬ ChartableR2`.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Logic.Equiv.PartialEquiv

import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

import RepresentationalIncompleteness.ChartableR2Neighbor
import RepresentationalIncompleteness.ChartableR2Models
import RepresentationalIncompleteness.CylinderBoundary
import RepresentationalIncompleteness.HalfPlaneVsPlane

set_option linter.unnecessarySimpa false

noncomputable section

namespace RepresentationalIncompleteness

open scoped Manifold Topology RealInnerProductSpace
open Topology Set ModelProd Complex EuclideanHalfSpace Isometry Metric Module

attribute [local instance] finrank_real_complex_fact'

set_option backward.isDefEq.respectTransparency false in
theorem stereographicPrime_neg_self_sphere {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) : stereographic' n (-v) v = 0 := by
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact stereographic_neg_apply v

/-- Chart model for `Circle × Icc (0 : ℝ) 1`. -/
abbrev ClosedCylinderModel :=
  ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)

/-! ### Coordinate swap `E¹ × H¹ ≃ₜ H²` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma continuous_euclideanSpace_single_param (i : ι) :
    Continuous fun a : ℝ => EuclideanSpace.single i a :=
  (Isometry.uniformContinuous (Isometry.of_dist_eq (EuclideanSpace.dist_single_same i))).continuous

noncomputable def homeomorph_closedCylinder_model_to_H2 : ClosedCylinderModel ≃ₜ H2 where
  toFun p :=
    ⟨EuclideanSpace.single (0 : Fin 2) (p.2.val 0) + EuclideanSpace.single (1 : Fin 2) (p.1 0),
      by
        simp only [PiLp.add_apply, EuclideanSpace.single_apply]
        simpa using p.2.property⟩
  invFun w :=
    ⟨EuclideanSpace.single (0 : Fin 1) (w.val 1),
      ⟨EuclideanSpace.single (0 : Fin 1) (w.val 0),
        by simpa [EuclideanSpace.single_apply] using w.property⟩⟩
  left_inv := by
    rintro ⟨u, v⟩
    refine Prod.ext ?_ ?_
    · ext i
      fin_cases i
      · simp [EuclideanSpace.single_apply, PiLp.add_apply]
    · refine Subtype.ext ?_
      ext i
      rw [Subsingleton.elim i 0]
      simp [EuclideanSpace.single_apply, PiLp.add_apply]
  right_inv := by
    intro w
    refine Subtype.ext ?_
    ext i
    fin_cases i
    · simp [EuclideanSpace.single_apply, PiLp.add_apply]
    · simp [EuclideanSpace.single_apply, PiLp.add_apply]
  continuous_toFun := by
    have hcoord2 : Continuous (fun p : ClosedCylinderModel => p.2.val 0) :=
      (@PiLp.continuous_apply 2 (Fin 1) (fun _ : Fin 1 => ℝ) _ (0 : Fin 1)).comp
        (continuous_subtype_val.comp continuous_snd)
    have hf1 : Continuous fun p : ClosedCylinderModel =>
        EuclideanSpace.single (0 : Fin 2) (p.2.val 0) :=
      (continuous_euclideanSpace_single_param (ι := Fin 2) 0).comp hcoord2
    have hcoord1 : Continuous (fun p : ClosedCylinderModel => p.1 0) :=
      (@PiLp.continuous_apply 2 (Fin 1) (fun _ : Fin 1 => ℝ) _ (0 : Fin 1)).comp continuous_fst
    have hf2 : Continuous fun p : ClosedCylinderModel => EuclideanSpace.single (1 : Fin 2) (p.1 0) :=
      (continuous_euclideanSpace_single_param (ι := Fin 2) 1).comp hcoord1
    refine Continuous.subtype_mk (hf1.add hf2) (fun p => by simpa using p.2.property)
  continuous_invFun := by
    have hv1 : Continuous (fun w : H2 => w.val 1) :=
      (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (1 : Fin 2)).comp continuous_subtype_val
    have hv0 : Continuous (fun w : H2 => w.val 0) :=
      (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (0 : Fin 2)).comp continuous_subtype_val
    have g1 : Continuous fun w : H2 => EuclideanSpace.single (0 : Fin 1) (w.val 1) :=
      (continuous_euclideanSpace_single_param (ι := Fin 1) 0).comp hv1
    have g2 : Continuous fun w : H2 => EuclideanSpace.single (0 : Fin 1) (w.val 0) :=
      (continuous_euclideanSpace_single_param (ι := Fin 1) 0).comp hv0
    refine continuous_prodMk.2 ⟨g1, Continuous.subtype_mk g2 (fun w => by simpa using w.property)⟩

private lemma OpenPartialHomeomorph.prod_apply_snd {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] (e : OpenPartialHomeomorph X X')
    (e' : OpenPartialHomeomorph Y Y') (x : X) (y : Y) :
    (e.prod e' (x, y)).2 = e' y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem homeomorph_closedCylinder_model_to_H2_apply_zero :
    homeomorph_closedCylinder_model_to_H2
        ((0 : EuclideanSpace ℝ (Fin 1)), (0 : EuclideanHalfSpace 1)) = (0 : H2) := by
  refine Subtype.ext ?_
  have hvec :
      EuclideanSpace.single (0 : Fin 2) (0 : ℝ) + EuclideanSpace.single (1 : Fin 2) (0 : ℝ) =
        (0 : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i <;> simp [PiLp.add_apply, EuclideanSpace.single_apply]
  simp [homeomorph_closedCylinder_model_to_H2]
  exact hvec

/-! ### Charts hit `(0,0)` at boundary points -/

theorem Circle.chartAt_self_eq_zero (c : Circle) : chartAt (EuclideanSpace ℝ (Fin 1)) c c = 0 := by
  let hc : sphere (0 : ℂ) 1 :=
    ⟨(c : ℂ), mem_sphere_zero_iff_norm.2 (by simpa using c.norm_coe)⟩
  simpa [chartAt, ChartedSpace.chartAt, EuclideanSpace.instChartedSpaceSphere] using
    stereographicPrime_neg_self_sphere (E := ℂ) (n := 1) hc

theorem Icc.chartAt_bot :
    chartAt (EuclideanHalfSpace 1) (⊥ : Icc (0 : ℝ) 1) = IccLeftChart (0 : ℝ) (1 : ℝ) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  exact Icc_chartedSpaceChartAt_of_le_top (x := (⊥ : Icc (0 : ℝ) 1)) zero_lt_one

theorem Icc.chartAt_top :
    chartAt (EuclideanHalfSpace 1) (⊤ : Icc (0 : ℝ) 1) = IccRightChart (0 : ℝ) (1 : ℝ) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  simpa using Icc_chartedSpaceChartAt_of_top_le (x := (⊤ : Icc (0 : ℝ) 1)) le_rfl

set_option backward.isDefEq.respectTransparency false in
theorem IccLeftChart_apply_bot_zero :
    IccLeftChart (0 : ℝ) (1 : ℝ) (⊥ : Icc (0 : ℝ) 1) = (0 : EuclideanHalfSpace 1) := by
  refine Subtype.ext ?_
  simpa [OpenPartialHomeomorph.extend_coe, Function.comp_apply] using
    IccLeftChart_extend_bot (x := (0 : ℝ)) (y := (1 : ℝ))

set_option backward.isDefEq.respectTransparency false in
theorem IccRightChart_apply_top_zero :
    IccRightChart (0 : ℝ) (1 : ℝ) (⊤ : Icc (0 : ℝ) 1) = (0 : EuclideanHalfSpace 1) := by
  refine Subtype.ext ?_
  simpa [OpenPartialHomeomorph.extend_coe, Function.comp_apply] using
    IccRightChart_extend_top (x := (0 : ℝ)) (y := (1 : ℝ))

theorem chartAt_closedCylinder_model_prod (x : ClosedCylinder) :
    chartAt ClosedCylinderModel x =
      (chartAt (EuclideanSpace ℝ (Fin 1)) x.1).prod (chartAt (EuclideanHalfSpace 1) x.2) := by
  simpa [ClosedCylinder, ClosedCylinderModel] using (prodChartedSpace_chartAt (x := x))

theorem chartAt_closedCylinder_apply_bot (c : Circle) :
    chartAt ClosedCylinderModel (c, (⊥ : Icc (0 : ℝ) 1)) (c, (⊥ : Icc (0 : ℝ) 1)) =
      (0, (0 : EuclideanHalfSpace 1)) := by
  rw [chartAt_closedCylinder_model_prod]
  refine Prod.ext (Circle.chartAt_self_eq_zero c) ?_
  simpa [OpenPartialHomeomorph.prod_apply_snd, Icc.chartAt_bot] using IccLeftChart_apply_bot_zero

theorem chartAt_closedCylinder_apply_top (c : Circle) :
    chartAt ClosedCylinderModel (c, (⊤ : Icc (0 : ℝ) 1)) (c, (⊤ : Icc (0 : ℝ) 1)) =
      (0, (0 : EuclideanHalfSpace 1)) := by
  rw [chartAt_closedCylinder_model_prod]
  refine Prod.ext (Circle.chartAt_self_eq_zero c) ?_
  simpa [OpenPartialHomeomorph.prod_apply_snd, Icc.chartAt_top] using IccRightChart_apply_top_zero

/-! ### Half-space chart on `chartAt.source` -/

noncomputable def openEmbedding_H2_chartAt_center (x : ClosedCylinder) :
    Subtype (chartAt ClosedCylinderModel x).source → H2 :=
  homeomorph_closedCylinder_model_to_H2 ∘ (chartAt ClosedCylinderModel x).source.restrict (chartAt ClosedCylinderModel x)

theorem isOpenEmbedding_openEmbedding_H2_chartAt_center (x : ClosedCylinder) :
    IsOpenEmbedding (openEmbedding_H2_chartAt_center x) :=
  homeomorph_closedCylinder_model_to_H2.isOpenEmbedding.comp
    (chartAt ClosedCylinderModel x).isOpenEmbedding_restrict

theorem openEmbedding_H2_chartAt_center_apply (x : ClosedCylinder)
    (hx : x ∈ (chartAt ClosedCylinderModel x).source) :
    openEmbedding_H2_chartAt_center x ⟨x, hx⟩ =
      homeomorph_closedCylinder_model_to_H2 (chartAt ClosedCylinderModel x x) :=
  rfl

theorem not_chartableR2_of_mem_chart_source_bot (c : Circle)
    (hx : (c, (⊥ : Icc (0 : ℝ) 1)) ∈ (chartAt ClosedCylinderModel (c, (⊥ : Icc (0 : ℝ) 1))).source) :
    ¬ ChartableR2 (c, (⊥ : Icc (0 : ℝ) 1)) :=
  not_chartableR2_of_isOpenEmbedding_H2
    (U := (chartAt ClosedCylinderModel (c, (⊥ : Icc (0 : ℝ) 1))).source)
    (chartAt ClosedCylinderModel (c, (⊥ : Icc (0 : ℝ) 1))).open_source hx
      (openEmbedding_H2_chartAt_center (c, (⊥ : Icc (0 : ℝ) 1)))
    (isOpenEmbedding_openEmbedding_H2_chartAt_center (c, (⊥ : Icc (0 : ℝ) 1)))
    (by
      rw [openEmbedding_H2_chartAt_center_apply, chartAt_closedCylinder_apply_bot]
      exact homeomorph_closedCylinder_model_to_H2_apply_zero)

theorem not_chartableR2_of_mem_chart_source_top (c : Circle)
    (hx : (c, (⊤ : Icc (0 : ℝ) 1)) ∈ (chartAt ClosedCylinderModel (c, (⊤ : Icc (0 : ℝ) 1))).source) :
    ¬ ChartableR2 (c, (⊤ : Icc (0 : ℝ) 1)) :=
  not_chartableR2_of_isOpenEmbedding_H2
    (U := (chartAt ClosedCylinderModel (c, (⊤ : Icc (0 : ℝ) 1))).source)
    (chartAt ClosedCylinderModel (c, (⊤ : Icc (0 : ℝ) 1))).open_source hx
      (openEmbedding_H2_chartAt_center (c, (⊤ : Icc (0 : ℝ) 1)))
    (isOpenEmbedding_openEmbedding_H2_chartAt_center (c, (⊤ : Icc (0 : ℝ) 1)))
    (by
      rw [openEmbedding_H2_chartAt_center_apply, chartAt_closedCylinder_apply_top]
      exact homeomorph_closedCylinder_model_to_H2_apply_zero)

theorem mem_chart_source_closedCylinder_bot (c : Circle) :
    (c, (⊥ : Icc (0 : ℝ) 1)) ∈ (chartAt ClosedCylinderModel (c, (⊥ : Icc (0 : ℝ) 1))).source := by
  rw [chartAt_closedCylinder_model_prod, OpenPartialHomeomorph.prod_source]
  exact ⟨mem_chart_source (EuclideanSpace ℝ (Fin 1)) c,
    mem_chart_source (EuclideanHalfSpace 1) (⊥ : Icc (0 : ℝ) 1)⟩

theorem mem_chart_source_closedCylinder_top (c : Circle) :
    (c, (⊤ : Icc (0 : ℝ) 1)) ∈ (chartAt ClosedCylinderModel (c, (⊤ : Icc (0 : ℝ) 1))).source := by
  rw [chartAt_closedCylinder_model_prod, OpenPartialHomeomorph.prod_source]
  exact ⟨mem_chart_source (EuclideanSpace ℝ (Fin 1)) c,
    mem_chart_source (EuclideanHalfSpace 1) (⊤ : Icc (0 : ℝ) 1)⟩

theorem not_chartableR2_of_mem_closedCylinderBotFace {p : ClosedCylinder}
    (hp : p ∈ closedCylinderBotFace) : ¬ ChartableR2 p := by
  rcases p with ⟨c, t⟩
  rcases hp with ⟨_, ht⟩
  rw [mem_singleton_iff] at ht
  subst ht
  exact not_chartableR2_of_mem_chart_source_bot c (mem_chart_source_closedCylinder_bot c)

theorem not_chartableR2_of_mem_closedCylinderTopFace {p : ClosedCylinder}
    (hp : p ∈ closedCylinderTopFace) : ¬ ChartableR2 p := by
  rcases p with ⟨c, t⟩
  rcases hp with ⟨_, ht⟩
  rw [mem_singleton_iff] at ht
  subst ht
  exact not_chartableR2_of_mem_chart_source_top c (mem_chart_source_closedCylinder_top c)

/-- **Cylinder C4:** boundary union ↔ non–`ChartableR2` -/
theorem closedCylinder_boundaryUnion_iff_not_chartableR2 (x : ClosedCylinder) :
    x ∈ closedCylinderBoundaryUnion ↔ ¬ ChartableR2 x := by
  constructor
  · intro hb
    rw [mem_closedCylinderBoundaryUnion_iff] at hb
    rcases x with ⟨c, t⟩
    rcases hb with h | h
    · subst h
      exact not_chartableR2_of_mem_chart_source_bot c (mem_chart_source_closedCylinder_bot c)
    · subst h
      exact not_chartableR2_of_mem_chart_source_top c (mem_chart_source_closedCylinder_top c)
  · intro hnC
    by_contra hb
    rw [closedCylinder_boundaryUnion_iff_Ioo, not_not] at hb
    exact hnC (chartableR2_closedCylinder_of_Ioo hb)

end RepresentationalIncompleteness

end
