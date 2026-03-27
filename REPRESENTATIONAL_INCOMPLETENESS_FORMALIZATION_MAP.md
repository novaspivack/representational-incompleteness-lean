# Representational Incompleteness — formalization map

**Purpose:** Module roles; pair with `MANIFEST.md` and `THEOREM_INVENTORY.md`.  
**Program spec:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`

---

## Module tree

| Path | Role |
|------|------|
| `RepresentationalIncompleteness/Basic.lean` | `RepresentationalSystem` (`represent`, bundled `iter_injective`), iterates `represent^n` as morphisms, `Over A` packaging (`metaOver`), `OntologicalSlot` |
| `RepresentationalIncompleteness/Regress.lean` | Injectivity of iterates + slice objects; unbounded levels (`regress_iterates_unbounded`) |
| `RepresentationalIncompleteness/FixedPoints.lean` | Monoidal-closed curry/uncurry injectivity; `EndoVsPoint`; non-collapse lemma vs `OntologicalSlot` |
| `RepresentationalIncompleteness/Lawvere.lean` | Lawvere fixed-point theorem and corollary in **`Type`** (diagonal / universal enumerator argument) |
| `RepresentationalIncompleteness/LawvereCCCType.lean` | Same story via **`MonoidalClosed (Type u)`**: `lawvereBinary`, `curry`/`uncurry`, surjectivity bridge |
| `RepresentationalIncompleteness/LawvereRegressBridge.lean` | Paper-facing: **`no_universal_parametric_unary*`** (incl. `_bool`), **`lawvere_diagonal_not_in_range*`** (partial-model blind spot), **`lawvere_fixed_point_stays_representational`** |
| `RepresentationalIncompleteness/NoEscapeClosure.lean` | Iterate collision → finite power repertoire (**`End.pow_iterate_dichotomy`**); section--retraction readout → idempotent loop, no injective ℕ-tower on either side (**`section_retraction_no_injective_tower_either_side`**) |
| `RepresentationalIncompleteness/SymbolGrounding.lean` | **`SymbolSystem`** (= `RepresentationalSystem`); semantic-regress aliases |
| `RepresentationalIncompleteness/Orientability.lean` | T₂ / Hausdorff as separation surrogate; invariance under homeomorphism |
| `RepresentationalIncompleteness/CylinderMobius.lean` | `mobiusRel₀`, compact Hausdorff **`MobiusStrip`**, **`mobiusStripBoundary`**, saturation **`mobiusQuot_mk_preimage_image`** |
| `RepresentationalIncompleteness/CylinderBoundary.lean` | Closed cylinder `Circle × Icc 0 1`: Mathlib `boundary_product`, two connected / disjoint boundary faces |
| `RepresentationalIncompleteness/CylinderChartableBoundary.lean` | Closed cylinder **C4:** **`closedCylinder_boundaryUnion_iff_not_chartableR2`**, **`H2`** boundary charts |
| `RepresentationalIncompleteness/ChartableR2Neighbor.lean` | Predicate **`ChartableR2`**; **`ChartableR2BoundaryModel`**; half-space obstruction; sequential stability |
| `RepresentationalIncompleteness/ChartableR2Bridge.lean` | **`ChartableR2`** under homeomorphism; **generic** **`not_homeomorphic_of_chartableR2_boundary_contrast`**; **`ChartableR2BoundaryModel.not_homeomorphic`**; **conditional** Möbius / cylinder corollaries **`mobiusStrip_not_homeomorphic_closedCylinder_of_*`** |
| `RepresentationalIncompleteness/ChartableR2ConcreteBoundaryModels.lean` | Möbius / cylinder **`ChartableR2BoundaryModel`** instances; **`conditional_observer_chain_not_homeomorphic_mobiusStrip`**; **`QuantumObserverChainHypothesis`** (schematic; **no axioms**) |
| `RepresentationalIncompleteness/ChartableR2Models.lean` | Interior charts on manifold models; cylinder interior **`ChartableR2`** |
| `RepresentationalIncompleteness/MobiusChartableBoundary.lean` | Möbius **open cell** charts; **bot/top** edge **`¬ ChartableR2`**; **`mobiusStripBoundary → ¬ ChartableR2`**; C4 packaging **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`** |
| `RepresentationalIncompleteness/MobiusSeamChartable.lean` | **`mobiusSeamSaturatedPatch`** (open, saturated); left/right patches; sheet-interior injectivity |
| `RepresentationalIncompleteness/MobiusSeamChart.lean` | Seam **local** maps, IFT **`OpenPartialHomeomorph`**, **`mobiusStripTrigCoord`** |
| `RepresentationalIncompleteness/MobiusSeamTrigInject.lean` | Trig coordinates injective on quotient window when **`δ < \|t₀-½\|`** |
| `RepresentationalIncompleteness/MobiusSeamChartableR2.lean` | Full seam **quotient** **`ChartableR2`** (trig + **unfold** at equator); **`chartableR2_mobiusQuotientMk_of_interior_height`**; **`mobiusStrip_not_homeomorphic_closedCylinder`** |
| `RepresentationalIncompleteness/MobiusCylinderBoundaryContrast.lean` | **`mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`** |
| `RepresentationalIncompleteness/HalfLineVsLine.lean`, `HalfPlaneVsPlane.lean`, `HalfSpaceNeighborVsPlane.lean` | Low-dimensional **half-space vs Euclidean** obstructions |
| `RepresentationalIncompleteness/PuncturedPlaneNotSimplyConnected.lean` | Punctured plane / disk not simply connected |
| `RepresentationalIncompleteness/Main.lean` | Re-imports **`SymbolGrounding`**, **`LawvereRegressBridge`**, **`ChartableR2ConcreteBoundaryModels`**; `representational_regress_master` + **`RepresentationalIncompletenessMasterExtended`** (`representational_regress_master_extended`: core + 1D half-line + **M-FINAL**) |

**Advisor narrative:** `docs/ADVISOR_OVERVIEW.md`

---

## Mathlib anchors (in use)

| Topic | Mathlib entry points |
|-------|----------------------|
| Categories / slice | `Mathlib.CategoryTheory.Category.Basic`, `Mathlib.CategoryTheory.Comma.Over.Basic`, `Mathlib.CategoryTheory.Endomorphism` |
| Monoidal closed | `Mathlib.CategoryTheory.Monoidal.Closed.Basic` (`curry_injective`, `uncurry_injective`) |
| Separation / glue | `Mathlib.Topology.Separation.Hausdorff`, `Mathlib.Topology.Constructions` (`continuous_quot_mk`) |
| Additive circle | `Mathlib.Topology.Instances.AddCircle.Real` (`UnitAddCircle`) |
| Intervals | `Mathlib.Order.Interval.Set.Defs` (`Set.Icc`, `Set.Ioo`) |
| Manifold boundary | `Mathlib.Geometry.Manifold.Instances.Real` (`boundary_product`), `Mathlib.Geometry.Manifold.Instances.Sphere` (`Circle` as `IsManifold (𝓡 1)`) |
| Circle / exp | `Mathlib.Analysis.SpecialFunctions.Complex.Circle` (`Circle.surjOn_exp_neg_pi_pi`) |
| Function logic | `Mathlib.Logic.Function.Basic` (`congr_fun`, used in `Lawvere`) |

---

## Notes

- **Regress vs `represent`:** Meta-stages are **definitionally** `represent^n : A ⟶ A`, packaged as `Over.mk (represent^n)`. Distinctness across `n` is still the **hypothesis** `iter_injective` (not derivable from `represent` alone in general).
- **Lawvere:** Full diagonal theorem is proved for `Type`; CCC packaging remains the `MonoidalClosed` fragment in `FixedPoints` plus the standalone `Lawvere` module.
- **Geometry / SPEC_002 (status):** **`mobiusStrip_not_homeomorphic_closedCylinder`** is proved in **`MobiusSeamChartableR2`** via **`chartableR2_mobiusQuotientMk_of_interior_height`** and **`ChartableR2Bridge`**. Cylinder **C4** remains **`CylinderChartableBoundary`**. Contradiction route: incompatible homeomorphisms would identify **boundary subspaces**, contradicting **`MobiusCylinderBoundaryContrast`**.
- Coinductive `RegressChain` from early prose remains optional if ergonomics improve; current story is `ℕ`-indexed iterates.
