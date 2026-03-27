# Representational Regress — formalization map

**Purpose:** Module roles; pair with `MANIFEST.md` and `THEOREM_INVENTORY.md`.  
**Program spec:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`

---

## Module tree

| Path | Role |
|------|------|
| `RepresentationalRegress/Basic.lean` | `RepresentationalSystem` (`represent`, bundled `iter_injective`), iterates `represent^n` as morphisms, `Over A` packaging (`metaOver`), `OntologicalSlot` |
| `RepresentationalRegress/Regress.lean` | Injectivity of iterates + slice objects; unbounded levels (`regress_iterates_unbounded`) |
| `RepresentationalRegress/FixedPoints.lean` | Monoidal-closed curry/uncurry injectivity; `EndoVsPoint`; non-collapse lemma vs `OntologicalSlot` |
| `RepresentationalRegress/Lawvere.lean` | Lawvere fixed-point theorem and corollary in **`Type`** (diagonal / universal enumerator argument) |
| `RepresentationalRegress/LawvereCCCType.lean` | Same story via **`MonoidalClosed (Type u)`**: `lawvereBinary`, `curry`/`uncurry`, surjectivity bridge |
| `RepresentationalRegress/Orientability.lean` | T₂ / Hausdorff as separation surrogate; invariance under homeomorphism |
| `RepresentationalRegress/CylinderMobius.lean` | `mobiusRel₀`, compact Hausdorff **`MobiusStrip`**, **`mobiusStripBoundary`**, saturation **`mobiusQuot_mk_preimage_image`** |
| `RepresentationalRegress/CylinderBoundary.lean` | Closed cylinder `Circle × Icc 0 1`: Mathlib `boundary_product`, two connected / disjoint boundary faces |
| `RepresentationalRegress/CylinderChartableBoundary.lean` | Closed cylinder **C4:** **`closedCylinder_boundaryUnion_iff_not_chartableR2`**, **`H2`** boundary charts |
| `RepresentationalRegress/ChartableR2Neighbor.lean` | Predicate **`ChartableR2`** (open nbhd **≃ₜ** `ℝ²`); half-space obstruction; sequential stability |
| `RepresentationalRegress/ChartableR2Bridge.lean` | **`ChartableR2`** under homeomorphism; **conditional** **`mobiusStrip_not_homeomorphic_closedCylinder_of_*`** |
| `RepresentationalRegress/ChartableR2Models.lean` | Interior charts on manifold models; cylinder interior **`ChartableR2`** |
| `RepresentationalRegress/MobiusChartableBoundary.lean` | Möbius **open cell** charts; **bot/top** edge **`¬ ChartableR2`**; **`mobiusStripBoundary → ¬ ChartableR2`**; C4 packaging **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`** |
| `RepresentationalRegress/MobiusSeamChartable.lean` | **`mobiusSeamSaturatedPatch`** (open, saturated); left/right patches; sheet-interior injectivity |
| `RepresentationalRegress/MobiusSeamChart.lean` | Seam **local** maps, IFT **`OpenPartialHomeomorph`**, **`mobiusStripTrigCoord`** |
| `RepresentationalRegress/MobiusSeamTrigInject.lean` | Trig coordinates injective on quotient window when **`δ < \|t₀-½\|`** |
| `RepresentationalRegress/MobiusSeamChartableR2.lean` | Full seam **quotient** **`ChartableR2`** (trig + **unfold** at equator); **`chartableR2_mobiusQuotientMk_of_interior_height`**; **`mobiusStrip_not_homeomorphic_closedCylinder`** |
| `RepresentationalRegress/MobiusCylinderBoundaryContrast.lean` | **`mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`** |
| `RepresentationalRegress/CylinderMobiusNonhomeo.lean` | Optional **Route W** (circle doubling / winding) |
| `RepresentationalRegress/HalfLineVsLine.lean`, `HalfPlaneVsPlane.lean`, `HalfSpaceNeighborVsPlane.lean` | Low-dimensional **half-space vs Euclidean** obstructions |
| `RepresentationalRegress/PuncturedPlaneNotSimplyConnected.lean` | Punctured plane / disk not simply connected |
| `RepresentationalRegress/Main.lean` | `representational_regress_master` + **`RepresentationalRegressMasterV2`** packaging |

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
- **Geometry / SPEC_002 (status):** **`mobiusStrip_not_homeomorphic_closedCylinder`** is proved in **`MobiusSeamChartableR2`** via **`chartableR2_mobiusQuotientMk_of_interior_height`** and **`ChartableR2Bridge`**. Cylinder **C4** remains **`CylinderChartableBoundary`**. Contradiction route: incompatible homeomorphisms would identify **boundary subspaces**, contradicting **`MobiusCylinderBoundaryContrast`**. **Route W** is optional; see **`docs/ADVISOR_OVERVIEW.md`**.
- Coinductive `RegressChain` from early prose remains optional if ergonomics improve; current story is `ℕ`-indexed iterates.
