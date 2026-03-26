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
| `RepresentationalRegress/CylinderMobius.lean` | Concrete topological models: Hausdorff open cylinder vs quotient Möbius strip (no non-homeomorphism proof yet) |
| `RepresentationalRegress/CylinderBoundary.lean` | Closed cylinder `Circle × Icc 0 1`: Mathlib `boundary_product`, two connected / disjoint boundary faces |
| `RepresentationalRegress/Main.lean` | `representational_regress_master` — conditional assembly of regress + slot + T₂ transport |

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
- **Geometry:** `CylinderMobius` gives rigorous **definitions** and T₂ for the cylinder side; `CylinderBoundary` proves the **closed** cylinder’s **manifold boundary** is **two disjoint connected components**. Distinguishing the Möbius quotient from the cylinder (e.g. one vs two boundary components) is still future work.
- Coinductive `RegressChain` from early prose remains optional if ergonomics improve; current story is `ℕ`-indexed iterates.
