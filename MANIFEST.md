# representational-regress-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` (via `lakefile.lean`); use `lake exe cache get`  
**Build:** `lake build RepresentationalRegress` (or `lake build`) from this directory  
**Root import:** `RepresentationalRegress.lean`  
**Formalization map:** `REPRESENTATIONAL_REGRESS_FORMALIZATION_MAP.md`  
**Theorem inventory:** `THEOREM_INVENTORY.md`  
**Program spec:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`  

---

## Layout

| Area | Path | Role |
|------|------|------|
| Core | `RepresentationalRegress/Basic.lean` | `RepresentationalSystem`, `iter_injective`, `metaRegressArrow` / `metaOver` / `metaRepresent`, `OntologicalSlot` |
| Regress | `RepresentationalRegress/Regress.lean` | `regress_no_termination`, `regress_over_injective`, `regress_iterates_unbounded`, `regress_is_infinite`, `meta_range_infinite` |
| Fixed points | `RepresentationalRegress/FixedPoints.lean` | `EndoVsPoint`, `curry_injective` packaging, `lawvere_wall_is_not_dissolution` |
| Lawvere | `RepresentationalRegress/Lawvere.lean` | `lawvere_fixed_point_Type`, corollary (no universal enumerator when `succ` has no fixed points) |
| Lawvere / CCC bridge | `RepresentationalRegress/LawvereCCCType.lean` | `curry`/`uncurry` packaging of the same hypothesis in `MonoidalClosed (Type u)` |
| Orientability | `RepresentationalRegress/Orientability.lean` | T₂ surrogate + homeomorphism invariance |
| Cylinder / Möbius | `RepresentationalRegress/CylinderMobius.lean` | `mobiusRel₀` (proved equivalence), closed glue graph, compact `MobiusStrip`, `instT2SpaceMobiusStrip`, `mobiusQuot_mk_preimage_image`; connected boundary band; global **`¬ (MobiusStrip ≃ₜ ClosedCylinder)`** still future (bridge lemma) |
| Non-homeo (Route W) | `RepresentationalRegress/CylinderMobiusNonhomeo.lean` | Steps 1–4: Möbius doubling chain + cylinder `cylinderToAddCircle` / `cylinderBoundaryLoop` with **injective** composite = `mobiusAddCircleRescale`; `two_zsmul_not_injective` on `AddCircle 2` and `2π`; rescale lemmas |
| Non-homeo (Route B subtype) | `RepresentationalRegress/MobiusCylinderBoundaryContrast.lean` | **`mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`** — boundary **subspaces** not homeomorphic (connected vs disconnected union) |
| Punctured plane | `RepresentationalRegress/PuncturedPlaneNotSimplyConnected.lean` | **`notSimplyConnected_complex_ne_zero`**, **`notSimplyConnected_punctured_open_unit_ball`** (simply connected obstruction via `exp` covering + path lifting) |
| Closed cylinder / boundary | `RepresentationalRegress/CylinderBoundary.lean` | `ClosedCylinder`, `closedCylinder_boundary`, two connected boundary faces |
| Half-line vs line | `RepresentationalRegress/HalfLineVsLine.lean` | `euclideanHalfSpace1_not_homeomorphic_euclidean1` (1D chart obstacle) |
| Half-plane vs plane | `RepresentationalRegress/HalfPlaneVsPlane.lean` | `euclideanHalfSpace2_not_homeomorphic_euclidean2` (2D punctured half-plane vs punctured `ℝ²` / simple connectivity) |
| Assembly | `RepresentationalRegress/Main.lean` | `representational_regress_master`, `representational_regress_master_claim`, `RepresentationalRegressMasterV2`, `representational_regress_master_v2` |

`RepresentationalRegress.lean` imports the above (including `Lawvere`, `CylinderMobius`, and `CylinderBoundary`) so they participate in the default library target.

---

## Proof status

- **0** `sorry` / **0** custom axioms in `RepresentationalRegress/`.
- **Fully machine-checked** relative to Mathlib + Lean’s standard logical core (see “Honest limits” for what is *assumed* vs *derived*).

---

## Honest limits (strength of claim)

1. **Regress:** “Infinitely many distinct meta-levels” is **conditional** on the bundled hypothesis **`iter_injective`**: distinct natural-number exponents give distinct endomorphisms `(End.of represent)^n`. That matches what we actually use in proofs; it is **not** automatic from picking any `represent : A ⟶ A`.

2. **Slice packaging:** `metaOver n` is `Over.mk (represent^n)`; inequality of slice objects follows from inequality of the structure maps once `Over.mk` is injective on parallel morphisms (`Over_mk_inj_parallel`).

3. **Object vs morphism:** `OntologicalSlot` makes disjointness **definitional** (constructor `noConfusion`). It is a disciplined tag, not a proof that an arbitrary morphism “can never” be identified with an object in some external metaphysical sense.

4. **Lawvere:** **`lawvere_fixed_point_Type`** is the standard Lawvere argument in **`Type`**. **`LawvereCCCType`** repackages the *same* universal-enumerator hypothesis as **surjectivity of `MonoidalClosed.curry (lawvereBinary s)`** and proves **`lawvere_fixed_point_MonoidalClosedType`**. This is still **`Type`**, not an abstract CCC over general `C`; a fully general “`C` with terminal + global elements” statement remains future work.

5. **Topology:** “Orientability” in the prose is modelled by **T₂ separation** and preservation under **homeomorphism**. **`CylinderMobius`** has a **closed** glue graph on the compact Hausdorff square, hence **compact Hausdorff** `MobiusStrip` (**`T2Space`** via the closed-graph quotient theorem), **connected** boundary band, and **`mobiusQuot_mk_preimage_image`**. **`CylinderBoundary`** proves the **closed** cylinder’s **manifold boundary** is the **disjoint union of two connected faces** (Mathlib `boundary_product`). **`HalfLineVsLine`** proves **`EuclideanHalfSpace 1 ≄ₜ` 1D Euclidean space** (punctured-ray connectivity). **`HalfPlaneVsPlane`** proves **`EuclideanHalfSpace 2 ≄ₜ EuclideanSpace ℝ (Fin 2)`** (star-convex punctured half-plane vs punctured plane). **`CylinderMobiusNonhomeo`** implements **Route W Steps 1–4** (Möbius doubling chain; **injective** cylinder-side circle composite to `AddCircle (2π)`). **`MobiusCylinderBoundaryContrast`** proves boundary **subtypes** are **not** homeomorphic. **`PuncturedPlaneNotSimplyConnected`** shows **`ℂ \\ {0}`** and the **punctured open unit disk** are **not** simply connected (covering-map lift proof). The full **`MobiusStrip ≄ₜ ClosedCylinder`** theorem remains **future work** until a **bridge** lemma (see **`SPEC_002`** master sequence). See `THEOREM_INVENTORY.md`.

---

## See also

- `ARTIFACT.md` — citation / reproduction  
- `../docs/submodule_workspace.md` — outer / inner git layout  
- `../docs/lean_mathlib_cache_workflow.md` — Mathlib cache workflow  
