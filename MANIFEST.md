# representational-regress-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` (via `lakefile.lean`); use `lake exe cache get`  
**Build:** `lake build RepresentationalRegress` (or `lake build`) from this directory  
**Root import:** `RepresentationalRegress.lean`  
**Formalization map:** `REPRESENTATIONAL_REGRESS_FORMALIZATION_MAP.md`  
**Theorem inventory:** `THEOREM_INVENTORY.md`  
**Program spec:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`  
**Topology punchline spec:** `../specs/IN-PROCESS/SPEC_002_K7P_TOPOLOGY_PUNCHLINE_AND_PAPER.md`  
**Seam charts / M-FINAL closure notes:** `../specs/IN-PROCESS/SPEC_003_NF8_MOBIUS_SEAM_CHARTABLE_AND_M_FINAL_CLOSURE.md`  
**Advisor overview (prose):** `docs/ADVISOR_OVERVIEW.md`  

---

## Topology punchline (SPEC_002) — agreed plan (don’t lose track)

**Goal:** `IsEmpty (MobiusStrip ≃ₜ ClosedCylinder)` (**M-FINAL** — **proved** as **`mobiusStrip_not_homeomorphic_closedCylinder`**).

**Primary spine (canonical):** **`ChartableR2` + boundary / chart bookkeeping** on both models → biconditionals **`mobiusStripBoundary ↔ ¬ ChartableR2`**, **`closedCylinderBoundaryUnion ↔ ¬ ChartableR2`** → apply **`mobiusStrip_not_homeomorphic_closedCylinder_of_chartable_boundary`** (`ChartableR2Bridge`; conditional theorem **already proved**). **Status:** cylinder **C4** is the proved biconditional (**`closedCylinder_boundaryUnion_iff_not_chartableR2`**). Möbius: **`mobiusStripBoundary → ¬ ChartableR2`** is proved (**`not_chartableR2_of_mem_mobiusStripBoundary`**); the reverse direction is packaged as **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`** and is now dischargeable via **`chartableR2_mobiusQuotientMk_of_interior_height`** (every FD point with **`0 < t < 1`**, including **vertical seam** and **equator** `t = ½`, is `ChartableR2` at the quotient class). **M-FINAL** is proved as **`mobiusStrip_not_homeomorphic_closedCylinder`** in **`MobiusSeamChartableR2`** (instantiating **`mobiusStrip_not_homeomorphic_closedCylinder_of_forall_off_edge_chartable`** from **`ChartableR2Bridge`**). Local input lemmas include **`HalfPlaneVsPlane`**, **`HalfSpaceNeighborVsPlane`** (**`isEmpty_homeomorph_subtype_openH2_zero_nbhd_subtype_openPlane`**).

**Ordered steps in SPEC_002:** **C1** (cylinder charts) → **C2** (Möbius charts / quotient) → **C3** (interior `ChartableR2`, boundary `¬ ChartableR2`) → **C4** (biconditionals; **closed cylinder done in `CylinderChartableBoundary.lean`**) → **M-FINAL** → **P2-2+** / **P3** (Main, inventory, paper).

**Fallback only:** **Route W Step 5** (`CylinderMobiusNonhomeo`) — optional cross-check; **not** the flagship dependency chain.

**Supporting (proved):** **`mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`** (`MobiusCylinderBoundaryContrast`). **Do not** run a separate “B-bridged master” track without tying it to the same boundary semantics as **C1–C2**.

---

## Layout

| Area | Path | Role |
|------|------|------|
| Core | `RepresentationalRegress/Basic.lean` | `RepresentationalSystem`, `iter_injective`, `metaRegressArrow` / `metaOver` / `metaRepresent`, `OntologicalSlot` |
| Regress | `RepresentationalRegress/Regress.lean` | `regress_no_termination`, `regress_over_injective`, `regress_iterates_unbounded`, `regress_is_infinite`, `meta_range_infinite` |
| Fixed points | `RepresentationalRegress/FixedPoints.lean` | `EndoVsPoint`, `curry_injective` packaging, `lawvere_wall_is_not_dissolution` |
| Lawvere | `RepresentationalRegress/Lawvere.lean` | `lawvere_fixed_point_Type`, corollary (no universal enumerator when `succ` has no fixed points) |
| Lawvere / CCC bridge | `RepresentationalRegress/LawvereCCCType.lean` | `curry`/`uncurry` packaging of the same hypothesis in `MonoidalClosed (Type u)` |
| Lawvere ↔ regress (paper) | `RepresentationalRegress/LawvereRegressBridge.lean` | **`no_universal_parametric_unary`**, **`no_universal_parametric_unary_nat`**; **`lawvere_fixed_point_stays_representational`** (iterate slots vs `OntologicalSlot.obj`) |
| Symbol grounding (paper) | `RepresentationalRegress/SymbolGrounding.lean` | **`SymbolSystem`** (= `RepresentationalSystem`); **`symbolGrounding_*`** aliases for semantic regress |
| Concrete boundary models | `RepresentationalRegress/ChartableR2ConcreteBoundaryModels.lean` | **`ChartableR2BoundaryModel`** instances for Möbius / cylinder; **`conditional_observer_chain_not_homeomorphic_mobiusStrip`**; **`QuantumObserverChainHypothesis`** (**no axioms**) |
| Orientability | `RepresentationalRegress/Orientability.lean` | T₂ surrogate + homeomorphism invariance |
| Cylinder / Möbius | `RepresentationalRegress/CylinderMobius.lean` | `mobiusRel₀` (proved equivalence), closed glue graph, compact `MobiusStrip`, `instT2SpaceMobiusStrip`, `mobiusQuot_mk_preimage_image`; connected boundary band; **M-FINAL** still future — **SPEC_002** **ChartableR2 spine** (primary) |
| Route W (fallback) | `RepresentationalRegress/CylinderMobiusNonhomeo.lean` | Steps **1–4** **done**; Step 5 optional (doubling vs injective cylinder composite); **not** main path to M-FINAL |
| Boundary subtype contrast | `RepresentationalRegress/MobiusCylinderBoundaryContrast.lean` | **`mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`** — supporting (connected vs disconnected union) |
| Chartable R2 (core) | `RepresentationalRegress/ChartableR2Neighbor.lean` | `ChartableR2`, **`ChartableR2BoundaryModel`**; **`not_chartableR2_of_isOpenEmbedding_H2`**; **`isOpen_setOf_chartableR2`**, **`isClosed_setOf_not_chartableR2`**, **`not_chartableR2_of_tendsto_seq_atTop`** (sequential stability off the chartable set) |
| Chartable R2 bridge | `RepresentationalRegress/ChartableR2Bridge.lean` | `Homeomorph.chartableR2_iff`; **generic:** **`not_homeomorphic_of_chartableR2_boundary_contrast`**; **`ChartableR2BoundaryModel.not_homeomorphic`**; concrete Möbius / cylinder corollaries **`mobiusStrip_not_homeomorphic_closedCylinder_of_*`**; unconditional **`mobiusStrip_not_homeomorphic_closedCylinder`** is in **`MobiusSeamChartableR2`** |
| Closed cylinder boundary charts | `RepresentationalRegress/CylinderChartableBoundary.lean` | **C4:** **`closedCylinder_boundaryUnion_iff_not_chartableR2`**, `homeomorph_closedCylinder_model_to_H2`, product-chart lemmas at `⊥`/`⊤` (`set_option linter.unnecessarySimpa false` locally for chart lemmas) |
| Chartable R2 models | `RepresentationalRegress/ChartableR2Models.lean` | Interior `chartableR2_of_isInteriorPoint_finTwo`; cylinder **`chartableR2_closedCylinder_of_Ioo`**, **`closedCylinder_boundaryUnion_iff_Ioo`**, `isInteriorPoint_closedCylinder_iff` |
| Möbius ChartableR2 (C2/C3; C4 via seam package) | `RepresentationalRegress/MobiusChartableBoundary.lean` (+ **`CylinderMobius`**: **`mobiusClass_eq_singleton_of_Ioo_fx`**) | Planar **open cell:** **`chartableR2_mobiusQuotientMk_of_planeOpenBox`**, **`chartableR2_mobiusQuotientMk_of_Ioo_square`**, **`chartableR2_mobiusQuotientMk_of_mobiusRel₀`**, **`chartableR2_mobiusQuotientMk_of_mobiusRel₀_chartable_left`**; quotient **open image** / **homeomorph** infrastructure (**`mobiusQuotientMk_subtype_homeomorph`**, saturations; **`mobiusQuotientMk_subtype_homeomorph_of_openMap`**); **FD windows with `0 < x < 1`:** **`mobiusQuot_mk_preimage_image_eq_of_forall_mem_Ioo_fx`**, **`isOpen_mobiusQuotient_image_of_forall_mem_Ioo_fx`**, **`mobiusQuotientMk_subtype_homeomorph_of_forall_mem_Ioo_fx`**, **`isOpenMap_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx`** (SPEC_003 IFT / one-sided charts); **boundary (horizontal edges):** `mobiusBotHStrip` / `mobiusTopHStrip` **H2** models, **`not_chartableR2_mobiusQuotientMk_of_bot_edge*`**, **`not_chartableR2_mobiusQuotientMk_of_top_edge*`**, **`not_chartableR2_of_mem_mobiusStripBoundary`**. **C4 packaging:** **`quot_mk_not_mem_mobiusStripBoundary_iff`**, **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`**; interior height discharge: **`chartableR2_mobiusQuotientMk_of_interior_height`** in **`MobiusSeamChartableR2`**. **Trig (in `MobiusSeamTrigInject`):** **`onPatch_mobiusFDTrigCoord_eq_iff_mobiusRel₀`** (needs `δ < \|t₀-½\|` where used). |
| Seam chart glue (SPEC_003_NF8) | `RepresentationalRegress/MobiusSeamChartableR2.lean` (+ `MobiusChartableBoundary`, `MobiusSeamTrigInject`, `MobiusSeamChartable`) | **Trig branch:** plane trig = FD trig after `mobiusPlaneCoord`; **`isOpen_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch`**; **`chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatch`** (full saturated patch when **`δ < |t₀ - ½|`** — excludes equator-center case for that window). **Left seam:** **`chartableR2_mobiusQuotientMk_of_left_seam`** (cases **`t = ½`** vs **`t ≠ ½`**); equator (**`chartableR2_mobiusQuotientMk_of_left_seam_half`**) via **piecewise-linear unfold** map + sub-patch **`V = π '' { q ∈ S \| unfoldFD q ∈ Ball }`** + helper **`continuous_quotientLift_unfold_on_saturatedImage`**. **Right seam:** **`chartableR2_mobiusQuotientMk_of_right_seam`**. **Closure:** **`chartableR2_mobiusQuotientMk_of_interior_height`** (**`0 < t < 1`** ⇒ **`ChartableR2 ⟦p⟧`**). Still see **`MobiusSeamChartableR2.lean` module doc** for plane-geometry caveats (full-patch plane image not open). |
| Seam trig injectivity | `RepresentationalRegress/MobiusSeamTrigInject.lean` | **`mobiusRel₀_of_eq_mobiusFDTrigCoord_of_seamPatch`**, **`onPatch_mobiusFDTrigCoord_eq_iff_mobiusRel₀`**, **`injective_mobiusStripTrigCoord_on_image_quotient_mk_mobiusSeamSaturatedPatch`**, **`image_mobiusStripTrigCoord_quotient_mk_image_mobiusSeamSaturatedPatch`**. Used in the trig seam charts in **`MobiusSeamChartableR2`**. |
| Seam local model (IFT-ready) | `RepresentationalRegress/MobiusSeamChart.lean` | Vertical seam **flattening** `mobiusSeamLocalMap*`, `C^∞`, Fréchet at `0`, **`mobiusSeamLocalMapOpenPartialHomeomorph`**, invertible `mobiusSeam*FderivContinuousLinearEquiv`; **`mobiusSeamPureFderivPi` / `mobiusSeamPureFderivAt`** (general-point Jacobian), **`hasStrictFDerivAt_mobiusSeamLocalMapPure_of_ne`**, **`map_nhds_mobiusPlaneTrigCoordMap`**; `mobiusPlaneTrigCoordMap`; `mobiusStripTrigCoord` on quotient. **Next:** quotient chart (saturated seam pairs) → seam `ChartableR2`. |
| Saturated seam patches (topology) | `RepresentationalRegress/MobiusSeamChartable.lean` | `mobiusSeamSaturatedPatch`, **`isOpen_mobiusSeamSaturatedPatch`**, **`isOpen_mobiusSeamLeftPatch`**, **`isOpen_mobiusSeamRightPatch`**, **`mobiusSeamSaturatedPatch_sat`**, **`mobiusSeamLeftPatchGluePartners`**, **`mobiusSeamLeftPatch_mk_preimage_image_eq`** (for **ε < ½**, left-sheet saturation is **left ∪** glued face on **x = 1**, not the full right-sheet thickening). Composes with seam **`ChartableR2`** in **`MobiusSeamChartableR2`**. |
| Punctured plane | `RepresentationalRegress/PuncturedPlaneNotSimplyConnected.lean` | **`notSimplyConnected_complex_ne_zero`**, **`notSimplyConnected_punctured_open_unit_ball`** (simply connected obstruction via `exp` covering + path lifting) |
| Closed cylinder / boundary | `RepresentationalRegress/CylinderBoundary.lean` | `ClosedCylinder`, `closedCylinder_boundary`, two connected boundary faces |
| Half-line vs line | `RepresentationalRegress/HalfLineVsLine.lean` | `euclideanHalfSpace1_not_homeomorphic_euclidean1` (1D chart obstacle) |
| Half-plane vs plane | `RepresentationalRegress/HalfPlaneVsPlane.lean` | `euclideanHalfSpace2_not_homeomorphic_euclidean2` (2D punctured half-plane vs punctured `ℝ²` / simple connectivity) |
| Half-space neighbor vs plane | `RepresentationalRegress/HalfSpaceNeighborVsPlane.lean` | `isEmpty_homeomorph_subtype_openH2_zero_nbhd_R2`; **`isEmpty_homeomorph_subtype_openH2_zero_nbhd_subtype_openPlane`** — open `V ⊆ H2`, `0 ∈ V`, open `O ⊆ ℝ²` ⇒ no `Subtype V ≃ₜ Subtype O` |
| Assembly | `RepresentationalRegress/Main.lean` | Imports **`SymbolGrounding`**, **`LawvereRegressBridge`**, **`ChartableR2ConcreteBoundaryModels`**; `representational_regress_master`, `representational_regress_master_claim`, `RepresentationalRegressMasterExtended`, `representational_regress_master_extended`, `representational_regress_topology_halfLineModel` |

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

5. **Topology:** “Orientability” in the prose is modelled by **T₂ separation** and preservation under **homeomorphism**. **`CylinderMobius`** has a **closed** glue graph on the compact Hausdorff square, hence **compact Hausdorff** `MobiusStrip` (**`T2Space`** via the closed-graph quotient theorem), **connected** boundary band, and **`mobiusQuot_mk_preimage_image`**. **`CylinderBoundary`** proves the **closed** cylinder’s **manifold boundary** is the **disjoint union of two connected faces** (Mathlib `boundary_product`). **`HalfLineVsLine`** proves **`EuclideanHalfSpace 1 ≄ₜ` 1D Euclidean space** (punctured-ray connectivity). **`HalfPlaneVsPlane`** / **`HalfSpaceNeighborVsPlane`** supply **2D local** half-space vs **plane** obstructions (including **`subtype_openPlane`**). **`ChartableR2Bridge`** packages **`ChartableR2`** invariance and the conditional **`mobiusStrip_not_homeomorphic_closedCylinder_of_*`** theorems. **`MobiusChartableBoundary`** proves **`mobiusStripBoundary → ¬ ChartableR2`**; **`MobiusSeamChartableR2`** proves **`chartableR2_mobiusQuotientMk_of_interior_height`** and **`mobiusStrip_not_homeomorphic_closedCylinder`**, so with **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`** the Möbius **C4** biconditional matches the cylinder side. **`CylinderMobiusNonhomeo`** has **Route W 1–4** (optional **W5** fallback). **`MobiusCylinderBoundaryContrast`** proves boundary **subtypes** are **not** homeomorphic. **`PuncturedPlaneNotSimplyConnected`** shows **`ℂ \\ {0}`** and the **punctured open unit disk** are **not** simply connected. **M-FINAL** is proved in **`ChartableR2Bridge`** from the above. See manifest **Topology punchline** and `THEOREM_INVENTORY.md`.

---

## See also

- `../specs/IN-PROCESS/SPEC_002_K7P_TOPOLOGY_PUNCHLINE_AND_PAPER.md` — **master checklist** for M-FINAL (C1–C4 + M-FINAL)  
- `../specs/IN-PROCESS/SPEC_003_NF8_MOBIUS_SEAM_CHARTABLE_AND_M_FINAL_CLOSURE.md` — seam charts + M-FINAL closure notes  
- `docs/ADVISOR_OVERVIEW.md` — **advisor-facing** summary of claims and proof architecture  
- `ARTIFACT.md` — citation / reproduction  
- `../docs/submodule_workspace.md` — outer / inner git layout  
- `../docs/lean_mathlib_cache_workflow.md` — Mathlib cache workflow  
