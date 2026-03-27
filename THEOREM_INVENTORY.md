# Representational Regress — theorem inventory (Lean names)

**Last updated:** 2026-03-27 — **0** `sorry` in `RepresentationalRegress/`; **M-FINAL** **`mobiusStrip_not_homeomorphic_closedCylinder`**; seam charts + **`chartableR2_mobiusQuotientMk_of_interior_height`** (incl. equator **`chartableR2_mobiusQuotientMk_of_left_seam_half`**). Counterexamples **`not_mem_image_mobiusFDTrigCoord_*`**, **`ne_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch_sheetInterior`** remain documented. Paired with `MANIFEST.md`, `REPRESENTATIONAL_REGRESS_FORMALIZATION_MAP.md`, `docs/ADVISOR_OVERVIEW.md`, and `lake build RepresentationalRegress`.  
**Purpose:** Index of principal `def`s / `theorem`s by module.

---

## Meta

| Module | Coverage |
|--------|----------|
| `Basic` | `RepresentationalSystem`, `representIter`, `metaRegressArrow`, `metaOver`, `metaRepresent`, `Over_mk_inj_parallel`, `OntologicalSlot`, injectivity lemmas |
| `Regress` | `regress_no_termination`, `regress_over_injective`, `regress_iterates_unbounded`, `regress_is_infinite`, `meta_range_infinite` |
| `FixedPoints` | `EndoVsPoint`, `endo_ne_point`, `fixed_point_preserves_distinction`, `uncurry_injective_on`, `lawvere_wall_is_not_dissolution` |
| `Lawvere` | `lawvere_fixed_point_Type`, `lawvere_fixed_point_corollary_no_universal` |
| `LawvereCCCType` | `lawvereBinary`, `curry_lawvereBinary`, `lawvere_universal_iff_surjective_curry`, `lawvere_fixed_point_MonoidalClosedType` |
| `Orientability` | `RepresentationalSeparationInvariant`, T₂ homeomorphism invariance, `surjective_continuous_maps_need_not_preserve_t2` |
| `CylinderMobius` | Models + relation: `mobiusRel₀`, compact Hausdorff `MobiusStrip`, closed graph, connected boundary; **`mobiusClass_eq_singleton_of_Ioo_fx`** (vertical interior off seam); see table below |
| `CylinderMobiusNonhomeo` | Toward punchline: `two_zsmul_not_injective_addCircle_twoPi` |
| `PuncturedPlaneNotSimplyConnected` | `notSimplyConnected_complex_ne_zero`, `notSimplyConnected_punctured_open_unit_ball`, `puncturedBall_loop_not_homotopic_const`; **scaled loop** `puncturedBallLoopOfReal` / `puncturedBall_loopOfReal_not_homotopic_const` (`exp` covering + path lifting) |
| `CylinderBoundary` | `ClosedCylinder`, `closedCylinder_boundary`, `closedCylinder_boundary_eq_union`, connected faces, disjoint faces, `not_isConnected_closedCylinderBoundaryUnion` (two circles disconnect) |
| `HalfLineVsLine` | 1D half-space vs line: `euclideanHalfSpace1_not_homeomorphic_euclidean1`, `euclideanFinOneHomeoReal`, plumbing lemmas |
| `HalfPlaneVsPlane` | 2D half-space vs plane: `euclideanHalfSpace2_not_homeomorphic_euclidean2` (punctured half-plane vs punctured `ℝ²` / simple connectivity); `complexNeZeroHomeoPuncturedE2`, `puncturedHalfPlaneHomeoH2NeZero`, `notSimplyConnected_punctured_E2`; **`tendsto_norm_complexHomeoE2_nhds_zero`** (shrink `‖complexHomeoE2 z‖` as `z → 0`, for half-ball vs `ℝ²` chart obstruction) |
| `HalfSpaceNeighborVsPlane` | Local model: `isEmpty_homeomorph_subtype_openH2_zero_nbhd_R2` (open `V ⊆ H2`, `0 ∈ V` ⇒ no `Subtype V ≃ₜ R2`); **`isEmpty_homeomorph_subtype_openH2_zero_nbhd_subtype_openPlane`** (same for `Subtype V ≃ₜ Subtype O` with `O ⊆ R2` open — small ball in `O`); supporting `puncturedRNBallInVHomeoPuncturedHalfBallR2`, star-convex punctured half-ball |
| `OpenCompactChartObstruction` | Compact nonempty patch of `ℝ²` not homeomorphic to all of `ℝ²` (`not_compactSpace_euclidean_two`, `isEmpty_homeomorph_euclideanClosedSquare_euclidean_two`) |
| `MobiusCylinderBoundaryContrast` | `mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion` (connected vs disconnected boundary union) |
| `ChartableR2Neighbor` | `ChartableR2`, `chartableR2_of_open_embeds_plane`, **`not_chartableR2_of_isOpenEmbedding_H2`**; **`isOpen_setOf_chartableR2`**, **`isClosed_setOf_not_chartableR2`**, **`not_chartableR2_of_tendsto_seq_atTop`** |
| `ChartableR2Bridge` | `Homeomorph.chartableR2_iff`, **`mobiusStrip_not_homeomorphic_closedCylinder_of_chartable_boundary`**, **`mobiusStrip_not_homeomorphic_closedCylinder_of_mobius_boundary_chartable`**, **`mobiusStrip_not_homeomorphic_closedCylinder_of_forall_off_edge_chartable`**. Unconditional **`mobiusStrip_not_homeomorphic_closedCylinder`**: **`MobiusSeamChartableR2`**. |
| `CylinderChartableBoundary` | Closed cylinder **C4:** `closedCylinder_boundaryUnion_iff_not_chartableR2`, `openEmbedding_H2_chartAt_center`, `homeomorph_closedCylinder_model_to_H2`, boundary-face `not_chartableR2_*` lemmas |
| `ChartableR2Models` | `chartableR2_of_isInteriorPoint_finTwo`, `homeomorph_subtype_extChartAt_ball`; cylinder: `isInteriorPoint_closedCylinder_iff`, `chartableR2_closedCylinder_of_Ioo`, `closedCylinder_boundaryUnion_iff_Ioo` |
| `MobiusChartableBoundary` | **Open cell** `ChartableR2` (**`chartableR2_mobiusQuotientMk_of_planeOpenBox`**, **`chartableR2_mobiusQuotientMk_of_Ioo_square`**, **`chartableR2_mobiusQuotientMk_of_mobiusRel₀`**, **`chartableR2_mobiusQuotientMk_of_mobiusRel₀_chartable_left`**); saturated quotient / plane-box homeomorph toolkit (**`mobiusQuotientMk_subtype_homeomorph`**, **`mobiusQuotientMk_subtype_homeomorph_of_openMap`**); **vertical interior (`0 < x < 1`):** **`mobiusQuot_mk_preimage_image_eq_of_forall_mem_Ioo_fx`**, **`isOpen_mobiusQuotient_image_of_forall_mem_Ioo_fx`**, **`mobiusRel₀_sat_of_forall_mem_Ioo_fx`**, **`injective_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx`**, **`isOpenMap_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx`**, **`mobiusQuotientMk_subtype_homeomorph_of_forall_mem_Ioo_fx`** (with **`mobiusClass_eq_singleton_of_Ioo_fx`** in **`CylinderMobius`**); SPEC_003 **B2:** **`injective_mobiusPlaneCoord`**, **`isClosedEmbedding_mobiusPlaneCoord`**, **`exists_isOpen_preimage_mobiusPlaneCoord_of_isOpen`**; **boundary** `H2` strips; **`not_chartableR2_mobiusQuotientMk_of_bot_edge*`**, **`not_chartableR2_mobiusQuotientMk_of_top_edge*`**, **`not_chartableR2_of_mem_mobiusStripBoundary`**; **C4 packaging:** **`quot_mk_not_mem_mobiusStripBoundary_iff`**, **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`**. Hypothesis discharged in **`MobiusSeamChartableR2`** via **`chartableR2_mobiusQuotientMk_of_interior_height`**. |
| `MobiusSeamChartableR2` | SPEC_003 seam **`ChartableR2`**: **trig** **`isOpen_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch`**, **`chartableR2_mobiusQuotientMk_of_mem_mobiusSeamSaturatedPatch`** (needs **`δ < |t₀-½|`** — excludes equator-center for that window); **left seam** **`chartableR2_mobiusQuotientMk_of_left_seam`** = **`chartableR2_mobiusQuotientMk_of_left_seam_half`** (equator unfold) ∪ **`chartableR2_mobiusQuotientMk_of_left_seam_ne_half`** (trig); **right seam** **`chartableR2_mobiusQuotientMk_of_right_seam`**; **global interior height** **`chartableR2_mobiusQuotientMk_of_interior_height`**; **M-FINAL** **`mobiusStrip_not_homeomorphic_closedCylinder`**. Helper (private): **`continuous_quotientLift_unfold_on_saturatedImage`** (quotient descent for unfold chart). Counterexamples: **`not_mem_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatchSheetInterior_of_horiz_ne`**, **`ne_image_mobiusFDTrigCoord_mobiusSeamSaturatedPatch_sheetInterior`**. |
| `MobiusSeamChart` | **Vertical seam local model** on `R²`: **`mobiusSeamSlidingCoord`**, **strict window** **`mobiusSeamSlidingStrictCoordSet`**, **`homeomorph_subtype_mobiusSeamSlidingCoord_preimage`**; **`mobiusSeamLocalMap*`** / IFT **`mobiusSeamLocalMapOpenPartialHomeomorph`**; **`mobiusStripTrigCoord`** / **`continuous_mobiusStripTrigCoord`**. Consumed by **`MobiusSeamChartableR2`** (trig charts, sliding windows). |
| `MobiusSeamChartable` | **`mobiusSeamLeftPatchGluePartners`**, **`mobiusSeamLeftPatch_mk_preimage_image_eq`**. Saturated patches **`mobiusSeamSaturatedPatch`**, **`isOpen_mobiusSeamSaturatedPatch`**, **`isOpen_mobiusSeamLeftPatch`**, **`isOpen_mobiusSeamRightPatch`**, **`mobiusSeamSaturatedPatch_sat`**, sheet interior **`mobiusSeamSaturatedPatchSheetInterior`**, **`mobiusSeamSaturatedPatchSheetInterior_sat`**, **`mobiusQuotientMk_injective_on_mobiusSeamSaturatedPatchSheetInterior`**. |
| `MobiusSeamTrigInject` | Away from `t = ½` on saturated seam patches: **`sub_half_ne_zero_of_mem_mobiusSeamSaturatedPatch`**, **`mobiusRel₀_of_eq_mobiusFDTrigCoord_of_seamPatch`**, **`onPatch_mobiusFDTrigCoord_eq_iff_mobiusRel₀`**, **`injective_mobiusStripTrigCoord_on_image_quotient_mk_mobiusSeamSaturatedPatch`**, **`image_mobiusStripTrigCoord_quotient_mk_image_mobiusSeamSaturatedPatch`**. Inputs: `MobiusSeamChart` / `MobiusSeamChartable` patch hypotheses + `δ < |t₀ - ½|` where needed. |
| `Main` | `representational_regress_master`, `representational_regress_master_claim`, `RepresentationalRegressMasterExtended`, `representational_regress_master_extended`, `representational_regress_topology_halfLineModel` |

---

## Basic

| Kind | Lean name | Notes |
|------|-----------|--------|
| `structure` | `RepresentationalSystem` | `C`, `A`, `represent : A ⟶ A`, hypothesis `iter_injective` on distinct powers in `End A` |
| `def` | `representIter`, `metaRegressArrow`, `metaOver`, `metaRepresent` | Iterates of `represent`; slice packaging `Over.mk (represent^n)`; `metaRepresent` abbreviates the regress **arrow** |
| `theorem` | `Over_mk_inj_parallel` | `Over.mk f = Over.mk g → f = g` for `f g : A ⟶ A` |
| `theorem` | `representIter_injective`, `metaRegressArrow_injective`, `metaOver_injective`, `metaRepresent_injective` | From `iter_injective` |
| `theorem` | `metaRepresent_zero`, `representIter_zero` | Power `0` is identity |
| `inductive` | `OntologicalSlot` | `obj` vs `endo` disjoint witnesses |
| `theorem` | `obj_ne_endo`, `represent_slot_ne_A` | Constructor discrimination |
| `theorem` | `OntologicalSlot.endo_injective` | `endo` branch is injective on morphisms |
| `theorem` | `OntologicalSlot.representational_tower_preserves_slot` | Distinct `n ≠ m` ⇒ distinct `endo (metaRegressArrow n)` slots |
| `theorem` | `OntologicalSlot.no_slot_collapse` | No `endo (metaRegressArrow n)` equals an `obj` slot |

## Regress

| Kind | Lean name | Notes |
|------|-----------|--------|
| `theorem` | `regress_no_termination` | Distinct `n ≠ m` ⇒ distinct `metaRegressArrow` |
| `theorem` | `regress_over_injective` | Distinct indices ⇒ distinct `metaOver` (slice objects) |
| `theorem` | `regress_iterates_unbounded` | For every `bound`, `∃ level > bound` with distinct iterate |
| `theorem` | `regress_is_infinite`, `meta_range_infinite` | Witness / unbounded `ℕ` |

## Fixed points

| Kind | Lean name | Notes |
|------|-----------|--------|
| `inductive` | `EndoVsPoint` | `endo` vs `point (⊤_ C ⟶ A)` under `[HasTerminal C]` |
| `theorem` | `endo_ne_point`, `point_ne_endo` | Constructor discrimination |
| `theorem` | `fixed_point_preserves_distinction` | `MonoidalClosed.curry_injective` |
| `theorem` | `uncurry_injective_on` | `MonoidalClosed.uncurry_injective` |
| `theorem` | `lawvere_wall_is_not_dissolution` | `OntologicalSlot` non-collapse (`endo represent ≠ obj fp`) |

## Lawvere (`Type`)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `theorem` | `lawvere_fixed_point_Type` | Universal `s : A → A → B` for unary `A → B` ⇒ every `f : B → B` has a fixed point |
| `theorem` | `lawvere_fixed_point_corollary_no_universal` | No fixed-point-free `succ` on `B` + universal `s` ⇒ `False` |

## Lawvere ↔ `MonoidalClosed (Type u)`

| Kind | Lean name | Notes |
|------|-----------|--------|
| `def` | `lawvereBinary` | Morphism `(A ⊗ A) ⟶ B` with `curry` projecting to `s : A ⟶ A ⟹ B` |
| `theorem` | `uncurry_eq_lawvereBinary`, `curry_lawvereBinary` | Curry/uncurry alignment with the function hypothesis |
| `theorem` | `lawvere_universal_iff_surjective_curry` | Enumerator hypothesis ↔ `Surjective (curry (lawvereBinary s))` |
| `theorem` | `lawvere_fixed_point_MonoidalClosedType` | Same conclusion with CCC-style surjectivity on `curry` |

## Orientability

| Kind | Lean name | Notes |
|------|-----------|--------|
| `abbrev` | `RepresentationalSeparationInvariant` | `T2Space` surrogate |
| `theorem` | `topology_invariant_under_homeomorph` | `Homeomorph.t2Space` |
| `theorem` | `orientability_is_homeomorphism_invariant` | Alias |
| `theorem` | `surjective_continuous_maps_need_not_preserve_t2` | Documentation anchor (`True`) |

## Cylinder / Möbius (topology models)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `abbrev` | `OpenCylinder` | `UnitAddCircle × Ioo (0, 1)`; `T2Space` by `inferInstance` |
| `abbrev` | `MobiusFundamentalDomain` | `Icc 0 1 × Icc 0 1`; compact Hausdorff (`inferInstance`) |
| `def` | `mobiusGlueStep`, `mobiusRel₀` | Vertical-edge glue + reflexive closure |
| `theorem` | `mobiusRel₀.symm`, `mobiusRel₀.trans`, `mobiusRel₀.equivalence` | `mobiusRel₀` is an equivalence (no separate transitivity scaffold) |
| `def` | `mobiusGlueSeamSet` | Two closed seam loci in `M × M` |
| `theorem` | `mobiusGlueSeamSet_isClosed` | From continuous coordinate projections into `ℝ` |
| `theorem` | `mobiusRel₀Graph_eq`, `mobiusRel₀Graph_isClosed` | Graph = diagonal ∪ seams ⇒ **closed** in `M × M` |
| `def` | `mobiusSetoid` | `r := mobiusRel₀` |
| `abbrev` | `MobiusStrip` | `Quotient mobiusSetoid` (`abbrev` so `CompactSpace` synthesizes) |
| `instance` | `CompactSpace MobiusStrip` | `Quotient.compactSpace` |
| `instance` | `instT2SpaceMobiusStrip` | Compact T₂ domain + closed glue graph ⇒ Hausdorff quotient |
| `theorem` | `continuous_mobiusQuot` | `continuous_quot_mk` |
| `theorem` | `mobiusQuot_mk_preimage_image` | `π ⁻¹' (π '' U) = { q | ∃ p ∈ U, mobiusRel₀ p q }` (saturation identity; lemma toward `IsOpenQuotientMap`) |
| `def` | `mobiusIcc0`, `mobiusIcc1`, `mobiusBotEdge`, `mobiusTopEdge`, `mobiusStripBoundary` | Canonical corners; horizontal edges; quotient boundary band |
| `theorem` | `mobiusIcc0_val`, `mobiusIcc1_val` | `@[simp]` endpoint values |
| `theorem` | `isConnected_univ_Icc01` | `Icc 0 1` subtype connected from `Set.Icc` connected |
| `theorem` | `isConnected_mobiusBotEdge`, `isConnected_mobiusTopEdge` | `univ ×ˢ {corner}` |
| `theorem` | `isConnected_mobiusStripBoundary` | Connected images of edges + `Quotient.sound` at corners |
| `theorem` | **`mobiusStrip_not_homeomorphic_closedCylinder`** | **`SPEC_002` M-FINAL** — in **`MobiusSeamChartableR2`** (see **`ChartableR2Bridge`** for conditional packaging) |
| *Open* | — | **`IsManifold` with boundary** on `MobiusStrip` as a separate Mathlib-style polish (not required for M-FINAL here) |

## Closed cylinder / manifold boundary (`CylinderBoundary`)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `abbrev` | `ClosedCylinder` | `Circle × Icc 0 1` with product `𝓡 1 × 𝓡∂ 1` structure |
| `def` | `closedCylinderBotFace`, `closedCylinderTopFace` | `S¹ × {0}` and `S¹ × {1}` as subsets |
| `def` | `closedCylinderBotCoords`, `closedCylinderTopCoords` | Continuous coordinate maps from `Circle` |
| `theorem` | `closedCylinder_boundary` | `boundary_product` ⇒ boundary is `univ ×ˢ {⊥, ⊤}` |
| `theorem` | `closedCylinder_boundary_eq_union` | Boundary = disjoint union of the two faces |
| `theorem` | `isConnected_closedCylinderBotFace`, `isConnected_closedCylinderTopFace` | Each face connected (image of connected `Circle`) |
| `theorem` | `closedCylinder_boundary_faces_disjoint` | The two faces are disjoint |
| `lemma` | `circleExp_surjective`, `isConnected_univ_circle` | Auxiliary connectivity of `Circle` |

## Main

| Kind | Lean name | Notes |
|------|-----------|--------|
| `def` | `representational_regress_master_claim` | Master conjunction as one `Prop` (universe-coupled to `R`) |
| `theorem` | `representational_regress_master` | Proves `representational_regress_master_claim` |
| `abbrev` | `RepresentationalRegressMasterExtended` | `representational_regress_master_claim R ∧` half-line `≄ₜ` **`∧`** **`IsEmpty (MobiusStrip ≃ₜ ClosedCylinder)`** (**M-FINAL**); **not** a replacement for the core master theorem |
| `theorem` | `representational_regress_master_extended` | Proves that extended conjunction (incl. **`mobiusStrip_not_homeomorphic_closedCylinder`**) |
| `theorem` | `representational_regress_topology_halfLineModel` | 1D half-space vs line only (first topology leg; pair with `representational_regress_master` if splitting the bundle) |

## Cylinder / Möbius non-homeomorphism (`CylinderMobiusNonhomeo`)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `lemma` | `equivAddCircle_symm_map_zsmul`, `homeomorphCircle_at_period`, `homeomorphAddCircle_self` | Circle rescaling / `homeomorphCircle (2π)` = `homeomorphCircle'` |
| `theorem` | `two_zsmul_not_injective_addCircle_twoPi`, `two_zsmul_not_injective_addCircle_two` | Doubling not injective on `AddCircle (2π)` and on `AddCircle 2` |
| `lemma` | `mobiusAddCircleRescale_symm_map_two_zsmul` | `mobiusAddCircleRescale.symm` commutes with `2 • ·` |
| `noncomputable def` | `cylinderToAddCircle`, `cylinderBoundaryLoop` | Bottom-face cylinder loop + `Circle` → `AddCircle (2π)` via `Prod.fst` |
| `theorem` | `continuous_cylinderToAddCircle`, `continuous_cylinderBoundaryLoop`, `cylinderToAddCircle_comp_cylinderBoundaryLoop`, `injective_cylinderToAddCircle_comp_cylinderBoundaryLoop` | Cylinder-side **Route W** step 4: composite equals **`mobiusAddCircleRescale`** (hence injective) |
| `def` / `theorem` | `mobiusStripToAddCircle`, `mobiusBoundaryLoop`, `mobiusStripToAddCircle_comp_mobiusBoundaryLoop`, `mobiusStripToAddCircle_comp_mobiusBoundaryLoop_not_injective` | Steps 1–3 (winding / doubling on `AddCircle`) |

## Boundary subtype contrast (`MobiusCylinderBoundaryContrast`)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `theorem` | `mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion` | `IsEmpty` of homeomorphism between **boundary subspaces**: connected vs disconnected union (Route B **without** global `MobiusStrip ≃ ClosedCylinder` yet) |

## Punctured plane / ball (`PuncturedPlaneNotSimplyConnected`)

| Kind | Lean name | Notes |
|------|-----------|-------|
| `def` | `ℂNeZero`, `complexCovering`, `PuncturedOpenUnitBall` | `{z // z≠0}`; `exp : ℂ → ℂNeZero` covering map; punctured unit ball subtype |
| `theorem` | `complexCovering_isCoveringMap` | `Complex.isCoveringMap_exp` |
| `theorem` | `puncturedBall_loop_not_homotopic_const` | Same-endpoint loops; **distinct** lifts ⇒ not `HomotopicRel` `{0,1}` |
| `theorem` | `notSimplyConnected_complex_ne_zero` | `¬ SimplyConnectedSpace ℂNeZero` |
| `theorem` | `notSimplyConnected_punctured_open_unit_ball` | `¬ SimplyConnectedSpace` on `{z // z≠0 ∧ ‖z‖<1}` (via inclusion) |

## Half-line vs line (`HalfLineVsLine`)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `abbrev` | `RealHalfLine` | `EuclideanHalfSpace 1` |
| `theorem` | `ne_zero_iff_pos` | Complement of `0` in the ray ↔ positive first coordinate |
| `def` | `halfLineComplZeroHomeomorph_Ioi` | `{z ≠ 0} ≃ₜ Ioi 0` |
| `theorem` | `isConnected_halfLine_compl_zero` | Punctured ray connected |
| `theorem` | `real_compl_singleton_not_preconnected` | `ℝ \ {c}` not preconnected |
| `theorem` | `euclideanHalfSpace1_not_homeomorphic_real`, `euclideanHalfSpace1_not_homeomorphic_euclidean1` | Main non-homeomorphism claims |
| `theorem` | `Homeomorph.image_compl_singleton` | Image of complement of a point under a homeomorphism |
| `def` | `euclideanFinOneHomeoReal` | `EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ` |

## Half-plane vs plane (`HalfPlaneVsPlane`)

| Kind | Lean name | Notes |
|------|-----------|-------|
| `theorem` | `euclideanHalfSpace2_not_homeomorphic_euclidean2` | `IsEmpty (EuclideanHalfSpace 2 ≃ₜ EuclideanSpace ℝ (Fin 2))` via punctured half-plane simply connected vs punctured plane not |
| `theorem` | `notSimplyConnected_punctured_E2` | Subtype `{v // v ≠ 0}` in `ℝ²` not simply connected |
| `def` | `complexNeZeroHomeoPuncturedE2`, `puncturedHalfPlaneHomeoH2NeZero` | Homeomorphisms linking punctured models |

## Chartable ℝ² bridge (`ChartableR2Bridge`)

| Kind | Lean name | Notes |
|------|-----------|-------|
| `def` | `ChartableR2` | ∃ open `U ∋ x`, `Nonempty (Subtype U ≃ₜ R2)` (global “planar chart” on an open neighborhood) |
| `theorem` | `chartableR2_of_open_embeds_plane` | Packages an explicit open neighborhood + homeomorphism |
| `theorem` | `Homeomorph.chartableR2_iff` | `ChartableR2` is invariant under homeomorphisms |
| `theorem` | `mobiusStrip_homeomorph_boundary_iff_closedCylinderBoundaryUnion` | From boundary `↔ ¬ChartableR2` on both sides: images match under any `MobiusStrip ≃ₜ ClosedCylinder` |
| `theorem` | `mobiusStrip_not_homeomorphic_closedCylinder_of_chartable_boundary` | **Conditional M-FINAL:** `IsEmpty (MobiusStrip ≃ₜ ClosedCylinder)` once the two boundary `↔ ¬ChartableR2` lemmas hold |
| `theorem` | `mobiusStrip_not_homeomorphic_closedCylinder_of_mobius_boundary_chartable` | Cylinder biconditional discharged (**`closedCylinder_boundaryUnion_iff_not_chartableR2`**) |
| `theorem` | `mobiusStrip_not_homeomorphic_closedCylinder_of_forall_off_edge_chartable` | From **`∀ p, 0 < t < 1 → ChartableR2 ⟦p⟧`** + **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`** |
| `theorem` | **`mobiusStrip_not_homeomorphic_closedCylinder`** | **Unconditional M-FINAL** — see **`MobiusSeamChartableR2`** |

## Chartable ℝ² neighbor toolkit (`ChartableR2Neighbor`)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `theorem` | `isOpen_setOf_chartableR2`, `isClosed_setOf_not_chartableR2` | Complement of plane-chartable points is closed |
| `theorem` | `not_chartableR2_of_tendsto_seq_atTop` | A seq of **`¬ ChartableR2`** points tending to `x` ⇒ **`¬ ChartableR2 x`** |

## Möbius `ChartableR2` / boundary (`MobiusChartableBoundary`)

| Kind | Lean name | Notes |
|------|-----------|--------|
| `theorem` | `chartableR2_mobiusQuotientMk_of_planeOpenBox`, `chartableR2_mobiusQuotientMk_of_Ioo_square` | Strict planar cell / open box quotient charts |
| `theorem` | `chartableR2_mobiusQuotientMk_of_mobiusRel₀`, `chartableR2_mobiusQuotientMk_of_mobiusRel₀_chartable_left` | `ChartableR2 ⟦·⟧` constant on `mobiusRel₀` classes (either quoted side) |
| `def` / `theorem` | `mobiusPlaneOpenBox`, `mobiusPlaneCoord`, `continuous_mobiusPlaneCoord`, `injective_mobiusPlaneCoord`, `isClosedEmbedding_mobiusPlaneCoord`, `exists_isOpen_preimage_mobiusPlaneCoord_of_isOpen`, `isOpen_mobiusQuotient_image_of_saturated`, `mobiusQuotientMk_subtype_homeomorph` | Saturated-open quotient toolbox |
| `def` / `theorem` | `mobiusBotHStrip*`, `mobiusTopHStrip*`, `mobiusBotHStripHomeomorph`, `mobiusTopHStripHomeomorph` | Boundary collars modeled in **`H2`** (height `t` or `1-t`); bot/top **saturation** + injectivity on strips interior in `x` |
| `theorem` | `not_chartableR2_mobiusQuotientMk_of_bot_edge_Ioo`, `not_chartableR2_mobiusQuotientMk_of_top_edge_Ioo` | Interior edge points (`0<t<1` in `x`, `t=0` or `1`) |
| `theorem` | `not_chartableR2_mobiusQuotientMk_of_bot_edge`, `not_chartableR2_mobiusQuotientMk_of_top_edge` | Full edges including **corners** (via **`not_chartableR2_of_tendsto_seq_atTop`**) |
| `theorem` | `not_chartableR2_of_mem_mobiusStripBoundary` | **`mobiusStripBoundary → ¬ ChartableR2`** |

---

## Not machine-checked in this artifact (philosophy / gaps)

- **Deriving `iter_injective`** from minimal data about `represent` alone (in general false — bundled hypothesis).
- **Cylinder vs Möbius (geometry track):** `CylinderBoundary` proves the **closed** cylinder’s **manifold boundary** is **two disjoint connected** faces and that **their union is not connected** as a subspace (`not_isConnected_closedCylinderBoundaryUnion`). `CylinderMobius` gives **compact Hausdorff** `MobiusStrip` and **connected** `mobiusStripBoundary`. **`MobiusChartableBoundary`** proves **`mobiusStripBoundary → ¬ ChartableR2`**; **`MobiusSeamChartableR2`** proves interior-height **`ChartableR2`** and **`mobiusStrip_not_homeomorphic_closedCylinder`**. Cylinder **C4**: **`closedCylinder_boundaryUnion_iff_not_chartableR2`**. `HalfLineVsLine`, **`HalfPlaneVsPlane`**, **`HalfSpaceNeighborVsPlane`**, **`OpenCompactChartObstruction`**, **`ChartableR2Bridge`**, **`CylinderMobiusNonhomeo`** (Route W 1–4), **`MobiusCylinderBoundaryContrast`**, **`PuncturedPlaneNotSimplyConnected`**. See **`SPEC_002`**, **`docs/ADVISOR_OVERVIEW.md`**.
- **HEq / cross-sort:** library uses tagged `OntologicalSlot` for object vs endomorphism contrast; fully general `¬ HEq (hom) (obj)` for arbitrary categories is not a single named deliverable here.
- **Bundled CCC Lawvere:** concrete theorem is in `Type`; the master package still uses `MonoidalClosed` fragments + `OntologicalSlot`.
</think>


<｜tool▁calls▁begin｜><｜tool▁call▁begin｜>
StrReplace