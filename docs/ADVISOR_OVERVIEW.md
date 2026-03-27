# Representational Regress (Lean) — overview for advisors

**Repository:** `representational-regress-lean`  
**Build:** `lake build RepresentationalRegress` — **0** `sorry`, **0** project axioms beyond Mathlib + Lean’s core  
**Navigation:** `MANIFEST.md`, `THEOREM_INVENTORY.md`, `REPRESENTATIONAL_REGRESS_FORMALIZATION_MAP.md`, `ARTIFACT.md`  
**Topology program spec:** `../specs/IN-PROCESS/SPEC_002_K7P_TOPOLOGY_PUNCHLINE_AND_PAPER.md`  
**Seam chart spec:** `../specs/IN-PROCESS/SPEC_003_NF8_MOBIUS_SEAM_CHARTABLE_AND_M_FINAL_CLOSURE.md`

This note is for **non-authors** who need a faithful map of **what is proved**, **what it depends on**, and **what it does *not* claim**.

---

## 1. Two strands in one artifact

### A. Categorical / “representational regress” strand

The project formalizes a **typed representational system**: an object `A`, an endomorphism `represent : A ⟶ A`, and a **bundled injectivity hypothesis** on distinct powers `represent^n`. From this it derives:

- **Non-termination of the regress** as morphism-inequality across stages (`Regress`, `Basic`).
- **Lawvere’s fixed-point argument** in **`Type`** and a parallel packaging via **`MonoidalClosed (Type u)`** (`Lawvere`, `LawvereCCCType`).
- **Tagged disjointness** of “object slots” vs “endomorphism slots” (`OntologicalSlot`, `FixedPoints`) — a **disciplined syntactic** distinction, not a claim about external metaphysics.

**Honest limits:** Infinite regress across levels is **conditional** on `iter_injective`. The Lawvere theorem is proved in **`Type`**, not for an arbitrary abstract CCC in full generality.

### B. Topological strand (SPEC_002): Möbius strip vs closed cylinder

The project constructs two concrete **compact Hausdorff** models:

- **`ClosedCylinder`**: `Circle × Icc 0 1` with the standard product / boundary semantics (`CylinderBoundary`, `CylinderChartableBoundary`).
- **`MobiusStrip`**: quotient of the unit square `Icc 0 1 × Icc 0 1` by the **edge identification** `(0, t) ~ (1, 1-t)` (`CylinderMobius`).

The flagship **non-homeomorphism** claim is:

> **`mobiusStrip_not_homeomorphic_closedCylinder`** — there is **no** homeomorphism `MobiusStrip ≃ₜ ClosedCylinder`.

This theorem is **fully proved** (in `MobiusSeamChartableR2.lean`, importing the conditional bridge from `ChartableR2Bridge.lean`).

---

## 2. Method: `ChartableR2` and boundary “sensors”

**`ChartableR2` (`ChartableR2Neighbor`)** — a point `x` of a topological space **admits a planar chart** if some **open neighborhood** of `x` is homeomorphic to **`ℝ²`** (implemented as `EuclideanSpace ℝ (Fin 2)`).

**Boundary detection on the cylinder** is packaged as **`closedCylinder_boundaryUnion_iff_not_chartableR2`** (`CylinderChartableBoundary`): points on the **manifold boundary** are **exactly** the points that are **not** `ChartableR2`, using explicit **half-space (`H2`)** models near the two faces.

**On the Möbius strip**, the code defines **`mobiusStripBoundary`**: the quotient image of the **top and bottom edges** of the fundamental square (`t ∈ {0,1}`). It proves:

- **`not_chartableR2_of_mem_mobiusStripBoundary`** — boundary points are **not** `ChartableR2` (via `H2` collars and sequential stability).

The **converse direction** — *every non-boundary point **is** `ChartableR2`* — reduces (`MobiusChartableBoundary`) to proving:

> **`∀ p : MobiusFundamentalDomain, 0 < p.2.val < 1 → ChartableR2 (Quotient.mk mobiusSetoid p)`**

i.e. **every point at **interior height** admits a planar chart on the quotient.

That universal statement is the theorem **`chartableR2_mobiusQuotientMk_of_interior_height`** (`MobiusSeamChartableR2.lean`). Together with **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`**, it yields the Möbius-side **C4** biconditional parallel to the cylinder.

---

## 3. Why the seam (and especially `(0, ½)`) matters

Interior points with **`0 < x < 1`** in the fundamental square are handled with **one-sided saturated windows** and standard quotient plumbing (`MobiusChartableBoundary`).

**Vertical seam** representatives have **`x ∈ {0, 1}`** with **`0 < t < 1`**. Here the mathematics is subtler:

- A **trigonometric** coordinate system (`MobiusSeamChart`, `MobiusSeamTrigInject`) gives **injective** maps on seam patches when the vertical window satisfies **`δ < |t₀ - ½|`**. That **excludes** a **simultaneous** patch centered at **`t₀ = ½`** with nontrivial height width — so the **equator point** `⟦(0, ½)⟧` is **not** covered by that trig-only chart family in the same patch.

- The **equator case** is resolved by a **different explicit chart**: a **piecewise-linear “unfolding” map** on the fundamental domain, constant on **`mobiusRel₀`**, lifted to the quotient, paired with a **piecewise section** from a Euclidean ball. Continuity of the inverse on the relevant quotient neighborhood uses a **quotient-descent** lemma (**`continuous_quotientLift_unfold_on_saturatedImage`** — private helper in `MobiusSeamChartableR2.lean`).

**Right edge** charts are also packaged (`chartableR2_mobiusQuotientMk_of_right_seam`).

**Net effect:** **all** fundamental-domain points with **`0 < t < 1`** are covered, including seam and equator.

---

## 4. Closing M-FINAL: where the contradiction enters

Even if a global homeomorphism `MobiusStrip ≃ₜ ClosedCylinder` existed, it would restrict to a homeomorphism between the respective **boundary subspaces**. The library proves **`mobiusStripBoundary_not_homeomorphic_closedCylinderBoundaryUnion`** (`MobiusCylinderBoundaryContrast`): the Möbius **boundary band is connected**, while the closed cylinder’s **boundary union is disconnected** (two disjoint circles).

With **C4** on both sides (`ChartableR2Bridge`), such a global homeomorphism would also force **compatibility** of “boundary points” as detected by **`ChartableR2`**, hence yield a homeomorphism of boundary subspaces — contradiction.

So **M-FINAL** is **not** a separate geometric argument; it is the **contradiction packaging** of:

1. Boundary subspaces **not** homeomorphic, and  
2. Consistent **`ChartableR2`** classification of interior vs boundary on both models.

---

## 5. What this artifact is *not*

- **Not phenomenology:** No formalized “what it is like” or first-person premises.  
- **Not general philosophy of mathematics:** `OntologicalSlot` is a **technical tag** for formal distinctness, not an argument against metaphysical monism.  
- **Not a complete differential-topology textbook:** Manifold-with-boundary polish for `MobiusStrip` as a **`IsManifold`** instance is **out of scope** for the current punchline (see `THEOREM_INVENTORY.md` “open” row for that optional extension).  
- **Not uniqueness of proof:** An alternative track (**Route W** in `CylinderMobiusNonhomeo.lean`) explores circle/winding obstructions; it is **not** required for the proved M-FINAL theorem.

---

## 6. Suggested citation strings

- **Regress / Lawvere package:** `RepresentationalRegress.representational_regress_master` and modules `Basic`, `Regress`, `Lawvere`.  
- **Möbius vs cylinder:** `RepresentationalRegress.mobiusStrip_not_homeomorphic_closedCylinder`.  
- **Interior charts:** `RepresentationalRegress.chartableR2_mobiusQuotientMk_of_interior_height`.  
- **Cylinder boundary sensor:** `RepresentationalRegress.closedCylinder_boundaryUnion_iff_not_chartableR2`.  
- **Möbius boundary sensor (conditional packaging):** `RepresentationalRegress.mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`.

For a full Lean name index, use **`THEOREM_INVENTORY.md`**.
