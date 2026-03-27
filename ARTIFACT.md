# representational-incompleteness-lean — artifact documentation

**Lean:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` — use **`lake exe cache get`** after `lake update`  
**Build:** `lake build RepresentationalIncompleteness` from this directory (`RepresentationalIncompleteness/` has **0** `sorry`)  
**Lake deps:** Mathlib only (`lakefile.lean`, `lake-manifest.json`)  
**Workspace handoff:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`  
**Topology punchline (Möbius vs cylinder):** `../specs/IN-PROCESS/SPEC_002_K7P_TOPOLOGY_PUNCHLINE_AND_PAPER.md`

---

## M-FINAL (closed)

**Theorem:** **`mobiusStrip_not_homeomorphic_closedCylinder`** — `IsEmpty (MobiusStrip ≃ₜ ClosedCylinder)` (**`MobiusSeamChartableR2`**, instantiating **`ChartableR2Bridge`**). **Spine:** cylinder **C4** vs Möbius interior **`ChartableR2`** (**`chartableR2_mobiusQuotientMk_of_interior_height`**, including seam + equator charts) → boundary biconditional → contradiction with boundary-subspace contrast. **MANIFEST.md** / **`docs/ADVISOR_OVERVIEW.md`** summarize the dependency graph. **Route W** in **`CylinderMobiusNonhomeo`** remains an optional cross-check.

---

## What this artifact aims to prove

Machine-checked renditions of:

1. A representational “awareness-of-awareness” story, encoded as a category with an endomorphism on an awareness object (`RepresentationalSystem`).

2. A non-terminating regress of meta-levels as **iterated morphisms** `represent^n` (`metaRegressArrow` / `metaRepresent`, `Regress`).

3. Fixed-point phenomena that do **not** identify morphisms with objects (`FixedPoints`), plus Lawvere’s theorem in **`Type`** (`Lawvere.lean`).

4. Orientability / invariance claims aligned to mathlib once the geometric interface is chosen (`Orientability`).

5. **No-escape horn closures** (`NoEscapeClosure`): iterate collision ⇒ bounded distinct powers; section--retraction readout ⇒ idempotent loop on host, blocking injective ℕ-towers on both source and host objects.

6. **Diagonal-exclusion and decidable Lawvere** (`LawvereRegressBridge`): partial self-models necessarily miss their own diagonal (`lawvere_diagonal_not_in_range`); no universal evaluator into `Bool` (`no_universal_parametric_unary_bool`) — decidable/computability analogue.

Explicitly **not** in scope for Lean: phenomenological immediacy premises, philosophical bridge to non-orientable identity structure.

---

## Reproduction

```bash
cd representational-incompleteness-lean
lake update
lake exe cache get
lake build
```

One-shot from workspace root: `scripts/verify-lean-build.sh`.

---

## Key theorem summary

See `THEOREM_INVENTORY.md`, `MANIFEST.md`, and **`docs/ADVISOR_OVERVIEW.md`** (advisor-facing narrative). Topology punchline: **SPEC_002** / **M-FINAL** above.
