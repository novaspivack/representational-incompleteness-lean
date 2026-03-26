# representational-regress-lean — artifact documentation

**Lean:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` — use **`lake exe cache get`** after `lake update`  
**Build:** `lake build RepresentationalRegress` from this directory (`RepresentationalRegress/` has no `sorry`)  
**Lake deps:** Mathlib only (`lakefile.lean`, `lake-manifest.json`)  
**Workspace handoff:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`

---

## What this artifact aims to prove

Machine-checked renditions of:

1. A representational “awareness-of-awareness” story, encoded as a category with an endomorphism on an awareness object (`RepresentationalSystem`).

2. A non-terminating regress of meta-levels as **iterated morphisms** `represent^n` (`metaRegressArrow` / `metaRepresent`, `Regress`).

3. Fixed-point phenomena that do **not** identify morphisms with objects (`FixedPoints`), plus Lawvere’s theorem in **`Type`** (`Lawvere.lean`).

4. Orientability / invariance claims aligned to mathlib once the geometric interface is chosen (`Orientability`).

Explicitly **not** in scope for Lean: phenomenological immediacy premises, philosophical bridge to non-orientable identity structure.

---

## Reproduction

```bash
cd representational-regress-lean
lake update
lake exe cache get
lake build
```

One-shot from workspace root: `scripts/verify-lean-build.sh`.

---

## Key theorem summary

See `THEOREM_INVENTORY.md` and `MANIFEST.md`.
