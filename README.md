# representational-incompleteness-lean


## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Representational Incompleteness (§B5c): no parametric self-model covers its own diagonal; six no-escape routes closed as theorems.

| Link | Description |
|------|-------------|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#b5c-representational-incompleteness) | Complete abstract for this library's papers |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.19429270) | Citable DOI hub for the NEMS program |

All results are machine-checked in Lean 4 with a zero-sorry policy on proof targets.
See [MANIFEST.md](MANIFEST.md) for the sorry audit (if present).

---

Formal verification of the representational regress argument in the philosophy of mind.

## What this proves

This library targets a Lean 4 + Mathlib proof that:

1. In category-theoretic settings, the object/morphism sorts are not collapsed; cross-sort identifications are ruled out via the appropriate formalization (`Basic`, `FixedPoints`).

2. A representational setup yields a non-terminating ascent of meta-levels **as iterated morphisms** `represent^n` (`metaRegressArrow` / `metaRepresent`) and corresponding **slice** objects `metaOver n` — **provided** the bundled hypothesis `iter_injective` holds (`Regress`).

3. Fixed-point phenomena: injective **currying** in monoidal closed categories (`FixedPoints`); Lawvere’s **diagonal fixed-point theorem in `Type`** (`Lawvere.lean`); and a tagged lemma that the representational arrow does not “become” an arbitrary object witness in `OntologicalSlot`.

4. Topology: **Hausdorff (T₂)** is preserved by homeomorphisms (`Orientability`). `CylinderMobius.lean` defines an open cylinder and a Möbius quotient model; `CylinderBoundary.lean` proves the **closed** cylinder’s **manifold boundary** is **two disjoint connected** faces. **Proving** the Möbius model is not homeomorphic to either cylinder (or formal manifold orientability on the quotient) is still open.

## What this does not prove

The phenomenological datum — that awareness-of-awareness terminates immediately in experience — is outside proof assistants.

The bridge inference to a non-orientable identity structure (distinct from the representational layer) is philosophical.

The full argument has the shape:

- **(A)** If awareness-of-awareness is representational, then it generates a non-terminating chain. **(Target of this repo.)**
- **(B)** Awareness-of-awareness terminates immediately. **(Phenomenology.)**
- **(C)** Therefore it is not representational. **(Modus tollens, needs B.)**
- **(D)** Therefore consciousness has non-orientable topological structure at the identity pole. **(Bridge; philosophical.)**

## Reference

Spivack, N. *The Figure Without Ground: AI, Consciousness, and the Topology of Mind.* novaspivack.com

Lawvere (1969): “Diagonal arguments and cartesian closed categories”; Mathlib4 hosts the CCC machinery used here.

## Build

**Use the Mathlib binary cache** — do not compile all of Mathlib from source:

```bash
lake update              # resolve deps → exact mathlib revision
lake exe cache get       # REQUIRED: download pre-built .olean blobs (GitHub source ≠ binaries)
lake build RepresentationalIncompleteness   # default library target; only this repo + uncached leaves
```

If `lake build` starts compiling thousands of `Mathlib.*` files, you skipped `cache get`, hit a cache miss for an untagged mathlib rev, or removed `~/.cache/mathlib/`. Fix: run `lake exe cache get` again; keep `lakefile.lean` on a **tagged** mathlib release (as pinned) so the community cache always has artifacts.

Workspace documentation: `../docs/lean_mathlib_cache_workflow.md`, `../docs/optional_mathlib.md`.

## Structure

- `RepresentationalIncompleteness/Basic.lean` — core definitions (`iter_injective`, iterates, `Over A`)
- `RepresentationalIncompleteness/Regress.lean` — regress chain theorems
- `RepresentationalIncompleteness/FixedPoints.lean` — curry/uncurry injectivity; `OntologicalSlot` “wall”
- `RepresentationalIncompleteness/Lawvere.lean` — Lawvere fixed-point theorem in `Type`
- `RepresentationalIncompleteness/Orientability.lean` — T₂ and homeomorphisms
- `RepresentationalIncompleteness/CylinderMobius.lean` — cylinder vs Möbius definitions  
- `RepresentationalIncompleteness/CylinderBoundary.lean` — closed cylinder boundary (two faces)
- `RepresentationalIncompleteness/Main.lean` — master conditional theorem
- `docs/argument-structure.md` — plain-language map

See also `MANIFEST.md`, `THEOREM_INVENTORY.md`, `REPRESENTATIONAL_INCOMPLETENESS_FORMALIZATION_MAP.md`, `ARTIFACT.md`.
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429237
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
