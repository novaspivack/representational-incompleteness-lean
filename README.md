# representational-regress-lean

Formal verification of the representational regress argument in the philosophy of mind.

## What this proves

This library targets a Lean 4 + Mathlib proof that:

1. In category-theoretic settings, the object/morphism sorts are not collapsed; cross-sort identifications are ruled out via the appropriate formalization (`Basic`, `FixedPoints`).

2. A representational account of awareness-of-awareness yields a non-terminating ascent of meta-levels, modeled through `metaRepresent` and the regress theorems (`Regress`).

3. Fixed-point phenomena (Lawvere / cartesian closed structure) do not equate morphisms with objects; the “wall” is a limitation, not a dissolution of the arrow/node distinction (`FixedPoints`).

4. Topological orientability links (homeomorphism invariance, contrast with non-orientable models) will be wired to the correct mathlib manifold API (`Orientability` — see `SPEC_001_RR1` for the exact statements).

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

From this directory (after `lake update`):

```bash
lake exe cache get   # fetch pre-built Mathlib .olean artifacts
lake build
```

Workspace documentation: `../docs/lean_mathlib_cache_workflow.md`, `../docs/optional_mathlib.md`.

## Structure

- `RepresentationalRegress/Basic.lean` — core definitions
- `RepresentationalRegress/Regress.lean` — regress chain theorems
- `RepresentationalRegress/FixedPoints.lean` — Lawvere / fixed-point layer
- `RepresentationalRegress/Orientability.lean` — topological hooks
- `RepresentationalRegress/Main.lean` — master conditional theorem
- `docs/argument-structure.md` — plain-language map

See also `MANIFEST.md`, `THEOREM_INVENTORY.md`, `REPRESENTATIONAL_REGRESS_FORMALIZATION_MAP.md`, `ARTIFACT.md`.
