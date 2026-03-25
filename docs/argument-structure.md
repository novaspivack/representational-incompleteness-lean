# Argument structure (plain language)

This note tracks the formal modules in `RepresentationalRegress/` against the philosophical argument. Detailed obligations live in `specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md` (outer workspace).

## `Basic.lean`

- Introduces a category with a distinguished awareness object and a self-representation endomorphism.
- Separates morphisms and objects at the level of Lean’s typing discipline; cross-sort claims use `HEq`/`¬ HEq`, not raw inequality between a hom and an object.

## `Regress.lean`

- Formalizes the idea that each meta-level of representation targets a new object-level node in the tower (`metaRepresent`).
- States injectivity of levels (distinct `ℕ` indices imply distinct objects) and inexhaustibility (no finite bound contains the whole tower).

## `FixedPoints.lean`

- Imports cartesian closed machinery suitable for Lawvere’s fixed-point theorem.
- States that fixed-point data remains *on the object side* of the ontology: morphisms are not identified with objects, even when fixed-point equations hold in the internal language of the category.

## `Orientability.lean`

- Placeholder bridge to mathlib’s orientability story (likely manifold-based). Goal: relate homotopy/homeomorphism invariance to the philosophical claim that “internal elaboration” cannot cross from orientable to non-orientable structure without a discontinuous cut.

## `Main.lean`

- Bundles the conditional: representational meta-awareness yields inexhaustible level growth; morphism/object distinction persists at fixed points; topological lemmas slot in once the mathlib-facing statements are pinned.

## Outside Lean

Claims (B)–(D) in `README.md` require phenomenology and philosophical inference; they are documented but not machine-checked.
