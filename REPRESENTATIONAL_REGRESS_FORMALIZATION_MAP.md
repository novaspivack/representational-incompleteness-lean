# Representational Regress — formalization map

**Purpose:** Module roles; pair with `MANIFEST.md` and `THEOREM_INVENTORY.md`.  
**Program spec:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`

---

## Module tree

| Path | Role |
|------|------|
| `RepresentationalRegress/Basic.lean` | `RepresentationalSystem`, `metaRepresent`, morphism/object sort separation (`HEq` lemmas) |
| `RepresentationalRegress/Regress.lean` | Regress injectivity + inexhaustibility |
| `RepresentationalRegress/FixedPoints.lean` | Cartesian closed / Lawvere-facing lemmas; fixed points vs hom-obj separation |
| `RepresentationalRegress/Orientability.lean` | Topological hooks; align to `Mathlib` orientability once chosen |
| `RepresentationalRegress/Main.lean` | Conditional master theorem |

---

## Mathlib anchors (planned)

| Topic | Mathlib entry points (to verify against pin) |
|-------|-----------------------------------------------|
| Categories | `Mathlib.CategoryTheory.Category.Basic` |
| Endomorphisms | `Mathlib.CategoryTheory.Endomorphism` |
| CCC / Lawvere | `Mathlib.CategoryTheory.Closed.Cartesian`, limits/shapes around fixed points |
| Topology | `Mathlib.Topology.Basic`, `Mathlib.Topology.Homotopy.*`, manifold orientability modules |

---

## Notes

- Coinductive `RegressChain` from the prose spec may replace `ℕ → R.C` if ergonomics improve; keep one mathematical story.
- Avoid stating `f ≠ x` for `f : X ⟶ X` and `x : C` — use `¬ HEq` or reformulate with a typed partial map / family.
