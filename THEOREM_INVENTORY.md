# Representational Regress — theorem inventory (Lean names)

**Last updated:** 2026-03-25 — scaffold from `SPEC_001_RR1`  
**Purpose:** Index of named `def`s / `theorem`s. Pair with `MANIFEST.md` + `REPRESENTATIONAL_REGRESS_FORMALIZATION_MAP.md`.

---

## Meta

| Module | Coverage |
|--------|----------|
| `Basic` | `RepresentationalSystem`, `metaRepresent`, `morphism_obj_not_heq` |
| `Regress` | `regress_no_termination`, `regress_is_infinite` |
| `FixedPoints` | `fixed_point_preserves_distinction`, `lawvere_wall_is_not_dissolution` |
| `Orientability` | `orientability_is_homeomorphism_invariant_stub`, `continuous_deformation_preserves_orientability_stub` |
| `Main` | `representational_regress_master` |

---

## Basic

| Kind | Lean name | Status |
|------|-----------|--------|
| `structure` | `RepresentationalSystem` | defined |
| `def` | `metaRepresent` | `sorry` in `n+1` case |
| `theorem` | `morphism_obj_not_heq` | `sorry` |

## Regress

| Kind | Lean name | Status |
|------|-----------|--------|
| `theorem` | `regress_no_termination` | `sorry` |
| `theorem` | `regress_is_infinite` | proved (trivial witness) |

## Fixed points

| Kind | Lean name | Status |
|------|-----------|--------|
| `theorem` | `fixed_point_preserves_distinction` | trivial stub |
| `theorem` | `lawvere_wall_is_not_dissolution` | `sorry` |

## Orientability

| Kind | Lean name | Status |
|------|-----------|--------|
| `theorem` | `orientability_is_homeomorphism_invariant_stub` | trivial stub |
| `theorem` | `continuous_deformation_preserves_orientability_stub` | trivial stub |

## Main

| Kind | Lean name | Status |
|------|-----------|--------|
| `theorem` | `representational_regress_master` | uses `lawvere_wall_is_not_dissolution` (`sorry` cascades) |

---

## Discharge order (from spec)

1. `morphism_obj_not_heq` / cross-sort discipline  
2. `metaRepresent` + `regress_no_termination`  
3. `lawvere_wall_is_not_dissolution`  
4. `fixed_point_preserves_distinction` against mathlib’s Lawvere API  
5. orientability lemmas once mathlib imports are fixed  
6. tighten `representational_regress_master` to eliminate dependency on `sorry` leaves  
