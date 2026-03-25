# representational-regress-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` (via `lakefile.lean`); use `lake exe cache get`  
**Build:** `lake build` from this directory  
**Root import:** `RepresentationalRegress.lean`  
**Formalization map:** `REPRESENTATIONAL_REGRESS_FORMALIZATION_MAP.md`  
**Theorem inventory:** `THEOREM_INVENTORY.md`  
**Program spec:** `../specs/IN-PROCESS/SPEC_001_RR1_REPRESENTATIONAL_REGRESS_LEAN_EPIC.md`  
**Last verified:** — (run `lake build` after `lake update && lake exe cache get`)

---

## Layout

| Area | Path | Role |
|------|------|------|
| Core definitions | `RepresentationalRegress/Basic.lean` | `RepresentationalSystem`, `metaRepresent` scaffold, cross-sort lemma hooks |
| Regress | `RepresentationalRegress/Regress.lean` | `regress_no_termination`, `regress_is_infinite` |
| Fixed points | `RepresentationalRegress/FixedPoints.lean` | CCC / Lawvere layer, `lawvere_wall_is_not_dissolution` |
| Orientability | `RepresentationalRegress/Orientability.lean` | Topological stubs pending mathlib API choice |
| Assembly | `RepresentationalRegress/Main.lean` | `representational_regress_master` |

---

## Proof status

Scaffold: `sorry` remain where noted; see `THEOREM_INVENTORY.md` and the IN-PROCESS spec for discharge order.

---

## See also

- `ARTIFACT.md` — citation / reproduction  
- `../docs/submodule_workspace.md` — outer / inner git layout  
- `../docs/lean_mathlib_cache_workflow.md` — Mathlib cache workflow  
