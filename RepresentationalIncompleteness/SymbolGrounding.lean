/-
  **Symbol grounding / semantic regress (paper-facing packaging).**

  Mathematically identical to `RepresentationalSystem`; this module exists so authors can
  cite **symbol-system** language without duplicating definitions. “Infinite regress of
  interpretation” is exactly **distinct** `metaRegressArrow` / `metaOver` stages.
-/

import RepresentationalIncompleteness.Basic

universe u

namespace RepresentationalIncompleteness

/-- Same structure as `RepresentationalSystem`; use when the intended reading is *symbols*,
  *interpretation*, or *grounding* rather than generic “awareness”. -/
abbrev SymbolSystem := RepresentationalSystem

theorem symbolGrounding_metaRegressArrow_injective (S : SymbolSystem.{u}) {n m : ℕ} (h : n ≠ m) :
    metaRegressArrow S n ≠ metaRegressArrow S m :=
  metaRegressArrow_injective S h

theorem symbolGrounding_metaOver_injective (S : SymbolSystem.{u}) {n m : ℕ} (h : n ≠ m) :
    metaOver S n ≠ metaOver S m :=
  metaOver_injective S h

theorem symbolGrounding_no_slot_collapse (S : SymbolSystem.{u}) (n : ℕ) (c : S.C) :
    OntologicalSlot.endo (metaRegressArrow S n) ≠ OntologicalSlot.obj c :=
  OntologicalSlot.no_slot_collapse S n c

end RepresentationalIncompleteness
