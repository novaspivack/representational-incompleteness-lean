/-
  Hausdorff quotients of compact Hausdorff spaces when the equivalence graph is closed.

  Classical fact (Bourbaki): if `X` is compact T₂ and `R ⊆ X × X` is a closed equivalence
  relation, then `X / R` is Hausdorff.

  Proof sketch (as formalized):
  * `Quotient.mk` has closed fibers (projection of a closed subset of `X × X`) and is a closed map
    (saturation of a closed set is the `Prod.fst`-image of a closed set in `X × X`).
  * Hence `Quotient.mk` is **proper** (`IsProperMap`).
  * `Prod.map (Quotient.mk s) (Quotient.mk s)` is proper, hence closed, so it sends the closed
    graph to a **closed** subset of `Y × Y`; that image is the diagonal, giving `T2Space (Quotient s)`.
-/

import Mathlib.Data.Set.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff

noncomputable section

open Set Topology

universe u

namespace RepresentationalRegress

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] {s : Setoid X}

/-- Equivalence class `{y | s.r x y}` is closed when the graph is closed. -/
theorem isClosed_setoid_class (hR : IsClosed {p : X × X | s.r p.1 p.2}) (x : X) :
    IsClosed {y : X | s.r x y} := by
  have :
      {y : X | s.r x y} =
        Prod.snd '' ({p : X × X | s.r p.1 p.2} ∩ ({x} ×ˢ univ)) := by
    ext y
    constructor
    · intro hr
      simp only [mem_setOf_eq] at hr
      exact ⟨(x, y), ⟨⟨hr, rfl, trivial⟩, rfl⟩⟩
    · rintro ⟨⟨x', y'⟩, ⟨hgraph, hmem⟩, rfl⟩
      simp only [mem_prod, mem_singleton_iff, mem_univ, and_true] at hmem
      subst hmem
      simpa [mem_setOf_eq] using hgraph
  rw [this]
  exact (isClosedMap_snd_of_compactSpace : IsClosedMap (@Prod.snd X X)) _
    (hR.inter (isClosed_singleton.prod isClosed_univ))

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] in
theorem preimage_image_quotient_mk (s : Setoid X) (A : Set X) :
    Quotient.mk s ⁻¹' (Quotient.mk s '' A) =
      Prod.fst '' ({p : X × X | s.r p.1 p.2} ∩ (univ ×ˢ A)) := by
  classical
  ext x
  constructor
  · rintro ⟨a, haA, he⟩
    refine ⟨(x, a), ?_, rfl⟩
    refine ⟨?_, ⟨mem_univ _, haA⟩⟩
    simp only [mem_setOf_eq]
    exact Setoid.symm' s (Quotient.exact he)
  · rintro ⟨⟨x', y'⟩, h12, rfl⟩
    rcases h12 with ⟨hg, hp⟩
    simp only [mem_setOf_eq] at hg
    simp only [mem_prod, mem_univ, true_and] at hp
    exact ⟨y', hp, Eq.symm (@Quotient.sound X s x' y' hg)⟩

omit [T2Space X] in
theorem isClosedMap_quotient_mk_of_isClosed_graph (hR : IsClosed {p : X × X | s.r p.1 p.2}) :
    IsClosedMap (@Quotient.mk X s) := by
  intro A hA
  have hsat :
      IsClosed (Quotient.mk s ⁻¹' (Quotient.mk s '' A)) := by
    rw [preimage_image_quotient_mk]
    refine (isClosedMap_fst_of_compactSpace (Y := X)) _ (hR.inter (isClosed_univ.prod hA))
  exact (isQuotientMap_quotient_mk').isClosed_preimage.mp hsat

theorem isCompact_fiber_quotient_mk (hR : IsClosed {p : X × X | s.r p.1 p.2}) (q : Quotient s) :
    IsCompact (Quotient.mk s ⁻¹' {q}) := by
  induction q using Quotient.inductionOn with
  | h x =>
    have hcl : IsClosed (Quotient.mk s ⁻¹' {Quotient.mk s x}) := by
      convert isClosed_setoid_class hR x using 1
      ext y
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, Quotient.eq'']
      exact ⟨fun h => Setoid.symm' s h, fun h => Setoid.symm' s h⟩
    exact IsClosed.isCompact hcl

theorem isProperMap_quotient_mk_of_isClosed_graph (hR : IsClosed {p : X × X | s.r p.1 p.2}) :
    IsProperMap (@Quotient.mk X s) := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  exact ⟨continuous_quot_mk, isClosedMap_quotient_mk_of_isClosed_graph hR,
    isCompact_fiber_quotient_mk hR⟩

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] in
theorem image_setoid_graph_eq_diagonal :
    (Prod.map (Quotient.mk s) (Quotient.mk s)) '' {p : X × X | s.r p.1 p.2} =
      diagonal (Quotient s) := by
  classical
  ext ⟨qa, qb⟩
  simp only [mem_image, mem_diagonal_iff, mem_setOf_eq, Prod.exists, Prod.map_apply]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    exact @Quotient.sound X s x y hxy
  · intro h
    rcases h with rfl
    obtain ⟨x, hx⟩ := Quotient.exists_rep qa
    subst hx
    exact ⟨x, x, Setoid.refl' s x, rfl⟩

theorem t2Space_quotient_of_isClosed_graph (hR : IsClosed {p : X × X | s.r p.1 p.2}) :
    T2Space (Quotient s) := by
  let π := @Quotient.mk X s
  have hπ : IsProperMap π := isProperMap_quotient_mk_of_isClosed_graph hR
  have hππ : IsClosedMap (Prod.map π π) := hπ.prodMap hπ |>.isClosedMap
  rw [t2_iff_isClosed_diagonal]
  rw [← image_setoid_graph_eq_diagonal]
  exact hππ _ hR

end RepresentationalRegress

end
