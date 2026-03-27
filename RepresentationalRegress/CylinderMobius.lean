/-
  Comparative geometry for the philosophical “cylinder vs Möbius” contrast.

  * **OpenCylinder:** `UnitAddCircle × Ioo (0:ℝ) 1` — Hausdorff (hence T₂), product topology.
  * **MobiusStrip:** quotient of the **closed square** `Icc 0 1 × Icc 0 1` identifying `(0, t)`
    with `(1, 1 - t)` along the two vertical edges.

  **New relative to the earliest scaffold:** `mobiusRel₀` is proved a genuine **equivalence**
  (so the inductive `mobiusRelTrans` layer is unnecessary), the equivalence **graph is closed**
  in the compact Hausdorff square, `MobiusStrip` is **compact**, and the projected **edge
  boundary** (the `t = 0` and `t = 1` sides) is **connected** (one circle after glueing).

  **Still open (full formalism, known classical math):**

  * **`T2Space MobiusStrip`:** **Yes** — `instT2SpaceMobiusStrip` via
    `t2Space_quotient_of_isClosed_graph mobiusRel₀Graph_isClosed` (`QuotientHausdorff.lean`). **Do not**
    expect `IsOpenQuotientMap` for `Quotient.mk mobiusSetoid`: the quotient map need not be open (small
    opens touching only `x = 0` can glue partners on `x = 1`, and metric thickenings of a class need
    not be saturated without extra shrinking).
    `mobiusQuot_mk_preimage_image` is the set-theoretic saturation identity.

  * **`IsManifold` with boundary on `MobiusStrip`:** Requires boundary charts (_corners / seam smoothing in
    the formal sense_). Comparable to, but more awkward than, `CylinderBoundary`’s product manifold; often
    **several days to a couple of weeks** depending on chart bookkeeping and Mathlib’s manifold API surface.

  * **`¬ Nonempty (MobiusStrip ≃ₜ ClosedCylinder)`:** Short **mathematically** (boundary component count or
    orientability). **Formally heavy** until intrinsic **boundary** is tied to `ModelWithCorners.boundary`
    and **homeomorphism invariance** for boundary components exists in convenient form—can be **weeks** if
    built from first principles rather than reusing emerging Mathlib lemmas.
-/

import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Separation.Hausdorff

import RepresentationalRegress.QuotientHausdorff

noncomputable section

open scoped Topology

namespace RepresentationalRegress

open Set

/-- Open cylinder `S¹ × (0,1)` (unit additive circle × open interval). -/
abbrev OpenCylinder :=
  UnitAddCircle × Ioo (0 : ℝ) 1

instance : TopologicalSpace OpenCylinder := inferInstance

instance : T2Space OpenCylinder := inferInstance

/-- Fundamental domain: compact unit square with the subspace topology. -/
abbrev MobiusFundamentalDomain :=
  Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1

instance : TopologicalSpace MobiusFundamentalDomain := inferInstance

instance : CompactSpace MobiusFundamentalDomain := inferInstance

instance : T2Space MobiusFundamentalDomain := inferInstance

/-- The generating binary relation for the Möbius edge glueing (before closure). -/
def mobiusGlueStep (p q : MobiusFundamentalDomain) : Prop :=
  (p.1.val = 0 ∧ q.1.val = 1 ∧ p.2.val + q.2.val = 1) ∨
    (q.1.val = 0 ∧ p.1.val = 1 ∧ p.2.val + q.2.val = 1)

/-- Edge identification + reflexive closure step `r` (already an equivalence — see below). -/
def mobiusRel₀ (p q : MobiusFundamentalDomain) : Prop :=
  p = q ∨ mobiusGlueStep p q

/-- The Möbius relation is symmetric. -/
theorem mobiusRel₀.symm {p q : MobiusFundamentalDomain} (h : mobiusRel₀ p q) : mobiusRel₀ q p := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · rcases h with h | h
    · exact Or.inr (Or.inr ⟨h.1, h.2.1, by rw [add_comm]; exact h.2.2⟩)
    · exact Or.inr (Or.inl ⟨h.1, h.2.1, by rw [add_comm]; exact h.2.2⟩)

theorem mobiusRel₀.trans {x y z : MobiusFundamentalDomain} (hxy : mobiusRel₀ x y) (hyz : mobiusRel₀ y z) :
    mobiusRel₀ x z := by
  rcases hxy with rfl | hxy <;> rcases hyz with rfl | hyz <;> try exact Or.inl rfl
  · exact Or.inr hyz
  · exact Or.inr hxy
  · rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
    · -- `y.1` cannot be both `1` (first seam) and `0` (first seam).
      exfalso
      have : (1 : ℝ) = 0 := hxy.2.1.symm.trans hyz.1
      linarith
    · refine Or.inl (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · rw [hxy.1, hyz.1]
      · linarith [hxy.2.2, hyz.2.2]
    · refine Or.inl (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · rw [hxy.2.1, hyz.2.1]
      · linarith [hxy.2.2, hyz.2.2]
    · -- `y.1` cannot be both `0` and `1`.
      exfalso
      have : (0 : ℝ) = 1 := hxy.1.symm.trans hyz.2.1
      linarith

theorem mobiusRel₀.equivalence : Equivalence mobiusRel₀ :=
  ⟨fun _ => Or.inl rfl, fun {_ _} h => mobiusRel₀.symm h, fun {_ _ _} h₁ h₂ => mobiusRel₀.trans h₁ h₂⟩

/-- The closed subset of `M × M` describing the two explicit glueing seams. -/
def mobiusGlueSeamSet : Set (MobiusFundamentalDomain × MobiusFundamentalDomain) :=
  {pq | pq.1.1.val = 0 ∧ pq.2.1.val = 1 ∧ pq.1.2.val + pq.2.2.val = 1} ∪
  {pq | pq.2.1.val = 0 ∧ pq.1.1.val = 1 ∧ pq.1.2.val + pq.2.2.val = 1}

theorem mobiusGlueSeamSet_isClosed : IsClosed mobiusGlueSeamSet := by
  let seamLo :=
    ({pq : MobiusFundamentalDomain × MobiusFundamentalDomain | pq.1.1.val = 0} ∩
        {pq | pq.2.1.val = 1}) ∩ {pq | pq.1.2.val + pq.2.2.val = 1}
  let seamHi :=
    ({pq : MobiusFundamentalDomain × MobiusFundamentalDomain | pq.2.1.val = 0} ∩
        {pq | pq.1.1.val = 1}) ∩ {pq | pq.1.2.val + pq.2.2.val = 1}
  have hfstfstval : Continuous fun (pq : MobiusFundamentalDomain × MobiusFundamentalDomain) =>
      pq.1.1.val :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hfstsndval : Continuous fun pq : MobiusFundamentalDomain × MobiusFundamentalDomain =>
      pq.1.2.val :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hsndfstval : Continuous fun pq : MobiusFundamentalDomain × MobiusFundamentalDomain =>
      pq.2.1.val :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hsndsndval : Continuous fun pq : MobiusFundamentalDomain × MobiusFundamentalDomain =>
      pq.2.2.val :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hsum : Continuous fun pq : MobiusFundamentalDomain × MobiusFundamentalDomain =>
      pq.1.2.val + pq.2.2.val :=
    hfstsndval.add hsndsndval
  have hLo : IsClosed seamLo := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_singleton.preimage hfstfstval
    · exact isClosed_singleton.preimage hsndfstval
    · exact isClosed_singleton.preimage hsum
  have hHi : IsClosed seamHi := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_singleton.preimage hsndfstval
    · exact isClosed_singleton.preimage hfstfstval
    · exact isClosed_singleton.preimage hsum
  convert IsClosed.union hLo hHi using 1
  ext pq
  simp only [mobiusGlueSeamSet, seamLo, seamHi, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq,
    and_assoc]

theorem mobiusRel₀Graph_eq :
    {pq : MobiusFundamentalDomain × MobiusFundamentalDomain | mobiusRel₀ pq.1 pq.2} =
    diagonal MobiusFundamentalDomain ∪ mobiusGlueSeamSet := by
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_union, mem_diagonal_iff, mobiusRel₀, mobiusGlueStep,
    mobiusGlueSeamSet, Set.mem_setOf_eq]

theorem mobiusRel₀Graph_isClosed :
    IsClosed {pq : MobiusFundamentalDomain × MobiusFundamentalDomain | mobiusRel₀ pq.1 pq.2} := by
  rw [mobiusRel₀Graph_eq]
  exact isClosed_diagonal.union mobiusGlueSeamSet_isClosed

/-- Setoid for the Möbius quotient (`mobiusRel₀` is already transitive). -/
def mobiusSetoid : Setoid MobiusFundamentalDomain where
  r := mobiusRel₀
  iseqv := mobiusRel₀.equivalence

/-- Topological Möbius strip (quotient of the fundamental domain). -/
abbrev MobiusStrip :=
  Quotient mobiusSetoid

instance : TopologicalSpace MobiusStrip :=
  inferInstanceAs (TopologicalSpace (Quotient mobiusSetoid))

instance : CompactSpace MobiusStrip :=
  inferInstance

instance instT2SpaceMobiusStrip : T2Space MobiusStrip :=
  t2Space_quotient_of_isClosed_graph (s := mobiusSetoid) mobiusRel₀Graph_isClosed

/-- Quotient projection (continuous by `coinduced`). -/
theorem continuous_mobiusQuot :
    Continuous (Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) :=
  continuous_quot_mk

/-! ### Quotient saturation (`π ⁻¹' (π '' U)`) — step toward an open quotient map -/

theorem mobiusQuot_mk_preimage_image (U : Set MobiusFundamentalDomain) :
    (Quotient.mk mobiusSetoid) ⁻¹'
        ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' U) =
      { q | ∃ p ∈ U, mobiusRel₀ p q } := by
  classical
  ext q
  simp only [mem_preimage, mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨p, hpU, he⟩
    exact ⟨p, hpU, Quotient.exact he⟩
  · rintro ⟨p, hpU, hr⟩
    exact ⟨p, hpU, Quotient.sound hr⟩

/-! ### Boundary of the square in the quotient (one circle) -/

/-- Closed `Icc 0 1 ⊂ ℝ` is compact connected; hence the subtype `Icc 0 1` is connected. -/
theorem isConnected_univ_Icc01 : IsConnected (univ : Set (Icc (0 : ℝ) 1)) := by
  have hIcc : IsConnected (Set.Icc (0 : ℝ) 1 : Set ℝ) := isConnected_Icc (by norm_num)
  haveI : ConnectedSpace (Icc (0 : ℝ) 1) := isConnected_iff_connectedSpace.mp hIcc
  exact isConnected_univ

/-- Canonical lower/upper endpoints in `Icc 0 1` (avoids ambiguous `⊥`/`⊤` across instances). -/
def mobiusIcc0 : Icc (0 : ℝ) 1 := ⟨(0 : ℝ), by norm_num, by norm_num⟩
def mobiusIcc1 : Icc (0 : ℝ) 1 := ⟨(1 : ℝ), by norm_num, by norm_num⟩

@[simp] theorem mobiusIcc0_val : mobiusIcc0.val = 0 := rfl
@[simp] theorem mobiusIcc1_val : mobiusIcc1.val = 1 := rfl

/-! ### Equivalence classes have size ≤ 2 (toward `T2Space MobiusStrip`)

Each `mobiusRel₀` class is either a singleton (off the vertical seams) or a pair across the glue.
Finiteness supports disjoint **saturated** opens in the compact metric square.
-/

/-- Reflect the vertical coordinate `t ↦ 1 - t` inside `Icc 0 1`. -/
def mobiusFlipHeight (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨(1 - t.val : ℝ), sub_nonneg.mpr t.2.2, sub_le_iff_le_add'.2 (by simpa using t.2.1)⟩

@[simp]
theorem mobiusFlipHeight_val (t : Icc (0 : ℝ) 1) : (mobiusFlipHeight t).val = 1 - t.val :=
  rfl

theorem mobiusFlipHeight_involutive (t : Icc (0 : ℝ) 1) : mobiusFlipHeight (mobiusFlipHeight t) = t := by
  refine Subtype.ext ?_
  simp only [mobiusFlipHeight_val]
  ring

/-- Nontrivial seam partner on the opposite vertical edge, if `p` lies on `x = 0` or `x = 1`. -/
def mobiusSeamPartner (p : MobiusFundamentalDomain) : Option MobiusFundamentalDomain :=
  if _ : p.1.val = 0 then
    some (mobiusIcc1, mobiusFlipHeight p.2)
  else if _ : p.1.val = 1 then
    some (mobiusIcc0, mobiusFlipHeight p.2)
  else
    none

theorem mobiusSeamPartner_eq_none_iff (p : MobiusFundamentalDomain) :
    mobiusSeamPartner p = none ↔ p.1.val ≠ 0 ∧ p.1.val ≠ 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hp0; simp [mobiusSeamPartner, hp0, Option.some_ne_none] at h
    · intro hp1; simp [mobiusSeamPartner, hp1, Option.some_ne_none] at h
  · rintro ⟨hn0, hn1⟩
    dsimp [mobiusSeamPartner]
    split_ifs <;> simp_all

theorem mobiusSeamPartner_involutive {p q : MobiusFundamentalDomain}
    (h : mobiusSeamPartner p = some q) : mobiusSeamPartner q = some p := by
  by_cases hp0 : p.1.val = 0
  · have hs : some (mobiusIcc1, mobiusFlipHeight p.2) = some q := by
      simpa [mobiusSeamPartner, hp0] using h
    have hq : q = (mobiusIcc1, mobiusFlipHeight p.2) := Option.some.inj hs.symm
    rw [hq]
    have hx : p.1 = mobiusIcc0 := Subtype.ext hp0
    conv_rhs => rw [show p = (mobiusIcc0, p.2) from Prod.ext hx rfl]
    simp [mobiusSeamPartner, mobiusIcc1_val, mobiusFlipHeight_involutive]
  · by_cases hp1 : p.1.val = 1
    · have hs : some (mobiusIcc0, mobiusFlipHeight p.2) = some q := by
        simpa [mobiusSeamPartner, hp0, hp1] using h
      have hq : q = (mobiusIcc0, mobiusFlipHeight p.2) := Option.some.inj hs.symm
      rw [hq]
      have hx : p.1 = mobiusIcc1 := Subtype.ext hp1
      conv_rhs => rw [show p = (mobiusIcc1, p.2) from Prod.ext hx rfl]
      simp [mobiusSeamPartner, mobiusIcc0_val, mobiusFlipHeight_involutive]
    · simp [mobiusSeamPartner, hp0, hp1] at h

/-- Underlying `{ q // mobiusRel₀ p q }` (a set of **at most two** points). -/
def mobiusClass (p : MobiusFundamentalDomain) : Set MobiusFundamentalDomain :=
  { q | mobiusRel₀ p q }

/-- Off the vertical seams `x ∈ {0, 1}`, nontrivial `mobiusGlueStep` is impossible, so the class is a
  singleton. Used for one-sided seam windows (`0 < x < 1` on a single Euclidean sheet) where
  `π ⁻¹' (π '' W) = W` and hence `π '' W` is open without enlarging `W` through glue partners. -/
theorem mobiusClass_eq_singleton_of_Ioo_fx {p : MobiusFundamentalDomain}
    (h : 0 < p.1.val ∧ p.1.val < 1) : mobiusClass p = {p} := by
  ext q
  simp only [mobiusClass, mem_singleton_iff, Set.mem_setOf_eq, mobiusRel₀]
  constructor
  · intro hr
    rcases hr with rfl | hglue
    · rfl
    · rcases hglue with ⟨hp0, _, _⟩ | ⟨_, hp1, _⟩
      · rcases h with ⟨hgt, _⟩
        rw [hp0] at hgt
        exact False.elim (lt_irrefl (0 : ℝ) hgt)
      · rcases h with ⟨_, hlt⟩
        rw [hp1] at hlt
        exact False.elim (lt_irrefl (1 : ℝ) hlt)
  · intro heq
    subst heq
    exact Or.inl rfl

theorem mobiusClass_eq_orPair (p : MobiusFundamentalDomain) :
    mobiusClass p =
      insert p
        (match mobiusSeamPartner p with
         | none => ∅
         | some q => {q}) := by
  classical
  ext q
  simp only [mobiusClass, Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · intro hr
    rcases hr with rfl | hglue
    · exact Or.inl rfl
    · rcases hglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
      · have hs' : q.2.val = 1 - p.2.val := by linarith
        have hq : q = (mobiusIcc1, mobiusFlipHeight p.2) := by
          refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
          · simpa [mobiusIcc1_val] using hq1
          · simp [mobiusFlipHeight_val, hs']
        subst hq
        simp [mobiusSeamPartner, hp0]
      · have hq' : q = (mobiusIcc0, mobiusFlipHeight p.2) := by
          refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
          · simpa [mobiusIcc0_val] using hq0
          · simp [mobiusFlipHeight_val]; linarith
        subst hq'
        simp [mobiusSeamPartner, hp1]
  · rintro (rfl | hmem)
    · exact Or.inl rfl
    · rcases hsp : mobiusSeamPartner p with _ | q'
      · simp [hsp] at hmem
      · have heqr : q' = q := (Set.mem_singleton_iff.mp (by simpa [hsp] using hmem)).symm
        rw [heqr] at hsp
        have hb : p.1.val = 0 ∨ p.1.val = 1 := by
          by_contra hn
          push_neg at hn
          simp [mobiusSeamPartner, hn.1, hn.2] at hsp
        rcases hb with hp0 | hp1
        · have hs : some (mobiusIcc1, mobiusFlipHeight p.2) = some q := by
            simpa [mobiusSeamPartner, hp0] using hsp
          have hq : q = (mobiusIcc1, mobiusFlipHeight p.2) := Option.some.inj hs.symm
          rw [hq]
          simp [mobiusRel₀, mobiusGlueStep, hp0, mobiusIcc1_val, mobiusFlipHeight_val]
        · have hs : some (mobiusIcc0, mobiusFlipHeight p.2) = some q := by
            simpa [mobiusSeamPartner, hp1] using hsp
          have hq : q = (mobiusIcc0, mobiusFlipHeight p.2) := Option.some.inj hs.symm
          rw [hq]
          simp [mobiusRel₀, mobiusGlueStep, mobiusIcc0_val, hp1, mobiusFlipHeight_val]

theorem mobiusClass_finite (p : MobiusFundamentalDomain) : (mobiusClass p).Finite := by
  rw [mobiusClass_eq_orPair p]
  rcases h : mobiusSeamPartner p with _ | q'
  · dsimp only
    rw [insert_empty_eq]
    exact finite_singleton p
  · dsimp only
    exact Set.Finite.insert p (finite_singleton q')

theorem isClosed_mobiusClass (p : MobiusFundamentalDomain) : IsClosed (mobiusClass p) :=
  (mobiusClass_finite p).isClosed

/-- Bottom edge `S × {0}` in the fundamental domain. -/
def mobiusBotEdge : Set MobiusFundamentalDomain :=
  (univ : Set (Icc (0 : ℝ) 1)) ×ˢ {mobiusIcc0}

/-- Top edge `S × {1}`. -/
def mobiusTopEdge : Set MobiusFundamentalDomain :=
  (univ : Set (Icc (0 : ℝ) 1)) ×ˢ {mobiusIcc1}

/-- Boundary of the usual Möbius strip model: union of the two horizontal edges, viewed in the quotient.
-/
def mobiusStripBoundary : Set MobiusStrip :=
  Quotient.mk mobiusSetoid '' (mobiusBotEdge ∪ mobiusTopEdge)

theorem isConnected_mobiusBotEdge : IsConnected mobiusBotEdge := by
  simpa [mobiusBotEdge] using
    isConnected_univ_Icc01.prod (isConnected_singleton (x := mobiusIcc0))

theorem isConnected_mobiusTopEdge : IsConnected mobiusTopEdge := by
  simpa [mobiusTopEdge] using
    isConnected_univ_Icc01.prod (isConnected_singleton (x := mobiusIcc1))

theorem Quotient_mk_mem_mobiusStripBoundary_iff (p : MobiusFundamentalDomain) :
    Quotient.mk mobiusSetoid p ∈ mobiusStripBoundary ↔ p.2 = mobiusIcc0 ∨ p.2 = mobiusIcc1 := by
  classical
  constructor
  · intro hx
    rw [mobiusStripBoundary, mem_image] at hx
    rcases hx with ⟨q, hq, he⟩
    have hr : mobiusRel₀ p q := mobiusRel₀.symm (Quotient.exact he)
    rcases hq with hqbot | hqtop
    · rw [mobiusBotEdge, mem_prod, mem_singleton_iff] at hqbot
      rcases hqbot with ⟨_, hq2⟩
      have q2 : q.2.val = 0 := by rw [hq2, mobiusIcc0_val]
      rcases hr with h | hrglue
      · rw [← h] at hq2
        exact Or.inl hq2
      · rcases hrglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
        · rw [q2, add_zero] at hs
          exact Or.inr (Subtype.ext hs)
        · rw [q2, add_zero] at hs
          exact Or.inr (Subtype.ext hs)
    · rw [mobiusTopEdge, mem_prod, mem_singleton_iff] at hqtop
      rcases hqtop with ⟨_, hq2⟩
      have q2 : q.2.val = 1 := by rw [hq2, mobiusIcc1_val]
      rcases hr with h | hrglue
      · rw [← h] at hq2
        exact Or.inr hq2
      · rcases hrglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
        · rw [q2] at hs
          have hpv : p.2.val = 0 := by linarith [hs]
          exact Or.inl (Subtype.ext hpv)
        · rw [q2] at hs
          have hpv : p.2.val = 0 := by linarith [hs]
          exact Or.inl (Subtype.ext hpv)
  · rintro (h2 | h2)
    · refine mem_image_of_mem (Quotient.mk mobiusSetoid) (Or.inl ⟨mem_univ p.1, ?_⟩)
      rwa [mem_singleton_iff]
    · refine mem_image_of_mem (Quotient.mk mobiusSetoid) (Or.inr ⟨mem_univ p.1, ?_⟩)
      rwa [mem_singleton_iff]

theorem isConnected_mobiusStripBoundary : IsConnected mobiusStripBoundary := by
  let π := Quotient.mk mobiusSetoid
  have hπ : Continuous π := continuous_quot_mk
  have hBot : IsConnected (π '' mobiusBotEdge) :=
    IsConnected.image isConnected_mobiusBotEdge _ hπ.continuousOn
  have hTop : IsConnected (π '' mobiusTopEdge) :=
    IsConnected.image isConnected_mobiusTopEdge _ hπ.continuousOn
  let p00 : MobiusFundamentalDomain := (mobiusIcc0, mobiusIcc0)
  let p11 : MobiusFundamentalDomain := (mobiusIcc1, mobiusIcc1)
  have hrel : mobiusSetoid.r p00 p11 := by
    refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
    · rfl
    · rfl
    · dsimp only [p00, p11]
      simp [mobiusIcc0_val, mobiusIcc1_val]
  have hp0 : p00 ∈ mobiusBotEdge :=
    ⟨mem_univ _, (mem_singleton_iff).2 rfl⟩
  have hp1 : p11 ∈ mobiusTopEdge :=
    ⟨mem_univ _, (mem_singleton_iff).2 rfl⟩
  have heq : π p00 = π p11 := Quotient.sound hrel
  have hInt : (π '' mobiusBotEdge ∩ π '' mobiusTopEdge).Nonempty := by
    use π p00
    constructor
    · exact ⟨p00, hp0, rfl⟩
    · rw [heq]
      exact ⟨p11, hp1, rfl⟩
  rw [mobiusStripBoundary, image_union]
  exact IsConnected.union hInt hBot hTop

end RepresentationalRegress

end
