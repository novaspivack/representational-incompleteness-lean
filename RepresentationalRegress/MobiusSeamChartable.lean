/-
  **Vertical seam** neighborhood in the fundamental domain: left/right Euclidean sheets and
  `mobiusRel₀`-**saturation** (`mobiusSeamSaturatedPatch`).

  A saturated set `S` is one where `x ∈ S` and `x ~ y` implies `y ∈ S`; then
  `π '' S` is open in `MobiusStrip` (`MobiusChartableBoundary.isOpen_mobiusQuotient_image_of_saturated`).

  **Note.** The full set `mobiusSeamLeftPatch ∪ mobiusSeamRightPatch` is **saturated** under the patch
  hypotheses below, but it is strictly larger than the saturation of the left sheet alone (the right
  sheet contains points with `x < 1` that are not glued to any point on the left sheet), so one must
  not identify it with `π ⁻¹' (π '' mobiusSeamLeftPatch)` in general.

  Boundary **H2** packaging and **`mobiusStripBoundary → ¬ ChartableR2`** are in
  `MobiusChartableBoundary`. **Interior-sheet** seam quotient `ChartableR2` and supporting **`mobiusRel₀`**
  lemmas live in **`MobiusSeamChartableR2`** / here; **edges** `x ∈ {0,1}`, equator, and the converse
  **`¬ ChartableR2 → mobiusStripBoundary`** remain.
-/

import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

import RepresentationalRegress.CylinderMobius

noncomputable section

namespace RepresentationalRegress

open scoped Topology
open Set Topology Function

/-! ### Saturated Euclidean patch around a seam height -/

/-- Left sheet near `x = 0` (strict inequalities on `t`, and `x < ε`). -/
def mobiusSeamLeftPatch (t₀ ε δ : ℝ) : Set MobiusFundamentalDomain :=
  { p |
    p.1.val < ε ∧ 0 < p.2.val ∧ p.2.val < 1 ∧
      t₀ - δ < p.2.val ∧ p.2.val < t₀ + δ }

/-- If the height window stays **off** the equator (`δ < |t₀ - ½|`), no left-patch point has `t = ½`. -/
theorem ne_half_of_mem_mobiusSeamLeftPatch_of_delta {t₀ ε δ : ℝ}
    (hδ₂ : δ < |t₀ - (1 / 2 : ℝ)|) {p : MobiusFundamentalDomain}
    (hp : p ∈ mobiusSeamLeftPatch t₀ ε δ) : p.2.val ≠ (1 / 2 : ℝ) := by
  rcases hp with ⟨_, _, _, htLo, htHi⟩
  intro h12
  rw [h12] at htLo htHi
  have habs : |t₀ - (1 / 2 : ℝ)| ≤ δ := by
    rw [abs_sub_le_iff]
    constructor <;> linarith only [htLo, htHi]
  linarith only [hδ₂, habs]

/-- Right sheet near `x = 1` (strict inequalities on `t`, and `1 - ε < x`). -/
def mobiusSeamRightPatch (t₀ ε δ : ℝ) : Set MobiusFundamentalDomain :=
  { p |
    1 - ε < p.1.val ∧ 0 < p.2.val ∧ p.2.val < 1 ∧
      1 - t₀ - δ < p.2.val ∧ p.2.val < 1 - t₀ + δ }

def mobiusSeamSaturatedPatch (t₀ ε δ : ℝ) : Set MobiusFundamentalDomain :=
  mobiusSeamLeftPatch t₀ ε δ ∪ mobiusSeamRightPatch t₀ ε δ

/-- **Interior (in `x`)** of the two Euclidean sheets inside `mobiusSeamSaturatedPatch`: keep points with
`0 < x` on the left sheet and `x < 1` on the right sheet. The planar image under `mobiusPlaneCoord` is
open in `R2` (product of open intervals), which is the foothold for SPEC_003 **B1** on `mobiusPlaneTrigCoordMap`.
The full saturated patch also contains the seam lines `x = 0` and `x = 1`; those points are not needed for
this open planar image (see seam-chart discussion in `MobiusSeamChartableR2`). -/
def mobiusSeamSaturatedPatchSheetInterior (t₀ ε δ : ℝ) : Set MobiusFundamentalDomain :=
  ({ p | 0 < p.1.val } ∩ mobiusSeamLeftPatch t₀ ε δ) ∪
  ({ p | p.1.val < 1 } ∩ mobiusSeamRightPatch t₀ ε δ)

lemma isOpen_mobiusSeamLeftPatch (t₀ ε δ : ℝ) : IsOpen (mobiusSeamLeftPatch t₀ ε δ) := by
  let πx : MobiusFundamentalDomain → ℝ := fun p => p.1.val
  let πt : MobiusFundamentalDomain → ℝ := fun p => p.2.val
  have hcπx : Continuous πx := continuous_subtype_val.comp continuous_fst
  have hcπt : Continuous πt := continuous_subtype_val.comp continuous_snd
  have h1 : IsOpen { p : MobiusFundamentalDomain | p.1.val < ε } :=
    hcπx.isOpen_preimage (Iio ε) isOpen_Iio
  have h2 : IsOpen { p : MobiusFundamentalDomain | 0 < p.2.val } :=
    hcπt.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi
  have h3 : IsOpen { p : MobiusFundamentalDomain | p.2.val < 1 } :=
    hcπt.isOpen_preimage (Iio (1 : ℝ)) isOpen_Iio
  have h4 : IsOpen { p : MobiusFundamentalDomain | t₀ - δ < p.2.val } :=
    hcπt.isOpen_preimage (Ioi (t₀ - δ)) isOpen_Ioi
  have h5 : IsOpen { p : MobiusFundamentalDomain | p.2.val < t₀ + δ } :=
    hcπt.isOpen_preimage (Iio (t₀ + δ)) isOpen_Iio
  dsimp [mobiusSeamLeftPatch]
  simpa using h1.inter (h2.inter (h3.inter (h4.inter h5)))

lemma isOpen_mobiusSeamRightPatch (t₀ ε δ : ℝ) : IsOpen (mobiusSeamRightPatch t₀ ε δ) := by
  let πx : MobiusFundamentalDomain → ℝ := fun p => p.1.val
  let πt : MobiusFundamentalDomain → ℝ := fun p => p.2.val
  have hcπx : Continuous πx := continuous_subtype_val.comp continuous_fst
  have hcπt : Continuous πt := continuous_subtype_val.comp continuous_snd
  have h1 : IsOpen { p : MobiusFundamentalDomain | 1 - ε < p.1.val } :=
    hcπx.isOpen_preimage (Ioi (1 - ε)) isOpen_Ioi
  have h2 : IsOpen { p : MobiusFundamentalDomain | 0 < p.2.val } :=
    hcπt.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi
  have h3 : IsOpen { p : MobiusFundamentalDomain | p.2.val < 1 } :=
    hcπt.isOpen_preimage (Iio (1 : ℝ)) isOpen_Iio
  have h4 : IsOpen { p : MobiusFundamentalDomain | 1 - t₀ - δ < p.2.val } :=
    hcπt.isOpen_preimage (Ioi (1 - t₀ - δ)) isOpen_Ioi
  have h5 : IsOpen { p : MobiusFundamentalDomain | p.2.val < 1 - t₀ + δ } :=
    hcπt.isOpen_preimage (Iio (1 - t₀ + δ)) isOpen_Iio
  dsimp [mobiusSeamRightPatch]
  simpa using h1.inter (h2.inter (h3.inter (h4.inter h5)))

/-- Nontrivial seam glue is impossible from `mobiusSeamSaturatedPatchSheetInterior`: both sheets keep
`x` strictly inside `Icc 0 1`, whereas `mobiusGlueStep` forces `x.1.val ∈ {0,1}`. -/
lemma not_mobiusGlueStep_of_mem_mobiusSeamSaturatedPatchSheetInterior {t₀ ε δ : ℝ}
    (hε : ε < (1 : ℝ)) {x y : MobiusFundamentalDomain}
    (hx : x ∈ mobiusSeamSaturatedPatchSheetInterior t₀ ε δ) : ¬ mobiusGlueStep x y := by
  intro hgs
  rcases hx with hxL | hxR
  · have ⟨hx0lt, hxP⟩ : 0 < x.1.val ∧ x ∈ mobiusSeamLeftPatch t₀ ε δ := by
      simpa [mobiusSeamSaturatedPatchSheetInterior, Set.mem_inter_iff, Set.mem_setOf] using hxL
    rcases hgs with h1 | h2
    · linarith [hx0lt, h1.1]
    · have x1 : x.1.val = 1 := h2.2.1
      linarith [x1, hxP.1, hε]
  · have ⟨hx1lt, hxP⟩ : x.1.val < 1 ∧ x ∈ mobiusSeamRightPatch t₀ ε δ := by
      simpa [mobiusSeamSaturatedPatchSheetInterior, Set.mem_inter_iff, Set.mem_setOf] using hxR
    rcases hgs with h1 | h2
    · have x0 : x.1.val = 0 := h1.1
      linarith [x0, hxP.1, hε]
    · linarith [hx1lt, h2.2.1]

/-- `mobiusRel₀`-saturation on the sheet interior: the only relations to interior points are reflexive. -/
theorem mobiusSeamSaturatedPatchSheetInterior_sat {t₀ ε δ : ℝ} (hε : ε < (1 : ℝ)) :
    ∀ ⦃x y : MobiusFundamentalDomain⦄,
      x ∈ mobiusSeamSaturatedPatchSheetInterior t₀ ε δ → mobiusRel₀ x y →
        y ∈ mobiusSeamSaturatedPatchSheetInterior t₀ ε δ := by
  rintro x y hx hr
  rcases hr with he | hgs
  · rwa [← he]
  · exfalso
    exact not_mobiusGlueStep_of_mem_mobiusSeamSaturatedPatchSheetInterior hε hx hgs

/-- On the sheet interior, each `mobiusRel₀` class is a singleton, so `Quotient.mk` is injective. -/
theorem mobiusQuotientMk_injective_on_mobiusSeamSaturatedPatchSheetInterior {t₀ ε δ : ℝ} (hε : ε < (1 : ℝ)) :
    Injective fun w : Subtype (mobiusSeamSaturatedPatchSheetInterior t₀ ε δ) =>
      Quotient.mk mobiusSetoid w.val := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
  rcases Quotient.exact heq with he | hgs
  · subst he; rfl
  · exfalso
    exact not_mobiusGlueStep_of_mem_mobiusSeamSaturatedPatchSheetInterior hε ha hgs

theorem isOpen_mobiusSeamSaturatedPatchSheetInterior (t₀ ε δ : ℝ) :
    IsOpen (mobiusSeamSaturatedPatchSheetInterior t₀ ε δ) := by
  let πx : MobiusFundamentalDomain → ℝ := fun p => p.1.val
  have hcπx : Continuous πx := continuous_subtype_val.comp continuous_fst
  have h0p : IsOpen { p : MobiusFundamentalDomain | 0 < p.1.val } :=
    hcπx.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi
  have hp1 : IsOpen { p : MobiusFundamentalDomain | p.1.val < 1 } :=
    hcπx.isOpen_preimage (Iio (1 : ℝ)) isOpen_Iio
  dsimp [mobiusSeamSaturatedPatchSheetInterior]
  exact (h0p.inter (isOpen_mobiusSeamLeftPatch t₀ ε δ)).union
    (hp1.inter (isOpen_mobiusSeamRightPatch t₀ ε δ))

theorem isOpen_mobiusSeamSaturatedPatch (t₀ ε δ : ℝ) :
    IsOpen (mobiusSeamSaturatedPatch t₀ ε δ) :=
  (isOpen_mobiusSeamLeftPatch t₀ ε δ).union (isOpen_mobiusSeamRightPatch t₀ ε δ)

/-- Right-edge partners of points `(0, t)` in the left seam sheet (i.e. the `x = 1` side of
  `mobiusGlueStep`). -/
def mobiusSeamLeftPatchGluePartners (t₀ ε δ : ℝ) : Set MobiusFundamentalDomain :=
  { q |
    q.1.val = 1 ∧
      ∃ p ∈ mobiusSeamLeftPatch t₀ ε δ, p.1.val = 0 ∧ p.2.val + q.2.val = 1 }

/-- For the **left** Euclidean sheet under `ε < ½`, `π ⁻¹' (π '' left)` is the union of the left
  patch and its `x = 1` glue partners (a slice of the `x = 1` face). Then `p.1 = 1` is impossible
  on the left sheet, so the reverse glue orientation never occurs. -/
theorem mobiusSeamLeftPatch_mk_preimage_image_eq {t₀ ε δ : ℝ} (hε : ε < (1 / 2 : ℝ)) :
    (Quotient.mk mobiusSetoid) ⁻¹'
        ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) ''
          mobiusSeamLeftPatch t₀ ε δ) =
      mobiusSeamLeftPatch t₀ ε δ ∪ mobiusSeamLeftPatchGluePartners t₀ ε δ := by
  classical
  rw [mobiusQuot_mk_preimage_image]
  ext q
  simp only [mem_setOf_eq, mem_union, mobiusSeamLeftPatchGluePartners]
  constructor
  · rintro ⟨p, hpL, hr⟩
    rcases hr with hpq | hglue
    · rw [← hpq]; exact Or.inl hpL
    · rcases hglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
      · exact Or.inr ⟨hq1, p, hpL, hp0, hs⟩
      · exfalso
        rcases hpL with ⟨hxLx, _⟩
        linarith [hxLx, hp1, hε]
  · rintro (hpL | ⟨hq1, p, hpL, hp0, hs⟩)
    · exact ⟨q, hpL, Or.inl rfl⟩
    · exact ⟨p, hpL, Or.inr (Or.inl ⟨hp0, hq1, hs⟩)⟩

/-- Saturated for `mobiusRel₀` once `ε, δ` are small enough that heights stay in `(0,1)` and the
  vertical windows on the two edges line up under `t ↦ 1 - t`. -/
theorem mobiusSeamSaturatedPatch_sat {t₀ ε δ : ℝ}
    (hε0 : 0 < ε) (hδ0 : 0 < δ)
    (hε : ε < 1 / 2)
    (htLo : 0 < t₀ - δ)
    (htHi : t₀ + δ < 1) :
    ∀ ⦃x y : MobiusFundamentalDomain⦄,
      x ∈ mobiusSeamSaturatedPatch t₀ ε δ → mobiusRel₀ x y →
        y ∈ mobiusSeamSaturatedPatch t₀ ε δ := by
  classical
  rintro x y hx hr
  rcases hr with rfl | hglue
  · exact hx
  · rcases hx with hxL | hxR
    · rcases hglue with ⟨hx0, hy1, hs⟩ | ⟨hy0, hx1, hs⟩
      · -- `(0,t) ~ (1,1-t)` and `x` lies in the left sheet
        have ht : y.2.val = 1 - x.2.val := by linarith [hs]
        rcases hxL with ⟨_, hxt0, hxt1, htL, htR⟩
        refine Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hy1]
          exact sub_lt_self _ hε0
        · rw [ht]; exact sub_pos.mpr hxt1
        · rw [ht]; exact sub_lt_self _ hxt0
        · rw [ht]
          linarith [htR]
        · rw [ht]
          linarith [htL]
      · exfalso
        rcases hxL with ⟨hxLx, _⟩
        have hx1' : x.1.val = 1 := hx1
        linarith [hxLx, hx1', hε]
    · rcases hglue with ⟨hx0, hy1, hs⟩ | ⟨hy0, hx1, hs⟩
      · exfalso
        rcases hxR with ⟨hxRx, _⟩
        rw [hx0] at hxRx
        linarith [hxRx, hε0, hε]
      · -- `(1,t) ~ (0,1-t)` and `x` lies in the right sheet
        have ht : y.2.val = 1 - x.2.val := by linarith [hs]
        rcases hxR with ⟨_, hxt0, hxt1, htL, htR⟩
        refine Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hy0]
          exact hε0
        · rw [ht]; exact sub_pos.mpr hxt1
        · rw [ht]; exact sub_lt_self _ hxt0
        · rw [ht]
          linarith [htR]
        · rw [ht]
          linarith [htL]

end RepresentationalRegress

end
