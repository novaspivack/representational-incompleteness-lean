/-
  Möbius strip toward **C4** for `ChartableR2`: **`mobiusStripBoundary → ¬ ChartableR2`**
  (`not_chartableR2_of_mem_mobiusStripBoundary`); **`quot_mk_not_mem_mobiusStripBoundary_iff`**
  (**`⟦p⟧` off strip boundary** ↔ **`0 < t < 1`**); full **`↔`** packages as
  **`mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable`** from **`∀ p, 0 < t < 1 → ChartableR2 ⟦p⟧`**
  (remaining work: **vertical seam** / equator — **`MobiusSeamChartableR2`**). The cylinder side has the full biconditional outright.
  **`mobiusStrip_not_homeomorphic_closedCylinder_of_forall_off_edge_chartable`** is in **`ChartableR2Bridge`**. **On-patch trig classification** is in **`MobiusSeamTrigInject`**.
  **`mobiusQuotientMk_subtype_homeomorph_of_openMap`** packages the quotient `Subtype` homeomorphism
  when `π '' W` is open and `Subtype W → MobiusStrip` is an open map.

  * **Open cell** (`mobiusPlaneOpenBox`): saturated Euclidean balls; **`chartableR2_mobiusQuotientMk_of_mobiusRel₀`** /
    **`chartableR2_mobiusQuotientMk_of_mobiusRel₀_chartable_left`** for `mobiusRel₀` transport.
  * **Plane coord:** `mobiusPlaneCoord` is a **closed embedding** (compact domain → Hausdorff `R2`); hence
    **SPEC_003 B2** `exists_isOpen_preimage_mobiusPlaneCoord_of_isOpen`.
  * **Vertical interior (`0 < x < 1`):** **`mobiusClass_eq_singleton_of_Ioo_fx`**, **`mobiusQuot_mk_preimage_image_eq_of_forall_mem_Ioo_fx`**, **`isOpen_mobiusQuotient_image_of_forall_mem_Ioo_fx`**, **`mobiusRel₀_sat_of_forall_mem_Ioo_fx`**, **`injective_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx`**, **`isOpenMap_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx`**, **`mobiusQuotientMk_subtype_homeomorph_of_forall_mem_Ioo_fx`**; **`injective_mobiusQuotientMk_subtype_of_subset`** (smaller **Subtype** inherits **`Quotient.mk`** injectivity) — one-sided FD windows have **`π ⁻¹' (π '' W) = W`**, **`π '' W`** open, and packaged **Subtype** quotient homeomorphs (**SPEC_003 Phase D** / IFT bookkeeping). **`MobiusSeamChart`:** **`mobiusSeamSlidingCoord`**, **`continuous_mobiusSeamSlidingCoord`**, **`mobiusSeamSlidingCoord_zero`**.
  * **Seam** (`0 < t < 1`): **interior-sheet** quotient `ChartableR2` in **`MobiusSeamChartableR2`**; seam lines **`x ∈ {0,1}`** / equator still open.
  * **Boundary** (`t ∈ {0,1}`): `H2` open embedding / `not_chartableR2_of_isOpenEmbedding_H2`, including corners.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Piecewise
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Geometry.Manifold.Instances.Real

import RepresentationalIncompleteness.CylinderMobius
import RepresentationalIncompleteness.ChartableR2Neighbor
import RepresentationalIncompleteness.ChartableR2Models
import RepresentationalIncompleteness.HalfPlaneVsPlane

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

namespace RepresentationalIncompleteness

open scoped Topology Manifold
open Set Metric Topology EuclideanSpace Module Function Filter

/-! ### Plane coordinates on the fundamental domain -/

noncomputable def mobiusPlaneCoord (p : MobiusFundamentalDomain) : R2 :=
  EuclideanSpace.single (0 : Fin 2) p.1.val + EuclideanSpace.single (1 : Fin 2) p.2.val

private lemma continuous_coord0 : Continuous fun v : R2 => v 0 :=
  @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (0 : Fin 2)

private lemma continuous_coord1 : Continuous fun v : R2 => v 1 :=
  @PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ (1 : Fin 2)

private lemma continuous_euclideanSpace_single_param (i : Fin 2) :
    Continuous fun a : ℝ => EuclideanSpace.single i a :=
  (Isometry.uniformContinuous (Isometry.of_dist_eq (EuclideanSpace.dist_single_same i))).continuous

theorem continuous_mobiusPlaneCoord : Continuous mobiusPlaneCoord := by
  have h1 : Continuous fun p : MobiusFundamentalDomain => p.1.val :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun p : MobiusFundamentalDomain => p.2.val :=
    continuous_subtype_val.comp continuous_snd
  refine Continuous.add ?_ ?_
  · exact (continuous_euclideanSpace_single_param 0).comp h1
  · exact (continuous_euclideanSpace_single_param 1).comp h2

theorem mobiusPlaneCoord_apply_zero (p : MobiusFundamentalDomain) :
    mobiusPlaneCoord p (0 : Fin 2) = p.1.val := by
  simp [mobiusPlaneCoord, PiLp.add_apply, EuclideanSpace.single_apply, add_zero]

theorem mobiusPlaneCoord_apply_one (p : MobiusFundamentalDomain) :
    mobiusPlaneCoord p (1 : Fin 2) = p.2.val := by
  simp [mobiusPlaneCoord, PiLp.add_apply, EuclideanSpace.single_apply, zero_add, add_zero]

theorem injective_mobiusPlaneCoord : Injective mobiusPlaneCoord := by
  intro p q h
  refine Prod.ext ?_ ?_
  · exact Subtype.ext (by rw [← mobiusPlaneCoord_apply_zero p, ← mobiusPlaneCoord_apply_zero q, h])
  · exact Subtype.ext (by rw [← mobiusPlaneCoord_apply_one p, ← mobiusPlaneCoord_apply_one q, h])

theorem isClosedMap_mobiusPlaneCoord : IsClosedMap mobiusPlaneCoord := fun s hs => by
  exact (hs.isCompact.image continuous_mobiusPlaneCoord).isClosed

theorem isClosedEmbedding_mobiusPlaneCoord : IsClosedEmbedding mobiusPlaneCoord :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_mobiusPlaneCoord
    injective_mobiusPlaneCoord isClosedMap_mobiusPlaneCoord

/-- **SPEC_003_NF8 (B2).** Every open subset of the fundamental domain is the preimage under
`mobiusPlaneCoord` of an open set in `R2` (`mobiusPlaneCoord` is a closed embedding, hence inducing). -/
theorem exists_isOpen_preimage_mobiusPlaneCoord_of_isOpen {S : Set MobiusFundamentalDomain}
    (hS : IsOpen S) :
    ∃ G : Set R2, IsOpen G ∧ S = mobiusPlaneCoord ⁻¹' G := by
  rcases (isClosedEmbedding_mobiusPlaneCoord.isInducing.isOpen_iff).1 hS with ⟨G, hG, h⟩
  exact ⟨G, hG, h.symm⟩

def mobiusPlaneOpenBox : Set R2 :=
  { v | 0 < v 0 ∧ v 0 < 1 ∧ 0 < v 1 ∧ v 1 < 1 }

theorem isOpen_mobiusPlaneOpenBox : IsOpen (mobiusPlaneOpenBox : Set R2) := by
  have h00 : IsOpen { v : R2 | 0 < v 0 } :=
    continuous_coord0.isOpen_preimage (s := Ioi (0 : ℝ)) isOpen_Ioi
  have h01 : IsOpen { v : R2 | v 0 < 1 } :=
    continuous_coord0.isOpen_preimage (s := Iio (1 : ℝ)) isOpen_Iio
  have h10 : IsOpen { v : R2 | 0 < v 1 } :=
    continuous_coord1.isOpen_preimage (s := Ioi (0 : ℝ)) isOpen_Ioi
  have h11 : IsOpen { v : R2 | v 1 < 1 } :=
    continuous_coord1.isOpen_preimage (s := Iio (1 : ℝ)) isOpen_Iio
  simpa [mobiusPlaneOpenBox] using h00.inter (h01.inter (h10.inter h11))

theorem mobiusPlaneCoord_mem_openBox_iff (p : MobiusFundamentalDomain) :
    mobiusPlaneCoord p ∈ mobiusPlaneOpenBox ↔
      0 < p.1.val ∧ p.1.val < 1 ∧ 0 < p.2.val ∧ p.2.val < 1 := by
  simp only [mobiusPlaneOpenBox, mem_setOf_eq, mobiusPlaneCoord_apply_zero,
    mobiusPlaneCoord_apply_one, Pi.lt_def, Pi.zero_apply]

theorem mobiusRel₀_of_planeOpenBox {p q : MobiusFundamentalDomain}
    (hp : mobiusPlaneCoord p ∈ mobiusPlaneOpenBox) (hq : mobiusPlaneCoord q ∈ mobiusPlaneOpenBox)
    (hr : mobiusRel₀ p q) : p = q := by
  rcases hr with rfl | hglue
  · rfl
  · rcases hglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
    · exact False.elim (by linarith [(mobiusPlaneCoord_mem_openBox_iff p).1 hp |>.1, hp0])
    · exact False.elim (by linarith [(mobiusPlaneCoord_mem_openBox_iff p).1 hp |>.2.1, hp1])

/-! ### Open quotient images of saturated opens -/

theorem isOpen_mobiusQuotient_image_iff_preimage (S : Set MobiusFundamentalDomain) :
    IsOpen ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' S) ↔
      IsOpen ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) ⁻¹'
        ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' S)) :=
  (isQuotientMap_quotient_mk' (s := mobiusSetoid)).isOpen_preimage (s := (Quotient.mk mobiusSetoid '' S))

theorem isOpen_mobiusQuotient_image_of_saturated (S : Set MobiusFundamentalDomain) (hS : IsOpen S)
    (hsat : ∀ ⦃x y⦄, x ∈ S → mobiusRel₀ x y → y ∈ S) :
    IsOpen ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' S) := by
  let π := Quotient.mk mobiusSetoid
  have hpre : π ⁻¹' (π '' S) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact hsat hy (Quotient.exact he)
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hopre : IsOpen (π ⁻¹' (π '' S)) := by simpa [hpre] using hS
  exact (isQuotientMap_quotient_mk' (s := mobiusSetoid)).isOpen_preimage.1 hopre

/-- **One-sided / vertical-interior windows:** if every point of `W` has `x` strictly between `0` and `1`
  (no vertical seam), then each `mobiusRel₀` class meets `W` in at most one point and
  `π ⁻¹' (π '' W) = W`. In particular `π '' W` is open whenever `W` is open — **no** glue saturation step.

  This is the natural hypothesis for **IFT / partial-homeomorph** charts supported entirely on
  `0 < x < 1` in one Euclidean sheet (SPEC_003 Phase D bookkeeping). -/
theorem mobiusQuot_mk_preimage_image_eq_of_forall_mem_Ioo_fx {W : Set MobiusFundamentalDomain}
    (hW : ∀ ⦃p : MobiusFundamentalDomain⦄, p ∈ W → 0 < p.1.val ∧ p.1.val < 1) :
    (Quotient.mk mobiusSetoid) ⁻¹'
        ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' W) = W := by
  ext q
  rw [mobiusQuot_mk_preimage_image]
  constructor
  · rintro ⟨p, hpW, hr⟩
    have hsing := mobiusClass_eq_singleton_of_Ioo_fx (hW hpW)
    have hqmem : q ∈ mobiusClass p := by simpa [mobiusClass, Set.mem_setOf_eq] using hr
    rw [hsing, mem_singleton_iff] at hqmem
    exact hqmem ▸ hpW
  · intro hqW
    exact ⟨q, hqW, Or.inl rfl⟩

theorem isOpen_mobiusQuotient_image_of_forall_mem_Ioo_fx {W : Set MobiusFundamentalDomain}
    (hWo : IsOpen W) (hW : ∀ ⦃p : MobiusFundamentalDomain⦄, p ∈ W → 0 < p.1.val ∧ p.1.val < 1) :
    IsOpen ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' W) := by
  let π := Quotient.mk mobiusSetoid
  have hpre := mobiusQuot_mk_preimage_image_eq_of_forall_mem_Ioo_fx (W := W) hW
  have hopre : IsOpen (π ⁻¹' (π '' W)) := by
    rw [hpre]
    exact hWo
  exact (isQuotientMap_quotient_mk' (s := mobiusSetoid)).isOpen_preimage.1 hopre

theorem mobiusRel₀_sat_of_forall_mem_Ioo_fx {W : Set MobiusFundamentalDomain}
    (hW : ∀ ⦃p : MobiusFundamentalDomain⦄, p ∈ W → 0 < p.1.val ∧ p.1.val < 1) :
    ∀ ⦃x y : MobiusFundamentalDomain⦄, x ∈ W → mobiusRel₀ x y → y ∈ W := by
  rintro x y hx hr
  rcases hr with rfl | hglue
  · exact hx
  · rcases hglue with ⟨hp0, _, _⟩ | ⟨_, hp1, _⟩
    · rcases hW hx with ⟨hgt, _⟩
      rw [hp0] at hgt
      exact False.elim (lt_irrefl (0 : ℝ) hgt)
    · rcases hW hx with ⟨_, hlt⟩
      rw [hp1] at hlt
      exact False.elim (lt_irrefl (1 : ℝ) hlt)

theorem injective_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx {W : Set MobiusFundamentalDomain}
    (hW : ∀ ⦃p : MobiusFundamentalDomain⦄, p ∈ W → 0 < p.1.val ∧ p.1.val < 1) :
    Injective fun w : Subtype W => Quotient.mk mobiusSetoid w.val := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
  have hr : mobiusRel₀ a b := Quotient.exact heq
  have hsing := mobiusClass_eq_singleton_of_Ioo_fx (hW ha)
  have hbmem : b ∈ mobiusClass a := by simpa [mobiusClass, Set.mem_setOf_eq] using hr
  rw [hsing, mem_singleton_iff] at hbmem
  exact Subtype.ext hbmem.symm

/-- **Monotonicity** of **`Quotient.mk` injectivity** on subtypes: smaller open windows inherit injectivity.

  Used for **Phase D** refinements (`mobiusSeamSlidingCoord` ball **`∩ { x < ½ }`** in `MobiusSeamChartableR2`). -/
theorem injective_mobiusQuotientMk_subtype_of_subset {A B : Set MobiusFundamentalDomain} (hAB : A ⊆ B)
    (hinj : Injective fun w : Subtype B => Quotient.mk mobiusSetoid w.val) :
    Injective fun w : Subtype A => Quotient.mk mobiusSetoid w.val := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
  have haB : a ∈ B := hAB ha
  have hbB : b ∈ B := hAB hb
  have hab : (⟨a, haB⟩ : Subtype B) = ⟨b, hbB⟩ := hinj heq
  have habval : a = b := congrArg Subtype.val hab
  subst habval
  exact Subtype.ext rfl

private theorem mobiusRel₀_ball_open_aux {B : Set R2} (hB : B ⊆ mobiusPlaneOpenBox) {x y : MobiusFundamentalDomain}
    (hx : mobiusPlaneCoord x ∈ B) (hr : mobiusRel₀ x y) : mobiusPlaneCoord y ∈ B := by
  rcases hr with rfl | hglue
  · exact hx
  · have hxb := (mobiusPlaneCoord_mem_openBox_iff x).1 (show mobiusPlaneCoord x ∈ mobiusPlaneOpenBox from hB hx)
    rcases hglue with ⟨hp0, hq1, hs⟩ | ⟨hq0, hp1, hs⟩
    · exact False.elim (by have h0 := hxb.1; rw [hp0] at h0; exact lt_irrefl _ h0)
    · exact False.elim (by have h1 := hxb.2.1; rw [hp1] at h1; exact lt_irrefl _ h1)

/-! ### `Subtype W ≃ₜ Subtype B` for plane coords -/

/-- Fundamental-domain point from a vector in the open coordinate box. -/
noncomputable def mobiusFDOfOpenBox (v : R2) (hv : v ∈ mobiusPlaneOpenBox) : MobiusFundamentalDomain :=
  have h := mem_setOf_eq.mp hv
  (⟨v 0, h.1.le, h.2.1.le⟩, ⟨v 1, h.2.2.1.le, h.2.2.2.le⟩)

theorem mobiusPlaneCoord_fdOfOpenBox (v : R2) (hv : v ∈ mobiusPlaneOpenBox) :
    mobiusPlaneCoord (mobiusFDOfOpenBox v hv) = v := by
  dsimp [mobiusFDOfOpenBox, mobiusPlaneCoord]
  ext i
  fin_cases i <;> simp [PiLp.add_apply, EuclideanSpace.single_apply]

theorem mobiusFDOfOpenBox_mobiusPlaneCoord (p : MobiusFundamentalDomain)
    (ho : mobiusPlaneCoord p ∈ mobiusPlaneOpenBox) :
    mobiusFDOfOpenBox (mobiusPlaneCoord p) ho = p := by
  rcases p with ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩
  dsimp [mobiusFDOfOpenBox, mobiusPlaneCoord]
  simp [PiLp.add_apply, EuclideanSpace.single_apply, add_zero, zero_add]

theorem continuous_mobiusFDOfOpenBox_subtype {B : Set R2} (hB : B ⊆ mobiusPlaneOpenBox) :
    Continuous fun b : Subtype B =>
      (mobiusFDOfOpenBox (b.val : R2) (hB b.property) : MobiusFundamentalDomain) := by
  let F : Subtype B → MobiusFundamentalDomain := fun b =>
    have hbO := mem_setOf_eq.mp (show (b.val : R2) ∈ mobiusPlaneOpenBox from hB b.property)
    (⟨(b.val : R2) 0, hbO.1.le, hbO.2.1.le⟩, ⟨(b.val : R2) 1, hbO.2.2.1.le, hbO.2.2.2.le⟩)
  have hFE : F = fun b => mobiusFDOfOpenBox (b.val : R2) (hB b.property) := by
    funext b
    dsimp [F, mobiusFDOfOpenBox]
  rw [← hFE]
  refine Continuous.prodMk ?_ ?_
  · exact Continuous.subtype_mk
      ((@PiLp.continuous_apply _ (Fin 2) (fun _ : Fin 2 => ℝ) _ 0).comp continuous_subtype_val)
      (by
        intro b
        have hbO := mem_setOf_eq.mp (show (b.val : R2) ∈ mobiusPlaneOpenBox from hB b.property)
        exact ⟨hbO.1.le, hbO.2.1.le⟩)
  · exact Continuous.subtype_mk
      ((@PiLp.continuous_apply _ (Fin 2) (fun _ : Fin 2 => ℝ) _ 1).comp continuous_subtype_val)
      (by
        intro b
        have hbO := mem_setOf_eq.mp (show (b.val : R2) ∈ mobiusPlaneOpenBox from hB b.property)
        exact ⟨hbO.2.2.1.le, hbO.2.2.2.le⟩)

noncomputable def mobiusPlaneBoxHomeomorph (B : Set R2) (hB : B ⊆ mobiusPlaneOpenBox) :
    { p : MobiusFundamentalDomain // mobiusPlaneCoord p ∈ B } ≃ₜ Subtype B where
  toFun w := ⟨mobiusPlaneCoord w.val, w.property⟩
  invFun b :=
    let v := (b.val : R2)
    have hvO : v ∈ mobiusPlaneOpenBox := hB b.property
    ⟨mobiusFDOfOpenBox v hvO, by rw [mobiusPlaneCoord_fdOfOpenBox v hvO]; exact b.property⟩
  left_inv := by
    rintro ⟨p, hw⟩
    refine Subtype.ext ?_
    exact mobiusFDOfOpenBox_mobiusPlaneCoord p (hB hw)
  right_inv := by
    intro b
    refine Subtype.ext ?_
    simpa [mobiusPlaneCoord_fdOfOpenBox] using rfl
  continuous_toFun := Continuous.subtype_mk (continuous_mobiusPlaneCoord.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (continuous_mobiusFDOfOpenBox_subtype hB) (by
      intro b
      rw [mobiusPlaneCoord_fdOfOpenBox (b.val : R2) (hB b.property)]
      exact b.property)

/-! ### Open cell ⇒ `ChartableR2` on `MobiusStrip` -/

theorem mobiusRel₀_injective_on_planeBox {W : Set MobiusFundamentalDomain}
    (hW : ∀ ⦃x : MobiusFundamentalDomain⦄, x ∈ W → mobiusPlaneCoord x ∈ mobiusPlaneOpenBox) :
    Injective (fun w : Subtype W => Quotient.mk mobiusSetoid w.val) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
  exact Subtype.ext (mobiusRel₀_of_planeOpenBox (hW ha) (hW hb) (Quotient.exact heq))

theorem mobius_quotient_mk_subtype_isOpenMap {W : Set MobiusFundamentalDomain} (hWo : IsOpen W)
    (hsat : ∀ ⦃x y : MobiusFundamentalDomain⦄, x ∈ W → mobiusRel₀ x y → y ∈ W)
    (hinj : Injective (fun w : Subtype W => Quotient.mk mobiusSetoid w.val)) :
    IsOpenMap (fun w : Subtype W => Quotient.mk mobiusSetoid w.val) := by
  let π := Quotient.mk mobiusSetoid
  intro U hU
  have himg : IsOpen (Subtype.val '' U) :=
    hWo.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.1 hU
  have hsatcap :
      ∀ ⦃x y : MobiusFundamentalDomain⦄, x ∈ Subtype.val '' U → mobiusRel₀ x y →
        y ∈ Subtype.val '' U := by
    rintro x y ⟨w, hwU, rfl⟩ hr
    have hyW : y ∈ W := hsat w.property hr
    have hwe : w = ⟨y, hyW⟩ := hinj (Quotient.sound hr)
    rw [hwe] at hwU
    exact ⟨⟨y, hyW⟩, hwU, rfl⟩
  have hop := isOpen_mobiusQuotient_image_of_saturated (Subtype.val '' U) himg hsatcap
  simpa [Set.image_image] using hop

/-- `Subtype` of an open ball in `R2` is homeomorphic to `R2` (via normalization). -/
noncomputable def homeomorph_subtype_ball_R2 (v : R2) {ε : ℝ} (hε : 0 < ε) :
    Subtype (Metric.ball v ε) ≃ₜ R2 :=
  let B := Metric.ball v ε
  have him :
      (IsometryEquiv.vaddConst (P := R2) v).symm.toHomeomorph '' B = ball (0 : R2) ε := by
    simpa [B] using (IsometryEquiv.image_ball ((IsometryEquiv.vaddConst (P := R2) v).symm) v ε : _)
  let φ₁ : Subtype B ≃ₜ Subtype (ball (0 : R2) ε) :=
    (Homeomorph.image ((IsometryEquiv.vaddConst (P := R2) v).symm).toHomeomorph B).trans
      (Homeomorph.setCongr him)
  let φ₂ : Subtype (ball (0 : R2) ε) ≃ₜ Subtype (ball (0 : R2) 1) :=
    (OpenPartialHomeomorph.unitBallBall (0 : R2) ε hε).toHomeomorphSourceTarget.symm
  let φ₃ : Subtype (ball (0 : R2) 1) ≃ₜ R2 := (Homeomorph.unitBall (E := R2)).symm
  φ₁.trans (φ₂.trans φ₃)

/-- The open right half-plane `{u : R2 | u 0 > 0}` is homeomorphic to `R2`,
  via `(x, y) ↦ (log x, y)` with inverse `(u, v) ↦ (exp u, v)`. -/
noncomputable def homeomorph_rightHalfPlane_R2 :
    Subtype ({u : R2 | u 0 > 0}) ≃ₜ R2 := by
  let toFun : {u : R2 | u 0 > 0} → R2 := fun u =>
    EuclideanSpace.single 0 (Real.log (u.val 0)) +
    EuclideanSpace.single 1 (u.val 1)
  let invFun : R2 → {u : R2 | u 0 > 0} := fun v =>
    ⟨EuclideanSpace.single 0 (Real.exp (v 0)) + EuclideanSpace.single 1 (v 1),
      by simp [PiLp.add_apply, EuclideanSpace.single_apply, Real.exp_pos]⟩
  have hleftInv : ∀ u : {u : R2 | u 0 > 0}, invFun (toFun u) = u := by
    rintro ⟨u, hu⟩
    ext i; fin_cases i <;>
      simp [toFun, invFun, PiLp.add_apply, EuclideanSpace.single_apply, Real.exp_log hu]
  have hrightInv : ∀ v : R2, toFun (invFun v) = v := by
    intro v; ext i; fin_cases i <;>
      simp [toFun, invFun, PiLp.add_apply, EuclideanSpace.single_apply]
  have hcont : Continuous toFun := by
    apply Continuous.add
    · apply (continuous_euclideanSpace_single_param 0).comp
      apply Real.continuousOn_log.comp_continuous
      · exact ((@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 0).comp
          continuous_subtype_val)
      · rintro ⟨u, (hu : u 0 > 0)⟩; exact ne_of_gt hu
    · exact (continuous_euclideanSpace_single_param 1).comp
        ((@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 1).comp continuous_subtype_val)
  have hcontInv : Continuous invFun := by
    refine Continuous.subtype_mk ?_ _
    apply Continuous.add
    · exact (continuous_euclideanSpace_single_param 0).comp
        (Real.continuous_exp.comp (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 0))
    · exact (continuous_euclideanSpace_single_param 1).comp
        (@PiLp.continuous_apply 2 (Fin 2) (fun _ : Fin 2 => ℝ) _ 1)
  exact Homeomorph.mk (Equiv.mk toFun invFun hleftInv hrightInv) hcont hcontInv

/-- An open right half-**ball** `{u : R2 | ‖u‖ < r ∧ u 0 > 0}` is homeomorphic to `R2`.
  Direct construction: the map `u ↦ (log(u 0), u 1 / u 0)` ... actually use the composition:
  scale to unit ball, apply unitBall.symm (preserves sign of u 0), then apply
  `homeomorph_rightHalfPlane_R2`. -/
noncomputable def homeomorph_halfBall_R2 {r : ℝ} (hr : 0 < r) :
    Subtype ({u : R2 | ‖u‖ < r ∧ (u 0 : ℝ) > 0}) ≃ₜ R2 := by
  -- Use the direct map: u ↦ (log u0 - log(r - ‖u‖), u1)  
  -- This maps the half-ball {‖u‖ < r, u0 > 0} to R2.
  -- Inverse: (s, t) ↦ (exp(s) · r / (exp(s) + 1), t · r / (exp(s) + 1)) ... complex.
  -- Simplest: compose homeomorphisms.
  -- Step 1: half-ball {‖u‖ < r, u0 > 0} → half-ball {‖u‖ < 1, u0 > 0} (scale by 1/r)
  -- Step 2: half-ball {‖u‖ < 1, u0 > 0} → half-plane {u0 > 0} via unitBall.symm
  -- Step 3: half-plane {u0 > 0} → R2 via homeomorph_rightHalfPlane_R2
  -- Steps 1 and 2 together: use homeomorph_subtype_ball_R2 restricted, or direct formula.
  -- DIRECT FORMULA: u ↦ (log(u0) - log(r - ‖u‖) + log r, u1 / (r - ‖u‖) · r)
  -- Simplify: use u ↦ (log(u0 / (r - ‖u‖)), u1 / (r - ‖u‖)) which maps to half-plane, then apply log.
  -- Actually the map u ↦ (u0 / (r - ‖u‖), u1 / (r - ‖u‖)) maps half-ball to half-plane directly:
  -- For u in half-ball: ‖u‖ < r, u0 > 0. The image has first component u0/(r - ‖u‖) > 0 ✓.
  -- Inverse: v ↦ r · v / (1 + ‖v‖) ... not obviously in half-ball but correct.
  -- Simpler: just use the composition
  -- half-ball ≃ₜ half-plane via u ↦ u / (r - ‖u‖)
  -- half-plane ≃ₜ R2 via homeomorph_rightHalfPlane_R2 (already defined)
  let toHP : {u : R2 | ‖u‖ < r ∧ (u 0 : ℝ) > 0} → {u : R2 | (u 0 : ℝ) > 0} := fun u =>
    ⟨(r - ‖u.val‖)⁻¹ • u.val, by
      have hpos : r - ‖u.val‖ > 0 := sub_pos.mpr u.2.1
      simp only [Set.mem_setOf_eq, PiLp.smul_apply]
      exact mul_pos (inv_pos.mpr hpos) u.2.2⟩
  let fromHP : {u : R2 | (u 0 : ℝ) > 0} → {u : R2 | ‖u‖ < r ∧ (u 0 : ℝ) > 0} := fun v =>
    ⟨(r / (1 + ‖v.val‖)) • v.val, by
      have hden : (1 : ℝ) + ‖v.val‖ > 0 := by positivity
      constructor
      · rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr.le hden.le)]
        calc r / (1 + ‖v.val‖) * ‖v.val‖ < r / (1 + ‖v.val‖) * (1 + ‖v.val‖) := by
              apply mul_lt_mul_of_pos_left (lt_one_add ‖v.val‖) (div_pos hr hden)
          _ = r := div_mul_cancel₀ r (ne_of_gt hden)
      · simp only [Set.mem_setOf_eq, PiLp.smul_apply]
        exact mul_pos (div_pos hr hden) v.2⟩
  have hleft : ∀ u : {u : R2 | ‖u‖ < r ∧ (u 0 : ℝ) > 0}, fromHP (toHP u) = u := by
    rintro ⟨u, hu_norm, hu_pos⟩
    apply Subtype.ext
    simp only [toHP, fromHP]
    rw [smul_smul]
    have hpos : r - ‖u‖ > 0 := sub_pos.mpr hu_norm
    have hden : (1 : ℝ) + ‖(r - ‖u‖)⁻¹ • u‖ > 0 := by positivity
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    have hne : r - ‖u‖ ≠ 0 := ne_of_gt hpos
    -- Goal: (r / (1 + (r - ‖u‖)⁻¹ * ‖u‖) * (r - ‖u‖)⁻¹) • u = u
    -- Simplify: r / (1 + ‖u‖/(r-‖u‖)) * 1/(r-‖u‖) = r/((r-‖u‖+‖u‖)/(r-‖u‖)) * 1/(r-‖u‖) = r/(r) * (r-‖u‖)/((r-‖u‖)*(r-‖u‖)^(-1)) = 1
    suffices h : r / (1 + (r - ‖u‖)⁻¹ * ‖u‖) * (r - ‖u‖)⁻¹ = 1 by rw [h, one_smul]
    field_simp; ring
  have hright : ∀ v : {u : R2 | (u 0 : ℝ) > 0}, toHP (fromHP v) = v := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    simp only [toHP, fromHP]
    rw [smul_smul]
    have hden : (1 : ℝ) + ‖v‖ > 0 := by positivity
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr.le hden.le)]
    -- Goal: (r / (1 + ‖v‖) * (r - r / (1 + ‖v‖) * ‖v‖)⁻¹) • v = v
    -- r - r/(1+‖v‖) * ‖v‖ = r * (1+‖v‖-‖v‖) / (1+‖v‖) = r/(1+‖v‖)
    have hne : (1 : ℝ) + ‖v‖ ≠ 0 := ne_of_gt hden
    have hkey : (r - r / (1 + ‖v‖) * ‖v‖)⁻¹ * (r / (1 + ‖v‖)) = 1 := by
      field_simp
      ring
    rw [hkey, one_smul]
  have hcont_toHP : Continuous toHP := by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · apply Continuous.inv₀
      · exact continuous_const.sub (continuous_norm.comp continuous_subtype_val)
      · intro ⟨u, hu_norm, _⟩; exact ne_of_gt (sub_pos.mpr hu_norm)
    · exact continuous_subtype_val
  have hcont_fromHP : Continuous fromHP := by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · apply Continuous.div continuous_const
      · exact (continuous_const.add (continuous_norm.comp continuous_subtype_val))
      · intro v; exact ne_of_gt (by positivity)
    · exact continuous_subtype_val
  let ψ : Subtype {u : R2 | ‖u‖ < r ∧ (u 0 : ℝ) > 0} ≃ₜ Subtype {u : R2 | (u 0 : ℝ) > 0} :=
    Homeomorph.mk (Equiv.mk toHP fromHP hleft hright) hcont_toHP hcont_fromHP
  exact ψ.trans homeomorph_rightHalfPlane_R2

/-- Quotient restriction to a **saturated** open set on which `π` is injective on `Subtype W`. -/
noncomputable def mobiusQuotientMk_subtype_homeomorph {W : Set MobiusFundamentalDomain}
    (hWo : IsOpen W)
    (hsat : ∀ ⦃x y : MobiusFundamentalDomain⦄, x ∈ W → mobiusRel₀ x y → y ∈ W)
    (hinj : Injective (fun w : Subtype W => Quotient.mk mobiusSetoid w.val)) :
    Subtype W ≃ₜ Subtype ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' W) := by
  let π := Quotient.mk mobiusSetoid
  let toFun (w : Subtype W) : Subtype (π '' W) :=
    ⟨π w.val, w.val, w.property, rfl⟩
  have h_inj : Injective toFun := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hπ : π a = π b := congrArg Subtype.val hab
    have := hinj (show (fun w : Subtype W => π w.val) ⟨a, ha⟩ = (fun w : Subtype W => π w.val) ⟨b, hb⟩ by
      simpa [Function.comp_apply, π] using hπ)
    simpa [Subtype.ext_iff] using congrArg Subtype.val this
  have h_surj : Function.Surjective toFun := by
    rintro ⟨m, hm⟩
    rcases hm with ⟨a, haW, rfl⟩
    exact ⟨⟨a, haW⟩, rfl⟩
  let e : Subtype W ≃ Subtype (π '' W) := Equiv.ofBijective toFun ⟨h_inj, h_surj⟩
  have hcont : Continuous toFun :=
    continuous_induced_rng.mpr (continuous_quot_mk.comp continuous_subtype_val)
  have hUimg : IsOpen (π '' W) := isOpen_mobiusQuotient_image_of_saturated W hWo hsat
  have hEmb :
      IsOpenEmbedding (Subtype.val : Subtype (π '' W) → MobiusStrip) :=
    hUimg.isOpenEmbedding_subtypeVal
  have hop : IsOpenMap toFun := by
    have hcomp : IsOpenMap (Subtype.val ∘ toFun) := by
      simpa [Function.comp_def, π] using mobius_quotient_mk_subtype_isOpenMap hWo hsat hinj
    intro V hV
    have hpreimg : IsOpen (Subtype.val '' (toFun '' V)) := by
      convert hcomp V hV using 1
      rw [← image_comp]
    exact (hEmb.isOpen_iff_image_isOpen).2 hpreimg
  exact e.toHomeomorphOfContinuousOpen hcont hop

/-- Same as `mobiusQuotientMk_subtype_homeomorph`, but the openness of `π '' W` and the openness of
  the induced `Subtype W → MobiusStrip` map are supplied directly (covers non-saturated windows,
  e.g. seam local models). -/
noncomputable def mobiusQuotientMk_subtype_homeomorph_of_openMap {W : Set MobiusFundamentalDomain}
    (_hWo : IsOpen W)
    (hπimg : IsOpen ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' W))
    (hinj : Injective (fun w : Subtype W => Quotient.mk mobiusSetoid w.val))
    (hopen : IsOpenMap (fun w : Subtype W => (Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) w.val)) :
    Subtype W ≃ₜ Subtype ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' W) := by
  let π := Quotient.mk mobiusSetoid
  let toFun (w : Subtype W) : Subtype (π '' W) :=
    ⟨π w.val, w.val, w.property, rfl⟩
  have h_inj : Injective toFun := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hπ : π a = π b := congrArg Subtype.val hab
    have := hinj (show (fun w : Subtype W => π w.val) ⟨a, ha⟩ = (fun w : Subtype W => π w.val) ⟨b, hb⟩ by
      simpa [Function.comp_apply, π] using hπ)
    simpa [Subtype.ext_iff] using congrArg Subtype.val this
  have h_surj : Function.Surjective toFun := by
    rintro ⟨m, hm⟩
    rcases hm with ⟨a, haW, rfl⟩
    exact ⟨⟨a, haW⟩, rfl⟩
  let e : Subtype W ≃ Subtype (π '' W) := Equiv.ofBijective toFun ⟨h_inj, h_surj⟩
  have hcont : Continuous toFun :=
    continuous_induced_rng.mpr (continuous_quot_mk.comp continuous_subtype_val)
  have hEmb :
      IsOpenEmbedding (Subtype.val : Subtype (π '' W) → MobiusStrip) :=
    hπimg.isOpenEmbedding_subtypeVal
  have hop : IsOpenMap toFun := by
    intro V hV
    have hcomp : IsOpenMap (Subtype.val ∘ toFun) := by
      simpa [Function.comp_def, π] using hopen
    have hpreimg : IsOpen (Subtype.val '' (toFun '' V)) := by
      convert hcomp V hV using 1
      rw [← image_comp]
    exact (hEmb.isOpen_iff_image_isOpen).2 hpreimg
  exact e.toHomeomorphOfContinuousOpen hcont hop

theorem isOpenMap_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx {W : Set MobiusFundamentalDomain}
    (hWo : IsOpen W) (hW : ∀ ⦃p : MobiusFundamentalDomain⦄, p ∈ W → 0 < p.1.val ∧ p.1.val < 1) :
    IsOpenMap fun w : Subtype W => Quotient.mk mobiusSetoid w.val :=
  mobius_quotient_mk_subtype_isOpenMap hWo (mobiusRel₀_sat_of_forall_mem_Ioo_fx hW)
    (injective_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx hW)

/-- Package `mobiusQuotientMk_subtype_homeomorph` under the vertical-interior (`0 < x < 1`) hypotheses. -/
noncomputable def mobiusQuotientMk_subtype_homeomorph_of_forall_mem_Ioo_fx
    {W : Set MobiusFundamentalDomain}
    (hWo : IsOpen W) (hW : ∀ ⦃p : MobiusFundamentalDomain⦄, p ∈ W → 0 < p.1.val ∧ p.1.val < 1) :
    Subtype W ≃ₜ Subtype ((Quotient.mk mobiusSetoid : MobiusFundamentalDomain → MobiusStrip) '' W) :=
  mobiusQuotientMk_subtype_homeomorph hWo (mobiusRel₀_sat_of_forall_mem_Ioo_fx hW)
    (injective_mobiusQuotientMk_subtype_of_forall_mem_Ioo_fx hW)

/-- **Open box / strict planar cell** ⇒ intrinsic `R²` chart at `⟦p⟧` (interior of the fundamental square,
  away from edges and the vertical seam in coordinates). -/
theorem chartableR2_mobiusQuotientMk_of_planeOpenBox {p : MobiusFundamentalDomain}
    (hp : mobiusPlaneCoord p ∈ mobiusPlaneOpenBox) : ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  let π := Quotient.mk mobiusSetoid
  let v := mobiusPlaneCoord p
  have hvo : IsOpen mobiusPlaneOpenBox := isOpen_mobiusPlaneOpenBox
  rcases Metric.mem_nhds_iff.mp (hvo.mem_nhds hp) with ⟨ε, hε, hball⟩
  let B : Set R2 := Metric.ball v ε
  have hB : B ⊆ mobiusPlaneOpenBox := hball
  let W : Set MobiusFundamentalDomain := mobiusPlaneCoord ⁻¹' B
  have hWo : IsOpen W := continuous_mobiusPlaneCoord.isOpen_preimage (s := B) Metric.isOpen_ball
  have hpW : p ∈ W := by
    have hmem : v ∈ Metric.ball v ε := Metric.mem_ball_self (α := R2) hε
    simpa [W, B, v] using hmem
  have hsat :
      ∀ ⦃x y : MobiusFundamentalDomain⦄, x ∈ W → mobiusRel₀ x y → y ∈ W :=
    fun _ _ hx hr => mobiusRel₀_ball_open_aux hB hx hr
  have hWbox :
      ∀ ⦃x : MobiusFundamentalDomain⦄, x ∈ W → mobiusPlaneCoord x ∈ mobiusPlaneOpenBox :=
    fun _ hx => hB hx
  have hinj := mobiusRel₀_injective_on_planeBox (W := W) hWbox
  let U : Set MobiusStrip := π '' W
  have hUo : IsOpen U := isOpen_mobiusQuotient_image_of_saturated W hWo hsat
  have hpU : π p ∈ U := ⟨p, hpW, rfl⟩
  let φ₀ : Subtype U ≃ₜ Subtype W := (mobiusQuotientMk_subtype_homeomorph hWo hsat hinj).symm
  let φ₁ : Subtype W ≃ₜ Subtype B := mobiusPlaneBoxHomeomorph B hB
  let φ₂ : Subtype B ≃ₜ R2 := homeomorph_subtype_ball_R2 v hε
  let ψ : Subtype U ≃ₜ R2 := φ₀.trans (φ₁.trans φ₂)
  exact chartableR2_of_open_embeds_plane (Quotient.mk mobiusSetoid p) hUo hpU ⟨ψ⟩

/-- Strict inequalities on **both** fundamental-domain coordinates ⇒ `ChartableR2` at the class.

  **Seam** representatives with `p.1.val ∈ {0, 1}` but `0 < p.2.val < 1` are not covered here; see
  `MobiusSeamChart.lean` for the local `R²` model / IFT-ready derivative and `REMAINING_QUEUE` for the
  quotient `ChartableR2` step. -/
theorem chartableR2_mobiusQuotientMk_of_Ioo_square {p : MobiusFundamentalDomain}
    (h1 : 0 < p.1.val ∧ p.1.val < 1) (h2 : 0 < p.2.val ∧ p.2.val < 1) :
    ChartableR2 (Quotient.mk mobiusSetoid p) :=
  chartableR2_mobiusQuotientMk_of_planeOpenBox
    ((mobiusPlaneCoord_mem_openBox_iff p).2 ⟨h1.1, h1.2, h2.1, h2.2⟩)

/-- `ChartableR2` is constant on `mobiusRel₀` classes (hence on `MobiusStrip` points). -/
theorem chartableR2_mobiusQuotientMk_of_mobiusRel₀ {p q : MobiusFundamentalDomain}
    (h : mobiusRel₀ p q) (hq : ChartableR2 (Quotient.mk mobiusSetoid q)) :
    ChartableR2 (Quotient.mk mobiusSetoid p) := by
  rw [Quotient.sound h]
  exact hq

/-- Same as `chartableR2_mobiusQuotientMk_of_mobiusRel₀`, but with the charted representative on the
  **left** (`p` rather than `q`). Convenient when a seam construction yields `ChartableR2 ⟦p⟧` first. -/
theorem chartableR2_mobiusQuotientMk_of_mobiusRel₀_chartable_left {p q : MobiusFundamentalDomain}
    (h : mobiusRel₀ p q) (hp : ChartableR2 (Quotient.mk mobiusSetoid p)) :
    ChartableR2 (Quotient.mk mobiusSetoid q) :=
  chartableR2_mobiusQuotientMk_of_mobiusRel₀ (mobiusRel₀.symm h) hp

/-! ### Bottom edge (interior in `x`, height `0`) ⇒ `¬ ChartableR2`

Use `H2 = EuclideanHalfSpace 2` with **first** coordinate the boundary coordinate (`0 ≤ v 0`).
Chart send `p` to `(p.2.val, p.1.val - x0)`.

*Compare `CylinderChartableBoundary.lean` (`homeomorph_closedCylinder_model_to_H2`).* -/

/-- Open “cap” in the fundamental square under a bot-edge interior point. -/
def mobiusBotHStrip (x0 η ε : ℝ) : Set MobiusFundamentalDomain :=
  { p | p.1.val ∈ Metric.ball x0 η ∧ p.2.val < ε }

theorem isOpen_mobiusBotHStrip {x0 η ε : ℝ} (_hη : 0 < η) (_hε : 0 < ε) :
    IsOpen (mobiusBotHStrip x0 η ε) := by
  have hx :
      IsOpen { p : MobiusFundamentalDomain | p.1.val ∈ Metric.ball x0 η } :=
    (continuous_subtype_val.comp continuous_fst).isOpen_preimage (s := Metric.ball x0 η)
      Metric.isOpen_ball
  have ht : IsOpen { p : MobiusFundamentalDomain | p.2.val < ε } :=
    (continuous_subtype_val.comp continuous_snd).isOpen_preimage (s := Iio ε) isOpen_Iio
  simpa [mobiusBotHStrip] using hx.inter ht

theorem mobiusBotHStrip_sat {x0 η ε : ℝ}
    (hx0 : 0 < x0 ∧ x0 < 1)
    (_hη : 0 < η)
    (hηb : η < x0 ∧ η < 1 - x0) :
    ∀ ⦃x y : MobiusFundamentalDomain⦄,
      x ∈ mobiusBotHStrip x0 η ε → mobiusRel₀ x y → y ∈ mobiusBotHStrip x0 η ε := by
  rintro x y hx hr
  rcases hr with rfl | hglue
  · exact hx
  · rcases hglue with ⟨hx0', hq1, hs⟩ | ⟨hq0, hp1, hs⟩
    · exfalso
      rcases hx with ⟨hball, _⟩
      rw [hx0'] at hball
      simp [Real.dist_eq, abs_of_pos hx0.1] at hball
      linarith [hball, hηb.1]
    · exfalso
      rcases hx with ⟨hball, _⟩
      rw [hp1] at hball
      have h1mx0 : 0 < 1 - x0 := sub_pos.mpr hx0.2
      simp [Real.dist_eq, abs_of_pos h1mx0] at hball
      linarith [hball, hηb.2]

theorem mobiusRel₀_injective_on_mobiusBotHStrip {x0 η ε : ℝ}
    (hx0 : 0 < x0 ∧ x0 < 1)
    (_hη : 0 < η)
    (hηb : η < x0 ∧ η < 1 - x0) :
    Injective (fun w : Subtype (mobiusBotHStrip x0 η ε) =>
      Quotient.mk mobiusSetoid w.val) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
  refine Subtype.ext ?_
  have hr := Quotient.exact heq
  rcases hr with rfl | hglue
  · rfl
  · rcases hglue with ⟨ha0, hb1, hs⟩ | ⟨hb0, ha1, hs⟩
    · exfalso
      rcases ha with ⟨haball, _⟩
      rw [ha0] at haball
      simp [Real.dist_eq, abs_of_pos hx0.1] at haball
      linarith [haball, hηb.1]
    · exfalso
      rcases ha with ⟨haball, _⟩
      rw [ha1] at haball
      have h1mx0 : 0 < 1 - x0 := sub_pos.mpr hx0.2
      simp [Real.dist_eq, abs_of_pos h1mx0] at haball
      linarith [haball, hηb.2]

/-! ### Half-space target (`H2`) and coordinate chart -/

/-- Open set in `H2`: height `< ε`, horizontal offset in `ball(0,η)`. -/
def mobiusBotHStrip_H2Target (η ε : ℝ) : Set H2 :=
  { w | w.val 0 < ε ∧ w.val 1 ∈ Metric.ball (0 : ℝ) η }

theorem isOpen_mobiusBotHStrip_H2Target {η ε : ℝ} (_hη : 0 < η) (_hε : 0 < ε) :
    IsOpen (mobiusBotHStrip_H2Target η ε) := by
  have h0 :
      Continuous fun w : H2 => w.val 0 :=
    continuous_coord0.comp continuous_subtype_val
  have h1 :
      Continuous fun w : H2 => w.val 1 :=
    continuous_coord1.comp continuous_subtype_val
  simp_rw [mobiusBotHStrip_H2Target, setOf_and]
  exact (h0.isOpen_preimage (s := Iio ε) isOpen_Iio).inter
    (h1.isOpen_preimage (s := Metric.ball (0 : ℝ) η) Metric.isOpen_ball)

theorem zero_mem_mobiusBotHStrip_H2Target {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    (0 : H2) ∈ mobiusBotHStrip_H2Target η ε := by
  refine And.intro (by simpa using hε) ?_
  have hz1 : (0 : H2).val 1 = (0 : ℝ) := rfl
  simpa [hz1, Metric.mem_ball, dist_eq] using (Metric.mem_ball_self hη : (0 : ℝ) ∈ ball (0 : ℝ) η)

noncomputable def mobiusBotHStrip_coord (x0 : ℝ) (p : MobiusFundamentalDomain) : R2 :=
  EuclideanSpace.single (0 : Fin 2) p.2.val + EuclideanSpace.single (1 : Fin 2) (p.1.val - x0)

private lemma mobiusBotHStrip_coord_apply_height (x0 : ℝ) (p : MobiusFundamentalDomain) :
    mobiusBotHStrip_coord x0 p 0 = p.2.val := by
  simp [mobiusBotHStrip_coord, PiLp.add_apply, EuclideanSpace.single_apply]

private lemma mobiusBotHStrip_coord_apply_offset (x0 : ℝ) (p : MobiusFundamentalDomain) :
    mobiusBotHStrip_coord x0 p 1 = p.1.val - x0 := by
  simp [mobiusBotHStrip_coord, PiLp.add_apply, EuclideanSpace.single_apply, add_zero]

theorem continuous_mobiusBotHStrip_coord (x0 : ℝ) :
    Continuous fun p : MobiusFundamentalDomain => mobiusBotHStrip_coord x0 p := by
  have ht : Continuous fun p : MobiusFundamentalDomain => p.2.val :=
    continuous_subtype_val.comp continuous_snd
  have hx : Continuous fun p : MobiusFundamentalDomain => p.1.val :=
    continuous_subtype_val.comp continuous_fst
  refine Continuous.add ?_ ?_
  · exact (continuous_euclideanSpace_single_param 0).comp ht
  · exact (continuous_euclideanSpace_single_param 1).comp (hx.sub continuous_const)

noncomputable def mobiusBotHStrip_toH2 (x0 : ℝ) (p : MobiusFundamentalDomain) : H2 :=
  ⟨mobiusBotHStrip_coord x0 p, by
    rw [mobiusBotHStrip_coord_apply_height]
    exact p.2.property.1⟩

theorem mobiusBotHStrip_toH2_mem_target {x0 η ε : ℝ} {p : MobiusFundamentalDomain}
    (hp : p ∈ mobiusBotHStrip x0 η ε) :
    mobiusBotHStrip_toH2 x0 p ∈ mobiusBotHStrip_H2Target η ε := by
  rcases hp with ⟨hxb, hxt⟩
  refine And.intro ?_ ?_
  · simpa [mobiusBotHStrip_toH2, mobiusBotHStrip_coord_apply_height] using hxt
  · simpa [mobiusBotHStrip_toH2, mobiusBotHStrip_coord_apply_offset, Metric.mem_ball, dist_eq,
      sub_zero] using mem_ball_iff_norm.mp hxb

noncomputable def mobiusFD_of_botHStrip_H2 (x0 η ε : ℝ)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) (h : H2)
    (hh : h ∈ mobiusBotHStrip_H2Target η ε) : MobiusFundamentalDomain :=
  have hv1 : |h.val 1| < η := by
    rcases hh with ⟨_, Hball⟩
    simpa [dist_eq, Real.norm_eq_abs] using mem_ball_iff_norm.mp Hball
  have hx_lo : 0 < x0 + h.val 1 := by
    have hvl := (abs_lt.mp hv1).1
    linarith [hvl, hηb.1]
  have hx_hi : x0 + h.val 1 < 1 := by
    have hvr := (abs_lt.mp hv1).2
    linarith [hvr, hηb.2]
  have ht0 : 0 ≤ h.val 0 := h.property
  have ht1 : h.val 0 < 1 := lt_of_lt_of_le hh.1 hε1
  (⟨x0 + h.val 1, ⟨le_of_lt hx_lo, le_of_lt hx_hi⟩⟩,
    ⟨h.val 0, ⟨ht0, le_of_lt ht1⟩⟩)

theorem mobiusFD_mem_mobiusBotHStrip_of_H2 {x0 η ε : ℝ} (_hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) {h : H2}
    (hh : h ∈ mobiusBotHStrip_H2Target η ε) :
    mobiusFD_of_botHStrip_H2 x0 η ε hηb hε1 h hh ∈ mobiusBotHStrip x0 η ε := by
  dsimp [mobiusBotHStrip, mobiusFD_of_botHStrip_H2]
  refine And.intro ?_ hh.1
  rw [mem_ball_iff_norm]
  rcases hh with ⟨_, Hball⟩
  simpa [sub_add_cancel, Real.norm_eq_abs, Real.dist_eq] using mem_ball_iff_norm.mp Hball

theorem mobiusBotHStrip_toH2_of_FD {x0 η ε : ℝ} (_hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) {p : MobiusFundamentalDomain}
    (hp : p ∈ mobiusBotHStrip x0 η ε) :
    mobiusFD_of_botHStrip_H2 x0 η ε hηb hε1 (mobiusBotHStrip_toH2 x0 p)
        (mobiusBotHStrip_toH2_mem_target hp) =
      p := by
  rcases p with ⟨px, pt⟩
  simp_rw [mobiusFD_of_botHStrip_H2, mobiusBotHStrip_toH2, mobiusBotHStrip_coord_apply_height,
    mobiusBotHStrip_coord_apply_offset]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp [add_sub_cancel]
  · rfl

theorem mobiusBotHStrip_toH2_of_H2 {x0 η ε : ℝ} (_hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) {h : H2}
    (hh : h ∈ mobiusBotHStrip_H2Target η ε) :
    mobiusBotHStrip_toH2 x0 (mobiusFD_of_botHStrip_H2 x0 η ε hηb hε1 h hh) = h :=
  EuclideanHalfSpace.ext (mobiusBotHStrip_toH2 x0 (mobiusFD_of_botHStrip_H2 x0 η ε hηb hε1 h hh)) h
    (by
      ext (i : Fin 2)
      fin_cases i <;> simp [mobiusBotHStrip_toH2, mobiusFD_of_botHStrip_H2, mobiusBotHStrip_coord,
        mobiusBotHStrip_coord_apply_height, mobiusBotHStrip_coord_apply_offset, add_sub_cancel])

theorem continuous_mobiusFD_of_botHStrip_H2_subtype (x0 η ε : ℝ) (hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) :
    Continuous fun hb : Subtype (mobiusBotHStrip_H2Target η ε) =>
      mobiusFD_of_botHStrip_H2 x0 η ε hηb hε1 hb.val hb.property := by
  have hh2 : Continuous fun hb : Subtype (mobiusBotHStrip_H2Target η ε) => (hb.val : H2).val :=
    continuous_subtype_val.comp continuous_subtype_val
  refine Continuous.prodMk ?_ ?_
  · exact Continuous.subtype_mk (continuous_const.add (continuous_coord1.comp hh2))
      (by
        intro han
        have hv1 : |((han.val : H2).val 1)| < η := by
          have hball :=
            (mobiusFD_mem_mobiusBotHStrip_of_H2 (h := han.val) (hh := han.property) hx0 hηb hε1).1
          simp [mobiusFD_of_botHStrip_H2, Real.norm_eq_abs, Real.dist_eq, sub_add_cancel] at hball
          simpa using hball
        have hv := abs_lt.mp hv1
        have hxp : 0 < x0 + (han.val : H2).val 1 := by linarith [hv.1, hηb.1, hx0.1]
        have hxu : x0 + (han.val : H2).val 1 < 1 := by linarith [hv.2, hηb.2, hx0.2]
        exact ⟨le_of_lt hxp, le_of_lt hxu⟩)
  · exact Continuous.subtype_mk (continuous_coord0.comp hh2)
      (by
        intro han
        exact (mobiusFD_of_botHStrip_H2 x0 η ε hηb hε1 han.val han.property).2.property)

/-- `Subtype` of the bot strip ↔ target charts in `H2`. -/
noncomputable def mobiusBotHStripHomeomorph (x0 η ε : ℝ) (hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) :
    { p : MobiusFundamentalDomain // p ∈ mobiusBotHStrip x0 η ε } ≃ₜ
      Subtype (mobiusBotHStrip_H2Target η ε) where
  toFun w :=
    ⟨mobiusBotHStrip_toH2 x0 w.val, mobiusBotHStrip_toH2_mem_target w.property⟩
  invFun hb :=
    ⟨mobiusFD_of_botHStrip_H2 x0 η ε hηb hε1 hb.val hb.property,
      mobiusFD_mem_mobiusBotHStrip_of_H2 hx0 hηb hε1 hb.property⟩
  left_inv := by
    rintro ⟨p, hp⟩
    exact Subtype.ext (mobiusBotHStrip_toH2_of_FD hx0 hηb hε1 hp)
  right_inv := by
    intro hb
    exact Subtype.ext (mobiusBotHStrip_toH2_of_H2 hx0 hηb hε1 hb.property)
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_mobiusBotHStrip_coord x0 |>.comp continuous_subtype_val)
      (by
        intro w
        simpa [mobiusBotHStrip_coord_apply_height] using w.val.2.property.1))
    (by
      intro w
      simpa [mobiusBotHStrip_toH2] using mobiusBotHStrip_toH2_mem_target w.property)
  continuous_invFun := Continuous.subtype_mk
    (continuous_mobiusFD_of_botHStrip_H2_subtype x0 η ε hx0 hηb hε1)
    (by intro hb; exact mobiusFD_mem_mobiusBotHStrip_of_H2 hx0 hηb hε1 hb.property)

/-! ### Top edge (interior in `x`, height `1`): `H2` chart with first coord `1 - t` -/

def mobiusTopHStrip (x0 η ε : ℝ) : Set MobiusFundamentalDomain :=
  { p | p.1.val ∈ Metric.ball x0 η ∧ 1 - p.2.val < ε }

theorem isOpen_mobiusTopHStrip {x0 η ε : ℝ} (_hη : 0 < η) (_hε : 0 < ε) :
    IsOpen (mobiusTopHStrip x0 η ε) := by
  have hx :
      IsOpen { p : MobiusFundamentalDomain | p.1.val ∈ Metric.ball x0 η } :=
    (continuous_subtype_val.comp continuous_fst).isOpen_preimage (s := Metric.ball x0 η)
      Metric.isOpen_ball
  have ht :
      IsOpen { p : MobiusFundamentalDomain | 1 - p.2.val < ε } :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).isOpen_preimage
      (s := Iio ε) isOpen_Iio
  simpa [mobiusTopHStrip] using hx.inter ht

theorem mobiusTopHStrip_sat {x0 η ε : ℝ}
    (hx0 : 0 < x0 ∧ x0 < 1)
    (_hη : 0 < η)
    (hηb : η < x0 ∧ η < 1 - x0) :
    ∀ ⦃x y : MobiusFundamentalDomain⦄,
      x ∈ mobiusTopHStrip x0 η ε → mobiusRel₀ x y → y ∈ mobiusTopHStrip x0 η ε := by
  rintro x y hx hr
  rcases hr with rfl | hglue
  · exact hx
  · rcases hglue with ⟨hx0', hq1, hs⟩ | ⟨hq0, hp1, hs⟩
    · exfalso
      rcases hx with ⟨hball, _⟩
      rw [hx0'] at hball
      simp [Real.dist_eq, abs_of_pos hx0.1] at hball
      linarith [hball, hηb.1]
    · exfalso
      rcases hx with ⟨hball, _⟩
      rw [hp1] at hball
      have h1mx0 : 0 < 1 - x0 := sub_pos.mpr hx0.2
      simp [Real.dist_eq, abs_of_pos h1mx0] at hball
      linarith [hball, hηb.2]

theorem mobiusRel₀_injective_on_mobiusTopHStrip {x0 η ε : ℝ}
    (hx0 : 0 < x0 ∧ x0 < 1)
    (_hη : 0 < η)
    (hηb : η < x0 ∧ η < 1 - x0) :
    Injective (fun w : Subtype (mobiusTopHStrip x0 η ε) =>
      Quotient.mk mobiusSetoid w.val) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
  refine Subtype.ext ?_
  have hr := Quotient.exact heq
  rcases hr with rfl | hglue
  · rfl
  · rcases hglue with ⟨ha0, hb1, hs⟩ | ⟨hb0, ha1, hs⟩
    · exfalso
      rcases ha with ⟨haball, _⟩
      rw [ha0] at haball
      simp [Real.dist_eq, abs_of_pos hx0.1] at haball
      linarith [haball, hηb.1]
    · exfalso
      rcases ha with ⟨haball, _⟩
      rw [ha1] at haball
      have h1mx0 : 0 < 1 - x0 := sub_pos.mpr hx0.2
      simp [Real.dist_eq, abs_of_pos h1mx0] at haball
      linarith [haball, hηb.2]

noncomputable def mobiusTopHStrip_coord (x0 : ℝ) (p : MobiusFundamentalDomain) : R2 :=
  EuclideanSpace.single (0 : Fin 2) (1 - p.2.val) + EuclideanSpace.single (1 : Fin 2) (p.1.val - x0)

private lemma mobiusTopHStrip_coord_apply_height (x0 : ℝ) (p : MobiusFundamentalDomain) :
    mobiusTopHStrip_coord x0 p 0 = 1 - p.2.val := by
  simp [mobiusTopHStrip_coord, PiLp.add_apply, EuclideanSpace.single_apply]

private lemma mobiusTopHStrip_coord_apply_offset (x0 : ℝ) (p : MobiusFundamentalDomain) :
    mobiusTopHStrip_coord x0 p 1 = p.1.val - x0 := by
  simp [mobiusTopHStrip_coord, PiLp.add_apply, EuclideanSpace.single_apply, add_zero]

theorem continuous_mobiusTopHStrip_coord (x0 : ℝ) :
    Continuous fun p : MobiusFundamentalDomain => mobiusTopHStrip_coord x0 p := by
  have ht : Continuous fun p : MobiusFundamentalDomain => p.2.val :=
    continuous_subtype_val.comp continuous_snd
  have hx : Continuous fun p : MobiusFundamentalDomain => p.1.val :=
    continuous_subtype_val.comp continuous_fst
  refine Continuous.add ?_ ?_
  · exact (continuous_euclideanSpace_single_param 0).comp (continuous_const.sub ht)
  · exact (continuous_euclideanSpace_single_param 1).comp (hx.sub continuous_const)

noncomputable def mobiusTopHStrip_toH2 (x0 : ℝ) (p : MobiusFundamentalDomain) : H2 :=
  ⟨mobiusTopHStrip_coord x0 p, by
    rw [mobiusTopHStrip_coord_apply_height]
    exact sub_nonneg.mpr p.2.property.2⟩

theorem mobiusTopHStrip_toH2_mem_target {x0 η ε : ℝ} {p : MobiusFundamentalDomain}
    (hp : p ∈ mobiusTopHStrip x0 η ε) :
    mobiusTopHStrip_toH2 x0 p ∈ mobiusBotHStrip_H2Target η ε := by
  rcases hp with ⟨hxb, hxt⟩
  refine And.intro ?_ ?_
  · simpa [mobiusTopHStrip_toH2, mobiusTopHStrip_coord_apply_height] using hxt
  · simpa [mobiusTopHStrip_toH2, mobiusTopHStrip_coord_apply_offset, Metric.mem_ball, dist_eq,
      sub_zero] using mem_ball_iff_norm.mp hxb

noncomputable def mobiusFD_of_topHStrip_H2 (x0 η ε : ℝ)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) (h : H2)
    (hh : h ∈ mobiusBotHStrip_H2Target η ε) : MobiusFundamentalDomain :=
  have hv1 : |h.val 1| < η := by
    rcases hh with ⟨_, Hball⟩
    simpa [dist_eq, Real.norm_eq_abs] using mem_ball_iff_norm.mp Hball
  have hx_lo : 0 < x0 + h.val 1 := by
    have hvl := (abs_lt.mp hv1).1
    linarith [hvl, hηb.1]
  have hx_hi : x0 + h.val 1 < 1 := by
    have hvr := (abs_lt.mp hv1).2
    linarith [hvr, hηb.2]
  have ht0_lo : 0 ≤ 1 - h.val 0 := sub_nonneg.mpr (le_of_lt (lt_of_lt_of_le hh.1 hε1))
  have ht0_hi : 1 - h.val 0 ≤ 1 := by linarith [h.property]
  (⟨x0 + h.val 1, ⟨le_of_lt hx_lo, le_of_lt hx_hi⟩⟩,
    ⟨1 - h.val 0, ⟨ht0_lo, ht0_hi⟩⟩)

theorem mobiusFD_mem_mobiusTopHStrip_of_H2 {x0 η ε : ℝ} (_hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) {h : H2}
    (hh : h ∈ mobiusBotHStrip_H2Target η ε) :
    mobiusFD_of_topHStrip_H2 x0 η ε hηb hε1 h hh ∈ mobiusTopHStrip x0 η ε := by
  dsimp [mobiusTopHStrip, mobiusFD_of_topHStrip_H2]
  refine And.intro ?_ ?_
  · rw [mem_ball_iff_norm]
    rcases hh with ⟨_, Hball⟩
    simpa [sub_add_cancel, Real.norm_eq_abs, Real.dist_eq] using mem_ball_iff_norm.mp Hball
  · have h01 : h.val 0 ≤ 1 := le_of_lt (lt_of_lt_of_le hh.1 hε1)
    simpa [tsub_tsub_cancel_of_le h01] using hh.1

theorem mobiusTopHStrip_toH2_of_FD {x0 η ε : ℝ} (_hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) {p : MobiusFundamentalDomain}
    (hp : p ∈ mobiusTopHStrip x0 η ε) :
    mobiusFD_of_topHStrip_H2 x0 η ε hηb hε1 (mobiusTopHStrip_toH2 x0 p)
        (mobiusTopHStrip_toH2_mem_target hp) =
      p := by
  rcases p with ⟨px, pt⟩
  simp [mobiusFD_of_topHStrip_H2, mobiusTopHStrip_toH2, mobiusTopHStrip_coord_apply_height,
    mobiusTopHStrip_coord_apply_offset, add_sub_cancel, tsub_tsub_cancel_of_le pt.property.2]

theorem mobiusTopHStrip_toH2_of_H2 {x0 η ε : ℝ} (_hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) {h : H2}
    (hh : h ∈ mobiusBotHStrip_H2Target η ε) :
    mobiusTopHStrip_toH2 x0 (mobiusFD_of_topHStrip_H2 x0 η ε hηb hε1 h hh) = h :=
  EuclideanHalfSpace.ext (mobiusTopHStrip_toH2 x0 (mobiusFD_of_topHStrip_H2 x0 η ε hηb hε1 h hh)) h
    (by
      ext (i : Fin 2)
      fin_cases i <;> simp [mobiusTopHStrip_toH2, mobiusFD_of_topHStrip_H2, mobiusTopHStrip_coord,
        mobiusTopHStrip_coord_apply_height, mobiusTopHStrip_coord_apply_offset, add_sub_cancel])

theorem continuous_mobiusFD_of_topHStrip_H2_subtype (x0 η ε : ℝ) (hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) :
    Continuous fun hb : Subtype (mobiusBotHStrip_H2Target η ε) =>
      mobiusFD_of_topHStrip_H2 x0 η ε hηb hε1 hb.val hb.property := by
  have hh2 : Continuous fun hb : Subtype (mobiusBotHStrip_H2Target η ε) => (hb.val : H2).val :=
    continuous_subtype_val.comp continuous_subtype_val
  refine Continuous.prodMk ?_ ?_
  · exact Continuous.subtype_mk (continuous_const.add (continuous_coord1.comp hh2))
      (by
        intro han
        have hv1 : |((han.val : H2).val 1)| < η := by
          have hball :=
            (mobiusFD_mem_mobiusTopHStrip_of_H2 (h := han.val) (hh := han.property) hx0 hηb hε1).1
          simp [mobiusFD_of_topHStrip_H2, Real.norm_eq_abs, Real.dist_eq, sub_add_cancel] at hball
          simpa using hball
        have hv := abs_lt.mp hv1
        have hxp : 0 < x0 + (han.val : H2).val 1 := by linarith [hv.1, hηb.1, hx0.1]
        have hxu : x0 + (han.val : H2).val 1 < 1 := by linarith [hv.2, hηb.2, hx0.2]
        exact ⟨le_of_lt hxp, le_of_lt hxu⟩)
  · exact Continuous.subtype_mk (continuous_const.sub (continuous_coord0.comp hh2))
      (by
        intro han
        exact (mobiusFD_of_topHStrip_H2 x0 η ε hηb hε1 han.val han.property).2.property)

noncomputable def mobiusTopHStripHomeomorph (x0 η ε : ℝ) (hx0 : 0 < x0 ∧ x0 < 1)
    (hηb : η < x0 ∧ η < 1 - x0) (hε1 : ε ≤ 1) :
    { p : MobiusFundamentalDomain // p ∈ mobiusTopHStrip x0 η ε } ≃ₜ
      Subtype (mobiusBotHStrip_H2Target η ε) where
  toFun w :=
    ⟨mobiusTopHStrip_toH2 x0 w.val, mobiusTopHStrip_toH2_mem_target w.property⟩
  invFun hb :=
    ⟨mobiusFD_of_topHStrip_H2 x0 η ε hηb hε1 hb.val hb.property,
      mobiusFD_mem_mobiusTopHStrip_of_H2 hx0 hηb hε1 hb.property⟩
  left_inv := by
    rintro ⟨p, hp⟩
    exact Subtype.ext (mobiusTopHStrip_toH2_of_FD hx0 hηb hε1 hp)
  right_inv := by
    intro hb
    exact Subtype.ext (mobiusTopHStrip_toH2_of_H2 hx0 hηb hε1 hb.property)
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_mobiusTopHStrip_coord x0 |>.comp continuous_subtype_val)
      (by
        intro w
        simpa [mobiusTopHStrip_coord_apply_height] using sub_nonneg.mpr w.val.2.property.2))
    (by
      intro w
      simpa [mobiusTopHStrip_toH2] using mobiusTopHStrip_toH2_mem_target w.property)
  continuous_invFun := Continuous.subtype_mk
    (continuous_mobiusFD_of_topHStrip_H2_subtype x0 η ε hx0 hηb hε1)
    (by intro hb; exact mobiusFD_mem_mobiusTopHStrip_of_H2 hx0 hηb hε1 hb.property)

/-! **`¬ ChartableR2` at bot-boundary interior edge -/

theorem not_chartableR2_mobiusQuotientMk_of_bot_edge_Ioo {p : MobiusFundamentalDomain}
    (h1 : 0 < p.1.val ∧ p.1.val < 1) (h2 : p.2.val = 0) :
    ¬ ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  let π := Quotient.mk mobiusSetoid
  let x0 := p.1.val
  have hx0 : 0 < x0 ∧ x0 < 1 := h1
  set η := min x0 (1 - x0) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    have hm : 0 < min x0 (1 - x0) := lt_min hx0.1 (sub_pos.mpr hx0.2)
    linarith
  have hηb : η < x0 ∧ η < 1 - x0 := by
    constructor
    · rw [hηdef]
      have hm := min_le_left x0 (1 - x0)
      nlinarith [hm, hx0.1]
    · rw [hηdef]
      have hm := min_le_right x0 (1 - x0)
      nlinarith [hm, sub_pos.mpr hx0.2]
  let ε : ℝ := (1 / 2 : ℝ)
  have hεpos : 0 < ε := by norm_num
  have hε1 : ε ≤ 1 := by norm_num
  let W : Set MobiusFundamentalDomain := mobiusBotHStrip x0 η ε
  have hWo : IsOpen W := isOpen_mobiusBotHStrip hηpos hεpos
  have hpW : p ∈ W := by
    constructor
    · exact Metric.mem_ball_self hηpos
    · simpa [ε, h2] using hεpos
  have hsat := mobiusBotHStrip_sat (ε := ε) hx0 hηpos hηb
  have hinj := mobiusRel₀_injective_on_mobiusBotHStrip (ε := ε) hx0 hηpos hηb
  let U : Set MobiusStrip := π '' W
  have hUo : IsOpen U := isOpen_mobiusQuotient_image_of_saturated W hWo hsat
  have hpU : π p ∈ U := ⟨p, hpW, rfl⟩
  let φQS := (mobiusQuotientMk_subtype_homeomorph hWo hsat hinj).symm
  let ψ := mobiusBotHStripHomeomorph x0 η ε hx0 hηb hε1
  let χ := φQS.trans ψ
  have hBt : IsOpen (mobiusBotHStrip_H2Target η ε) :=
    isOpen_mobiusBotHStrip_H2Target hηpos hεpos
  have hfEmb :
      IsOpenEmbedding fun u : Subtype U => (χ u : H2) :=
    hBt.isOpenEmbedding_subtypeVal.comp χ.isOpenEmbedding
  have hf0 : (χ ⟨π p, hpU⟩ : H2) = 0 := by
    let Ξ := mobiusQuotientMk_subtype_homeomorph hWo hsat hinj
    have hπeq : π (φQS ⟨π p, hpU⟩).val = π p :=
      congrArg Subtype.val (Ξ.apply_symm_apply ⟨π p, hpU⟩)
    have hu : φQS ⟨π p, hpU⟩ = ⟨p, hpW⟩ := hinj hπeq
    have hval : (χ ⟨π p, hpU⟩ : H2) = mobiusBotHStrip_toH2 x0 p := by
      dsimp [χ, mobiusBotHStripHomeomorph, Homeomorph.trans_apply]
      rw [hu]
      rfl
    rw [hval]
    refine EuclideanHalfSpace.ext (mobiusBotHStrip_toH2 x0 p) (0 : H2) ?_
    simp only [mobiusBotHStrip_toH2]
    have hH0val : (0 : H2).val = (0 : R2) := rfl
    rw [hH0val]
    ext (i : Fin 2)
    fin_cases i
    · simp [mobiusBotHStrip_coord_apply_height, h2]
    · simp [mobiusBotHStrip_coord_apply_offset, show x0 = p.1.val from rfl, sub_self]
  exact not_chartableR2_of_isOpenEmbedding_H2 (U := U) hUo hpU
    (fun u => (χ u : H2)) hfEmb hf0

/-! **`¬ ChartableR2` at top-boundary interior edge (`t = 1`) -/

theorem not_chartableR2_mobiusQuotientMk_of_top_edge_Ioo {p : MobiusFundamentalDomain}
    (h1 : 0 < p.1.val ∧ p.1.val < 1) (h2 : p.2.val = 1) :
    ¬ ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  let π := Quotient.mk mobiusSetoid
  let x0 := p.1.val
  have hx0 : 0 < x0 ∧ x0 < 1 := h1
  set η := min x0 (1 - x0) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    have hm : 0 < min x0 (1 - x0) := lt_min hx0.1 (sub_pos.mpr hx0.2)
    linarith
  have hηb : η < x0 ∧ η < 1 - x0 := by
    constructor
    · rw [hηdef]
      have hm := min_le_left x0 (1 - x0)
      nlinarith [hm, hx0.1]
    · rw [hηdef]
      have hm := min_le_right x0 (1 - x0)
      nlinarith [hm, sub_pos.mpr hx0.2]
  let ε : ℝ := (1 / 2 : ℝ)
  have hεpos : 0 < ε := by norm_num
  have hε1 : ε ≤ 1 := by norm_num
  let W : Set MobiusFundamentalDomain := mobiusTopHStrip x0 η ε
  have hWo : IsOpen W := isOpen_mobiusTopHStrip hηpos hεpos
  have hpW : p ∈ W := by
    constructor
    · exact Metric.mem_ball_self hηpos
    · simpa [ε, h2] using hεpos
  have hsat := mobiusTopHStrip_sat (ε := ε) hx0 hηpos hηb
  have hinj := mobiusRel₀_injective_on_mobiusTopHStrip (ε := ε) hx0 hηpos hηb
  let U : Set MobiusStrip := π '' W
  have hUo : IsOpen U := isOpen_mobiusQuotient_image_of_saturated W hWo hsat
  have hpU : π p ∈ U := ⟨p, hpW, rfl⟩
  let φQS := (mobiusQuotientMk_subtype_homeomorph hWo hsat hinj).symm
  let ψ := mobiusTopHStripHomeomorph x0 η ε hx0 hηb hε1
  let χ := φQS.trans ψ
  have hBt : IsOpen (mobiusBotHStrip_H2Target η ε) :=
    isOpen_mobiusBotHStrip_H2Target hηpos hεpos
  have hfEmb :
      IsOpenEmbedding fun u : Subtype U => (χ u : H2) :=
    hBt.isOpenEmbedding_subtypeVal.comp χ.isOpenEmbedding
  have hf0 : (χ ⟨π p, hpU⟩ : H2) = 0 := by
    let Ξ := mobiusQuotientMk_subtype_homeomorph hWo hsat hinj
    have hπeq : π (φQS ⟨π p, hpU⟩).val = π p :=
      congrArg Subtype.val (Ξ.apply_symm_apply ⟨π p, hpU⟩)
    have hu : φQS ⟨π p, hpU⟩ = ⟨p, hpW⟩ := hinj hπeq
    have hval : (χ ⟨π p, hpU⟩ : H2) = mobiusTopHStrip_toH2 x0 p := by
      dsimp [χ, mobiusTopHStripHomeomorph, Homeomorph.trans_apply]
      rw [hu]
      rfl
    rw [hval]
    refine EuclideanHalfSpace.ext (mobiusTopHStrip_toH2 x0 p) (0 : H2) ?_
    simp only [mobiusTopHStrip_toH2]
    have hH0val : (0 : H2).val = (0 : R2) := rfl
    rw [hH0val]
    ext (i : Fin 2)
    fin_cases i
    · simp [mobiusTopHStrip_coord_apply_height, h2]
    · simp [mobiusTopHStrip_coord_apply_offset, show x0 = p.1.val from rfl, sub_self]
  exact not_chartableR2_of_isOpenEmbedding_H2 (U := U) hUo hpU
    (fun u => (χ u : H2)) hfEmb hf0

/-! ### Boundary **corners** (endpoints in `x`) via sequential limits -/

private lemma mobiusFD_hIcc_div_succ_mem (n : ℕ) : (1 / (n + 2 : ℝ)) ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg zero_le_one (by simpa [Nat.cast_add, Nat.cast_one] using Nat.cast_nonneg (n + 2)),
    by
      rw [div_le_one₀]
      · norm_cast
        linarith
      · exact_mod_cast Nat.zero_lt_succ _⟩

private lemma mobiusFD_hIcc_one_sub_div_succ_mem (n : ℕ) : (1 - 1 / (n + 2 : ℝ)) ∈ Icc (0 : ℝ) 1 := by
  have hnn : 0 ≤ 1 / (n + 2 : ℝ) :=
    div_nonneg zero_le_one (by simpa [Nat.cast_add, Nat.cast_one] using Nat.cast_nonneg (n + 2))
  have hle1 : 1 / (n + 2 : ℝ) ≤ 1 := by
    rw [div_le_one₀]
    · norm_cast
      linarith
    · exact_mod_cast Nat.zero_lt_succ _
  exact ⟨sub_nonneg.mpr hle1, by linarith [hnn]⟩

private lemma tendsto_quotient_mk_fd_bot_left_corner :
    Tendsto (fun n : ℕ =>
        Quotient.mk mobiusSetoid
          (⟨(1 / (n + 2 : ℝ)), mobiusFD_hIcc_div_succ_mem n⟩, mobiusIcc0)) atTop
      (𝓝 (Quotient.mk mobiusSetoid (mobiusIcc0, mobiusIcc0))) := by
  have hπ : Continuous (Quotient.mk mobiusSetoid) :=
    continuous_quotient_mk' (X := MobiusFundamentalDomain) (s := mobiusSetoid)
  refine (hπ.tendsto (mobiusIcc0, mobiusIcc0)).comp ?_
  refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
  refine tendsto_subtype_rng.mpr ?_
  have hseq :
      (fun n : ℕ => (1 / (n + 2 : ℝ) : ℝ)) =
        (fun m : ℕ => (1 / (m + 1 : ℝ) : ℝ)) ∘ (fun n : ℕ => n + 1) := by
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  rw [hseq]
  exact Tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (tendsto_add_atTop_nat 1)

private lemma tendsto_quotient_mk_fd_bot_right_corner :
    Tendsto (fun n : ℕ =>
        Quotient.mk mobiusSetoid
          (⟨(1 - 1 / (n + 2 : ℝ)), mobiusFD_hIcc_one_sub_div_succ_mem n⟩, mobiusIcc0)) atTop
      (𝓝 (Quotient.mk mobiusSetoid (mobiusIcc1, mobiusIcc0))) := by
  have hπ : Continuous (Quotient.mk mobiusSetoid) :=
    continuous_quotient_mk' (X := MobiusFundamentalDomain) (s := mobiusSetoid)
  refine (hπ.tendsto (mobiusIcc1, mobiusIcc0)).comp ?_
  refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
  have hseq :
      (fun n : ℕ => (1 / (n + 2 : ℝ) : ℝ)) =
        (fun m : ℕ => (1 / (m + 1 : ℝ) : ℝ)) ∘ (fun n : ℕ => n + 1) := by
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hlim : Tendsto (fun n : ℕ => (1 / (n + 2 : ℝ) : ℝ)) atTop (𝓝 0) := by
    rw [hseq]
    exact Tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (tendsto_add_atTop_nat 1)
  have Hco :=
    Tendsto.congr (by intro n; rfl) (Tendsto.const_sub (1 : ℝ) hlim)
  have hp : (1 - 0 : ℝ) = (mobiusIcc1 : ℝ) := by
    rw [sub_zero]
    rfl
  rw [congrArg nhds hp] at Hco
  exact tendsto_subtype_rng.mpr Hco

private lemma tendsto_quotient_mk_fd_top_left_corner :
    Tendsto (fun n : ℕ =>
        Quotient.mk mobiusSetoid
          (⟨(1 / (n + 2 : ℝ)), mobiusFD_hIcc_div_succ_mem n⟩, mobiusIcc1)) atTop
      (𝓝 (Quotient.mk mobiusSetoid (mobiusIcc0, mobiusIcc1))) := by
  have hπ : Continuous (Quotient.mk mobiusSetoid) :=
    continuous_quotient_mk' (X := MobiusFundamentalDomain) (s := mobiusSetoid)
  refine (hπ.tendsto (mobiusIcc0, mobiusIcc1)).comp ?_
  refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
  refine tendsto_subtype_rng.mpr ?_
  have hseq :
      (fun n : ℕ => (1 / (n + 2 : ℝ) : ℝ)) =
        (fun m : ℕ => (1 / (m + 1 : ℝ) : ℝ)) ∘ (fun n : ℕ => n + 1) := by
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  rw [hseq]
  exact Tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (tendsto_add_atTop_nat 1)

private lemma tendsto_quotient_mk_fd_top_right_corner :
    Tendsto (fun n : ℕ =>
        Quotient.mk mobiusSetoid
          (⟨(1 - 1 / (n + 2 : ℝ)), mobiusFD_hIcc_one_sub_div_succ_mem n⟩, mobiusIcc1)) atTop
      (𝓝 (Quotient.mk mobiusSetoid (mobiusIcc1, mobiusIcc1))) := by
  have hπ : Continuous (Quotient.mk mobiusSetoid) :=
    continuous_quotient_mk' (X := MobiusFundamentalDomain) (s := mobiusSetoid)
  refine (hπ.tendsto (mobiusIcc1, mobiusIcc1)).comp ?_
  refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
  have hseq :
      (fun n : ℕ => (1 / (n + 2 : ℝ) : ℝ)) =
        (fun m : ℕ => (1 / (m + 1 : ℝ) : ℝ)) ∘ (fun n : ℕ => n + 1) := by
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hlim : Tendsto (fun n : ℕ => (1 / (n + 2 : ℝ) : ℝ)) atTop (𝓝 0) := by
    rw [hseq]
    exact Tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (tendsto_add_atTop_nat 1)
  have Hco :=
    Tendsto.congr (by intro n; rfl) (Tendsto.const_sub (1 : ℝ) hlim)
  have hp : (1 - 0 : ℝ) = (mobiusIcc1 : ℝ) := by
    rw [sub_zero]
    rfl
  rw [congrArg nhds hp] at Hco
  exact tendsto_subtype_rng.mpr Hco

/-! **All bot / top boundary classes** -/

theorem not_chartableR2_mobiusQuotientMk_of_bot_edge {p : MobiusFundamentalDomain}
    (h2 : p.2.val = 0) : ¬ ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  by_cases hmid : 0 < p.1.val ∧ p.1.val < 1
  · exact not_chartableR2_mobiusQuotientMk_of_bot_edge_Ioo hmid h2
  · rcases p.1.property with ⟨h0, h1⟩
    have hdec : p.1.val = 0 ∨ p.1.val = 1 := by
      by_contra hn'
      push_neg at hn'
      obtain ⟨hn0, hn1⟩ := hn'
      have hpos : 0 < p.1.val := lt_of_le_of_ne h0 hn0.symm
      have hlt1 : p.1.val < 1 := lt_of_le_of_ne h1 hn1
      exact hmid ⟨hpos, hlt1⟩
    rcases hdec with hp0 | hp1
    · have hp : p = (mobiusIcc0, mobiusIcc0) := by
        rcases p with ⟨px, pt⟩
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simpa [mobiusIcc0_val] using hp0
        · simpa [mobiusIcc0_val] using h2
      subst hp
      refine not_chartableR2_of_tendsto_seq_atTop tendsto_quotient_mk_fd_bot_left_corner ?_
      intro n
      have hx :
          0 < (⟨(1 / (n + 2 : ℝ)), mobiusFD_hIcc_div_succ_mem n⟩ : Icc (0 : ℝ) 1).val ∧
            (⟨(1 / (n + 2 : ℝ)), mobiusFD_hIcc_div_succ_mem n⟩ : Icc (0 : ℝ) 1).val < 1 := by
        constructor
        · positivity
        · have : (1 / (n + 2 : ℝ) : ℝ) < 1 := by
            rw [div_lt_one₀]
            · norm_cast
              linarith
            · exact_mod_cast Nat.zero_lt_succ _
          simpa using this
      exact not_chartableR2_mobiusQuotientMk_of_bot_edge_Ioo hx rfl
    · have hp : p = (mobiusIcc1, mobiusIcc0) := by
        rcases p with ⟨px, pt⟩
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simpa [mobiusIcc1_val] using hp1
        · simpa [mobiusIcc0_val] using h2
      subst hp
      refine not_chartableR2_of_tendsto_seq_atTop tendsto_quotient_mk_fd_bot_right_corner ?_
      intro n
      have hm0 : 0 < 1 - 1 / (n + 2 : ℝ) := by
        have : (1 / (n + 2 : ℝ) : ℝ) < 1 := by
          rw [div_lt_one₀]
          · norm_cast
            linarith
          · exact_mod_cast Nat.zero_lt_succ _
        linarith
      have hm1 : 1 - 1 / (n + 2 : ℝ) < 1 := sub_lt_self _ (by positivity)
      exact not_chartableR2_mobiusQuotientMk_of_bot_edge_Ioo ⟨hm0, hm1⟩ rfl

theorem not_chartableR2_mobiusQuotientMk_of_top_edge {p : MobiusFundamentalDomain}
    (h2 : p.2.val = 1) : ¬ ChartableR2 (Quotient.mk mobiusSetoid p) := by
  classical
  by_cases hmid : 0 < p.1.val ∧ p.1.val < 1
  · exact not_chartableR2_mobiusQuotientMk_of_top_edge_Ioo hmid h2
  · rcases p.1.property with ⟨h0, h1⟩
    have hdec : p.1.val = 0 ∨ p.1.val = 1 := by
      by_contra hn'
      push_neg at hn'
      obtain ⟨hn0, hn1⟩ := hn'
      have hpos : 0 < p.1.val := lt_of_le_of_ne h0 hn0.symm
      have hlt1 : p.1.val < 1 := lt_of_le_of_ne h1 hn1
      exact hmid ⟨hpos, hlt1⟩
    rcases hdec with hp0 | hp1
    · have hp : p = (mobiusIcc0, mobiusIcc1) := by
        rcases p with ⟨px, pt⟩
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simpa [mobiusIcc0_val] using hp0
        · simpa [mobiusIcc1_val] using h2
      subst hp
      refine not_chartableR2_of_tendsto_seq_atTop tendsto_quotient_mk_fd_top_left_corner ?_
      intro n
      have hx :
          0 < (⟨(1 / (n + 2 : ℝ)), mobiusFD_hIcc_div_succ_mem n⟩ : Icc (0 : ℝ) 1).val ∧
            (⟨(1 / (n + 2 : ℝ)), mobiusFD_hIcc_div_succ_mem n⟩ : Icc (0 : ℝ) 1).val < 1 := by
        constructor
        · positivity
        · have : (1 / (n + 2 : ℝ) : ℝ) < 1 := by
            rw [div_lt_one₀]
            · norm_cast
              linarith
            · exact_mod_cast Nat.zero_lt_succ _
          simpa using this
      exact not_chartableR2_mobiusQuotientMk_of_top_edge_Ioo hx rfl
    · have hp : p = (mobiusIcc1, mobiusIcc1) := by
        rcases p with ⟨px, pt⟩
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simpa [mobiusIcc1_val] using hp1
        · simpa [mobiusIcc1_val] using h2
      subst hp
      refine not_chartableR2_of_tendsto_seq_atTop tendsto_quotient_mk_fd_top_right_corner ?_
      intro n
      have hm0 : 0 < 1 - 1 / (n + 2 : ℝ) := by
        have : (1 / (n + 2 : ℝ) : ℝ) < 1 := by
          rw [div_lt_one₀]
          · norm_cast
            linarith
          · exact_mod_cast Nat.zero_lt_succ _
        linarith
      have hm1 : 1 - 1 / (n + 2 : ℝ) < 1 := sub_lt_self _ (by positivity)
      exact not_chartableR2_mobiusQuotientMk_of_top_edge_Ioo ⟨hm0, hm1⟩ rfl

/-- **Möbius model C4 (boundary ⇒ not plane-chartable):** every point of `mobiusStripBoundary` fails
  `ChartableR2`. -/
theorem not_chartableR2_of_mem_mobiusStripBoundary {x : MobiusStrip}
    (hx : x ∈ mobiusStripBoundary) : ¬ ChartableR2 x := by
  classical
  rcases Quotient.exists_rep x with ⟨p, rfl⟩
  rw [Quotient_mk_mem_mobiusStripBoundary_iff] at hx
  rcases hx with h2 | h2
  · have hval := congrArg Subtype.val h2
    simpa [mobiusIcc0_val] using not_chartableR2_mobiusQuotientMk_of_bot_edge hval
  · have hval := congrArg Subtype.val h2
    simpa [mobiusIcc1_val] using not_chartableR2_mobiusQuotientMk_of_top_edge hval

/-- For a fundamental-domain representative, **not** on the strip boundary iff **height is strictly
  between `0` and `1`** (`SPEC_003` **E2** bookkeeping). -/
theorem quot_mk_not_mem_mobiusStripBoundary_iff {p : MobiusFundamentalDomain} :
    Quotient.mk mobiusSetoid p ∉ mobiusStripBoundary ↔ 0 < p.2.val ∧ p.2.val < 1 := by
  classical
  rw [Quotient_mk_mem_mobiusStripBoundary_iff (p := p), not_or]
  constructor
  · rintro ⟨hn0, hn1⟩
    refine ⟨lt_of_le_of_ne p.2.property.1 ?_, lt_of_le_of_ne p.2.property.2 ?_⟩
    · rintro hval
      apply hn0
      rw [Subtype.ext_iff]
      simp [mobiusIcc0_val, hval]
    · rintro hval
      apply hn1
      rw [Subtype.ext_iff]
      simp [mobiusIcc1_val, hval]
  · rintro ⟨ht0, ht1⟩
    refine ⟨?_, ?_⟩
    · intro heq
      have hv0 : p.2.val = 0 := by simpa [mobiusIcc0_val] using congrArg Subtype.val heq
      linarith
    · intro heq
      have hv1 : p.2.val = 1 := by simpa [mobiusIcc1_val] using congrArg Subtype.val heq
      linarith

/-- **SPEC_003 (E2 reduction).** Full Möbius **C4**
  `∀ x, x ∈ mobiusStripBoundary ↔ ¬ ChartableR2 x` follows from **`not_chartableR2_of_mem_mobiusStripBoundary`**
  and **height–interior** `ChartableR2` on **every** `p` with **`0 < t < 1`**.

  The **remaining mathematical work** is exactly **discharging** the hypothesis
  (**vertical seam** `x ∈ {0,1}` with **`0 < t < 1`**, **`t₀ = ½`**, etc. — see **`MobiusSeamChartableR2`**). -/
theorem mobiusStripBoundary_iff_not_chartableR2_of_forall_off_edge_chartable
    (h :
      ∀ p : MobiusFundamentalDomain, 0 < p.2.val ∧ p.2.val < 1 →
        ChartableR2 (Quotient.mk mobiusSetoid p)) :
    ∀ x : MobiusStrip, x ∈ mobiusStripBoundary ↔ ¬ ChartableR2 x := by
  classical
  intro x
  constructor
  · exact fun hx => not_chartableR2_of_mem_mobiusStripBoundary hx
  · intro hnC
    by_contra hbnd
    rcases Quotient.exists_rep x with ⟨p, rfl⟩
    have ht := quot_mk_not_mem_mobiusStripBoundary_iff.1 hbnd
    exact hnC (h p ht)

end RepresentationalIncompleteness

end
