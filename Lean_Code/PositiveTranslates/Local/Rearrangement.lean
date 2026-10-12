import Lean_Code.PositiveTranslates.Local.Defs
import Lean_Code.SchauderTranslates.Lp.AffineCellMeasure

/-!
# Piecewise affine rearrangements: the pointwise formula

A `Rearrangement ι` consists of countably many pairs (source interval, target interval), all
half-open and nondegenerate, the source intervals pairwise disjoint and the target intervals
pairwise disjoint. It induces the weighted composition

`(R.fn p f) x = ρᵢ^{1/p} · f (αᵢ x)` for `x` in the `i`-th target interval, `0` elsewhere,

where `αᵢ` is the increasing affine map of the `i`-th target interval onto the `i`-th source
interval and `ρᵢ` is its slope. This file contains the pointwise definitions, measurability,
and the change of variables

`∫ |R.fn p f|^p = ∫_{⋃ sources} |f|^p`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

/-- Countably many pairs (source interval `[s₁, s₂)`, target interval `[t₁, t₂)`). -/
structure Rearrangement (ι : Type*) where
  /-- endpoints of the source intervals -/
  src : ι → ℝ × ℝ
  /-- endpoints of the target intervals -/
  tgt : ι → ℝ × ℝ
  src_lt : ∀ i, (src i).1 < (src i).2
  tgt_lt : ∀ i, (tgt i).1 < (tgt i).2
  src_disjoint : Pairwise (Function.onFun Disjoint fun i => Set.Ico (src i).1 (src i).2)
  tgt_disjoint : Pairwise (Function.onFun Disjoint fun i => Set.Ico (tgt i).1 (tgt i).2)

namespace Rearrangement

variable {ι : Type*} (R : Rearrangement ι)

/-- The inverse rearrangement: sources and targets exchanged. -/
def symm : Rearrangement ι where
  src := R.tgt
  tgt := R.src
  src_lt := R.tgt_lt
  tgt_lt := R.src_lt
  src_disjoint := R.tgt_disjoint
  tgt_disjoint := R.src_disjoint

@[simp] theorem symm_symm : R.symm.symm = R := rfl
@[simp] theorem symm_src : R.symm.src = R.tgt := rfl
@[simp] theorem symm_tgt : R.symm.tgt = R.src := rfl

/-- The `i`-th source interval. -/
def srcSet (i : ι) : Set ℝ := Set.Ico (R.src i).1 (R.src i).2

/-- The `i`-th target interval. -/
def tgtSet (i : ι) : Set ℝ := Set.Ico (R.tgt i).1 (R.tgt i).2

/-- The union of the source intervals. -/
def srcUnion : Set ℝ := ⋃ i, R.srcSet i

/-- The union of the target intervals. -/
def tgtUnion : Set ℝ := ⋃ i, R.tgtSet i

@[simp] theorem symm_srcSet (i : ι) : R.symm.srcSet i = R.tgtSet i := rfl
@[simp] theorem symm_tgtSet (i : ι) : R.symm.tgtSet i = R.srcSet i := rfl
@[simp] theorem symm_srcUnion : R.symm.srcUnion = R.tgtUnion := rfl
@[simp] theorem symm_tgtUnion : R.symm.tgtUnion = R.srcUnion := rfl

theorem srcSet_disjoint : Pairwise (Function.onFun Disjoint R.srcSet) := R.src_disjoint
theorem tgtSet_disjoint : Pairwise (Function.onFun Disjoint R.tgtSet) := R.tgt_disjoint

theorem srcSet_subset_srcUnion (i : ι) : R.srcSet i ⊆ R.srcUnion := Set.subset_iUnion _ i
theorem tgtSet_subset_tgtUnion (i : ι) : R.tgtSet i ⊆ R.tgtUnion := Set.subset_iUnion _ i

theorem tgt_index_unique {i j : ι} {x : ℝ} (hi : x ∈ R.tgtSet i) (hj : x ∈ R.tgtSet j) :
    i = j := by
  by_contra hne
  exact Set.disjoint_left.mp (R.tgt_disjoint hne) hi hj

theorem src_index_unique {i j : ι} {x : ℝ} (hi : x ∈ R.srcSet i) (hj : x ∈ R.srcSet j) :
    i = j := R.symm.tgt_index_unique hi hj

/-- The slope of the affine map of the `i`-th target interval onto the `i`-th source
interval. -/
def slope (i : ι) : ℝ := ((R.src i).2 - (R.src i).1) / ((R.tgt i).2 - (R.tgt i).1)

theorem slope_pos (i : ι) : 0 < R.slope i :=
  div_pos (sub_pos.mpr (R.src_lt i)) (sub_pos.mpr (R.tgt_lt i))

theorem symm_slope (i : ι) : R.symm.slope i = (R.slope i)⁻¹ := by
  simp [slope, inv_div]

theorem slope_mul (i : ι) :
    R.slope i * ((R.tgt i).2 - (R.tgt i).1) = (R.src i).2 - (R.src i).1 :=
  div_mul_cancel₀ _ (sub_pos.mpr (R.tgt_lt i)).ne'

/-- The increasing affine map carrying the `i`-th target interval onto the `i`-th source
interval, as a measurable equivalence of the line. -/
def aff (i : ι) : ℝ ≃ᵐ ℝ := affineCell (R.tgt i).1 (R.src i).1 (R.slope i) (R.slope_pos i)

theorem aff_apply (i : ι) (x : ℝ) :
    R.aff i x = (R.src i).1 + R.slope i * (x - (R.tgt i).1) :=
  affineCell_apply _ _ _ _ _

theorem aff_le_aff_iff (i : ι) {x y : ℝ} : R.aff i x ≤ R.aff i y ↔ x ≤ y := by
  rw [aff_apply, aff_apply, add_le_add_iff_left, mul_le_mul_iff_right₀ (R.slope_pos i),
    sub_le_sub_iff_right]

theorem aff_lt_aff_iff (i : ι) {x y : ℝ} : R.aff i x < R.aff i y ↔ x < y := by
  rw [aff_apply, aff_apply, add_lt_add_iff_left, mul_lt_mul_iff_right₀ (R.slope_pos i),
    sub_lt_sub_iff_right]

theorem aff_tgt_fst (i : ι) : R.aff i (R.tgt i).1 = (R.src i).1 := by
  rw [aff_apply, sub_self, mul_zero, add_zero]

theorem aff_tgt_snd (i : ι) : R.aff i (R.tgt i).2 = (R.src i).2 := by
  rw [aff_apply, R.slope_mul i, add_sub_cancel]

theorem aff_mem_srcSet_iff (i : ι) (x : ℝ) : R.aff i x ∈ R.srcSet i ↔ x ∈ R.tgtSet i := by
  rw [srcSet, tgtSet, Set.mem_Ico, Set.mem_Ico, ← R.aff_tgt_fst i, ← R.aff_tgt_snd i,
    aff_le_aff_iff, aff_lt_aff_iff]

theorem symm_aff_aff (i : ι) (x : ℝ) : R.symm.aff i (R.aff i x) = x := by
  have h := (R.slope_pos i).ne'
  rw [aff_apply, aff_apply, symm_slope]
  simp only [symm_src, symm_tgt]
  field_simp
  ring

theorem aff_symm_aff (i : ι) (y : ℝ) : R.aff i (R.symm.aff i y) = y :=
  R.symm.symm_aff_aff i y

theorem symm_aff_le_iff (i : ι) {x y : ℝ} : R.symm.aff i y ≤ x ↔ y ≤ R.aff i x := by
  rw [← R.aff_le_aff_iff i, aff_symm_aff]

theorem lt_symm_aff_iff (i : ι) {x y : ℝ} : x < R.symm.aff i y ↔ R.aff i x < y := by
  rw [← R.aff_lt_aff_iff i, aff_symm_aff]

theorem symm_aff_src_fst (i : ι) : R.symm.aff i (R.src i).1 = (R.tgt i).1 :=
  R.symm.aff_tgt_fst i

theorem symm_aff_src_snd (i : ι) : R.symm.aff i (R.src i).2 = (R.tgt i).2 :=
  R.symm.aff_tgt_snd i

theorem symm_aff_mem_tgtSet_iff (i : ι) (y : ℝ) :
    R.symm.aff i y ∈ R.tgtSet i ↔ y ∈ R.srcSet i :=
  R.symm.aff_mem_srcSet_iff i y

/-- The `i`-th affine map transports `ρᵢ dx` on the target interval to Lebesgue measure on
the source interval. -/
theorem aff_measurePreserving (i : ι) :
    MeasurePreserving (R.aff i) (ENNReal.ofReal (R.slope i) • volume.restrict (R.tgtSet i))
      (volume.restrict (R.srcSet i)) := by
  have h := affineCell_measurePreserving (R.tgt i).1 (R.tgt i).2 (R.src i).1 (R.slope i)
    (R.slope_pos i)
  rw [R.slope_mul i, add_sub_cancel] at h
  exact h

theorem aff_quasiMeasurePreserving (i : ι) :
    Measure.QuasiMeasurePreserving (R.aff i) volume volume := by
  refine ⟨(R.aff i).measurable, ?_⟩
  rw [aff, affineCell, haarAffine_map_volume]
  exact Measure.smul_absolutelyContinuous

/-- An almost everywhere property holds almost everywhere along all the affine maps. -/
theorem ae_aff [Countable ι] {P : ℝ → Prop} (h : ∀ᵐ y : ℝ, P y) :
    ∀ᵐ x : ℝ, ∀ i, P (R.aff i x) :=
  ae_all_iff.mpr fun i => (R.aff_quasiMeasurePreserving i).ae h

/-! ### The weights -/

/-- The weight `ρᵢ^{1/p}` of the `i`-th piece. -/
def weight (p : ℝ≥0∞) (i : ι) : ℝ := R.slope i ^ p.toReal⁻¹

theorem weight_pos (p : ℝ≥0∞) (i : ι) : 0 < R.weight p i :=
  Real.rpow_pos_of_pos (R.slope_pos i) _

theorem symm_weight_mul_weight (p : ℝ≥0∞) (i : ι) : R.symm.weight p i * R.weight p i = 1 := by
  rw [weight, weight, symm_slope, Real.inv_rpow (R.slope_pos i).le,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos (R.slope_pos i) _).ne']

theorem weight_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (i : ι) :
    R.weight p i ^ p.toReal = R.slope i :=
  Real.rpow_inv_rpow (R.slope_pos i).le (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩)

/-! ### The pointwise formula -/

open Classical in
/-- The weighted composition: `ρᵢ^{1/p} · f (αᵢ x)` on the `i`-th target interval and `0`
outside the union of the target intervals. -/
def fn (p : ℝ≥0∞) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if h : ∃ i, x ∈ R.tgtSet i then (R.weight p h.choose : ℂ) * f (R.aff h.choose x) else 0

variable {p : ℝ≥0∞}

theorem fn_of_mem {f : ℝ → ℂ} {i : ι} {x : ℝ} (hx : x ∈ R.tgtSet i) :
    R.fn p f x = (R.weight p i : ℂ) * f (R.aff i x) := by
  have h : ∃ j, x ∈ R.tgtSet j := ⟨i, hx⟩
  have hj : h.choose = i := R.tgt_index_unique h.choose_spec hx
  rw [fn, dif_pos h, hj]

theorem fn_of_notMem {f : ℝ → ℂ} {x : ℝ} (hx : x ∉ R.tgtUnion) : R.fn p f x = 0 := by
  have h : ¬ ∃ j, x ∈ R.tgtSet j := fun ⟨j, hj⟩ => hx (Set.mem_iUnion.mpr ⟨j, hj⟩)
  rw [fn, dif_neg h]

theorem fn_add (f g : ℝ → ℂ) : R.fn p (f + g) = R.fn p f + R.fn p g := by
  funext x
  by_cases hx : x ∈ R.tgtUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [Pi.add_apply, R.fn_of_mem hi, R.fn_of_mem hi, R.fn_of_mem hi, Pi.add_apply, mul_add]
  · rw [Pi.add_apply, R.fn_of_notMem hx, R.fn_of_notMem hx, R.fn_of_notMem hx, add_zero]

theorem fn_smul (a : ℂ) (f : ℝ → ℂ) : R.fn p (a • f) = a • R.fn p f := by
  funext x
  by_cases hx : x ∈ R.tgtUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [Pi.smul_apply, R.fn_of_mem hi, R.fn_of_mem hi, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_left_comm]
  · rw [Pi.smul_apply, R.fn_of_notMem hx, R.fn_of_notMem hx, smul_zero]

/-- Applying the rearrangement and then its inverse cuts a function off to the union of the
source intervals. -/
theorem symm_fn_fn (f : ℝ → ℂ) : R.symm.fn p (R.fn p f) = R.srcUnion.indicator f := by
  funext x
  by_cases hx : x ∈ R.srcUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hi' : x ∈ R.symm.tgtSet i := hi
    rw [R.symm.fn_of_mem hi', R.fn_of_mem ((R.symm_aff_mem_tgtSet_iff i x).mpr hi),
      R.aff_symm_aff, Set.indicator_of_mem hx, ← mul_assoc, ← Complex.ofReal_mul,
      R.symm_weight_mul_weight, Complex.ofReal_one, one_mul]
  · have hx' : x ∉ R.symm.tgtUnion := hx
    rw [R.symm.fn_of_notMem hx', Set.indicator_of_notMem hx]

theorem fn_congr_ae [Countable ι] {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    R.fn p f =ᵐ[volume] R.fn p g := by
  filter_upwards [R.ae_aff h] with x hx
  by_cases hmem : x ∈ R.tgtUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    rw [R.fn_of_mem hi, R.fn_of_mem hi, hx i]
  · rw [R.fn_of_notMem hmem, R.fn_of_notMem hmem]

theorem fn_measurable [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (R.fn p f) := by
  intro s hs
  have hset : R.fn p f ⁻¹' s =
      (⋃ i, R.tgtSet i ∩ (fun x => (R.weight p i : ℂ) * f (R.aff i x)) ⁻¹' s) ∪
        (R.tgtUnionᶜ ∩ {_x : ℝ | (0 : ℂ) ∈ s}) := by
    ext x
    by_cases hx : x ∈ R.tgtUnion
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      constructor
      · intro h
        refine Or.inl (Set.mem_iUnion.mpr ⟨i, hi, ?_⟩)
        rw [Set.mem_preimage, R.fn_of_mem hi] at h
        exact h
      · rintro (h | h)
        · obtain ⟨j, hj, hjs⟩ := Set.mem_iUnion.mp h
          obtain rfl := R.tgt_index_unique hj hi
          rw [Set.mem_preimage, R.fn_of_mem hi]
          exact hjs
        · exact absurd hx h.1
    · constructor
      · intro h
        rw [Set.mem_preimage, R.fn_of_notMem hx] at h
        exact Or.inr ⟨hx, h⟩
      · rintro (h | h)
        · obtain ⟨j, hj, -⟩ := Set.mem_iUnion.mp h
          exact absurd (R.tgtSet_subset_tgtUnion j hj) hx
        · rw [Set.mem_preimage, R.fn_of_notMem hx]
          exact h.2
  rw [hset]
  refine (MeasurableSet.iUnion fun i => measurableSet_Ico.inter ?_).union
    ((MeasurableSet.iUnion fun i => measurableSet_Ico).compl.inter (MeasurableSet.const _))
  exact (measurable_const.mul (hf.comp (R.aff i).measurable)) hs

/-- The change of variables: the `p`-th power integral of `R.fn p f` is the `p`-th power
integral of `f` over the union of the source intervals. -/
theorem lintegral_fn [Countable ι] (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (f : ℝ → ℂ) :
    ∫⁻ x, ‖R.fn p f x‖ₑ ^ p.toReal = ∫⁻ y in R.srcUnion, ‖f y‖ₑ ^ p.toReal := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  have hsupp : Function.support (fun x => ‖R.fn p f x‖ₑ ^ p.toReal) ⊆ R.tgtUnion := by
    intro x hx
    by_contra hout
    apply hx
    simp [R.fn_of_notMem hout, hpR]
  rw [← setLIntegral_eq_of_support_subset hsupp, tgtUnion, srcUnion,
    lintegral_iUnion (s := R.tgtSet) (fun i => measurableSet_Ico) R.tgtSet_disjoint,
    lintegral_iUnion (s := R.srcSet) (fun i => measurableSet_Ico) R.srcSet_disjoint]
  congr 1
  funext i
  have hmp := (R.aff_measurePreserving i).lintegral_comp_emb (R.aff i).measurableEmbedding
    (fun y => ‖f y‖ₑ ^ p.toReal)
  rw [← hmp, lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ico
  intro x hx
  have hw : ‖(R.weight p i : ℂ)‖ₑ ^ p.toReal = ENNReal.ofReal (R.slope i) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (R.weight_pos p i),
      ENNReal.ofReal_rpow_of_nonneg (R.weight_pos p i).le hpR.le, R.weight_rpow hp0 hpfin]
  change ‖R.fn p f x‖ₑ ^ p.toReal = ENNReal.ofReal (R.slope i) * ‖f (R.aff i x)‖ₑ ^ p.toReal
  rw [R.fn_of_mem hx, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hpR.le, hw]

theorem eLpNorm_fn [Countable ι] (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (f : ℝ → ℂ) :
    eLpNorm (R.fn p f) p volume = eLpNorm f p (volume.restrict R.srcUnion) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpfin,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpfin, R.lintegral_fn hp0 hpfin]

theorem eLpNorm_fn_le [Countable ι] (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (f : ℝ → ℂ) :
    eLpNorm (R.fn p f) p volume ≤ eLpNorm f p volume := by
  rw [R.eLpNorm_fn hp0 hpfin]
  exact eLpNorm_mono_measure f Measure.restrict_le_self

end Rearrangement

end StructuredBases.PositiveTranslates
