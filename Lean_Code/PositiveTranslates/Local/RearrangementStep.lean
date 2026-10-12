import Lean_Code.PositiveTranslates.Local.RearrangementOp
import Lean_Code.SchauderTranslates.Lp.IndexedIntervalStep

/-!
# Piecewise affine rearrangements: step functions and local bases

The operator of a rearrangement maps the indicator of an interval `[c, d)` to a combination of
indicators of intervals, one for every source interval meeting `[c, d)`
(`Rearrangement.op_intervalAtom`). If every bounded interval meets only finitely many source
intervals (`Rearrangement.LocallyFinite`), compactly supported step functions are mapped to
compactly supported step functions (`Rearrangement.op_isCompactStep`).

`LocalBasis.rearrange` transports a local basis of `Lᵖ(⋃ sources)` to a local basis of
`Lᵖ(⋃ targets)` with the same prefix constant. `Rearrangement.isCellIsometry_compIsometry`
composes a cell isometry onto `Lᵖ(⋃ sources)` with the operator of the rearrangement.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

/-- The value of a finite real combination of interval atoms. -/
theorem Local.finset_sum_smul_intervalAtom_ae {ι : Type*} (p : ℝ≥0∞) (s : Finset ι) (a : ι → ℝ)
    (J : ι → ℝ × ℝ) :
    (∑ i ∈ s, a i • intervalAtom p (J i) : LebesgueLp p) =ᵐ[volume]
      fun x => ∑ i ∈ s, (a i : ℂ) *
        (Set.Ico (J i).1 (J i).2).indicator (fun _ => (1 : ℂ)) x := by
  have hall : ∀ᵐ x ∂volume, ∀ i ∈ s, (a i • intervalAtom p (J i)) x =
      (a i : ℂ) * (Set.Ico (J i).1 (J i).2).indicator (fun _ => (1 : ℂ)) x := by
    simp only [Filter.eventually_all_finset]
    intro i _
    filter_upwards [intervalAtom_ae p (J i), Lp.coeFn_smul (a i) (intervalAtom p (J i))]
      with x hi hs
    rw [hs, Pi.smul_apply, hi, Complex.real_smul]
  filter_upwards [hall, Lp.coeFn_fun_finsetSum s (fun i => a i • intervalAtom p (J i))]
    with x hall hx
  rw [hx]
  exact Finset.sum_congr rfl (fun i hi => hall i hi)

namespace Rearrangement

variable {ι : Type*} (R : Rearrangement ι)

/-- The endpoints of the part of the `i`-th target interval which the `i`-th affine map
carries into `[c, d)`. -/
def pre (i : ι) (c d : ℝ) : ℝ × ℝ :=
  (R.symm.aff i (max c (R.src i).1), R.symm.aff i (min d (R.src i).2))

theorem mem_pre_iff (i : ι) (c d x : ℝ) :
    x ∈ Set.Ico (R.pre i c d).1 (R.pre i c d).2 ↔
      x ∈ R.tgtSet i ∧ R.aff i x ∈ Set.Ico c d := by
  change R.symm.aff i (max c (R.src i).1) ≤ x ∧ x < R.symm.aff i (min d (R.src i).2) ↔ _
  rw [R.symm_aff_le_iff, R.lt_symm_aff_iff, max_le_iff, lt_min_iff, ← R.aff_mem_srcSet_iff,
    srcSet, Set.mem_Ico, Set.mem_Ico]
  tauto

theorem pre_of_subset {i : ι} {c d : ℝ} (h : R.srcSet i ⊆ Set.Ico c d) :
    R.pre i c d = R.tgt i := by
  have hcd := (Set.Ico_subset_Ico_iff (R.src_lt i)).mp h
  rw [pre, max_eq_right hcd.1, min_eq_right hcd.2, R.symm_aff_src_fst, R.symm_aff_src_snd]

/-- Every bounded interval meets only finitely many source intervals. -/
def LocallyFinite : Prop :=
  ∀ c d : ℝ, ∃ s : Finset ι, ∀ i, i ∉ s → Disjoint (R.srcSet i) (Set.Ico c d)

theorem locallyFinite_of_finite [Finite ι] : R.LocallyFinite := by
  intro c d
  cases nonempty_fintype ι
  exact ⟨Finset.univ, fun i hi => absurd (Finset.mem_univ i) hi⟩

variable [Countable ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpfin : p ≠ ∞)

/-- The image of the indicator of `[c, d)`: one interval for every source interval meeting
`[c, d)`. -/
theorem op_intervalAtom (c d : ℝ) (s : Finset ι)
    (hs : ∀ i, i ∉ s → Disjoint (R.srcSet i) (Set.Ico c d)) :
    R.op hpfin (intervalAtom p (c, d)) =
      ∑ i ∈ s, R.weight p i • intervalAtom p (R.pre i c d) := by
  have hatom : intervalAtom p (c, d) =ᵐ[volume] (Set.Ico c d).indicator (fun _ => (1 : ℂ)) :=
    intervalAtom_ae p (c, d)
  apply R.op_eq_of_ae hpfin hatom
  filter_upwards [finset_sum_smul_intervalAtom_ae p s (R.weight p) (fun i => R.pre i c d)]
    with x hx
  rw [hx]
  by_cases hmem : x ∈ R.tgtUnion
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
    rw [R.fn_of_mem hj]
    have hterm : ∀ i ∈ s, i ≠ j → (R.weight p i : ℂ) *
        (Set.Ico (R.pre i c d).1 (R.pre i c d).2).indicator (fun _ => (1 : ℂ)) x = 0 := by
      intro i _ hij
      have hout : x ∉ Set.Ico (R.pre i c d).1 (R.pre i c d).2 := fun h =>
        hij (R.tgt_index_unique ((R.mem_pre_iff i c d x).mp h).1 hj)
      rw [Set.indicator_of_notMem hout, mul_zero]
    by_cases hjs : j ∈ s
    · rw [Finset.sum_eq_single_of_mem j hjs hterm]
      by_cases hcd : R.aff j x ∈ Set.Ico c d
      · rw [Set.indicator_of_mem hcd,
          Set.indicator_of_mem ((R.mem_pre_iff j c d x).mpr ⟨hj, hcd⟩)]
      · rw [Set.indicator_of_notMem hcd,
          Set.indicator_of_notMem (fun h => hcd ((R.mem_pre_iff j c d x).mp h).2)]
    · have hcd : R.aff j x ∉ Set.Ico c d := fun h =>
        Set.disjoint_left.mp (hs j hjs) ((R.aff_mem_srcSet_iff j x).mpr hj) h
      rw [Set.indicator_of_notMem hcd, mul_zero]
      exact Finset.sum_eq_zero (fun i hi => hterm i hi (fun h => hjs (h ▸ hi)))
  · rw [R.fn_of_notMem hmem]
    apply Finset.sum_eq_zero
    intro i _
    have hout : x ∉ Set.Ico (R.pre i c d).1 (R.pre i c d).2 := fun h =>
      hmem (R.tgtSet_subset_tgtUnion i ((R.mem_pre_iff i c d x).mp h).1)
    rw [Set.indicator_of_notMem hout, mul_zero]

/-- The image of the indicator of an interval which is a finite union of whole source
intervals (and is disjoint from the others). -/
theorem op_intervalAtom_of_union (c d : ℝ) (s : Finset ι)
    (hsub : ∀ i ∈ s, R.srcSet i ⊆ Set.Ico c d)
    (hdis : ∀ i, i ∉ s → Disjoint (R.srcSet i) (Set.Ico c d)) :
    R.op hpfin (intervalAtom p (c, d)) = ∑ i ∈ s, R.weight p i • intervalAtom p (R.tgt i) := by
  rw [R.op_intervalAtom hpfin c d s hdis]
  exact Finset.sum_congr rfl fun i hi => by rw [R.pre_of_subset (hsub i hi)]

/-- The image of the indicator of a source interval is a multiple of the indicator of the
corresponding target interval. -/
theorem op_intervalAtom_src (i : ι) :
    R.op hpfin (intervalAtom p (R.src i)) = R.weight p i • intervalAtom p (R.tgt i) := by
  have h := R.op_intervalAtom_of_union hpfin (R.src i).1 (R.src i).2 {i}
    (fun j hj => by rw [Finset.mem_singleton.mp hj]; exact subset_rfl)
    (fun j hj => R.srcSet_disjoint (fun hji => hj (Finset.mem_singleton.mpr hji)))
  rw [Finset.sum_singleton] at h
  exact h

/-- A locally finite rearrangement maps compactly supported step functions to compactly
supported step functions. -/
theorem op_isCompactStep (hfin : R.LocallyFinite) {F : LebesgueLp p}
    (hF : IsCompactStep p F) : IsCompactStep p (R.op hpfin F) := by
  have hle : (stepSpace p).map ((R.op hpfin).restrictScalars ℝ) ≤ stepSpace p := by
    rw [stepSpace, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨ab, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := hfin ab.1 ab.2
    have h : R.op hpfin (intervalAtom p ab) =
        ∑ i ∈ s, R.weight p i • intervalAtom p (R.pre i ab.1 ab.2) :=
      R.op_intervalAtom hpfin ab.1 ab.2 s hs
    change R.op hpfin (intervalAtom p ab) ∈ _
    rw [h]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  exact hle ⟨F, hF, rfl⟩

/-- A cell isometry onto `Lᵖ(⋃ sources)` followed by the operator of the rearrangement. -/
def compIsometry (T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p)
    (hT : ∀ F, SupportedOn (T F) R.srcUnion) : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p where
  toLinearMap := (R.op hpfin).comp T.toLinearMap
  norm_map' F := by
    change ‖R.op hpfin (T F)‖ = ‖F‖
    rw [R.norm_op_of_supported hpfin (hT F), T.norm_map]

@[simp] theorem compIsometry_apply (T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p)
    (hT : ∀ F, SupportedOn (T F) R.srcUnion) (F : LebesgueLp p) :
    R.compIsometry hpfin T hT F = R.op hpfin (T F) := rfl

/-- A cell isometry onto `Lᵖ(⋃ sources)` followed by a locally finite rearrangement is a
cell isometry onto `Lᵖ(⋃ targets)`. -/
theorem isCellIsometry_compIsometry (hfin : R.LocallyFinite)
    {T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p} (hT : IsCellIsometry T R.srcUnion) :
    IsCellIsometry (R.compIsometry hpfin T hT.supported) R.tgtUnion where
  nonneg F hF := R.op_nonneg hpfin (hT.nonneg F hF)
  step F hF := R.op_isCompactStep hpfin hfin (hT.step F hF)
  supported F := R.op_supported hpfin (T F)
  surj G hG := by
    obtain ⟨F₁, hF₁, rfl⟩ := R.exists_op_eq hpfin hG
    obtain ⟨F, rfl⟩ := hT.surj F₁ hF₁
    exact ⟨F, rfl⟩

end Rearrangement

/-- **Transport of local bases.** A locally finite rearrangement carries a local basis of
`Lᵖ(⋃ sources)` to a local basis of `Lᵖ(⋃ targets)` with the same prefix constant. -/
theorem LocalBasis.rearrange {ι : Type*} [Countable ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β : ℕ → LebesgueLp p} {B : ℝ} (R : Rearrangement ι) (hpfin : p ≠ ∞)
    (hfin : R.LocallyFinite) (h : LocalBasis p β R.srcUnion B) :
    LocalBasis p (fun n => R.op hpfin (β n)) R.tgtUnion B :=
  h.map (R.opL hpfin) (fun n => R.op_isCompactStep hpfin hfin (h.step n))
    (fun n => R.op_nonneg hpfin (h.nonneg n))
    (fun _ hF => R.norm_op_of_supported hpfin hF) (fun F _ => R.op_supported hpfin F)
    (fun _ hG => R.exists_op_eq hpfin hG)

end StructuredBases.PositiveTranslates
