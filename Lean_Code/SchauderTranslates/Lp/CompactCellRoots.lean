import Lean_Code.SchauderTranslates.Lp.UnitIntervalStep

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem normalized_system_ordered_coordinates {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (u : ι → E) (coord : ι → E →L[ℂ] ℂ)
    {H : ℝ} (hu : NormalizedUnconditionalSystem u coord H) (e : ℕ ≃ ι) (x : E) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, coord (e j) x • u (e j)) atTop (𝓝 x) := by
  classical
  have ht := (hu.2.2.2 x).comp
    ((tendsto_finset_image_atTop_atTop e.apply_symm_apply).comp tendsto_finset_range)
  have he : (fun n : ℕ => ∑ j ∈ Finset.range n, coord (e j) x • u (e j)) =
      (fun n : ℕ => ∑ i ∈ (Finset.range n).image e, coord i x • u i) := by
    funext n
    symm
    apply Finset.sum_image
    exact e.injective.injOn
  rw [he]
  exact ht

/-- The local root data installed when a permanent cell is born. The
carrier is an actual submodule of whole-line Lebesgue Lᵖ; every root is
a real compact step vector, with continuous ordered coordinates. -/
structure CompactCellRoots (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set ℝ) (H : ℝ) where
  space : Submodule ℂ (LebesgueLp p)
  supported : ∀ x : space, SupportedOn x.val A
  root : ℕ → space
  normalized : ∀ n, ‖root n‖ = 1
  compactStep : ∀ n, IsCompactStep p (root n).val
  coordinate : ℕ → space →L[ℂ] ℂ
  biorthogonal : ∀ i j, coordinate i (root j) = if i = j then 1 else 0
  basis : Construction.OrderedSchauderBasis root
  multiplier : FiniteMultiplierBound root H
  convergence : ∀ x : space,
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, coordinate j x • root j) atTop (𝓝 x)

def CompactCellRoots.ofIndexed {p : ℝ≥0∞} [Fact (1 ≤ p)] {A : Set ℝ} {H : ℝ}
    (S : Submodule ℂ (LebesgueLp p)) (hS : ∀ x : S, SupportedOn x.val A)
    {ι : Type*} [DecidableEq ι] (u : ι → S) (c : ι → S →L[ℂ] ℂ)
    (hu : NormalizedUnconditionalSystem u c H) (e : ℕ ≃ ι)
    (hc : ∀ i j, c i (u j) = if i = j then 1 else 0)
    (hstep : ∀ i, IsCompactStep p (u i).val) : CompactCellRoots p A H where
  space := S
  supported := hS
  root n := u (e n)
  normalized n := hu.2.1 (e n)
  compactStep n := hstep (e n)
  coordinate n := c (e n)
  biorthogonal i j := by simpa only [e.injective.eq_iff] using hc (e i) (e j)
  basis := (hu.2.2.1 e).1
  multiplier := (hu.2.2.1 e).2
  convergence := normalized_system_ordered_coordinates u c hu e

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
variable {e : LebesgueLp p} (D : DisjointStepData p e)
variable (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1) (hp2 : 2 < p)

def DisjointStepData.fullCellRoots : CompactCellRoots p D.supportSet (haarStrongConstant q.toReal) :=
  CompactCellRoots.ofIndexed (supportedLpSubmodule p volume D.supportSet) (fun x => x.property)
    (D.fullCellAtom hp0 hpfin he) (D.fullCellCoordinate (q := q) hp0 hpfin he)
    (D.fullCell_system hp0 hpfin he hp2) haarOrdering
    (D.fullCellCoordinate_atom hp0 hpfin he) (D.fullCellAtom_isCompactStep hp0 hpfin he)

def DisjointStepData.privateCellRoots : CompactCellRoots p D.supportSet (haarStrongConstant q.toReal) :=
  CompactCellRoots.ofIndexed (D.wholeComplementSpace (q := q) hp0 hpfin he)
    (D.wholeComplementSpace_supported hp0 hpfin he)
    (D.wholeComplementAtom (q := q) hp0 hpfin he) (D.wholeComplementCoordinate (q := q) hp0 hpfin he)
    (D.wholeComplement_system hp0 hpfin he hp2) haarMeanZeroOrdering
    (D.wholeComplementCoordinate_atom hp0 hpfin he)
    (D.wholeComplementAtom_isCompactStep hp0 hpfin he)

theorem ordinary_interval_roots (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (ab : ℝ × ℝ) (hab : ab.1 < ab.2) :
    Nonempty (CompactCellRoots p (Set.Ico ab.1 ab.2) (haarStrongConstant q.toReal)) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp2)
  let D := unitIntervalStepData p hp0 hpfin ab hab
  have hroot := D.fullCellRoots (q := q) hp0 hpfin
    (unitIntervalVector_norm p hp0 hpfin ab hab) hp2
  have hsupport : D.supportSet = Set.Ico ab.1 ab.2 := unitIntervalStepData_support p hp0 hpfin ab hab
  rw [hsupport] at hroot
  exact ⟨hroot⟩

/-- The ordinary-cell witness retains the full supported carrier, so it
can be assembled with the private complements in the global kernel. -/
theorem ordinary_interval_roots_full (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (ab : ℝ × ℝ) (hab : ab.1 < ab.2) :
    Nonempty {R : CompactCellRoots p (Set.Ico ab.1 ab.2) (haarStrongConstant q.toReal) //
      R.space = supportedLpSubmodule p volume (Set.Ico ab.1 ab.2)} := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp2)
  let D := unitIntervalStepData p hp0 hpfin ab hab
  have h : Nonempty {R : CompactCellRoots p D.supportSet (haarStrongConstant q.toReal) //
      R.space = supportedLpSubmodule p volume D.supportSet} :=
    ⟨⟨D.fullCellRoots (q := q) hp0 hpfin (unitIntervalVector_norm p hp0 hpfin ab hab) hp2, rfl⟩⟩
  have hsupport : D.supportSet = Set.Ico ab.1 ab.2 := unitIntervalStepData_support p hp0 hpfin ab hab
  rwa [hsupport] at h

end SchauderTranslates.LpConstruction
