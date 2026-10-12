import Lean_Code.PositiveTranslates.Local.Defs
import Lean_Code.SchauderTranslates.Lp.StepCellOrdering
import Lean_Code.SchauderTranslates.Lp.StepCellAvoidance

/-!
# Normal form of non-negative compact step functions

Every nonzero compactly supported step function `e ∈ Lᵖ(ℝ)` which is non-negative almost
everywhere is a finite sum `∑ₖ cₖ 𝟙_{Iₖ}` with positive values `cₖ` and nondegenerate pairwise
disjoint half-open intervals `Iₖ = [(I k).1, (I k).2)`
(`exists_positive_normalForm`). The intervals can be listed from left to right
(`exists_ordered_positive_normalForm`), and their union is the set where `e` does not vanish
(up to a null set). In particular they are disjoint from every interval `[a, b)` on which `e`
vanishes almost everywhere.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

variable {p : ℝ≥0∞} {e : LebesgueLp p}

/-- In a disjoint representation of a non-negative step function all values are positive. -/
theorem Local.value_pos_of_isNonneg (D : DisjointStepData p e) (hpos : IsNonneg e) {ab : ℝ × ℝ}
    (hab : ab ∈ D.cells) : 0 < D.value ab := by
  refine lt_of_le_of_ne ?_ (Ne.symm (D.value_ne_zero ab hab))
  by_contra hneg
  have hnull : ∀ᵐ x : ℝ, x ∉ Set.Ico ab.1 ab.2 := by
    filter_upwards [D.valueFunction_ae, hpos] with x hx hx0 hmem
    rw [hx, D.valueFunction_on_cell hab hmem] at hx0
    exact hneg (Complex.zero_le_real.mp hx0)
  have hzero : volume (Set.Ico ab.1 ab.2) = 0 := measure_eq_zero_iff_ae_notMem.mpr hnull
  rw [Real.volume_Ico, ENNReal.ofReal_eq_zero] at hzero
  linarith [D.length_pos ab hab]

/-- **Normal form, ordered and with its support.** A nonzero non-negative compact step
function is `∑ₖ cₖ 𝟙_{Iₖ}` with positive `cₖ` and nondegenerate intervals `Iₖ` listed from left
to right (`(I k).2 ≤ (I l).1` for `k < l`, hence pairwise disjoint). The function is nonzero
almost exactly on `⋃ₖ Iₖ`, and the `Iₖ` are disjoint from every interval `[a, b)` on which the
function vanishes almost everywhere. -/
theorem exists_ordered_positive_normalForm (he : IsCompactStep p e) (hpos : IsNonneg e)
    (hne : e ≠ 0) :
    ∃ (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ),
      0 < m ∧ (∀ k, (I k).1 < (I k).2) ∧ (∀ k, 0 < c k) ∧
      (∀ k l, k < l → (I k).2 ≤ (I l).1) ∧
      e = ∑ k, (c k : ℂ) • intervalAtom p (I k) ∧
      (∀ᵐ x : ℝ, e x ≠ 0 ↔ x ∈ ⋃ k, Set.Ico (I k).1 (I k).2) ∧
      (∀ a b : ℝ, SupportedOn e (Set.Ico a b)ᶜ →
        ∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) := by
  obtain ⟨D⟩ := he.disjoint_data
  have hunion : (⋃ k, Set.Ico (D.cellOrdering k).val.1 (D.cellOrdering k).val.2) =
      D.supportSet := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion₂.mpr ⟨(D.cellOrdering k).val, (D.cellOrdering k).property, hk⟩
    · intro hx
      obtain ⟨ab, hab, hxab⟩ := Set.mem_iUnion₂.mp hx
      refine Set.mem_iUnion.mpr ⟨D.cellOrdering.symm ⟨ab, hab⟩, ?_⟩
      simpa using hxab
  refine ⟨D.cells.card, fun k => (D.cellOrdering k).val, fun k => D.value (D.cellOrdering k).val,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_pos]
    by_contra h
    apply hne
    have hrep := D.representation
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hrep
    exact hrep
  · intro k
    exact D.length_pos _ (D.cellOrdering k).property
  · intro k
    exact value_pos_of_isNonneg D hpos (D.cellOrdering k).property
  · intro k l hkl
    have hlt : (D.cellOrdering k).val.1 < (D.cellOrdering l).val.1 := D.cellOrdering_strictMono hkl
    have hdis := D.disjoint _ (D.cellOrdering k).property _ (D.cellOrdering l).property
      (fun h => hkl.ne (D.cellOrdering.injective (Subtype.ext h)))
    by_contra hcon
    exact Set.disjoint_left.mp hdis ⟨hlt.le, not_le.mp hcon⟩
      ⟨le_rfl, D.length_pos _ (D.cellOrdering l).property⟩
  · calc e = ∑ ab ∈ D.cells, D.value ab • intervalAtom p ab := D.representation
      _ = ∑ ab : D.cells, D.value ab.val • intervalAtom p ab.val :=
        (Finset.sum_coe_sort D.cells (fun ab => D.value ab • intervalAtom p ab)).symm
      _ = ∑ k, D.value (D.cellOrdering k).val • intervalAtom p (D.cellOrdering k).val :=
        (D.cellOrdering.sum_comp
          (fun ab : D.cells => D.value ab.val • intervalAtom p ab.val)).symm
      _ = ∑ k, (D.value (D.cellOrdering k).val : ℂ) • intervalAtom p (D.cellOrdering k).val :=
        Finset.sum_congr rfl fun k _ => (ofReal_smul_eq _ _).symm
  · rw [hunion]
    exact D.nonzero_iff_support_ae
  · intro a b hab k
    exact (D.supportSet_disjoint_ico a b hab).mono_left (fun x hx =>
      Set.mem_iUnion₂.mpr ⟨(D.cellOrdering k).val, (D.cellOrdering k).property, hx⟩)

/-- Intervals listed from left to right are pairwise disjoint. -/
theorem pairwise_disjoint_Ico_of_ordered {m : ℕ} {I : Fin m → ℝ × ℝ}
    (hord : ∀ k l, k < l → (I k).2 ≤ (I l).1) :
    Pairwise (fun k l => Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)) := by
  have key : ∀ k l : Fin m, k < l →
      Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2) := fun k l hkl =>
    Set.disjoint_left.mpr fun x hx hy => absurd (hx.2.trans_le ((hord k l hkl).trans hy.1))
      (lt_irrefl _)
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact key k l h
  · exact (key l k h).symm

/-- **Normal form.** A nonzero compactly supported step function which is non-negative almost
everywhere is a finite sum `∑ₖ cₖ 𝟙_{Iₖ}`, with at least one term, positive values `cₖ`, and
nondegenerate pairwise disjoint half-open intervals `Iₖ = [(I k).1, (I k).2)`. -/
theorem exists_positive_normalForm (he : IsCompactStep p e) (hpos : IsNonneg e) (hne : e ≠ 0) :
    ∃ (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ),
      0 < m ∧ (∀ k, (I k).1 < (I k).2) ∧ (∀ k, 0 < c k) ∧
      Pairwise (fun k l => Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)) ∧
      e = ∑ k, (c k : ℂ) • intervalAtom p (I k) := by
  obtain ⟨m, I, c, hm, hI, hc, hord, hrep, -, -⟩ :=
    exists_ordered_positive_normalForm he hpos hne
  exact ⟨m, I, c, hm, hI, hc, pairwise_disjoint_Ico_of_ordered hord, hrep⟩

end StructuredBases.PositiveTranslates
