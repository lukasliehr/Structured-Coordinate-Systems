import Lean_Code.SchauderTranslates.Lp.DyadicSelection

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem dyadicCell_mass (j : DyadicCell) :
    haarMeasure.real (dyadicCellSet j) = 1 / (2 : ℝ) ^ j.1 := by
  rw [measureReal_def, dyadicCellSet, haarInterval_measure _ _ j.2.isLt,
    ENNReal.toReal_ofReal (by positivity)]

theorem dyadicCell_mass_pos (j : DyadicCell) : 0 < haarMeasure.real (dyadicCellSet j) := by
  rw [dyadicCell_mass]
  positivity

theorem dyadicCell_parent_mass {j : DyadicCell} (hj : 0 < j.1) :
    haarMeasure.real (dyadicCellSet (dyadicCellParent j)) =
      2 * haarMeasure.real (dyadicCellSet j) := by
  rw [dyadicCell_mass, dyadicCell_mass]
  rcases j with ⟨n, k⟩
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hj).elim
  | succ n =>
    change 1 / (2 : ℝ) ^ n = 2 * (1 / (2 : ℝ) ^ (n + 1))
    rw [pow_succ]
    field_simp

def dyadicRootCell : DyadicCell := ⟨0, ⟨0, by norm_num⟩⟩

@[simp] theorem dyadicCellSet_root : dyadicCellSet dyadicRootCell = Set.Ico (0 : ℝ) 1 :=
  dyadicInterval_zero

theorem dyadicCell_eq_root_of_level_zero {j : DyadicCell} (hj : j.1 = 0) : j = dyadicRootCell := by
  rcases j with ⟨n, k⟩
  dsimp at hj
  subst n
  have hk : k = 0 := Fin.eq_zero k
  subst k
  rfl

theorem haarMeasure_restrict_unit : haarMeasure.restrict (Set.Ico (0 : ℝ) 1) = haarMeasure := by
  simp [haarMeasure, Measure.restrict_restrict]

theorem dyadicCell_integral_root (f : ℝ → ℝ) :
    (∫ x in dyadicCellSet dyadicRootCell, f x ∂haarMeasure) = ∫ x, f x ∂haarMeasure := by
  rw [dyadicCellSet_root, haarMeasure_restrict_unit]

def dyadicCellMean (f : ℝ → ℂ) (j : DyadicCell) : ℂ :=
  (haarMeasure.real (dyadicCellSet j) : ℂ)⁻¹ * ∫ x in dyadicCellSet j, f x ∂haarMeasure

theorem norm_dyadicCellMean_le (f : ℝ → ℂ) (j : DyadicCell) :
    ‖dyadicCellMean f j‖ ≤ (haarMeasure.real (dyadicCellSet j))⁻¹ *
      ∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure := by
  rw [dyadicCellMean, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (dyadicCell_mass_pos j)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.mpr (dyadicCell_mass_pos j).le)

theorem dyadicCellMean_integral (f : ℝ → ℂ) (j : DyadicCell) :
    (∫ _ in dyadicCellSet j, dyadicCellMean f j ∂haarMeasure) =
      ∫ x in dyadicCellSet j, f x ∂haarMeasure := by
  rw [setIntegral_const, Complex.real_smul, dyadicCellMean]
  have hm : (haarMeasure.real (dyadicCellSet j) : ℂ) ≠ 0 := by
    exact_mod_cast (dyadicCell_mass_pos j).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]

theorem dyadicCellMean_sub_integral_zero (f : ℝ → ℂ) (hf : Integrable f haarMeasure)
    (j : DyadicCell) : (∫ x in dyadicCellSet j, f x - dyadicCellMean f j ∂haarMeasure) = 0 := by
  rw [integral_sub hf.integrableOn (integrable_const _), dyadicCellMean_integral, sub_self]

/-- Cells are bad when their average absolute value exceeds the threshold.
The equivalent undivided inequality avoids any zero-measure division. -/
def dyadicBadCells (N : ℕ) (f : ℝ → ℂ) (a : ℝ) : Finset DyadicCell := by
  classical
  exact (dyadicCellsThrough N).filter (fun j =>
    a * haarMeasure.real (dyadicCellSet j) < ∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure)

@[simp] theorem mem_dyadicBadCells (N : ℕ) (f : ℝ → ℂ) (a : ℝ) (j : DyadicCell) :
    j ∈ dyadicBadCells N f a ↔ j.1 ≤ N ∧
      a * haarMeasure.real (dyadicCellSet j) < ∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure := by
  classical
  simp [dyadicBadCells]

def dyadicBadUnion (N : ℕ) (f : ℝ → ℂ) (a : ℝ) : Set ℝ :=
  ⋃ j ∈ maximalDyadicCells (dyadicBadCells N f a), dyadicCellSet j

theorem dyadicRootCell_not_bad (N : ℕ) (f : ℝ → ℂ) {a : ℝ}
    (hf : (∫ x, ‖f x‖ ∂haarMeasure) ≤ a) : dyadicRootCell ∉ dyadicBadCells N f a := by
  intro hj
  have hb := (mem_dyadicBadCells N f a dyadicRootCell).mp hj |>.2
  have hm : haarMeasure.real (dyadicCellSet dyadicRootCell) = 1 := by
    rw [dyadicCell_mass]
    norm_num [dyadicRootCell]
  rw [hm, mul_one, dyadicCell_integral_root] at hb
  exact (not_lt_of_ge hf) hb

theorem dyadic_selected_level_pos (N : ℕ) (f : ℝ → ℂ) {a : ℝ}
    (hf : (∫ x, ‖f x‖ ∂haarMeasure) ≤ a) {j : DyadicCell}
    (hj : j ∈ maximalDyadicCells (dyadicBadCells N f a)) : 0 < j.1 := by
  by_contra h
  have he : j = dyadicRootCell := dyadicCell_eq_root_of_level_zero (Nat.eq_zero_of_not_pos h)
  subst j
  exact dyadicRootCell_not_bad N f hf (maximalDyadicCells_subset _ hj)

theorem dyadicBadUnion_measurable (N : ℕ) (f : ℝ → ℂ) (a : ℝ) :
    MeasurableSet (dyadicBadUnion N f a) :=
  Finset.measurableSet_biUnion _ (fun j _ => dyadicCellSet_measurable j)

/-- The selected bad union has the exact weak maximal-function measure
bound needed by the finite dyadic Calderón–Zygmund decomposition. -/
theorem dyadicBadUnion_measure_bound (N : ℕ) (f : ℝ → ℂ) (hf : Integrable f haarMeasure)
    {a : ℝ} (ha : 0 < a) :
    haarMeasure.real (dyadicBadUnion N f a) ≤ (∫ x, ‖f x‖ ∂haarMeasure) / a := by
  let s := maximalDyadicCells (dyadicBadCells N f a)
  have hd : Set.PairwiseDisjoint (s : Set DyadicCell) dyadicCellSet :=
    fun _ hi _ hj hij => maximalDyadicCells_disjoint _ hi hj hij
  have hm : ∀ j ∈ s, MeasurableSet (dyadicCellSet j) := fun j _ => dyadicCellSet_measurable j
  apply (le_div_iff₀ ha).mpr
  change haarMeasure.real (⋃ j ∈ s, dyadicCellSet j) * a ≤ _
  rw [measureReal_biUnion_finset hd hm, Finset.sum_mul]
  calc
    _ ≤ ∑ j ∈ s, ∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := (mem_dyadicBadCells N f a j).mp (maximalDyadicCells_subset _ hj)
      simpa [mul_comm] using hb.2.le
    _ = ∫ x in ⋃ j ∈ s, dyadicCellSet j, ‖f x‖ ∂haarMeasure :=
      (integral_biUnion_finset s hm hd (fun _ _ => hf.norm.integrableOn)).symm
    _ ≤ ∫ x, ‖f x‖ ∂haarMeasure := setIntegral_le_integral hf.norm
      (Eventually.of_forall fun x => norm_nonneg (f x))

theorem dyadic_selected_parent_good (N : ℕ) (f : ℝ → ℂ) (a : ℝ) {j : DyadicCell}
    (hj : j ∈ maximalDyadicCells (dyadicBadCells N f a)) (hlevel : 0 < j.1) :
    (∫ x in dyadicCellSet (dyadicCellParent j), ‖f x‖ ∂haarMeasure) ≤
      a * haarMeasure.real (dyadicCellSet (dyadicCellParent j)) := by
  have hparent := maximalDyadicCell_parent_not_mem _ hj hlevel
  have hN := (mem_dyadicBadCells N f a j).mp (maximalDyadicCells_subset _ hj) |>.1
  have hPN : (dyadicCellParent j).1 ≤ N :=
    (mem_dyadicCellsThrough N _).mp (dyadicCellParent_mem_through
      ((mem_dyadicCellsThrough N j).mpr hN))
  by_contra h
  exact hparent ((mem_dyadicBadCells N f a _).mpr ⟨hPN, lt_of_not_ge h⟩)

theorem norm_dyadicCellMean_le_of_parent_good (f : ℝ → ℂ) (hf : Integrable f haarMeasure)
    {a : ℝ} {j : DyadicCell} (hlevel : 0 < j.1)
    (hparent : (∫ x in dyadicCellSet (dyadicCellParent j), ‖f x‖ ∂haarMeasure) ≤
      a * haarMeasure.real (dyadicCellSet (dyadicCellParent j))) :
    ‖dyadicCellMean f j‖ ≤ 2 * a := by
  have hi : (∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure) ≤
      ∫ x in dyadicCellSet (dyadicCellParent j), ‖f x‖ ∂haarMeasure :=
    setIntegral_mono_set hf.norm.integrableOn (Eventually.of_forall fun x => norm_nonneg (f x))
      (Eventually.of_forall fun _ hx => dyadicCell_subset_parent j hx)
  calc
    _ ≤ (haarMeasure.real (dyadicCellSet j))⁻¹ *
      ∫ x in dyadicCellSet j, ‖f x‖ ∂haarMeasure := norm_dyadicCellMean_le f j
    _ ≤ (haarMeasure.real (dyadicCellSet j))⁻¹ *
      (a * haarMeasure.real (dyadicCellSet (dyadicCellParent j))) :=
      mul_le_mul_of_nonneg_left (hi.trans hparent) (inv_nonneg.mpr (dyadicCell_mass_pos j).le)
    _ = 2 * a := by
      rw [dyadicCell_parent_mass hlevel]
      field_simp [(dyadicCell_mass_pos j).ne']

end SchauderTranslates.LpConstruction
