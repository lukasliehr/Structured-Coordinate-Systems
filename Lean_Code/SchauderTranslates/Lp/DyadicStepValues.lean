import Lean_Code.SchauderTranslates.Lp.HaarDensity
import Lean_Code.SchauderTranslates.Lp.DyadicAverages

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- One representative of a finite complex dyadic step function, shared
by all exponent-specific Lᵖ classes. -/
def dyadicStepValue (N : ℕ) (c : Fin (2 ^ N) → ℂ) (x : ℝ) : ℂ :=
  ∑ k, c k * (dyadicInterval N k).indicator (fun _ => (1 : ℂ)) x

theorem haarDyadicStep_ae_value (p : ℝ≥0∞) (N : ℕ) (c : Fin (2 ^ N) → ℂ) :
    (haarDyadicStep p N c : ℝ → ℂ) =ᵐ[haarMeasure] dyadicStepValue N c :=
  haarDyadicStep_ae p N c

theorem dyadicStepValue_on_cell (N : ℕ) (c : Fin (2 ^ N) → ℂ) (k : Fin (2 ^ N))
    {x : ℝ} (hx : x ∈ dyadicInterval N k) : dyadicStepValue N c x = c k :=
  haarDyadicStep_value N c k hx

theorem dyadicStepValue_integrable (N : ℕ) (c : Fin (2 ^ N) → ℂ) :
    Integrable (dyadicStepValue N c) haarMeasure :=
  (L1.integrable_coeFn (haarDyadicStep 1 N c)).congr (haarDyadicStep_ae_value 1 N c)

theorem dyadicStepValue_memLp (p : ℝ≥0∞) (N : ℕ) (c : Fin (2 ^ N) → ℂ) :
    MemLp (dyadicStepValue N c) p haarMeasure :=
  (memLp_congr_ae (haarDyadicStep_ae_value p N c)).mp (Lp.memLp (haarDyadicStep p N c))

theorem dyadicStepValue_norm_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ) :
    (∫ x, ‖dyadicStepValue N c x‖ ∂haarMeasure) = ‖haarDyadicStep 1 N c‖ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((haarDyadicStep_ae_value 1 N c).symm.fun_comp norm)

theorem dyadicStepValue_cell_norm_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ)
    (k : Fin (2 ^ N)) :
    (∫ x in dyadicInterval N k, ‖dyadicStepValue N c x‖ ∂haarMeasure) =
      haarMeasure.real (dyadicInterval N k) * ‖c k‖ := by
  calc
    _ = ∫ _ in dyadicInterval N k, ‖c k‖ ∂haarMeasure :=
      setIntegral_congr_fun (dyadicInterval_measurable N k)
        (fun _ hx => congrArg norm (dyadicStepValue_on_cell N c k hx))
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

theorem dyadicStepValue_zero_outside_unit (N : ℕ) (c : Fin (2 ^ N) → ℂ)
    {x : ℝ} (hx : x ∉ Set.Ico (0 : ℝ) 1) : dyadicStepValue N c x = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hcell : x ∉ dyadicInterval N k := fun h => hx (dyadicInterval_subset_unit N k k.isLt h)
  simp [hcell]

theorem dyadicStepValue_outside_bad_bound (N : ℕ) (c : Fin (2 ^ N) → ℂ) {a : ℝ}
    (ha : 0 ≤ a) {x : ℝ} (hx : x ∉ dyadicBadUnion N (dyadicStepValue N c) a) :
    ‖dyadicStepValue N c x‖ ≤ a := by
  by_cases hunit : x ∈ Set.Ico (0 : ℝ) 1
  · obtain ⟨k, hk, hxk⟩ := dyadicInterval_unit_cover N hunit
    let i : Fin (2 ^ N) := ⟨k, hk⟩
    let j : DyadicCell := ⟨N, i⟩
    have hnot : j ∉ dyadicBadCells N (dyadicStepValue N c) a := by
      intro hj
      obtain ⟨l, hl, _, hjl⟩ := maximalDyadicCells_cover _ hj
      exact hx (Set.mem_iUnion₂.mpr ⟨l, hl, hjl hxk⟩)
    have hgood : (∫ y in dyadicCellSet j, ‖dyadicStepValue N c y‖ ∂haarMeasure) ≤
        a * haarMeasure.real (dyadicCellSet j) := by
      by_contra h
      exact hnot ((mem_dyadicBadCells N (dyadicStepValue N c) a j).mpr ⟨le_rfl, lt_of_not_ge h⟩)
    change (∫ y in dyadicInterval N i, ‖dyadicStepValue N c y‖ ∂haarMeasure) ≤
      a * haarMeasure.real (dyadicInterval N i) at hgood
    rw [dyadicStepValue_cell_norm_integral, mul_comm a] at hgood
    rw [dyadicStepValue_on_cell N c i hxk]
    exact (mul_le_mul_iff_of_pos_left (dyadicCell_mass_pos j)).mp hgood
  · rw [dyadicStepValue_zero_outside_unit N c hunit, norm_zero]
    exact ha

theorem dyadicStepValue_constant_on_finer_cell (N : ℕ) (c : Fin (2 ^ N) → ℂ)
    (j : DyadicCell) (hNj : N ≤ j.1) :
    ∃ z : ℂ, ∀ x ∈ dyadicCellSet j, dyadicStepValue N c x = z := by
  obtain ⟨x, hx⟩ := dyadicCellSet_nonempty j
  obtain ⟨k, hk, hxk⟩ := dyadicInterval_unit_cover N (dyadicCellSet_subset_unit j hx)
  let i : Fin (2 ^ N) := ⟨k, hk⟩
  refine ⟨c i, ?_⟩
  rcases dyadicInterval_nested_or_disjoint hNj k j.2 with hsub | hdis
  · exact fun y hy => dyadicStepValue_on_cell N c i (hsub hy)
  · exact (Set.disjoint_left.mp hdis hx hxk).elim

end SchauderTranslates.LpConstruction
