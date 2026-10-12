import Lean_Code.SchauderTranslates.Lp.StepCellNorm

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {ι : Type*} [Fintype ι]

def indexedIntervalStep (p : ℝ≥0∞) (a : ι → ℝ × ℝ) (d : ι → ℝ) : LebesgueLp p :=
  ∑ i, d i • intervalAtom p (a i)

theorem indexedIntervalStep_ae (p : ℝ≥0∞) (a : ι → ℝ × ℝ) (d : ι → ℝ) :
    indexedIntervalStep p a d =ᵐ[volume]
      fun x => ∑ i, (d i : ℂ) * (Set.Ico (a i).1 (a i).2).indicator (fun _ => (1 : ℂ)) x := by
  classical
  have hall : ∀ᵐ x ∂volume, ∀ i ∈ (Finset.univ : Finset ι),
      (d i • intervalAtom p (a i)) x =
        (d i : ℂ) * (Set.Ico (a i).1 (a i).2).indicator (fun _ => (1 : ℂ)) x := by
    simp only [Filter.eventually_all_finset]
    intro i _
    filter_upwards [intervalAtom_ae p (a i), Lp.coeFn_smul (d i) (intervalAtom p (a i))]
      with x hi hs
    rw [hs, Pi.smul_apply, hi, Complex.real_smul]
  filter_upwards [hall, Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => d i • intervalAtom p (a i))] with x hall hx
  change (∑ i, d i • intervalAtom p (a i)) x = _
  rw [hx]
  exact Finset.sum_congr rfl (fun i hi => hall i hi)

theorem indexedIntervalStep_isCompactStep (p : ℝ≥0∞) (a : ι → ℝ × ℝ) (d : ι → ℝ) :
    IsCompactStep p (indexedIntervalStep p a d) :=
  IsCompactStep.finset_sum _ _ (fun i _ => (intervalAtom_isCompactStep p (a i)).smul (d i))

theorem indexedIntervalStep_supported (p : ℝ≥0∞) (a : ι → ℝ × ℝ) (d : ι → ℝ)
    (A : Set ℝ) (hA : ∀ i, Set.Ico (a i).1 (a i).2 ⊆ A) :
    SupportedOn (indexedIntervalStep p a d) A :=
  SupportedOn.finset_sum _ _ (fun i _ =>
    ((intervalAtom_supported_cell p (a i)).mono (hA i)).real_smul (d i))

end SchauderTranslates.LpConstruction
