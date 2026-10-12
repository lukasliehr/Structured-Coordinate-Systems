import Lean_Code.PositiveBiorthogonal.HaarSupport

/-! The exact averaging increment associated to one admissible refinement. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem IntervalCell.averageCLM_apply_normalized (D : IntervalCell) (f : L 𝕜 p) :
    D.averageCLM (q := q) f = (∫ x in D.carrier, f x) • D.normalizedIndicator := by
  rw [D.averageCLM_apply, IntervalCell.normalizedIndicator, smul_smul, mul_comm]

theorem IntervalSplit.integral_parent (S : IntervalSplit) (f : L 𝕜 p) :
    (∫ x in S.parent.carrier, f x) = (∫ x in S.leftChild.carrier, f x) + ∫ x in S.rightChild.carrier, f x := by
  rw [← S.children_union]
  exact setIntegral_union S.children_disjoint S.rightChild.measurable (S.leftChild.integrableOn f) (S.rightChild.integrableOn f)

theorem IntervalSplit.pairing_haarPhi (S : IntervalSplit) (f : L 𝕜 p) :
    pairing f (S.haarPhi : L 𝕜 q) =
      (1 - (S.ratio : 𝕜)) * (∫ x in S.leftChild.carrier, f x) -
        (S.ratio : 𝕜) * (∫ x in S.rightChild.carrier, f x) := by
  rw [IntervalSplit.haarPhi, ← pairingCLM_apply, map_sub, map_smul]
  simp only [pairingCLM_apply, smul_eq_mul]
  rw [S.leftChild.pairing_indicator, S.parent.pairing_indicator, S.integral_parent]
  ring

theorem IntervalSplit.cell_average_increment (S : IntervalSplit) :
    S.leftChild.averageCLM (𝕜 := 𝕜) (p := p) (q := q) + S.rightChild.averageCLM (q := q) -
      S.parent.averageCLM (q := q) = (representedFunctional (S.haarPhi : L 𝕜 q)).smulRight S.haarH := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply, add_apply, ContinuousLinearMap.smulRight_apply, representedFunctional_apply]
  rw [S.leftChild.averageCLM_apply_normalized, S.rightChild.averageCLM_apply_normalized,
    S.parent.averageCLM_apply_normalized, S.normalized_left_expansion, S.normalized_right_expansion,
    S.integral_parent, S.pairing_haarPhi]
  module

theorem ActivePartition.refine_average_formula (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) :
    (P.refine j S hS).averageCLM (𝕜 := 𝕜) (p := p) (q := q) =
      P.averageCLM (q := q) - S.parent.averageCLM (q := q) +
        S.leftChild.averageCLM (q := q) + S.rightChild.averageCLM (q := q) := by
  classical
  change (∑ i : Fin (P.R + 1), (P.splitCells j S i).averageCLM (𝕜 := 𝕜) (p := p) (q := q)) = _
  rw [Fin.sum_univ_castSucc, P.splitCells_last]
  have he (i : Fin P.R) : (P.splitCells j S i.castSucc).averageCLM (𝕜 := 𝕜) (p := p) (q := q) =
      (P.cell i).averageCLM (q := q) +
        if i = j then S.rightChild.averageCLM (q := q) - S.parent.averageCLM (q := q) else 0 := by
    rw [P.splitCells_old]
    by_cases hi : i = j
    · subst i
      simp only [if_true, hS]
      abel
    · simp [hi]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change P.averageCLM (𝕜 := 𝕜) (p := p) (q := q) +
    (S.rightChild.averageCLM (q := q) - S.parent.averageCLM (q := q)) + S.leftChild.averageCLM (q := q) = _
  abel

theorem ActivePartition.refine_average_increment (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) :
    (P.refine j S hS).averageCLM (𝕜 := 𝕜) (p := p) (q := q) - P.averageCLM (q := q) =
      (representedFunctional (S.haarPhi : L 𝕜 q)).smulRight S.haarH := by
  rw [P.refine_average_formula j S hS, ← S.cell_average_increment]
  abel

end PositiveBiorthogonal
