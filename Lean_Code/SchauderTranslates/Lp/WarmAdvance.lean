import Lean_Code.SchauderTranslates.Lp.BranchAdvance
import Lean_Code.SchauderTranslates.Lp.ForestWarm

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

def FiniteStage.Warm (S : FiniteStage p q hp2 hpfin) : Prop :=
  ∀ k : Fin S.branches.length,
    3 * branchBeta p.toReal ^ (S.branches[k.val]).layers.length ≤ forestWarmWeight k.val

def FiniteStage.WarmExcept (S : FiniteStage p q hp2 hpfin) (j : ℕ) : Prop :=
  ∀ k : Fin S.branches.length, k.val ≠ j →
    3 * branchBeta p.toReal ^ (S.branches[k.val]).layers.length ≤ forestWarmWeight k.val

theorem BranchAdvanceResult.warm {S : FiniteStage p q hp2 hpfin}
    {j : Fin S.branches.length} {n : ℕ} (R : BranchAdvanceResult S j n)
    (hS : S.WarmExcept j.val)
    (hn : 3 * branchBeta p.toReal ^ n ≤ forestWarmWeight j.val) : R.stage.Warm := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin
  intro k
  have hk : k.val < S.branches.length := by rw [← R.branch_count]; exact k.isLt
  by_cases hkj : k.val = j.val
  · have hdepth : (R.stage.branches[k.val]).layers.length = (S.branches[j.val]).layers.length + n := by
      simpa only [hkj] using R.selected_depth
    apply forest_warm_depth_bound hpR (L := n)
    · rw [hdepth]
      omega
    · simpa only [hkj] using hn
  · have he := R.other_branch k.val hk (Ne.symm hkj)
    rw [he]
    exact hS ⟨k.val, hk⟩ hkj

theorem FiniteStage.introduceLeast_warm_except (S : FiniteStage p q hp2 hpfin) (hS : S.Warm) :
    S.introduceLeast.WarmExcept S.branches.length := by
  intro k hk
  have hkold : k.val < S.branches.length := by
    have hbound : k.val < S.branches.length + 1 := by
      simpa only [S.introduceLeast_branch_count] using k.isLt
    omega
  change 3 * branchBeta p.toReal ^
    ((S.branches ++ [S.newBranch _ _])[k.val]).layers.length ≤ _
  rw [List.getElem_append_left hkold]
  exact hS ⟨k.val, hkold⟩

theorem initialStage_warm : (FiniteStage.initial p q hp2 hpfin).Warm := by
  intro k
  exact Fin.elim0 k

end SchauderTranslates.LpConstruction
