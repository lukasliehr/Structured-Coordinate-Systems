import Lean_Code.SchauderTranslates.Lp.RoundStages

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp2 : 2 < p) (hpfin : p ≠ ∞)

/-- Every root in a cell installed at a finite round is eventually
introduced. An infinite tail of distinct smaller priorities would lie
in a finite initial priority segment, which is impossible. -/
theorem introducedRoot_exhausts_installed (ab : ℕ × ℕ) (r : ℕ)
    (hcell : ab.1 < (roundStage p q hp2 hpfin r).cells.length) :
    ∃ n, introducedRoot p q hp2 hpfin n = ab := by
  by_contra hnever
  have hnot (n : ℕ) : introducedRoot p q hp2 hpfin n ≠ ab :=
    fun he => hnever ⟨n, he⟩
  have havailable (n : ℕ) (hrn : r ≤ n) : (roundStage p q hp2 hpfin n).AvailableRoot ab := by
    refine ⟨hcell.trans_le (roundStage_cells_mono p q hp2 hpfin hrn).length_le, ?_⟩
    intro hmem
    obtain ⟨j, _, he⟩ := (roundStage_origins_mem p q hp2 hpfin n ab).mp hmem
    exact hnot j he
  let f : ℕ → ℕ × ℕ := fun n => introducedRoot p q hp2 hpfin (n + r)
  have hf : Function.Injective f := by
    intro i j hij
    have he : i + r = j + r := introducedRoot_injective p q hp2 hpfin hij
    omega
  have hinfinite : (Set.range f).Infinite := Set.infinite_range_of_injective hf
  have hfinite : (Set.range f).Finite := (rootPriority_finite_initial (rootPriority ab + 1)).subset (by
    rintro cd ⟨n, rfl⟩
    have hp := (roundStage p q hp2 hpfin (n + r)).leastAvailable_minimal ab (havailable (n + r) (by omega))
    change rootPriority (introducedRoot p q hp2 hpfin (n + r)) ≤ rootPriority ab at hp
    change rootPriority (introducedRoot p q hp2 hpfin (n + r)) < rootPriority ab + 1
    omega)
  exact hinfinite.not_finite hfinite

/-- Once branch j exists, each further completed round adds a layer. -/
theorem round_branch_depth_lower (j n : ℕ) (hjn : j + 1 ≤ n) :
    n - (j + 1) ≤
      ((roundStage p q hp2 hpfin n).branches[j]'(by rw [roundStage_branch_count]; omega)).layers.length := by
  induction n, hjn using Nat.le_induction with
  | base => simp only [Nat.sub_self]; exact Nat.zero_le _
  | succ n hjn ih =>
      have hj : j < (roundStage p q hp2 hpfin n).branches.length := by rw [roundStage_branch_count]; omega
      have hd := (roundStep p q hp2 hpfin n).old_depth j hj
      change ((roundStage p q hp2 hpfin (n + 1)).branches[j]'_).layers.length =
        ((roundStage p q hp2 hpfin n).branches[j]'_).layers.length + 1 at hd
      rw [hd]
      omega

theorem round_branch_arbitrarily_long (j L : ℕ) :
    ∃ n, ∃ hjn : j < n,
      L ≤ ((roundStage p q hp2 hpfin n).branches[j]'(by rw [roundStage_branch_count]; exact hjn)).layers.length := by
  let n := j + 1 + L
  have hjn : j < n := by dsimp [n]; omega
  have hdepth := round_branch_depth_lower p q hp2 hpfin j n (by dsimp [n]; omega)
  refine ⟨n, hjn, ?_⟩
  dsimp [n] at hdepth
  dsimp [n]
  omega

end SchauderTranslates.LpConstruction
