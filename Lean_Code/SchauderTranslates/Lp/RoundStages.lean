import Lean_Code.SchauderTranslates.Lp.FiniteRound

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp2 : 2 < p) (hpfin : p ≠ ∞)

def roundState : ℕ → {S : FiniteStage p q hp2 hpfin // S.Warm}
  | 0 => ⟨FiniteStage.initial p q hp2 hpfin, initialStage_warm⟩
  | n + 1 =>
      let W := roundState n
      let R := Classical.choice (finite_round W.val W.property)
      ⟨R.stage, R.warm⟩

def roundStage (n : ℕ) : FiniteStage p q hp2 hpfin := (roundState p q hp2 hpfin n).val

def roundStep (n : ℕ) : FiniteRoundResult (roundStage p q hp2 hpfin n) :=
  Classical.choice (finite_round (roundState p q hp2 hpfin n).val (roundState p q hp2 hpfin n).property)

def introducedRoot (n : ℕ) : ℕ × ℕ := (roundStage p q hp2 hpfin n).leastAvailable

theorem roundStage_zero : roundStage p q hp2 hpfin 0 = FiniteStage.initial p q hp2 hpfin := rfl

theorem roundStage_succ (n : ℕ) : roundStage p q hp2 hpfin (n + 1) = (roundStep p q hp2 hpfin n).stage := rfl

theorem roundStage_branch_count (n : ℕ) : (roundStage p q hp2 hpfin n).branches.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [roundStage_succ, (roundStep p q hp2 hpfin n).branch_count, ih]

theorem roundStage_warm (n : ℕ) : (roundStage p q hp2 hpfin n).Warm :=
  (roundState p q hp2 hpfin n).property

theorem roundStage_cells_step (n : ℕ) :
    (roundStage p q hp2 hpfin n).cells <+: (roundStage p q hp2 hpfin (n + 1)).cells :=
  (roundStep p q hp2 hpfin n).run.cells_prefix

theorem roundStage_births_step (n : ℕ) :
    (roundStage p q hp2 hpfin n).births <+: (roundStage p q hp2 hpfin (n + 1)).births :=
  (roundStep p q hp2 hpfin n).run.births_prefix

theorem roundStage_cells_mono {n m : ℕ} (h : n ≤ m) :
    (roundStage p q hp2 hpfin n).cells <+: (roundStage p q hp2 hpfin m).cells := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ m _ ih => exact ih.trans (roundStage_cells_step p q hp2 hpfin m)

theorem roundStage_births_mono {n m : ℕ} (h : n ≤ m) :
    (roundStage p q hp2 hpfin n).births <+: (roundStage p q hp2 hpfin m).births := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ m _ ih => exact ih.trans (roundStage_births_step p q hp2 hpfin m)

theorem roundStage_origins_append (n : ℕ) :
    (roundStage p q hp2 hpfin (n + 1)).branches.map PhysicalBranch.origin =
      (roundStage p q hp2 hpfin n).branches.map PhysicalBranch.origin ++ [introducedRoot p q hp2 hpfin n] :=
  (roundStep p q hp2 hpfin n).origins

theorem roundStage_origins_mem (n : ℕ) (ab : ℕ × ℕ) :
    ab ∈ (roundStage p q hp2 hpfin n).branches.map PhysicalBranch.origin ↔
      ∃ j < n, introducedRoot p q hp2 hpfin j = ab := by
  induction n with
  | zero => simp [roundStage_zero, FiniteStage.initial]
  | succ n ih =>
      rw [roundStage_origins_append, List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨j, hj, he⟩ | he)
        · exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
        · exact ⟨n, Nat.lt_succ_self n, he.symm⟩
      · rintro ⟨j, hj, he⟩
        by_cases hjn : j < n
        · exact Or.inl ⟨j, hjn, he⟩
        · have hje : j = n := by omega
          subst j
          exact Or.inr he.symm

theorem introducedRoot_injective : Function.Injective (introducedRoot p q hp2 hpfin) := by
  intro i j hij
  by_contra hne
  have hnot (i j : ℕ) (hijlt : i < j) : introducedRoot p q hp2 hpfin i ≠ introducedRoot p q hp2 hpfin j := by
    intro he
    have hmem := (roundStage_origins_mem p q hp2 hpfin j (introducedRoot p q hp2 hpfin i)).mpr ⟨i, hijlt, rfl⟩
    have hfresh := (roundStage p q hp2 hpfin j).leastAvailable_available.2
    change introducedRoot p q hp2 hpfin j ∉
      (roundStage p q hp2 hpfin j).branches.map PhysicalBranch.origin at hfresh
    exact hfresh (he ▸ hmem)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hnot i j hlt hij
  · exact hnot j i hlt hij.symm

theorem roundStage_time_ge (n : ℕ) : n ≤ (roundStage p q hp2 hpfin n).time := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hs := (roundStep p q hp2 hpfin n).time_strict
      change (roundStage p q hp2 hpfin n).time < (roundStage p q hp2 hpfin (n + 1)).time at hs
      omega

theorem roundStage_birth_count_ge (n : ℕ) : n + 1 ≤ (roundStage p q hp2 hpfin n).births.length := by
  induction n with
  | zero => exact (roundStage p q hp2 hpfin 0).old_count_pos
  | succ n ih =>
      have hs := (roundStep p q hp2 hpfin n).birth_count_strict
      change (roundStage p q hp2 hpfin n).births.length <
        (roundStage p q hp2 hpfin (n + 1)).births.length at hs
      omega

theorem roundStage_radius_ge (n : ℕ) : (n : ℝ) ≤ (roundStage p q hp2 hpfin n).radius := by
  have htime : (n : ℝ) ≤ (roundStage p q hp2 hpfin n).time := by
    exact_mod_cast (roundStage_time_ge p q hp2 hpfin n)
  exact htime.trans (roundStage p q hp2 hpfin n).radius_time

/-- Finite round intervals exhaust the actual whole real line. -/
theorem roundStage_committed_cover (x : ℝ) :
    ∃ n, x ∈ Set.Ico (-(roundStage p q hp2 hpfin n).radius) (roundStage p q hp2 hpfin n).radius := by
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  have hR := roundStage_radius_ge p q hp2 hpfin n
  refine ⟨n, ?_⟩
  have hl := neg_abs_le x
  have hr := le_abs_self x
  constructor <;> linarith

end SchauderTranslates.LpConstruction
