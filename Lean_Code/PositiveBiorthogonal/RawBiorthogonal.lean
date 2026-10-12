import Lean_Code.PositiveBiorthogonal.RawProjections
import Lean_Code.PositiveBiorthogonal.FiniteSplitting

/-! Global biorthogonality from exact averaging projections and matching stage dimensions. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

namespace ActivePartition

def cellCoordinate (P : ActivePartition) (j : Fin P.R) : L 𝕜 p →L[𝕜] 𝕜 :=
  ((P.cell j).length : 𝕜)⁻¹ • representedFunctional ((P.cell j).indicator : L 𝕜 q)

theorem cellCoordinate_indicator (P : ActivePartition) (i j : Fin P.R) :
    P.cellCoordinate (q := q) j ((P.cell i).indicator : L 𝕜 p) = if i = j then 1 else 0 := by
  classical
  simp only [cellCoordinate, smul_apply, representedFunctional_apply, smul_eq_mul]
  rw [IntervalCell.pairing_indicators]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, Set.inter_self, IntervalCell.volume_real, inv_mul_cancel₀]
    exact_mod_cast (P.cell i).length_pos.ne'
  · rw [if_neg h, Set.disjoint_iff_inter_eq_empty.mp (P.disjoint h)]
    simp

theorem cellCoordinate_average (P : ActivePartition) (f : L 𝕜 p) :
    (∑ i, P.cellCoordinate (q := q) i f • (P.cell i).indicator) = P.averageCLM (q := q) f := by
  simp [cellCoordinate, averageCLM, IntervalCell.averageCLM, smul_smul]

theorem biorthogonal_of_projection (P : ActivePartition) (v : ℕ → L 𝕜 p)
    (g : ℕ → L 𝕜 q)
    (hproj : initialProjection v (fun n => representedFunctional (g n)) P.R =
      P.averageCLM (q := q)) (i j : Fin P.R) :
    pairing (v i.val) (g j.val) = if i = j then 1 else 0 := by
  classical
  rw [← representedFunctional_apply]
  apply finiteBiorthogonal_of_equal_projectors
    (fun i : Fin P.R => (P.cell i).indicator)
    (fun i : Fin P.R => v i.val)
    (fun i => (P.cellCoordinate (q := q) i).toLinearMap)
    (fun i => (representedFunctional (g i.val)).toLinearMap)
    P.cellCoordinate_indicator
  intro f
  change (∑ i : Fin P.R, representedFunctional (g i.val) f • v i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => representedFunctional (g n) f • v n)]
  rw [← initialProjection_apply, hproj, ← P.cellCoordinate_average]
  rfl

end ActivePartition

namespace ConstructionData
variable (C : ConstructionData 𝕜 p q)

theorem stage_cell_count_eq_totalCount (k : ℕ) : (C.stage k).part.R = (C.stage k).totalCount := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [C.stage_cell_count_succ, C.stage_totalCount_succ, ← ih]
    change (C.stage k).part.R * (C.steps k + 1) + 2 * ((C.stage k).part.R * C.steps k) =
      (C.stage k).part.R + 3 * ((C.stage k).part.R * C.steps k)
    ring

theorem raw_biorthogonal_on_stage (k : ℕ) (i j : Fin (C.stage k).part.R) :
    pairing (C.rawVector i.val) (C.rawCoefficient j.val) = if i = j then 1 else 0 := by
  apply (C.stage k).part.biorthogonal_of_projection C.rawVector C.rawCoefficient
  rw [C.stage_cell_count_eq_totalCount]
  exact C.rawProjection_stage k

theorem raw_biorthogonal (i j : ℕ) :
    pairing (C.rawVector i) (C.rawCoefficient j) = if i = j then 1 else 0 := by
  let k := max i j
  have hi : i < (C.stage k).part.R := by
    rw [C.stage_cell_count_eq_totalCount]
    exact lt_of_le_of_lt (le_max_left i j) (lt_of_lt_of_le (Nat.lt_succ_self k) (C.stage_totalCount_lower k))
  have hj : j < (C.stage k).part.R := by
    rw [C.stage_cell_count_eq_totalCount]
    exact lt_of_le_of_lt (le_max_right i j) (lt_of_lt_of_le (Nat.lt_succ_self k) (C.stage_totalCount_lower k))
  simpa only [Fin.mk.injEq] using C.raw_biorthogonal_on_stage k ⟨i, hi⟩ ⟨j, hj⟩

end ConstructionData
end PositiveBiorthogonal
