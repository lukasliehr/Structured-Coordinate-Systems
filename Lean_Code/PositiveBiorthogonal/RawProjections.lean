import Lean_Code.PositiveBiorthogonal.Flatten
import Lean_Code.PositiveBiorthogonal.BasisCriterion

/-! Cumulative raw projections agree with stage averaging and satisfy the batch bound globally. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

def rawProjection (n : ℕ) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  initialProjection C.rawVector (fun j => representedFunctional (C.rawCoefficient j)) n

@[simp] theorem rawProjection_zero : C.rawProjection 0 = 0 := by
  simp [rawProjection, initialProjection]

theorem rawProjection_succ (n : ℕ) :
    C.rawProjection (n + 1) = C.rawProjection n + rankPair (C.rawVector n) (C.rawCoefficient n) :=
  Finset.sum_range_succ _ n

theorem rawProjection_one : C.rawProjection 1 = rootPartition.averageCLM (𝕜 := 𝕜) (p := p) (q := q) := by
  rw [show 1 = 0 + 1 from rfl, C.rawProjection_succ, C.rawProjection_zero,
    C.rawVector_zero, C.rawCoefficient_zero, zero_add]
  have he : rootPartition.averageCLM (𝕜 := 𝕜) (p := p) (q := q) =
      (gridUnit 0).averageCLM (q := q) := by
    change (∑ i : Fin 1, (gridUnit 0).averageCLM (𝕜 := 𝕜) (p := p) (q := q)) = _
    rw [Fin.sum_univ_one]
  rw [he]
  simp [IntervalCell.averageCLM, rankPair, gridUnit, IntervalCell.length]

theorem rawProjection_block (k t : ℕ) (ht : t ≤ 3 * C.batchSize k) :
    C.rawProjection ((C.stage k).totalCount + t) = C.rawProjection (C.stage k).totalCount +
      lpPrefix (C.batchVectors k) (C.batchCoefficients k) t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t < 3 * C.batchSize k := by omega
    let j : Fin (3 * C.batchSize k) := ⟨t, ht'⟩
    have hv := C.rawVector_batch k j
    have hg := C.rawCoefficient_batch k j
    have hp := lpPrefix_succ (C.batchVectors k) (C.batchCoefficients k) j
    change C.rawVector ((C.stage k).totalCount + t) = C.batchVectors k j at hv
    change C.rawCoefficient ((C.stage k).totalCount + t) = C.batchCoefficients k j at hg
    change lpPrefix (C.batchVectors k) (C.batchCoefficients k) (t + 1) =
      lpPrefix (C.batchVectors k) (C.batchCoefficients k) t + rankPair (C.batchVectors k j) (C.batchCoefficients k j) at hp
    change C.rawProjection ((C.stage k).totalCount + t + 1) = _
    rw [C.rawProjection_succ, hv, hg, ih (by omega), hp, add_assoc]

theorem stage_average_succ (k : ℕ) :
    (C.stage (k + 1)).part.averageCLM (𝕜 := 𝕜) (p := p) (q := q) =
      (C.trace k).averages (q := q) (C.batchSize k) + (C.fresh k).averageCLM (q := q) := by
  have he : (C.trace k).averages (𝕜 := 𝕜) (p := p) (q := q) (C.batchSize k) =
      ((C.trace k).state (Fin.last (C.batchSize k))).averageCLM (q := q) := by
    simp only [RefinementTrace.averages, min_self]
    rfl
  rw [he]
  exact (C.stage k).extendAfter_average (C.trace k) rfl

theorem batch_end_projection (k : ℕ) :
    (C.stage k).part.averageCLM (q := q) +
      lpPrefix (C.batchVectors k) (C.batchCoefficients k) (3 * C.batchSize k) =
        (C.stage (k + 1)).part.averageCLM (q := q) := by
  have h := C.aux.batch_final_projection (lt_of_lt_of_le (by decide : 0 < 2) (C.batchSize_ge_two k))
    (C.trace k) (C.fresh k) (C.scale k : 𝕜)
  change (C.stage k).part.averageCLM (q := q) +
    lpPrefix (C.batchVectors k) (C.batchCoefficients k) (3 * C.batchSize k) =
      (C.trace k).averages (q := q) (C.batchSize k) + (C.fresh k).averageCLM (q := q) at h
  exact h.trans (C.stage_average_succ k).symm

theorem rawProjection_stage (k : ℕ) :
    C.rawProjection (C.stage k).totalCount = (C.stage k).part.averageCLM (q := q) := by
  induction k with
  | zero => exact C.rawProjection_one
  | succ k ih =>
    rw [C.stage_totalCount_succ, C.rawProjection_block k _ le_rfl, ih]
    exact C.batch_end_projection k

theorem rawProjection_bound (n : ℕ) : ‖C.rawProjection n‖ ≤ 1 + C.δ + C.η := by
  by_cases hn : n = 0
  · subst n
    rw [C.rawProjection_zero, norm_zero]
    have hd := C.δ_pos
    have he := C.η_pos
    linarith
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    have h := C.batch_bound (C.locate n) (C.offset n).val (C.offset n).isLt.le
    rw [← C.rawProjection_stage, ← C.rawProjection_block _ _ (C.offset n).isLt.le] at h
    rw [← C.flatten_index n hp] at h
    exact h

end ConstructionData
end PositiveBiorthogonal
