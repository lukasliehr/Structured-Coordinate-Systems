import Lean_Code.PositiveBiorthogonal.BatchBounds

/-! The source scaling parameter and the resulting sharp uniform batch bound. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem splittingSchedule_haar_bound (P : ActivePartition) (steps : ℕ) (hL : 2 ≤ steps)
    (hpfin : p ≠ ∞) (j : Fin (P.R * steps)) :
    ‖(((splittingSchedule P steps hL).split j).haarH : L 𝕜 p)‖ ≤
      2 * (splitTheta steps) ^ (-(1 / q.toReal)) * P.minLength ^ (-(1 / q.toReal)) := by
  have hr : ((splittingSchedule P steps hL).split j).ratio = splitTheta steps := by
    rw [splittingSchedule_split, geometricSplit_ratio]
  have h := ((splittingSchedule P steps hL).split j).haarH_norm_bound (𝕜 := 𝕜) (q := q) hpfin
    (by rw [hr]; exact (splitTheta_le_quarter steps hL).trans (by norm_num))
    P.minLength P.minLength_pos (splittingSchedule_parent_lower P steps hL j)
  simpa only [hr] using h

namespace AuxiliaryFamily
variable {δ : ℝ} (A : AuxiliaryFamily 𝕜 p q δ)

def batchScale (P : ActivePartition) (steps : ℕ) (η : ℝ) : ℝ :=
  (2 * A.M / η) * (splitTheta steps) ^ (-(1 / q.toReal)) * P.minLength ^ (-(1 / q.toReal))

theorem batchScale_pos (P : ActivePartition) (steps : ℕ) (hL : 2 ≤ steps) (η : ℝ) (hη : 0 < η) :
    0 < A.batchScale P steps η := by
  have hM : 0 < A.M := zero_lt_one.trans_le A.M_ge_one
  exact mul_pos (mul_pos (div_pos (mul_pos (by norm_num) hM) hη)
    (Real.rpow_pos_of_pos (splitTheta_pos steps hL) _)) (Real.rpow_pos_of_pos P.minLength_pos _)

theorem batchScale_mul (P : ActivePartition) (steps : ℕ) (η : ℝ) (hη : 0 < η) :
    A.batchScale P steps η * η =
      (2 * (splitTheta steps) ^ (-(1 / q.toReal)) * P.minLength ^ (-(1 / q.toReal))) * A.M := by
  unfold batchScale
  field_simp
  <;> ring

theorem scheduled_perturbation_bound (hpfin : p ≠ ∞) (P : ActivePartition) (steps : ℕ) (hL : 2 ≤ steps)
    (F : UnitBlock (2 * (P.R * steps))) (η : ℝ) (hη : 0 < η) (j : Fin (P.R * steps)) :
    ‖((A.batchScale P steps η : ℝ) : 𝕜)⁻¹ •
      rankPair (((splittingSchedule P steps hL).split j).haarH : L 𝕜 p)
        (F.transfer (A.s (P.R * steps) (batchFirst j)))‖ ≤ η := by
  apply rankPair_perturbation_bound _ _ (A.batchScale P steps η)
    (2 * (splitTheta steps) ^ (-(1 / q.toReal)) * P.minLength ^ (-(1 / q.toReal))) A.M η
    (A.batchScale_pos P steps hL η hη) (zero_le_one.trans A.M_ge_one)
    (splittingSchedule_haar_bound P steps hL hpfin j)
  · rw [F.transfer_norm]
    exact A.s_norm_le _ (Nat.mul_pos P.R_pos (by omega)) _
  · exact A.batchScale_mul P steps η hη

theorem scheduled_batch_bound (hpfin : p ≠ ∞) (hδ : 0 ≤ δ)
    (P : ActivePartition) (steps : ℕ) (hL : 2 ≤ steps) (F : UnitBlock (2 * (P.R * steps)))
    (hF : Disjoint F.carrier P.active) (η : ℝ) (hη : 0 < η) (t : ℕ) (ht : t ≤ 3 * (P.R * steps)) :
    ‖P.averageCLM (q := q) +
      lpPrefix (A.batchVectors (splittingSchedule P steps hL) F (A.batchScale P steps η : 𝕜))
        (A.batchCoefficients (splittingSchedule P steps hL) F (A.batchScale P steps η : 𝕜)) t‖ ≤ 1 + δ + η := by
  have h := A.batch_projection_bound (Nat.mul_pos P.R_pos (by omega)) hδ
    (splittingSchedule P steps hL) F (by simpa only [splittingSchedule_initial] using hF)
    (A.batchScale P steps η : 𝕜) η hη.le (A.scheduled_perturbation_bound hpfin P steps hL F η hη) t ht
  have he : (splittingSchedule P steps hL).averages (𝕜 := 𝕜) (p := p) (q := q) 0 =
      P.averageCLM (q := q) := rfl
  rw [he] at h
  exact h

end AuxiliaryFamily
end PositiveBiorthogonal
