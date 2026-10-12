import Lean_Code.PositiveBiorthogonal.BatchCuts

/-! The bound at every cut, with actual averaging and fresh-block operators. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem batch_all_cuts_bound {N : ℕ}
    (d : Fin (2 * N) → L 𝕜 p) (s : Fin (2 * N) → L 𝕜 q)
    (H : Fin N → L 𝕜 p) (φ : Fin N → L 𝕜 q) (a : 𝕜)
    (E : ℕ → L 𝕜 p →L[𝕜] L 𝕜 p)
    (hE : ∀ j : Fin N, E (j.val + 1) - E j.val = rankPair (H j) (φ j))
    (C η : ℝ) (hη : 0 ≤ η)
    (hbase : ∀ j ≤ N, ∀ k ≤ 2 * N, ‖E j + lpPrefix d s k‖ ≤ C)
    (hpert : ∀ j : Fin N, ‖a⁻¹ • rankPair (H j) (s (batchFirst j))‖ ≤ η)
    (t : ℕ) (ht : t ≤ 3 * N) : ‖E 0 + batchPartial d s H φ a t‖ ≤ C + η := by
  by_cases hfirst : t ≤ 2 * N
  · by_cases heven : t % 2 = 0
    · have he : t = 2 * (t / 2) := by omega
      rw [he, batch_cut_even d s H φ a E hE _ (by omega)]
      exact (hbase _ (by omega) _ (by omega)).trans (le_add_of_nonneg_right hη)
    · have hj : t / 2 < N := by omega
      let j : Fin N := ⟨t / 2, hj⟩
      have he : t = 2 * j.val + 1 := by dsimp [j]; omega
      rw [he, batch_cut_odd d s H φ a E hE j]
      exact (norm_sub_le _ _).trans (add_le_add (hbase j.val j.isLt.le _ (by omega)) (hpert j))
  · have hh : t - 2 * N ≤ N := by omega
    have he : t = 2 * N + (t - 2 * N) := by omega
    rw [he, batch_cut_residual d s H φ a E hE _ hh]
    exact (hbase N le_rfl _ (by omega)).trans (le_add_of_nonneg_right hη)

namespace RefinementTrace
variable {N : ℕ} (T : RefinementTrace N)

def averages (h : ℕ) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  (T.state ⟨min h N, by omega⟩).averageCLM (q := q)

theorem averages_of_le (h : ℕ) (hh : h ≤ N) :
    T.averages (𝕜 := 𝕜) (p := p) (q := q) h =
      (T.state ⟨h, by omega⟩).averageCLM (q := q) := by
  simp only [averages, min_eq_left hh]

theorem averages_increment (j : Fin N) :
    T.averages (𝕜 := 𝕜) (p := p) (q := q) (j.val + 1) - T.averages (q := q) j.val =
      rankPair (q := q) (T.split j).haarH (T.split j).haarPhi := by
  rw [T.averages_of_le _ j.isLt, T.averages_of_le _ j.isLt.le]
  exact T.average_increment j

theorem averages_norm_le (h : ℕ) : ‖T.averages (𝕜 := 𝕜) (p := p) (q := q) h‖ ≤ 1 :=
  (T.state _).averageCLM_norm_le

theorem averages_localized (h : ℕ) :
    LocalizedOperator (T.state 0).active (T.state 0).active_measurable
      (T.averages (𝕜 := 𝕜) (p := p) (q := q) h) := by
  have hl := (T.state ⟨min h N, by omega⟩).averageCLM_localized (𝕜 := 𝕜) (p := p) (q := q)
  simpa only [T.active_eq_initial, averages] using hl

end RefinementTrace

namespace AuxiliaryFamily
variable {δ : ℝ} (A : AuxiliaryFamily 𝕜 p q δ) {N : ℕ}

theorem batch_base_bound (hN : 0 < N) (hδ : 0 ≤ δ) (T : RefinementTrace N) (F : UnitBlock (2 * N))
    (hF : Disjoint F.carrier (T.state 0).active) (j k : ℕ) (hk : k ≤ 2 * N) :
    ‖T.averages (𝕜 := 𝕜) (p := p) (q := q) j +
      lpPrefix (fun i => F.transfer (A.d N i)) (fun i => F.transfer (A.s N i)) k‖ ≤ 1 + δ := by
  change ‖T.averages (q := q) j + F.projection (A.d N) (A.s N) k‖ ≤ 1 + δ
  exact disjoint_operators _ _ (T.state 0).active_measurable F.measurable hF.symm _ _
    (T.averages_localized j) (F.projection_localized _ _ k) (1 + δ)
    ((T.averages_norm_le j).trans (le_add_of_nonneg_right hδ))
    (F.auxiliary_projection_bound hN A k hk)

theorem batch_projection_bound (hN : 0 < N) (hδ : 0 ≤ δ)
    (T : RefinementTrace N) (F : UnitBlock (2 * N)) (hF : Disjoint F.carrier (T.state 0).active)
    (a : 𝕜) (η : ℝ) (hη : 0 ≤ η)
    (hpert : ∀ j : Fin N,
      ‖a⁻¹ • rankPair ((T.split j).haarH : L 𝕜 p) (F.transfer (A.s N (batchFirst j)))‖ ≤ η)
    (t : ℕ) (ht : t ≤ 3 * N) :
    ‖T.averages (q := q) 0 + lpPrefix (A.batchVectors T F a) (A.batchCoefficients T F a) t‖ ≤
      1 + δ + η := by
  exact batch_all_cuts_bound _ _ _ _ a (T.averages (q := q)) T.averages_increment
    (1 + δ) η hη (fun j _ k hk => A.batch_base_bound hN hδ T F hF j k hk) hpert t ht

theorem batch_final_projection (hN : 0 < N) (T : RefinementTrace N) (F : UnitBlock (2 * N))
    (a : 𝕜) :
    T.averages (q := q) 0 + lpPrefix (A.batchVectors T F a) (A.batchCoefficients T F a) (3 * N) =
      T.averages (q := q) N + F.averageCLM (q := q) := by
  have he := batch_cut_residual (fun i => F.transfer (A.d N i)) (fun i => F.transfer (A.s N i))
    (fun j => (T.split j).haarH) (fun j => (T.split j).haarPhi) a
    (T.averages (q := q)) T.averages_increment N le_rfl
  have hn : 2 * N + N = 3 * N := by omega
  rw [hn] at he
  have hm : N + N = 2 * N := by omega
  rw [hm] at he
  change _ = T.averages (q := q) N + F.projection (A.d N) (A.s N) (2 * N) at he
  rw [F.projection_full _ _ (A.biorthogonal N hN)] at he
  exact he

end AuxiliaryFamily

theorem rankPair_perturbation_bound (H : L 𝕜 p) (s : L 𝕜 q) (a B M η : ℝ)
    (ha : 0 < a) (hM : 0 ≤ M) (hH : ‖H‖ ≤ B) (hs : ‖s‖ ≤ M) (he : a * η = B * M) :
    ‖(a : 𝕜)⁻¹ • rankPair H s‖ ≤ η := by
  rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos ha, rankPair, represented_rank_one_norm]
  calc
    _ ≤ a⁻¹ * (B * M) := mul_le_mul_of_nonneg_left
      (mul_le_mul hH hs (norm_nonneg _) ((norm_nonneg _).trans hH)) (inv_nonneg.mpr ha.le)
    _ = η := by rw [← he, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

end PositiveBiorthogonal
