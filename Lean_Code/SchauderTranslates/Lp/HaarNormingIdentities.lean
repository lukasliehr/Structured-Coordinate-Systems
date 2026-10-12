import Lean_Code.SchauderTranslates.Lp.HaarNorming

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haarNorming_norm (hp2 : 2 < p) (hpfin : p ≠ ∞) (f : HaarLp p) :
    ‖haarNorming (q := q) hp2 hpfin f‖ = ‖f‖ ^ (p.toReal - 1) := by
  have hs2 : 2 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp2
  have hpq := ENNReal.HolderConjugate.toReal (q := q) (by linarith : 1 < p.toReal)
  have hqfin : q ≠ ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr
    (lt_trans (by norm_num) hp2) |>.ne
  apply (Real.rpow_left_inj (norm_nonneg _)
    (Real.rpow_nonneg (norm_nonneg f) _) hpq.symm.ne_zero).mp
  rw [← Real.rpow_mul (norm_nonneg f), hpq.sub_one_mul_conj,
    ← integral_norm_rpow (haarNorming (q := q) hp2 hpfin f)
      (ENNReal.HolderConjugate.ne_zero q p) hqfin,
    ← integral_norm_rpow f (ENNReal.HolderConjugate.ne_zero p q) hpfin]
  apply integral_congr_ae
  filter_upwards [haarNorming_ae (q := q) hp2 hpfin f] with x hx
  rw [hx, haarNormingValue_norm hs2, ← Real.rpow_mul (norm_nonneg _), hpq.sub_one_mul_conj]

theorem haarNorming_pairing (hp2 : 2 < p) (hpfin : p ≠ ∞) (f : HaarLp p) :
    haarPairing p q f (haarNorming (q := q) hp2 hpfin f) = (‖f‖ ^ p.toReal : ℝ) := by
  have hs2 : 2 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp2
  rw [haarPairing_apply, ← integral_norm_rpow f (ENNReal.HolderConjugate.ne_zero p q) hpfin,
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [haarNorming_ae (q := q) hp2 hpfin f] with x hx
  rw [hx, haarNormingValue_product hs2]

/-- The explicit norming function recovers the norm from a bound for
every dual pairing. The zero case needs no division. -/
theorem haar_norm_le_of_pairing_bound (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (f : HaarLp p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ g : HaarLp q, ‖haarPairing p q f g‖ ≤ C * ‖g‖) : ‖f‖ ≤ C := by
  by_cases hf : f = 0
  · simpa [hf] using hC
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hb := h (haarNorming (q := q) hp2 hpfin f)
  rw [haarNorming_pairing, haarNorming_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg f) _)] at hb
  have he : ‖f‖ ^ p.toReal = ‖f‖ * ‖f‖ ^ (p.toReal - 1) := by
    rw [mul_comm, ← Real.rpow_add_one hn.ne']
    congr 1
    ring
  rw [he] at hb
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hn _)).mp hb

end SchauderTranslates.LpConstruction
