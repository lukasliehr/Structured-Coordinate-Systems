import Lean_Code.SchauderTranslates.ScalarNumerics

noncomputable section
namespace SchauderTranslates

/-- Every simultaneous upper constraint in the scalar induction can be enforced by one
strictly positive rare-activation parameter, including an arbitrarily small gain. -/
theorem exists_small_rare_parameter {ε Z C δ : ℝ} (he : 0 < ε) (he1 : ε < 1)
    (hZ : 0 < Z) (hδ : 0 < δ) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 / 100 ∧ p ≤ ε / (Z + ε) ∧
      p * C ≤ ε / 100 ∧ 0 < rareGain ε Z p ∧ rareGain ε Z p < δ := by
  let a : ℝ := 1 / 100
  let b : ℝ := ε / (Z + ε)
  let c : ℝ := ε / (100 * (|C| + 1))
  let d : ℝ := δ * (1 - ε) / (Z + ε ^ 2)
  have ha : 0 < a := by dsimp [a]; norm_num
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; exact div_pos (mul_pos hδ (by linarith)) (by positivity)
  obtain ⟨p, hp, hpl⟩ := exists_between (lt_min ha (lt_min hb (lt_min hc hd)))
  have hpa : p < a := lt_of_lt_of_le hpl (min_le_left _ _)
  have hpb : p < b := lt_of_lt_of_le hpl ((min_le_left b _).trans' (min_le_right a _))
  have hpc : p < c := lt_of_lt_of_le hpl
    ((min_le_left c d).trans' ((min_le_right b _).trans' (min_le_right a _)))
  have hpd : p < d := lt_of_lt_of_le hpl
    ((min_le_right c d).trans' ((min_le_right b _).trans' (min_le_right a _)))
  have hC : p * C ≤ ε / 100 := by
    have hec := (lt_div_iff₀ (by positivity : 0 < 100 * (|C| + 1))).mp hpc
    have hCa : p * C ≤ p * (|C| + 1) :=
      mul_le_mul_of_nonneg_left ((le_abs_self C).trans (by linarith)) hp.le
    nlinarith
  have hgp := rareGain_pos he he1 hZ hp hpb.le
  have hgu := (rareGain_bounds he he1 hZ hp hpb.le).2
  have hpd' := (lt_div_iff₀ (by positivity : 0 < Z + ε ^ 2)).mp hpd
  have hgδ : rareGain ε Z p < δ := by
    exact (mul_lt_mul_iff_left₀ (by linarith : 0 < 1 - ε)).mp (by nlinarith)
  exact ⟨p, hp, hpa.le, hpb.le, hC, hgp, hgδ⟩

end SchauderTranslates
