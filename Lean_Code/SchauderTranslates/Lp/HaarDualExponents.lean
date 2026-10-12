import Lean_Code.SchauderTranslates.Lp.HaarStrong

noncomputable section
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

theorem haar_dual_exponents {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp2 : 2 < p) (hpfin : p ≠ ∞) : 1 < q ∧ q < 2 := by
  have hq1 := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hpfin.lt_top
  have hqfin : q ≠ ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr
    (lt_trans (by norm_num) hp2) |>.ne
  have hs2 : 2 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp2
  have hpq := ENNReal.HolderConjugate.toReal (q := q) (by linarith : 1 < p.toReal)
  have hqR : q.toReal < 2 := by
    have he := hpq.sub_one_mul_conj
    nlinarith [hpq.symm.pos]
  exact ⟨hq1, (ENNReal.toReal_lt_toReal hqfin (by norm_num)).mp (by simpa using hqR)⟩

end SchauderTranslates.LpConstruction
