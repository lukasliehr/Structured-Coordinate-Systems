import Lean_Code.SchauderTranslates.Lp.HaarPairing

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- The conjugate of the paper's unnormalized norming function, for the
bilinear integral pairing. Its value at zero is zero as well. -/
def haarNormingValue (s : ℝ) (z : ℂ) : ℂ := ‖z‖ ^ (s - 2) • star z

theorem haarNormingValue_norm {s : ℝ} (hs : 2 < s) (z : ℂ) :
    ‖haarNormingValue s z‖ = ‖z‖ ^ (s - 1) := by
  rw [haarNormingValue, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), norm_star]
  exact (Real.rpow_add_one' (norm_nonneg z) (by linarith : (s - 2) + 1 ≠ 0)).symm.trans
    (congrArg (fun a : ℝ => ‖z‖ ^ a) (by ring))

theorem haarNormingValue_product {s : ℝ} (hs : 2 < s) (z : ℂ) :
    z * haarNormingValue s z = (‖z‖ ^ s : ℝ) := by
  rw [haarNormingValue, Complex.real_smul, mul_left_comm]
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add_natCast' (norm_nonneg z) (by linarith : (s - 2) + (2 : ℕ) ≠ 0)]
  congr 1
  ring

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
theorem haarNormingValue_memLp (hp2 : 2 < p) (hpfin : p ≠ ∞) (f : HaarLp p) :
    MemLp (fun x => haarNormingValue p.toReal (f x)) q haarMeasure := by
  have hs2 : 2 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp2
  have hpq := ENNReal.HolderConjugate.toReal (q := q) (by linarith : 1 < p.toReal)
  have hqfin : q ≠ ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr
    (by exact lt_trans (by norm_num) hp2) |>.ne
  have hm : AEStronglyMeasurable (fun x => haarNormingValue p.toReal (f x)) haarMeasure := by
    exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable.smul
      (continuous_star.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  apply (integrable_norm_rpow_iff hm (ENNReal.HolderConjugate.ne_zero q p) hqfin).mp
  convert integrable_norm_rpow f (ENNReal.HolderConjugate.ne_zero p q) hpfin using 1
  funext x
  rw [haarNormingValue_norm hs2, ← Real.rpow_mul (norm_nonneg _), hpq.sub_one_mul_conj]

def haarNorming (hp2 : 2 < p) (hpfin : p ≠ ∞) (f : HaarLp p) : HaarLp q :=
  (haarNormingValue_memLp (q := q) hp2 hpfin f).toLp _

theorem haarNorming_ae (hp2 : 2 < p) (hpfin : p ≠ ∞) (f : HaarLp p) :
    haarNorming (q := q) hp2 hpfin f =ᵐ[haarMeasure]
      (fun x => haarNormingValue p.toReal (f x)) := MemLp.coeFn_toLp _

end SchauderTranslates.LpConstruction
