import Lean_Code.SchauderTranslates.MatrixInverseOrder

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive interpolation metric in the soft-capture function. -/
def softGram (G : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ := t • 1 + (1 - t) • G

def softCapture (G : Matrix ι ι ℂ) (b : ι → ℂ) (t : ℝ) : ℝ :=
  (1 - t) ^ 2 * gramCapture (softGram G t) b

theorem softGram_posDef {G : Matrix ι ι ℂ} (hG : G.PosDef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (softGram G t).PosDef := by
  by_cases ht : t = 1
  · subst t
    simpa [softGram] using (Matrix.PosDef.one (n := ι) (R := ℂ))
  · have h1 : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 ht)
    have h := (hG.smul h1).add_posSemidef (Matrix.PosSemidef.one.smul ht0)
    simpa only [softGram, add_comm] using h

theorem softCapture_nonneg {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ softCapture G b t :=
  mul_nonneg (sq_nonneg _) (gramCapture_nonneg (softGram_posDef hG ht0 ht1) b)

@[simp] theorem softCapture_zero (G : Matrix ι ι ℂ) (b : ι → ℂ) : softCapture G b 0 = gramCapture G b := by
  simp [softCapture, softGram]

@[simp] theorem softCapture_one (G : Matrix ι ι ℂ) (b : ι → ℂ) : softCapture G b 1 = 0 := by
  simp [softCapture]

/-- Positive contraction metrics give a decreasing soft-capture function on the entire closed interval. -/
theorem softCapture_antitone {G : Matrix ι ι ℂ} (hG : G.PosDef) (hG1 : (1 - G).PosSemidef)
    (b : ι → ℂ) : AntitoneOn (softCapture G b) (Set.Icc 0 1) := by
  intro u hu t ht hut
  have he : softGram G t - softGram G u = (t - u) • (1 - G) := by
    simp only [softGram, sub_smul, smul_sub, one_smul]
    abel
  have horder : (softGram G t - softGram G u).PosSemidef := by
    rw [he]
    exact hG1.smul (sub_nonneg.mpr hut)
  have hc := gramCapture_antitone (softGram_posDef hG hu.1 hu.2) (softGram_posDef hG ht.1 ht.2) horder b
  have hf : (1 - t) ^ 2 ≤ (1 - u) ^ 2 := by nlinarith [hu.1, hu.2, ht.1, ht.2]
  exact mul_le_mul hf hc (gramCapture_nonneg (softGram_posDef hG ht.1 ht.2) b) (sq_nonneg _)

/-- The upper endpoint estimate uses only the squared Euclidean norm of the moment column. -/
theorem softCapture_le_norm_div {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    softCapture G b t ≤ ‖(WithLp.toLp 2 b : EuclideanSpace ℂ ι)‖ ^ 2 / t := by
  have hTI : (t • (1 : Matrix ι ι ℂ)).PosDef := Matrix.PosDef.one.smul ht0
  have horder : (softGram G t - t • (1 : Matrix ι ι ℂ)).PosSemidef := by
    simpa only [softGram, add_sub_cancel_left] using hG.posSemidef.smul (sub_nonneg.mpr ht1)
  have hc := gramCapture_antitone hTI (softGram_posDef hG ht0.le ht1) horder b
  rw [gramCapture_real_smul Matrix.PosDef.one ht0, gramCapture_one] at hc
  have hf : (1 - t) ^ 2 ≤ 1 := by nlinarith
  have hnon := gramCapture_nonneg (softGram_posDef hG ht0.le ht1) b
  calc
    softCapture G b t ≤ gramCapture (softGram G t) b := mul_le_of_le_one_left hnon hf
    _ ≤ t⁻¹ * ‖(WithLp.toLp 2 b : EuclideanSpace ℂ ι)‖ ^ 2 := hc
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- A spectral floor controls the capture at the square of the deficit. -/
theorem softCapture_floor_lower {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hfloor : (G - (ε ^ 2) • 1).PosSemidef) :
    gramCapture G b / 4 ≤ softCapture G b (ε ^ 2) := by
  have he1 : ε ^ 2 ≤ 1 := by nlinarith
  have he : (2 : ℝ) • G - softGram G (ε ^ 2) = (G - (ε ^ 2) • 1) + (ε ^ 2) • G := by
    simp only [softGram, sub_smul, one_smul]
    module
  have horder : ((2 : ℝ) • G - softGram G (ε ^ 2)).PosSemidef := by
    rw [he]
    exact hfloor.add (hG.posSemidef.smul (sq_nonneg ε))
  have hc := gramCapture_antitone (softGram_posDef hG (sq_nonneg ε) he1)
    (hG.smul (by norm_num : (0 : ℝ) < 2)) horder b
  rw [gramCapture_real_smul hG (by norm_num : (0 : ℝ) < 2)] at hc
  have hf : (1 / 2 : ℝ) ≤ (1 - ε ^ 2) ^ 2 := by nlinarith [sq_nonneg (ε ^ 2)]
  have hn := gramCapture_nonneg (softGram_posDef hG (sq_nonneg ε) he1) b
  have hg := gramCapture_nonneg hG b
  have hm := mul_le_mul hf hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) hg) (sq_nonneg (1 - ε ^ 2))
  dsimp only [softCapture]
  nlinarith

/-- Capture at a larger scale retains the explicit `1/(4R)` proportion. -/
theorem softCapture_scale_lower {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ)
    {R t : ℝ} (hR : 1 ≤ R) (ht : 0 ≤ t) (hRt : R * t ≤ 1 / 2) :
    softCapture G b t / (4 * R) ≤ softCapture G b (R * t) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRt0 : 0 ≤ R * t := mul_nonneg hR0.le ht
  have htt : t ≤ R * t := le_mul_of_one_le_left ht hR
  have ht1 : t ≤ 1 := by linarith
  have hRt1 : R * t ≤ 1 := by linarith
  have he : R • softGram G t - softGram G (R * t) = (R - 1) • G := by
    simp only [softGram, smul_add, smul_smul, sub_smul, one_smul]
    module
  have horder : (R • softGram G t - softGram G (R * t)).PosSemidef := by
    rw [he]
    exact hG.posSemidef.smul (sub_nonneg.mpr hR)
  have hc := gramCapture_antitone (softGram_posDef hG hRt0 hRt1)
    ((softGram_posDef hG ht ht1).smul hR0) horder b
  rw [gramCapture_real_smul (softGram_posDef hG ht ht1) hR0] at hc
  have hc' : gramCapture (softGram G t) b ≤ R * gramCapture (softGram G (R * t)) b := by
    have hh := mul_le_mul_of_nonneg_left hc hR0.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hR0.ne', one_mul] using hh
  have hf : (1 - t) ^ 2 ≤ 1 := by nlinarith
  have hfr : (1 / 4 : ℝ) ≤ (1 - R * t) ^ 2 := by nlinarith
  have hn := gramCapture_nonneg (softGram_posDef hG hRt0 hRt1) b
  have hn' := gramCapture_nonneg (softGram_posDef hG ht ht1) b
  apply (div_le_iff₀ (by positivity : 0 < 4 * R)).mpr
  dsimp only [softCapture]
  have hsmall := mul_le_mul_of_nonneg_right hf hn'
  have hbig := mul_le_mul_of_nonneg_right hfr hn
  nlinarith [mul_le_mul_of_nonneg_left hbig hR0.le]

end SchauderTranslates
