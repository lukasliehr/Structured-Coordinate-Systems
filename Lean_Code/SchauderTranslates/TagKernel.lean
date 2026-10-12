import Lean_Code.SchauderTranslates.PiKernel
import Lean_Code.SchauderTranslates.ScalarData
import Lean_Code.SchauderTranslates.ScalarPrefixes
import Lean_Code.SchauderTranslates.Characters

/-!
# Scalar tag kernels

A scalar block used as a tag: its normalized density is a fiber kernel that does not
depend on the slow variable. This file records the normalized tag moments, their relation
to the centered Gram and gain of the scalar block, and the Gram form of Cauchy–Schwarz
used for the mean functional (blueprint `tag:packet`, `tag:lift`).
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Cauchy–Schwarz for a positive definite Gram: `|a* x|² ≤ (a* G⁻¹ a) ‖Σ x R‖²`. -/
theorem gram_cauchy_schwarz {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : ι → H) (hR : (Matrix.gram ℂ R).PosDef) (a x : ι → ℂ) :
    ‖star a ⬝ᵥ x‖ ^ 2 ≤ (star a ⬝ᵥ (Matrix.gram ℂ R)⁻¹ *ᵥ a).re * ‖∑ i, x i • R i‖ ^ 2 := by
  set G := Matrix.gram ℂ R with hG
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hR.isUnit
  set y := G⁻¹ *ᵥ a with hy
  have hGy : G *ᵥ y = a := by rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  have hH : Gᴴ = G := hR.isHermitian
  have hinner (u v : ι → ℂ) : star u ⬝ᵥ G *ᵥ v = inner ℂ (∑ i, u i • R i) (∑ i, v i • R i) := by
    rw [Matrix.star_dotProduct_gram_mulVec]
  have h1 : star a ⬝ᵥ x = star y ⬝ᵥ G *ᵥ x := by
    rw [← hGy, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
  have h2 : star a ⬝ᵥ G⁻¹ *ᵥ a = star y ⬝ᵥ G *ᵥ y := by
    rw [hGy, ← hy]
    rw [← hGy, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH, hGy]
  rw [h1, h2, hinner, hinner]
  have hre : (inner ℂ (∑ i, y i • R i) (∑ i, y i • R i)).re = ‖∑ i, y i • R i‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hre, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

namespace ScalarData
variable {dt nt : ℕ} (s : ScalarData dt nt)

/-- Expectation for the normalized scalar density. -/
def nIntegral (f : UnitAddTorus (Fin dt) → ℂ) : ℂ :=
  ∫ y, ((s.density y / s.mass : ℝ) : ℂ) * f y ∂torusMeasure dt

theorem nIntegral_rawGram (k l : Fin dt → ℤ) :
    s.nIntegral (fun y => star (UnitAddTorus.mFourier k y) * UnitAddTorus.mFourier l y) =
      inner ℂ (s.vector k) (s.vector l) / (s.mass : ℂ) := by
  rw [TorusWeight.vector_inner, nIntegral, eq_div_iff (by exact_mod_cast s.toTorusWeight.mass_pos.ne'),
    ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with y
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  push_cast
  field_simp

/-- Normalized expectation of the `k`th tag character. -/
def tagMean (k : Fin nt) : ℂ := s.nIntegral (UnitAddTorus.mFourier (s.frequencies k))

/-- Normalized second moments of the tag characters. -/
def tagSecond (k l : Fin nt) : ℂ :=
  s.nIntegral (fun y => star (UnitAddTorus.mFourier (s.frequencies k) y) *
    UnitAddTorus.mFourier (s.frequencies l) y)

theorem tagMean_eq_star_mean (k : Fin nt) : s.tagMean k = star (s.mean k) := by
  have h := s.nIntegral_rawGram 0 (s.frequencies k)
  have he : (fun y => star (UnitAddTorus.mFourier (0 : Fin dt → ℤ) y) *
      UnitAddTorus.mFourier (s.frequencies k) y) = UnitAddTorus.mFourier (s.frequencies k) := by
    funext y
    simp [UnitAddTorus.mFourier]
  rw [he] at h
  rw [tagMean, h]
  have hg : inner ℂ (s.vector 0) (s.vector (s.frequencies k)) = star (s.moment k) := by
    change s.rawGram (Sum.inl ()) (Sum.inr k) = star (s.rawGram (Sum.inr k) (Sum.inl ()))
    exact (s.rawGram_posDef.isHermitian.apply (Sum.inl ()) (Sum.inr k)).symm
  rw [hg, mean]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_inv₀, Complex.star_def,
    Complex.conj_ofReal]
  rw [div_eq_inv_mul]

theorem tagSecond_eq (k l : Fin nt) :
    s.tagSecond k l = s.nonconstantGram k l / (s.mass : ℂ) := by
  rw [tagSecond, s.nIntegral_rawGram]
  rfl

/-- The second moments are the centered Gram plus the mean dyad. -/
theorem tagSecond_eq_centered (k l : Fin nt) :
    s.tagSecond k l = s.centeredGram k l + star (s.tagMean k) * s.tagMean l := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  rw [tagSecond_eq, tagMean_eq_star_mean, tagMean_eq_star_mean, star_star]
  simp only [centeredGram, rawCenteredGram, mean, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul', star_inv₀,
    Complex.star_def, Complex.conj_ofReal]
  field_simp
  ring

/-- The normalized variance of the synthesis `Σ x k ψ k` is the centered quadratic form. -/
def tagVariance (x : Fin nt → ℂ) : ℝ := (star x ⬝ᵥ s.centeredGram *ᵥ x).re

/-- The normalized mean of the synthesis `Σ x k ψ k`. -/
def tagExpect (x : Fin nt → ℂ) : ℂ := ∑ k, s.tagMean k * x k

theorem tagExpect_eq (x : Fin nt → ℂ) : s.tagExpect x = star s.mean ⬝ᵥ x := by
  simp [tagExpect, dotProduct, tagMean_eq_star_mean]

/-- The centered Gram is the Gram of the normalized centered vectors. -/
def normalizedCentered (k : Fin nt) : Lp ℂ 2 (torusMeasure dt) :=
  ((Real.sqrt s.mass)⁻¹ : ℂ) • s.centeredVector k

theorem normalizedCentered_gram : Matrix.gram ℂ s.normalizedCentered = s.centeredGram := by
  have hm := s.toTorusWeight.mass_pos
  ext k l
  have hg := congrFun (congrFun s.centeredVector_gram k) l
  rw [Matrix.gram_apply] at hg
  rw [Matrix.gram_apply, normalizedCentered, normalizedCentered, inner_smul_left,
    inner_smul_right, hg]
  have hs : ((Real.sqrt s.mass : ℝ) : ℂ)⁻¹ * ((Real.sqrt s.mass : ℝ) : ℂ)⁻¹ = (s.mass : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hm.le]
  have hc : (starRingEnd ℂ) ((Real.sqrt s.mass : ℝ) : ℂ)⁻¹ = ((Real.sqrt s.mass : ℝ) : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  rw [hc, ← mul_assoc, hs]
  rfl

theorem tagVariance_eq_norm (x : Fin nt → ℂ) :
    s.tagVariance x = ‖∑ k, x k • s.normalizedCentered k‖ ^ 2 := by
  rw [tagVariance, ← s.normalizedCentered_gram, Matrix.star_dotProduct_gram_mulVec]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem tagVariance_nonneg (x : Fin nt → ℂ) : 0 ≤ s.tagVariance x := by
  rw [tagVariance_eq_norm]; positivity

/-- The mean functional has squared norm equal to the gain in the variance metric. -/
theorem tagExpect_sq_le (x : Fin nt → ℂ) :
    ‖s.tagExpect x‖ ^ 2 ≤ s.gain * s.tagVariance x := by
  have hpos : (Matrix.gram ℂ s.normalizedCentered).PosDef := by
    rw [normalizedCentered_gram]
    exact s.centeredGram_posDef
  have h := gram_cauchy_schwarz s.normalizedCentered hpos s.mean x
  rw [normalizedCentered_gram, ← tagVariance_eq_norm] at h
  rw [tagExpect_eq]
  exact h

/-- Centered prefix bounds of the scalar block, in variance form. -/
theorem tagVariance_prefix {q : ℝ} (hq : s.CenteredPrefixSqBound q) (j : ℕ) (x : Fin nt → ℂ) :
    s.tagVariance (fun k => if k.val < j then x k else 0) ≤ q * s.tagVariance x := by
  have hm := s.toTorusWeight.mass_pos
  have h := hq j x
  rw [tagVariance_eq_norm, tagVariance_eq_norm]
  have hscale (v : Fin nt → ℂ) : ∑ k, v k • s.normalizedCentered k =
      ((Real.sqrt s.mass)⁻¹ : ℂ) • ∑ k, v k • s.centeredVector k := by
    simp only [normalizedCentered, Finset.smul_sum, smul_smul, mul_comm]
  rw [hscale, hscale, norm_smul, norm_smul, mul_pow, mul_pow]
  have hp : (∑ k, (if k.val < j then x k else 0) • s.centeredVector k) =
      ∑ k, if k.val < j then x k • s.centeredVector k else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [hp]
  have hn : 0 ≤ ‖((Real.sqrt s.mass)⁻¹ : ℂ)‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h hn]

end ScalarData

/-- The scalar density, normalized to conditional mass one, as a fiber kernel that does
not depend on the slow variable. -/
def scalarKernel (S : Type*) [MeasurableSpace S] {dt nt : ℕ} (s : ScalarData dt nt) :
    FiberKernel S (UnitAddTorus (Fin dt)) (torusMeasure dt) where
  density p := s.density p.2 / s.mass
  measurable := (s.measurable.comp measurable_snd).div_const _
  nonneg p := div_nonneg (s.positive _).le s.toTorusWeight.mass_pos.le
  bound := 1 / s.mass
  upper p := div_le_div_of_nonneg_right (s.le_one _) s.toTorusWeight.mass_pos.le
  mass x := by
    rw [integral_div]
    exact div_self s.toTorusWeight.mass_pos.ne'

/-- The tag kernel: independent normalized scalar densities on `m` tag blocks. -/
abbrev tagKernel (S : Type*) [MeasurableSpace S] {dt nt : ℕ} (s : ScalarData dt nt) (m : ℕ) :=
  FiberKernel.piKernel (fun _ : Fin m => scalarKernel S s)

end SchauderTranslates
