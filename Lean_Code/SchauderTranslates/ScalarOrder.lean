import Lean_Code.SchauderTranslates.ScalarData
import Lean_Code.SchauderTranslates.PositiveMatrixNorm

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The unweighted probability torus, used to compare finite character sums. -/
def unitTorusWeight (d : ℕ) : TorusWeight d where
  density := fun _ => 1
  measurable := measurable_const
  positive := fun _ => zero_lt_one
  le_one := fun _ => le_rfl

theorem unitTorusWeight_orthonormal {d : ℕ} :
    Orthonormal ℂ (fun k : Fin d → ℤ => (unitTorusWeight d).vector k) := by
  have he (k : Fin d → ℤ) : (unitTorusWeight d).vector k =
      ContinuousMap.toLp 2 (torusMeasure d) ℂ (UnitAddTorus.mFourier k) := by
    apply Lp.ext
    filter_upwards [(unitTorusWeight d).vector_ae k,
      (UnitAddTorus.mFourier k).coeFn_toLp (p := 2) (μ := torusMeasure d) (𝕜 := ℂ)] with x hx hy
    rw [hx, hy]
    simp only [TorusWeight.vectorFn, unitTorusWeight, Real.sqrt_one, Complex.ofReal_one, one_mul]
  simp_rw [he]
  simpa only [UnitAddTorus.mFourierLp, torusMeasure] using!
    (UnitAddTorus.orthonormal_mFourier (d := Fin d))

namespace TorusWeight
variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A density bounded by one contracts every finite synthesis relative to Haar measure. -/
theorem synthesis_norm_le_unit (w : TorusWeight d) (k : ι → Fin d → ℤ) (c : ι → ℂ) :
    ‖∑ i, c i • w.vector (k i)‖ ≤ ‖∑ i, c i • (unitTorusWeight d).vector (k i)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [w.vector_sum_ae k Finset.univ c,
    (unitTorusWeight d).vector_sum_ae k Finset.univ c] with x hw hu
  rw [hw, hu]
  simp only [unitTorusWeight, Real.sqrt_one, Complex.ofReal_one, one_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.mpr (w.le_one x))

/-- A positive density floor controls the same synthesis from below. -/
theorem sqrt_mul_unit_norm_le_synthesis (w : TorusWeight d) {b : ℝ} (_hb : 0 ≤ b)
    (hfloor : ∀ x, b ≤ w.density x) (k : ι → Fin d → ℤ) (c : ι → ℂ) :
    Real.sqrt b * ‖∑ i, c i • (unitTorusWeight d).vector (k i)‖ ≤
      ‖∑ i, c i • w.vector (k i)‖ := by
  rw [← norm_smul_of_nonneg (Real.sqrt_nonneg b)]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_smul (Real.sqrt b)
    (∑ i, c i • (unitTorusWeight d).vector (k i)),
    w.vector_sum_ae k Finset.univ c,
    (unitTorusWeight d).vector_sum_ae k Finset.univ c] with x hs hw hu
  rw [hs, Pi.smul_apply, hw, hu]
  simp only [unitTorusWeight, Real.sqrt_one, Complex.ofReal_one, one_mul, norm_smul,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hfloor x)) (norm_nonneg _)

theorem synthesis_norm_sq_bounds (w : TorusWeight d) {b : ℝ} (hb : 0 ≤ b)
    (hfloor : ∀ x, b ≤ w.density x) (k : ι → Fin d → ℤ) (hk : Function.Injective k)
    (c : EuclideanSpace ℂ ι) :
    b * ‖c‖ ^ 2 ≤ ‖hilbertSynthesis (fun i => w.vector (k i)) c‖ ^ 2 ∧
      ‖hilbertSynthesis (fun i => w.vector (k i)) c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
  have ho := (unitTorusWeight_orthonormal (d := d)).comp k hk
  have hunit : ‖∑ i, c i • (unitTorusWeight d).vector (k i)‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    have hi := ho.inner_sum (fun i => c i) (fun i => c i) Finset.univ
    simp only [Function.comp_apply] at hi
    rw [hi]
    simp only [map_sum, Complex.conj_mul', ← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
    rfl
  have hl := w.sqrt_mul_unit_norm_le_synthesis hb hfloor k (fun i => c i)
  have hu := w.synthesis_norm_le_unit k (fun i => c i)
  have hls := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg b) (norm_nonneg _)) hl 2
  have hus := pow_le_pow_left₀ (norm_nonneg _) hu 2
  rw [mul_pow, Real.sq_sqrt hb, hunit] at hls
  rw [hunit] at hus
  exact ⟨hls, hus⟩

end TorusWeight

namespace ScalarData
variable {d n : ℕ}

theorem rawGram_quadratic (s : ScalarData d n) (c : EuclideanSpace ℂ (Unit ⊕ Fin n)) :
    RCLike.re (inner ℂ ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram c) c) =
      ‖hilbertSynthesis (fun i => s.vector (s.augmentedFrequency i)) c‖ ^ 2 := by
  let u := fun i => s.vector (s.augmentedFrequency i)
  have hg : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram =
      ((hilbertSynthesis u)†).comp (hilbertSynthesis u) :=
    (hilbertSynthesis_gram u).symm
  rw [hg, ContinuousLinearMap.comp_apply, adjoint_inner_left, inner_self_eq_norm_sq]

theorem rawGram_quadratic_bounds (s : ScalarData d n) {b : ℝ} (hb : 0 ≤ b)
    (hfloor : ∀ x, b ≤ s.density x) (c : EuclideanSpace ℂ (Unit ⊕ Fin n)) :
    b * ‖c‖ ^ 2 ≤ RCLike.re (inner ℂ
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram c) c) ∧
    RCLike.re (inner ℂ
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram c) c) ≤ ‖c‖ ^ 2 := by
  rw [s.rawGram_quadratic]
  exact s.toTorusWeight.synthesis_norm_sq_bounds hb hfloor s.augmentedFrequency
    s.augmentedFrequency_injective c

end ScalarData
end SchauderTranslates
