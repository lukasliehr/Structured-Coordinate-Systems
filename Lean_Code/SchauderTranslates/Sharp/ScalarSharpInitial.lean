import Lean_Code.SchauderTranslates.InitialScalar

/-!
# The parametrized initial scalar block

Paper (`h2:ss:scalar-induction`, eq. `h2:eq:scalar-initial`): the circle weight
`w₀(x) = 1 - a + a cos (2 π x)` with the single character `e^{2 π i x}`. Its augmented Gram is
`[[1 - a, a / 2], [a / 2, 1 - a]]`, so `ε₀ = a`, `Z₀ = a² / (4 - 8 a + 3 a²)` and the inverse
diagonal is `(1 - a) / ((1 - a)² - (a / 2)²)`. The block of `InitialScalar` is the case
`a = 1 / 10`.
-/

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp.Scalar
open SchauderTranslates

/-- The density `1 - a + a cos (2 π x)` on the circle. -/
def sharpDensity (a : ℝ) (x : UnitAddTorus (Fin 1)) : ℝ :=
  1 - a + a * (UnitAddTorus.mFourier initialMode x).re

theorem sharpDensity_bounds {a : ℝ} (ha0 : 0 ≤ a) (x : UnitAddTorus (Fin 1)) :
    1 - 2 * a ≤ sharpDensity a x ∧ sharpDensity a x ≤ 1 := by
  have hl := (abs_le.mp (Complex.abs_re_le_norm (UnitAddTorus.mFourier initialMode x))).1
  have hu := Complex.re_le_norm (UnitAddTorus.mFourier initialMode x)
  rw [torus_character_norm] at hl hu
  unfold sharpDensity
  constructor <;> nlinarith

/-- The determinant `(1 - a)² - (a / 2)²` of the initial augmented Gram. -/
def sharpDet (a : ℝ) : ℝ := (1 - a) ^ 2 - (a / 2) ^ 2

theorem sharpDet_pos {a : ℝ} (ha1 : a < 1 / 2) : 0 < sharpDet a := by
  unfold sharpDet
  nlinarith [sq_nonneg a]

/-- The explicit seed: density `1 - a + a cos (2 π x)` and the character of frequency one. -/
def sharpInitial (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1 / 2) : ScalarData 1 1 where
  density := sharpDensity a
  measurable := by unfold sharpDensity; fun_prop
  positive x := lt_of_lt_of_le (by linarith) (sharpDensity_bounds ha0 x).1
  le_one x := (sharpDensity_bounds ha0 x).2
  frequencies := fun _ => initialMode
  injective := fun _ _ _ => Subsingleton.elim _ _
  nonconstant i h := by
    have h0 := congrFun h 0
    norm_num [initialMode] at h0

theorem sharpDensity_fourier (a : ℝ) (x : UnitAddTorus (Fin 1)) :
    (sharpDensity a x : ℂ) = ((1 - a : ℝ) : ℂ) +
      ((a / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier initialMode x +
      ((a / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (-initialMode) x := by
  rw [UnitAddTorus.mFourier_neg]
  have h := Complex.add_conj (UnitAddTorus.mFourier initialMode x)
  unfold sharpDensity
  push_cast at h ⊢
  linear_combination -((a : ℂ) / 2) * h

theorem sharpDensity_mul_character (a : ℝ) (k : Fin 1 → ℤ) (x : UnitAddTorus (Fin 1)) :
    (sharpDensity a x : ℂ) * UnitAddTorus.mFourier k x =
      ((1 - a : ℝ) : ℂ) * UnitAddTorus.mFourier k x +
      ((a / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (initialMode + k) x +
      ((a / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (-initialMode + k) x := by
  rw [sharpDensity_fourier, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
  ring

/-- Every weighted Fourier moment of the seed, computed against probability Haar measure. -/
theorem sharp_fourier_moment (a : ℝ) (k : Fin 1 → ℤ) :
    (∫ x, (sharpDensity a x : ℂ) * UnitAddTorus.mFourier k x ∂torusMeasure 1) =
      ((1 - a : ℝ) : ℂ) * (if k = 0 then 1 else 0) +
      ((a / 2 : ℝ) : ℂ) * (if initialMode + k = 0 then 1 else 0) +
      ((a / 2 : ℝ) : ℂ) * (if -initialMode + k = 0 then 1 else 0) := by
  simp_rw [sharpDensity_mul_character]
  have h₁ : Integrable (fun x => ((1 - a : ℝ) : ℂ) * UnitAddTorus.mFourier k x)
      (torusMeasure 1) := (torus_character_integrable k).const_mul _
  have h₂ : Integrable (fun x => ((a / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (initialMode + k) x)
      (torusMeasure 1) := (torus_character_integrable (initialMode + k)).const_mul _
  have h₃ : Integrable (fun x => ((a / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (-initialMode + k) x)
      (torusMeasure 1) := (torus_character_integrable (-initialMode + k)).const_mul _
  have h₁₂ : Integrable (fun x => ((1 - a : ℝ) : ℂ) * UnitAddTorus.mFourier k x +
      ((a / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (initialMode + k) x) (torusMeasure 1) :=
    h₁.add h₂
  rw [integral_add h₁₂ h₃, integral_add h₁ h₂]
  simp only [integral_const_mul, integral_torus_character]

variable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1 / 2)

theorem sharpInitial_mass : (sharpInitial a ha0 ha1).mass = 1 - a := by
  have h := sharp_fourier_moment a 0
  simp [initialMode_ne_zero] at h
  have hm : ((sharpInitial a ha0 ha1).mass : ℂ) = ((1 - a : ℝ) : ℂ) := by
    calc
      _ = ∫ x, (sharpDensity a x : ℂ) ∂torusMeasure 1 :=
        (integral_ofReal (𝕜 := ℂ) (f := sharpDensity a)).symm
      _ = _ := by
        simpa only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one,
          Complex.ofReal_sub, Complex.ofReal_one] using h
  exact_mod_cast hm

/-- The only nonconstant raw moment is `a / 2`, with the Gram conjugation convention. -/
theorem sharpInitial_moment (i : Fin 1) :
    (sharpInitial a ha0 ha1).moment i = ((a / 2 : ℝ) : ℂ) := by
  change inner ℂ ((sharpInitial a ha0 ha1).vector initialMode)
    ((sharpInitial a ha0 ha1).vector 0) = _
  rw [TorusWeight.vector_inner]
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one,
    Complex.star_def, ← UnitAddTorus.mFourier_neg]
  have hn : -initialMode + -initialMode ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [initialMode] at h0
  have h := sharp_fourier_moment a (-initialMode)
  change (∫ x, (sharpDensity a x : ℂ) * UnitAddTorus.mFourier (-initialMode) x
    ∂torusMeasure 1) = _
  simpa [initialMode_ne_zero, hn] using h

theorem sharpInitial_rawGram :
    (sharpInitial a ha0 ha1).rawGram = initialGram ((1 - a : ℝ) : ℂ) ((a / 2 : ℝ) : ℂ) := by
  rw [(sharpInitial a ha0 ha1).rawGram_fromBlocks]
  ext (i | i) (j | j)
  · cases i; cases j
    simp [initialGram, sharpInitial_mass]
  · cases i
    simp [initialGram, sharpInitial_moment]
  · cases j
    simp [initialGram, sharpInitial_moment]
  · have hij : i = j := Subsingleton.elim _ _
    subst j
    simpa [initialGram, ScalarData.nonconstantGram, sharpInitial_mass] using
      (sharpInitial a ha0 ha1).rawGram_diagonal (Sum.inr i)

/-- The inverse of a symmetric two-by-two matrix with equal diagonal entries. -/
theorem initialGram_inverse_of_ne (α β : ℂ) (h : α ^ 2 - β ^ 2 ≠ 0) :
    (initialGram α β)⁻¹ = initialGram (α / (α ^ 2 - β ^ 2)) (-β / (α ^ 2 - β ^ 2)) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [initialGram, Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals
    field_simp
  all_goals ring

theorem sharpInitial_inverse :
    (sharpInitial a ha0 ha1).rawGram⁻¹ =
      initialGram (((1 - a) / sharpDet a : ℝ) : ℂ) ((-(a / 2) / sharpDet a : ℝ) : ℂ) := by
  have hdet : (((1 - a : ℝ) : ℂ)) ^ 2 - ((a / 2 : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have h := (sharpDet_pos ha1).ne'
    unfold sharpDet at h
    exact_mod_cast h
  rw [sharpInitial_rawGram, initialGram_inverse_of_ne _ _ hdet]
  unfold sharpDet
  push_cast
  rfl

theorem sharpInitial_inverse_diagonal (i : Unit ⊕ Fin 1) :
    (sharpInitial a ha0 ha1).rawGram⁻¹ i i = (((1 - a) / sharpDet a : ℝ) : ℂ) := by
  rw [sharpInitial_inverse]
  simp [initialGram]

/-- Paper `h2:eq:scalar-initial`: `Z₀ = a² / (4 - 8 a + 3 a²)`. -/
theorem sharpInitial_gain :
    (sharpInitial a ha0 ha1).gain = a ^ 2 / (4 - 8 * a + 3 * a ^ 2) := by
  have h := (sharpInitial a ha0 ha1).rawGram_inverse_constant_gain
  rw [sharpInitial_inverse_diagonal, sharpInitial_mass] at h
  have hr : (1 - a) / sharpDet a = (1 + (sharpInitial a ha0 ha1).gain) / (1 - a) := by
    exact_mod_cast h
  have hdet := sharpDet_pos ha1
  have hm : 0 < 1 - a := by linarith
  have hD : 0 < 4 - 8 * a + 3 * a ^ 2 := by nlinarith [sq_nonneg a]
  rw [div_eq_div_iff hdet.ne' hm.ne'] at hr
  rw [eq_div_iff hD.ne']
  unfold sharpDet at hr
  linear_combination (-4) * hr

theorem sharpInitial_even : (sharpInitial a ha0 ha1).IsEven := by
  intro x
  change sharpDensity a (-x) = sharpDensity a x
  simp [sharpDensity, torus_character_neg_apply]

theorem sharpInitial_floor : (sharpInitial a ha0 ha1).HasPositiveFloor :=
  ⟨1 - 2 * a, by linarith, fun x => (sharpDensity_bounds ha0 x).1⟩

/-- The raw inverse norm is at most `(1 - a / 2) / det = 1 / (1 - 3 a / 2)`. -/
theorem sharpInitial_inverse_norm_le :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin 1))
      (sharpInitial a ha0 ha1).rawGram⁻¹‖ ≤ (1 - a / 2) / sharpDet a := by
  have hdet := sharpDet_pos ha1
  have hr : 0 ≤ (1 - a / 2) / sharpDet a := div_nonneg (by linarith) hdet.le
  apply positive_matrix_norm_le (sharpInitial a ha0 ha1).rawGram_posDef.inv.posSemidef hr
  rw [sharpInitial_inverse]
  have he : (((1 - a / 2) / sharpDet a : ℝ) : ℂ) •
        (1 : Matrix (Unit ⊕ Fin 1) (Unit ⊕ Fin 1) ℂ) -
        initialGram (((1 - a) / sharpDet a : ℝ) : ℂ) ((-(a / 2) / sharpDet a : ℝ) : ℂ) =
      (((a / 2) / sharpDet a : ℝ) : ℂ) • Matrix.gram ℂ (fun _ : Unit ⊕ Fin 1 => (1 : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [initialGram, Matrix.gram_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, if_true, smul_eq_mul, mul_one, inner_self_eq_norm_sq_to_K,
        norm_one]
      push_cast
      ring
    · simp only [initialGram, Matrix.gram_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, hij, if_false, smul_eq_mul, mul_zero, zero_sub,
        inner_self_eq_norm_sq_to_K, norm_one]
      push_cast
      ring
  rw [he]
  exact (Matrix.posSemidef_gram ℂ (fun _ : Unit ⊕ Fin 1 => (1 : ℂ))).smul (by
    exact_mod_cast (div_nonneg (by linarith) hdet.le : 0 ≤ (a / 2) / sharpDet a))

theorem sharpInitial_centered_prefix_iff (q : ℝ) :
    (sharpInitial a ha0 ha1).CenteredPrefixSqBound q ↔ 1 ≤ q :=
  single_prefixSqBound_iff (sharpInitial a ha0 ha1).centeredVector
    ((sharpInitial a ha0 ha1).centeredVectors_linearIndependent.ne_zero 0) q

end SchauderTranslates.Sharp.Scalar
