import Lean_Code.SchauderTranslates.ScalarGram
import Lean_Code.SchauderTranslates.PositiveMatrixNorm
import Lean_Code.SchauderTranslates.ScalarPrefixes

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The first nonconstant character on the one-dimensional torus. -/
def initialMode : Fin 1 → ℤ := fun _ => 1

def initialDensity (x : UnitAddTorus (Fin 1)) : ℝ :=
  9 / 10 + (1 / 10) * (UnitAddTorus.mFourier initialMode x).re

theorem initialDensity_bounds (x : UnitAddTorus (Fin 1)) :
    4 / 5 ≤ initialDensity x ∧ initialDensity x ≤ 1 := by
  have hl := (abs_le.mp (Complex.abs_re_le_norm (UnitAddTorus.mFourier initialMode x))).1
  have hu := Complex.re_le_norm (UnitAddTorus.mFourier initialMode x)
  rw [torus_character_norm] at hl hu
  unfold initialDensity
  constructor <;> linarith

/-- The explicit seed: density `9/10 + cos(2πx)/10` and the character of frequency one. -/
def initialScalar : ScalarData 1 1 where
  density := initialDensity
  measurable := by unfold initialDensity; fun_prop
  positive x := lt_of_lt_of_le (by norm_num) (initialDensity_bounds x).1
  le_one x := (initialDensity_bounds x).2
  frequencies := fun _ => initialMode
  injective := fun _ _ _ => Subsingleton.elim _ _
  nonconstant i h := by
    have h0 := congrFun h 0
    norm_num [initialMode] at h0

theorem torus_character_integrable {d : ℕ} (k : Fin d → ℤ) :
    Integrable (UnitAddTorus.mFourier k) (torusMeasure d) :=
  Integrable.of_bound (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => (torus_character_norm k x).le))

theorem initialDensity_fourier (x : UnitAddTorus (Fin 1)) :
    (initialDensity x : ℂ) = (9 / 10 : ℂ) +
      (1 / 20 : ℂ) * UnitAddTorus.mFourier initialMode x +
      (1 / 20 : ℂ) * UnitAddTorus.mFourier (-initialMode) x := by
  rw [UnitAddTorus.mFourier_neg]
  have h := Complex.add_conj (UnitAddTorus.mFourier initialMode x)
  unfold initialDensity
  push_cast at h ⊢
  linear_combination -(1 / 20 : ℂ) * h

theorem initialDensity_mul_character (k : Fin 1 → ℤ) (x : UnitAddTorus (Fin 1)) :
    (initialDensity x : ℂ) * UnitAddTorus.mFourier k x =
      (9 / 10 : ℂ) * UnitAddTorus.mFourier k x +
      (1 / 20 : ℂ) * UnitAddTorus.mFourier (initialMode + k) x +
      (1 / 20 : ℂ) * UnitAddTorus.mFourier (-initialMode + k) x := by
  rw [initialDensity_fourier, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
  ring

/-- Every weighted Fourier moment of the seed, computed against probability Haar measure. -/
theorem initial_fourier_moment (k : Fin 1 → ℤ) :
    (∫ x, (initialDensity x : ℂ) * UnitAddTorus.mFourier k x ∂torusMeasure 1) =
      (9 / 10 : ℂ) * (if k = 0 then 1 else 0) +
      (1 / 20 : ℂ) * (if initialMode + k = 0 then 1 else 0) +
      (1 / 20 : ℂ) * (if -initialMode + k = 0 then 1 else 0) := by
  simp_rw [initialDensity_mul_character]
  have h₁ : Integrable (fun x => (9 / 10 : ℂ) * UnitAddTorus.mFourier k x) (torusMeasure 1) :=
    (torus_character_integrable k).const_mul _
  have h₂ : Integrable (fun x => (1 / 20 : ℂ) * UnitAddTorus.mFourier (initialMode + k) x) (torusMeasure 1) :=
    (torus_character_integrable (initialMode + k)).const_mul _
  have h₃ : Integrable (fun x => (1 / 20 : ℂ) * UnitAddTorus.mFourier (-initialMode + k) x) (torusMeasure 1) :=
    (torus_character_integrable (-initialMode + k)).const_mul _
  have h₁₂ : Integrable (fun x => (9 / 10 : ℂ) * UnitAddTorus.mFourier k x +
      (1 / 20 : ℂ) * UnitAddTorus.mFourier (initialMode + k) x) (torusMeasure 1) := h₁.add h₂
  rw [integral_add h₁₂ h₃, integral_add h₁ h₂]
  simp only [integral_const_mul, integral_torus_character]

theorem initialMode_ne_zero : initialMode ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [initialMode] at h0

theorem initialScalar_mass : initialScalar.mass = 9 / 10 := by
  have h := initial_fourier_moment 0
  simp [initialMode_ne_zero] at h
  have hm : (initialScalar.mass : ℂ) = (9 / 10 : ℂ) := by
    calc
      _ = ∫ x, (initialDensity x : ℂ) ∂torusMeasure 1 :=
        (integral_ofReal (𝕜 := ℂ) (f := initialDensity)).symm
      _ = _ := by simpa only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one] using h
  have hr := congrArg Complex.re hm
  norm_num at hr
  exact hr

/-- The only nonconstant raw moment is `1/20`, with the Gram conjugation convention. -/
theorem initialScalar_moment (i : Fin 1) : initialScalar.moment i = (1 / 20 : ℂ) := by
  change inner ℂ (initialScalar.vector initialMode) (initialScalar.vector 0) = _
  rw [TorusWeight.vector_inner]
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one,
    Complex.star_def, ← UnitAddTorus.mFourier_neg]
  have hn : -initialMode + -initialMode ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [initialMode] at h0
  have h := initial_fourier_moment (-initialMode)
  change (∫ x, (initialDensity x : ℂ) * UnitAddTorus.mFourier (-initialMode) x ∂torusMeasure 1) = _
  simpa [initialMode_ne_zero, hn] using h

/-- The two equal diagonal entries and the two equal off-diagonal entries. -/
def initialGram (a b : ℂ) : Matrix (Unit ⊕ Fin 1) (Unit ⊕ Fin 1) ℂ :=
  fun i j => if i = j then a else b

theorem initialScalar_rawGram : initialScalar.rawGram = initialGram (9 / 10) (1 / 20) := by
  rw [initialScalar.rawGram_fromBlocks]
  ext (i | i) (j | j)
  · cases i; cases j
    simp [initialGram, initialScalar_mass]
  · cases i
    simp [initialGram, initialScalar_moment]
  · cases j
    simp [initialGram, initialScalar_moment]
  · have hij : i = j := Subsingleton.elim _ _
    subst j
    simpa [initialGram, ScalarData.nonconstantGram, initialScalar_mass] using
      initialScalar.rawGram_diagonal (Sum.inr i)

theorem initialGram_inverse : (initialGram (9 / 10) (1 / 20))⁻¹ =
    initialGram (360 / 323) (-20 / 323) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [initialGram, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_one,
    Matrix.one_apply, Sum.inl_ne_inr, Sum.inr_ne_inl]

theorem initialScalar_inverse : initialScalar.rawGram⁻¹ = initialGram (360 / 323) (-20 / 323) := by
  rw [initialScalar_rawGram, initialGram_inverse]

theorem initialScalar_gain : initialScalar.gain = 1 / 323 := by
  have h := initialScalar.rawGram_inverse_constant_gain
  rw [initialScalar_inverse, initialScalar_mass] at h
  have hr := congrArg Complex.re h
  change (initialGram (360 / 323) (-20 / 323) (Sum.inl ()) (Sum.inl ())).re =
    (1 + initialScalar.gain) / (9 / 10) at hr
  norm_num [initialGram] at hr
  linarith

theorem initialScalar_inverse_diagonal (i : Unit ⊕ Fin 1) :
    initialScalar.rawGram⁻¹ i i = (360 / 323 : ℂ) := by
  rw [initialScalar_inverse]
  simp [initialGram]

theorem torus_character_neg_apply {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (-x) = star (UnitAddTorus.mFourier k x) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply,
    smul_neg, fourier_neg', Complex.star_def, map_prod]

theorem initialScalar_even : initialScalar.IsEven := by
  intro x
  change initialDensity (-x) = initialDensity x
  simp [initialDensity, torus_character_neg_apply]

theorem initialScalar_floor : initialScalar.HasPositiveFloor :=
  ⟨4 / 5, by norm_num, fun x => (initialDensity_bounds x).1⟩

/-- The intrinsic torus definition is the cosine density in real coordinates. -/
theorem initialDensity_on_line (x : ℝ) :
    initialDensity (fun _ => (x : UnitAddCircle)) = 9 / 10 + (1 / 10) * Real.cos (2 * Real.pi * x) := by
  simp only [initialDensity, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_one, initialMode]
  rw [fourier_coe_apply]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

/-- The antisymmetric coordinate vector realizes the larger inverse eigenvalue. -/
def initialMinus : EuclideanSpace ℂ (Unit ⊕ Fin 1) :=
  WithLp.toLp 2 (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1))

theorem initialMinus_ne_zero : initialMinus ≠ 0 := by
  intro h
  have hi := congrArg (fun x : EuclideanSpace ℂ (Unit ⊕ Fin 1) => x (Sum.inl ())) h
  norm_num [initialMinus] at hi

theorem initialGram_apply_minus (a b : ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin 1)) (initialGram a b) initialMinus =
      (a - b) • initialMinus := by
  apply (WithLp.equiv 2 ((Unit ⊕ Fin 1) → ℂ)).injective
  change WithLp.ofLp ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin 1))
    (initialGram a b) initialMinus) = _
  rw [Matrix.ofLp_toEuclideanCLM]
  ext i
  fin_cases i
  all_goals simp [initialMinus, Matrix.mulVec, dotProduct, initialGram, Fintype.sum_sum_type,
    Sum.inl_ne_inr, Sum.inr_ne_inl, sub_eq_add_neg]

theorem initialScalar_inverse_norm :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin 1)) initialScalar.rawGram⁻¹‖ = 20 / 17 := by
  apply le_antisymm
  · apply positive_matrix_norm_le initialScalar.rawGram_posDef.inv.posSemidef (by norm_num)
    rw [initialScalar_inverse]
    have he : (20 / 17 : ℂ) • (1 : Matrix (Unit ⊕ Fin 1) (Unit ⊕ Fin 1) ℂ) -
        initialGram (360 / 323) (-20 / 323) =
        (20 / 323 : ℂ) • Matrix.gram ℂ (fun _ : Unit ⊕ Fin 1 => (1 : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        norm_num [initialGram, Matrix.gram_apply, Matrix.sub_apply, Matrix.smul_apply]
      · norm_num [initialGram, Matrix.gram_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, hij]
    push_cast
    rw [he]
    exact (Matrix.posSemidef_gram ℂ (fun _ : Unit ⊕ Fin 1 => (1 : ℂ))).smul (by
      apply RCLike.nonneg_iff.mpr
      constructor <;> norm_num [Complex.div_re, Complex.div_im])
  · let T := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin 1)) initialScalar.rawGram⁻¹
    have hv : T initialMinus = (20 / 17 : ℂ) • initialMinus := by
      dsimp [T]
      rw [initialScalar_inverse, initialGram_apply_minus]
      norm_num
    have h := T.le_opNorm initialMinus
    rw [hv, norm_smul] at h
    norm_num at h
    exact le_of_mul_le_mul_right h (norm_pos_iff.mpr initialMinus_ne_zero)

/-- The exact lower eigenvalue bound in the raw coefficient metric. -/
theorem initialScalar_gram_floor :
    (initialScalar.rawGram - (17 / 20 : ℂ) • (1 : Matrix (Unit ⊕ Fin 1) (Unit ⊕ Fin 1) ℂ)).PosSemidef := by
  rw [initialScalar_rawGram]
  have he : initialGram (9 / 10) (1 / 20) -
      (17 / 20 : ℂ) • (1 : Matrix (Unit ⊕ Fin 1) (Unit ⊕ Fin 1) ℂ) =
      (1 / 20 : ℂ) • Matrix.gram ℂ (fun _ : Unit ⊕ Fin 1 => (1 : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      norm_num [initialGram, Matrix.gram_apply, Matrix.sub_apply, Matrix.smul_apply]
    · norm_num [initialGram, Matrix.gram_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, hij]
  rw [he]
  exact (Matrix.posSemidef_gram ℂ (fun _ : Unit ⊕ Fin 1 => (1 : ℂ))).smul (by
    apply RCLike.nonneg_iff.mpr
    constructor <;> norm_num [Complex.div_re, Complex.div_im])

theorem initialScalar_centered_prefix_iff (q : ℝ) :
    initialScalar.CenteredPrefixSqBound q ↔ 1 ≤ q :=
  single_prefixSqBound_iff initialScalar.centeredVector
    (initialScalar.centeredVectors_linearIndependent.ne_zero 0) q

/-- All numerical and prefix invariants of the actual initial scalar block. -/
theorem initial_scalar_block :
    1 - initialScalar.mass = 1 / 10 ∧ initialScalar.gain = 1 / 323 ∧
      (∀ i : Fin 1, (initialScalar.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 = 37 / 323 ∧
        (initialScalar.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 ≤ 2 * (1 - initialScalar.mass)) ∧
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin 1)) initialScalar.rawGram⁻¹‖ = 20 / 17 ∧
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin 1)) initialScalar.rawGram⁻¹‖ <
        ((1 - initialScalar.mass)⁻¹) ^ 2 ∧ initialScalar.CenteredPrefixSqBound 1 := by
  refine ⟨?_, initialScalar_gain, ?_, initialScalar_inverse_norm, ?_, ?_⟩
  · rw [initialScalar_mass]
    norm_num
  · intro i
    rw [initialScalar_inverse_diagonal, initialScalar_mass]
    norm_num
  · rw [initialScalar_inverse_norm, initialScalar_mass]
    norm_num
  · exact (initialScalar_centered_prefix_iff 1).mpr le_rfl

end SchauderTranslates
