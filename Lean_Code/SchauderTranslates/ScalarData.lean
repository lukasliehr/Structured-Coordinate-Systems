import Lean_Code.SchauderTranslates.TorusTransfer
import Lean_Code.SchauderTranslates.HilbertSynthesis

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A scalar density on a finite probability torus. A positive lower bound, when needed,
is an additional property; it is not confused with mere pointwise positivity. -/
structure TorusWeight (d : ℕ) where
  density : UnitAddTorus (Fin d) → ℝ
  measurable : Measurable density
  positive : ∀ x, 0 < density x
  le_one : ∀ x, density x ≤ 1

/-- The ordered nonconstant characters of a scalar block. -/
structure ScalarData (d n : ℕ) extends TorusWeight d where
  frequencies : Fin n → (Fin d → ℤ)
  injective : Function.Injective frequencies
  nonconstant : ∀ i, frequencies i ≠ 0

instance torusMeasure_openPos (d : ℕ) : (torusMeasure d).IsOpenPosMeasure := by
  rw [torusMeasure_eq_volume]
  infer_instance

@[simp] theorem torus_character_norm {d : ℕ} (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply, norm_prod]

namespace TorusWeight
variable {d : ℕ}

def mass (w : TorusWeight d) : ℝ := ∫ x, w.density x ∂torusMeasure d

theorem integrable (w : TorusWeight d) : Integrable w.density (torusMeasure d) :=
  Integrable.of_bound w.measurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (w.positive x)]
      exact w.le_one x))

theorem mass_pos (w : TorusWeight d) : 0 < w.mass := by
  rw [mass, integral_pos_iff_support_of_nonneg (fun x => (w.positive x).le) w.integrable]
  have hs : Function.support w.density = Set.univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (w.positive x)]
  simp [hs]

theorem mass_le_one (w : TorusWeight d) : w.mass ≤ 1 := by
  have h := integral_mono w.integrable (integrable_const (1 : ℝ)) w.le_one
  simpa [mass] using h

/-- Haar-space vectors representing the raw weighted Gram. -/
def vectorFn (w : TorusWeight d) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) : ℂ :=
  (Real.sqrt (w.density x) : ℂ) * UnitAddTorus.mFourier k x

theorem vectorFn_norm (w : TorusWeight d) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    ‖w.vectorFn k x‖ = Real.sqrt (w.density x) := by
  simp [vectorFn, Real.sqrt_nonneg]

theorem vectorFn_memLp (w : TorusWeight d) (k : Fin d → ℤ) :
    MemLp (w.vectorFn k) 2 (torusMeasure d) := by
  apply MemLp.of_bound (C := 1)
  · exact (Complex.continuous_ofReal.measurable.comp w.measurable.sqrt).aestronglyMeasurable.mul
      (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable
  · filter_upwards [] with x
    rw [vectorFn_norm]
    exact Real.sqrt_le_one.mpr (w.le_one x)

def vector (w : TorusWeight d) (k : Fin d → ℤ) :
    Lp ℂ 2 (torusMeasure d : Measure (UnitAddTorus (Fin d))) :=
  (w.vectorFn_memLp k).toLp (w.vectorFn k)

theorem vector_ae (w : TorusWeight d) (k : Fin d → ℤ) :
    (w.vector k : UnitAddTorus (Fin d) → ℂ) =ᵐ[torusMeasure d] w.vectorFn k :=
  (w.vectorFn_memLp k).coeFn_toLp

theorem vector_inner (w : TorusWeight d) (k l : Fin d → ℤ) :
    inner ℂ (w.vector k) (w.vector l) =
      ∫ x, (w.density x : ℂ) * star (UnitAddTorus.mFourier k x) * UnitAddTorus.mFourier l x ∂torusMeasure d := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.vector_ae k, w.vector_ae l] with x hk hl
  rw [hk, hl]
  simp only [vectorFn, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  change ((Real.sqrt (w.density x) : ℂ) * UnitAddTorus.mFourier l x) *
    ((Real.sqrt (w.density x) : ℂ) * star (UnitAddTorus.mFourier k x)) = _
  have hs : (Real.sqrt (w.density x) : ℂ) ^ 2 = (w.density x : ℂ) := by
    exact_mod_cast Real.sq_sqrt (w.positive x).le
  calc
    _ = (Real.sqrt (w.density x) : ℂ) ^ 2 *
        star (UnitAddTorus.mFourier k x) * UnitAddTorus.mFourier l x := by ring
    _ = _ := by rw [hs]

@[simp] theorem vector_norm_sq (w : TorusWeight d) (k : Fin d → ℤ) :
    ‖w.vector k‖ ^ 2 = w.mass := by
  have h : inner ℂ (w.vector k) (w.vector k) = (w.mass : ℂ) := by
    rw [vector_inner]
    calc
      _ = ∫ x, (w.density x : ℂ) ∂torusMeasure d := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hk : star (UnitAddTorus.mFourier k x) * UnitAddTorus.mFourier k x = 1 := by
          rw [Complex.star_def]
          simpa only [torus_character_norm, Complex.ofReal_one, one_pow] using
            Complex.conj_mul' (UnitAddTorus.mFourier k x)
        calc
          _ = (w.density x : ℂ) *
              (star (UnitAddTorus.mFourier k x) * UnitAddTorus.mFourier k x) := by ring
          _ = _ := by rw [hk, mul_one]
      _ = (w.mass : ℂ) := integral_ofReal (𝕜 := ℂ) (f := w.density)
  have hr := congrArg Complex.re h
  change RCLike.re (inner ℂ (w.vector k) (w.vector k)) = w.mass at hr
  simpa only [inner_self_eq_norm_sq] using hr

/-- Finite synthesis has the common square-root density factor pointwise almost everywhere. -/
theorem vector_sum_ae {ι : Type*} (w : TorusWeight d) (μ : ι → (Fin d → ℤ))
    (s : Finset ι) (c : ι → ℂ) :
    ((∑ i ∈ s, c i • w.vector (μ i) : Lp ℂ 2 (torusMeasure d : Measure (UnitAddTorus (Fin d)))) :
        UnitAddTorus (Fin d) → ℂ) =ᵐ[torusMeasure d]
      (fun x => (Real.sqrt (w.density x) : ℂ) * ∑ i ∈ s, c i * UnitAddTorus.mFourier (μ i) x) := by
  classical
  have h (i : ι) : (c i • w.vector (μ i) : Lp ℂ 2 (torusMeasure d : Measure (UnitAddTorus (Fin d)))) =ᵐ[torusMeasure d]
      (fun x => c i * w.vectorFn (μ i) x) := by
    filter_upwards [Lp.coeFn_smul (c i) (w.vector (μ i)), w.vector_ae (μ i)] with x hs hv
    simp only [hs, hv, smul_eq_mul, Pi.smul_apply]
  have hall := s.eventually_all.mpr (fun i _ => h i)
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => c i • w.vector (μ i)), hall] with x hx hi
  rw [hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i his
  rw [hi i his]
  simp only [vectorFn]
  ring

/-- Positive multiplication preserves independence of every finite torus character list. -/
theorem vectors_linearIndependent {ι : Type*} (w : TorusWeight d) (μ : ι → (Fin d → ℤ))
    (hμ : Function.Injective μ) : LinearIndependent ℂ (fun i => w.vector (μ i)) := by
  classical
  let L : C(UnitAddTorus (Fin d), ℂ) →ₗ[ℂ]
      Lp ℂ 2 (torusMeasure d : Measure (UnitAddTorus (Fin d))) :=
    (ContinuousMap.toLp (E := ℂ) 2 (torusMeasure d) ℂ).toLinearMap
  have hli : LinearIndependent ℂ (fun i => UnitAddTorus.mFourierLp (d := Fin d) 2 (μ i)) :=
    (UnitAddTorus.orthonormal_mFourier (d := Fin d)).linearIndependent.comp μ hμ
  have hcont : LinearIndependent ℂ (fun i => UnitAddTorus.mFourier (μ i)) := by
    apply LinearIndependent.of_comp (v := fun i => UnitAddTorus.mFourier (μ i)) L
    simpa only [L, Function.comp_def, ContinuousLinearMap.coe_coe, UnitAddTorus.mFourierLp, torusMeasure] using! hli
  rw [linearIndependent_iff']
  intro s c hc
  have hp : (fun x => (Real.sqrt (w.density x) : ℂ) *
      ∑ i ∈ s, c i * UnitAddTorus.mFourier (μ i) x) =ᵐ[torusMeasure d] 0 := by
    have h := (w.vector_sum_ae μ s c).symm
    rw [hc] at h
    exact h.trans (Lp.coeFn_zero ℂ 2 (torusMeasure d))
  have hz : (fun x => ∑ i ∈ s, c i * UnitAddTorus.mFourier (μ i) x) =ᵐ[torusMeasure d] 0 := by
    filter_upwards [hp] with x hx
    have hs : (Real.sqrt (w.density x) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (w.positive x)).ne'
    exact (mul_eq_zero.mp hx).resolve_left hs
  have he : (∑ i ∈ s, c i • UnitAddTorus.mFourier (μ i) : C(UnitAddTorus (Fin d), ℂ)) = 0 := by
    have hf := Measure.eq_of_ae_eq hz (by fun_prop) continuous_const
    ext x
    simpa using congrFun hf x
  exact linearIndependent_iff'.mp hcont s c he

end TorusWeight

namespace ScalarData
variable {d n : ℕ}

/-- The constant is the left summand and precedes all entries of the given finite list. -/
def augmentedFrequency (s : ScalarData d n) : Unit ⊕ Fin n → (Fin d → ℤ) :=
  Sum.elim (fun _ => 0) s.frequencies

theorem augmentedFrequency_injective (s : ScalarData d n) :
    Function.Injective s.augmentedFrequency := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · exact False.elim (s.nonconstant b h.symm)
  · exact False.elim (s.nonconstant a h)
  · exact congrArg Sum.inr (s.injective h)

def rawGram (s : ScalarData d n) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ :=
  Matrix.gram ℂ (fun i => s.toTorusWeight.vector (s.augmentedFrequency i))

theorem rawGram_posDef (s : ScalarData d n) : s.rawGram.PosDef :=
  Matrix.posDef_gram_iff_linearIndependent.mpr
    (s.toTorusWeight.vectors_linearIndependent s.augmentedFrequency s.augmentedFrequency_injective)

theorem rawGram_diagonal (s : ScalarData d n) (i : Unit ⊕ Fin n) :
    s.rawGram i i = (s.mass : ℂ) := by
  change inner ℂ (s.vector (s.augmentedFrequency i)) (s.vector (s.augmentedFrequency i)) = _
  calc
    _ = (‖s.vector (s.augmentedFrequency i)‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
    _ = (s.mass : ℂ) := by exact_mod_cast s.toTorusWeight.vector_norm_sq (s.augmentedFrequency i)

def moment (s : ScalarData d n) : Fin n → ℂ := fun i => s.rawGram (Sum.inr i) (Sum.inl ())

def nonconstantGram (s : ScalarData d n) : Matrix (Fin n) (Fin n) ℂ :=
  s.rawGram.submatrix Sum.inr Sum.inr

def rawCenteredGram (s : ScalarData d n) : Matrix (Fin n) (Fin n) ℂ :=
  s.nonconstantGram - (s.mass : ℂ)⁻¹ • Matrix.vecMulVec s.moment (star s.moment)

def centeredGram (s : ScalarData d n) : Matrix (Fin n) (Fin n) ℂ :=
  (s.mass : ℂ)⁻¹ • s.rawCenteredGram

def mean (s : ScalarData d n) : Fin n → ℂ := (s.mass : ℂ)⁻¹ • s.moment

def gain (s : ScalarData d n) : ℝ :=
  (star s.mean ⬝ᵥ s.centeredGram⁻¹ *ᵥ s.mean).re

def IsEven (s : ScalarData d n) : Prop := ∀ x, s.density (-x) = s.density x

def HasPositiveFloor (s : ScalarData d n) : Prop := ∃ b : ℝ, 0 < b ∧ ∀ x, b ≤ s.density x

/-- A finite complex Fourier expansion of a real-valued scalar density. -/
def IsPolynomial (s : ScalarData d n) : Prop :=
  ∃ (K : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
    ∀ x, (s.density x : ℂ) = ∑ k ∈ K, c k * UnitAddTorus.mFourier k x

theorem rawGram_fromBlocks (s : ScalarData d n) :
    s.rawGram = Matrix.fromBlocks (fun _ _ : Unit => (s.mass : ℂ))
      (fun (_ : Unit) j => star (s.moment j)) (fun i (_ : Unit) => s.moment i)
      s.nonconstantGram := by
  ext (i | i) (j | j)
  · cases i; cases j
    exact s.rawGram_diagonal (Sum.inl ())
  · cases i
    exact (s.rawGram_posDef.isHermitian.apply (Sum.inl ()) (Sum.inr j)).symm
  · cases j
    rfl
  · rfl

/-- Subtract the actual expectation of each character. `moment` is its conjugate Gram column. -/
def centeredVector (s : ScalarData d n) (i : Fin n) :
    Lp ℂ 2 (torusMeasure d) :=
  s.vector (s.frequencies i) - ((s.mass : ℂ)⁻¹ * star (s.moment i)) • s.vector 0

theorem centeredVector_gram (s : ScalarData d n) :
    Matrix.gram ℂ s.centeredVector = s.rawCenteredGram := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  have h00 : inner ℂ (s.vector 0) (s.vector 0) = (s.mass : ℂ) :=
    s.rawGram_diagonal (Sum.inl ())
  have hi0 (i : Fin n) : inner ℂ (s.vector (s.frequencies i)) (s.vector 0) = s.moment i := rfl
  have h0i (i : Fin n) : inner ℂ (s.vector 0) (s.vector (s.frequencies i)) = star (s.moment i) :=
    (s.rawGram_posDef.isHermitian.apply (Sum.inl ()) (Sum.inr i)).symm
  ext i j
  simp only [Matrix.gram_apply, centeredVector, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, hi0, h0i, h00, rawCenteredGram,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  change _ = inner ℂ (s.vector (s.frequencies i)) (s.vector (s.frequencies j)) - _
  simp only [Complex.star_def, Complex.conj_ofReal, map_mul,
    map_inv₀, Complex.conj_conj]
  field_simp
  ring

theorem centeredVectors_linearIndependent (s : ScalarData d n) :
    LinearIndependent ℂ s.centeredVector := by
  let v := fun i => s.vector (s.augmentedFrequency i)
  let c : Unit ⊕ Fin n → ℂ := Sum.elim (fun _ => 0)
    (fun i => -((s.mass : ℂ)⁻¹ * star (s.moment i)))
  have hc : c (Sum.inl ()) = 0 := rfl
  have hv : LinearIndependent ℂ v :=
    s.toTorusWeight.vectors_linearIndependent s.augmentedFrequency s.augmentedFrequency_injective
  have hl := (linearIndependent_add_smul_iff (v := v) hc).mpr hv
  have hr := hl.comp Sum.inr Sum.inr_injective
  simpa only [Function.comp_def, Pi.add_apply, c, v, augmentedFrequency,
    Sum.elim_inr, Sum.elim_inl, neg_smul, ← sub_eq_add_neg, centeredVector] using! hr

theorem rawCenteredGram_posDef (s : ScalarData d n) : s.rawCenteredGram.PosDef := by
  rw [← s.centeredVector_gram]
  exact Matrix.posDef_gram_iff_linearIndependent.mpr s.centeredVectors_linearIndependent

theorem centeredGram_posDef (s : ScalarData d n) : s.centeredGram.PosDef := by
  unfold centeredGram
  apply s.rawCenteredGram_posDef.smul
  rw [← Complex.ofReal_inv]
  exact_mod_cast inv_pos.mpr s.toTorusWeight.mass_pos

end ScalarData
end SchauderTranslates
