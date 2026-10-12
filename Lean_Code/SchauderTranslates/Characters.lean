import Lean_Code.SchauderTranslates.Contracts

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexOrder

namespace SchauderTranslates
open Construction

@[fun_prop] theorem continuous_character (ξ : ℝ) : Continuous (character ξ) := by
  unfold character
  fun_prop

@[simp] theorem norm_character (ξ t : ℝ) : ‖character ξ t‖ = 1 := by
  simp [character, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem character_add (ξ s t : ℝ) : character ξ (s + t) = character ξ s * character ξ t := by
  simp [character, mul_add, Complex.exp_add]

@[simp] theorem character_zero (ξ : ℝ) : character ξ 0 = 1 := by simp [character]

theorem hasDerivAt_character_zero (ξ : ℝ) :
    HasDerivAt (character ξ) (2 * Real.pi * Complex.I * ξ) 0 := by
  convert!
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul
      (2 * Real.pi * Complex.I * ξ)).cexp using 1
  simp

theorem character_injective : Function.Injective character := by
  intro ξ η he
  have hd := (hasDerivAt_character_zero ξ).unique (he ▸ hasDerivAt_character_zero η)
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  exact Complex.ofReal_injective (mul_left_cancel₀ hc hd)

def characterHom (ξ : ℝ) : Multiplicative ℝ →* ℂ where
  toFun t := character ξ t.toAdd
  map_one' := character_zero ξ
  map_mul' s t := character_add ξ s.toAdd t.toAdd

theorem characterHom_injective : Function.Injective characterHom := by
  intro ξ η h
  apply character_injective
  funext t
  exact DFunLike.congr_fun h (Multiplicative.ofAdd t)

/-- Dedekind independence avoids differentiation of arbitrary high order. -/
theorem characters_function_linearIndependent {ι : Type*} (ξ : ι → ℝ)
    (hξ : Function.Injective ξ) : LinearIndependent ℂ (fun i => character (ξ i)) := by
  exact (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    (fun i => characterHom (ξ i)) (characterHom_injective.comp hξ)

instance Construction.Weight.instIsFiniteMeasure (w : Weight) : IsFiniteMeasure w.measure :=
  isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable w.integrable.1
    (w.positive.mono (fun _ h => h.le))).mpr w.integrable)

theorem Construction.Weight.ae_iff (w : Weight) {p : ℝ → Prop} :
    (∀ᵐ t ∂w.measure, p t) ↔ ∀ᵐ t ∂volume, p t := by
  rw [Weight.measure, ae_withDensity_iff (w.measurable.ennreal_ofReal)]
  constructor
  · intro h
    filter_upwards [h, w.positive] with t ht hp
    exact ht (ENNReal.ofReal_ne_zero_iff.mpr hp)
  · intro h
    exact h.mono (fun _ ht _ => ht)

theorem character_memLp (w : Weight) (ξ : ℝ) : MemLp (character ξ) 2 w.measure :=
  (memLp_const (μ := w.measure) (p := 2) (1 : ℂ)).of_le
    (continuous_character ξ).aestronglyMeasurable
    (Eventually.of_forall (fun t => by simp))

def weightedCharacter (w : Weight) (ξ : ℝ) : WeightedL2 w :=
  (character_memLp w ξ).toLp (character ξ)

theorem weightedCharacter_ae (w : Weight) (ξ : ℝ) :
    (weightedCharacter w ξ : ℝ → ℂ) =ᵐ[w.measure] character ξ :=
  (character_memLp w ξ).coeFn_toLp

/-- The representative of a finite linear combination agrees a.e. with its polynomial. -/
theorem weightedCharacter_sum_ae {ι : Type*} (w : Weight) (ξ : ι → ℝ)
    (s : Finset ι) (c : ι → ℂ) :
    ((∑ i ∈ s, c i • weightedCharacter w (ξ i) : WeightedL2 w) : ℝ → ℂ) =ᵐ[w.measure]
      (fun t => ∑ i ∈ s, c i * character (ξ i) t) := by
  classical
  have h (i : ι) :
      (c i • weightedCharacter w (ξ i) : WeightedL2 w) =ᵐ[w.measure]
        (fun t => c i * character (ξ i) t) := by
    filter_upwards [Lp.coeFn_smul (c i) (weightedCharacter w (ξ i)),
      weightedCharacter_ae w (ξ i)] with t ht ht'
    simpa [ht', smul_eq_mul] using ht
  have ha := s.eventually_all.mpr (fun i _ => h i)
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => c i • weightedCharacter w (ξ i)), ha]
    with t ht hall
  exact ht.trans (Finset.sum_congr rfl (fun i hi => hall i hi))

/-- Distinct real characters are independent in the whole weighted L² space. -/
theorem characters_linearIndependent {ι : Type*} (w : Weight) (ξ : ι → ℝ)
    (hξ : Function.Injective ξ) :
    LinearIndependent ℂ (fun i => weightedCharacter w (ξ i)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc
  have he : (fun t => ∑ i ∈ s, c i * character (ξ i) t) =ᵐ[w.measure] 0 := by
    have hs := (weightedCharacter_sum_ae w ξ s c).symm
    rw [hc] at hs
    exact hs.trans (Lp.coeFn_zero ℂ 2 w.measure)
  have hf : (∑ i ∈ s, c i • character (ξ i) : ℝ → ℂ) = 0 := by
    have hf' := MeasureTheory.Measure.eq_of_ae_eq ((w.ae_iff).mp he)
      (by fun_prop) continuous_const
    ext t
    simpa using congrFun hf' t
  exact linearIndependent_iff'.mp (characters_function_linearIndependent ξ hξ) s c hf

theorem characters_gram_posDef {ι : Type*} [Finite ι]
    (w : Weight) (ξ : ι → ℝ) (hξ : Function.Injective ξ) :
    (Matrix.gram ℂ (fun i => weightedCharacter w (ξ i))).PosDef :=
  Matrix.posDef_gram_iff_linearIndependent.mpr (characters_linearIndependent w ξ hξ)

end SchauderTranslates
