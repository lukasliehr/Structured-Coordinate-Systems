import Lean_Code.SchauderTranslates.Characters

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction

theorem integrable_mul_character {h : ℝ → ℂ} (hh : Integrable h) (ξ : ℝ) :
    Integrable (fun t => h t * character ξ t) :=
  hh.mul_bdd (continuous_character ξ).aestronglyMeasurable
    (Eventually.of_forall (fun t => (norm_character ξ t).le))

theorem character_rescale (s t : ℝ) :
    character (s / (2 * Real.pi)) t = Complex.exp (s * t * Complex.I) := by
  unfold character
  congr 1
  push_cast
  field_simp

theorem charFun_density (f : ℝ → ℝ) (hf : Integrable f) (hn : ∀ t, 0 ≤ f t) (s : ℝ) :
    charFun (volume.withDensity (fun t => ENNReal.ofReal (f t))) s =
      ∫ t, (f t : ℂ) * character (s / (2 * Real.pi)) t := by
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul₀
    hf.1.aemeasurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with t
  rw [ENNReal.toReal_ofReal (hn t), Complex.real_smul, character_rescale]

/-- Equality of all Fourier moments determines a nonnegative integrable density. -/
theorem nonneg_l1_character_unique (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (hfn : ∀ t, 0 ≤ f t) (hgn : ∀ t, 0 ≤ g t)
    (he : ∀ ξ : ℝ, (∫ t, (f t : ℂ) * character ξ t) =
      ∫ t, (g t : ℂ) * character ξ t) : f =ᵐ[volume] g := by
  let μ := volume.withDensity (fun t => ENNReal.ofReal (f t))
  let ν := volume.withDensity (fun t => ENNReal.ofReal (g t))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hf.1 (Eventually.of_forall hfn)).mpr hf)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hg.1 (Eventually.of_forall hgn)).mpr hg)
  have hm : μ = ν := by
    apply Measure.ext_of_charFun
    funext s
    exact (charFun_density f hf hfn s).trans ((he _).trans (charFun_density g hg hgn s).symm)
  have ha := (withDensity_eq_iff_of_sigmaFinite
    hf.1.aemeasurable.ennreal_ofReal hg.1.aemeasurable.ennreal_ofReal).mp hm
  filter_upwards [ha] with t ht
  exact (ENNReal.ofReal_eq_ofReal_iff (hfn t) (hgn t)).mp ht

/-- Real L¹ Fourier uniqueness, with all frequencies quantified (either sign is equivalent). -/
theorem real_l1_fourier_unique (h : ℝ → ℝ) (hh : Integrable h)
    (hz : ∀ ξ : ℝ, (∫ t, (h t : ℂ) * character ξ t) = 0) : h =ᵐ[volume] 0 := by
  let f (t : ℝ) := max (h t) 0
  let g (t : ℝ) := max (-h t) 0
  have hf : Integrable f := hh.pos_part
  have hg : Integrable g := hh.neg.pos_part
  have hd (t : ℝ) : h t = f t - g t := by
    dsimp [f, g]
    simp only [max_def]
    split_ifs <;> linarith
  have he : f =ᵐ[volume] g := by
    apply nonneg_l1_character_unique f g hf hg (fun t => le_max_right _ _)
      (fun t => le_max_right _ _)
    intro ξ
    apply sub_eq_zero.mp
    rw [← integral_sub]
    · convert hz ξ using 1
      congr 1
      funext t
      rw [← sub_mul, ← Complex.ofReal_sub, ← hd]
    · exact integrable_mul_character hf.ofReal ξ
    · exact integrable_mul_character hg.ofReal ξ
  filter_upwards [he] with t ht
  simpa [ht] using hd t

@[simp] theorem conj_character (ξ t : ℝ) : conj (character ξ t) = character (-ξ) t := by
  simp [character, ← Complex.exp_conj, mul_assoc, map_ofNat]

/-- Conjugation reverses the frequency. -/
theorem integral_conj_mul_character (h : ℝ → ℂ) (ξ : ℝ) :
    (∫ t, conj (h t) * character ξ t) =
      conj (∫ t, h t * character (-ξ) t) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp

/-- Complex L¹ Fourier uniqueness; this proof does not assume any L² integrability. -/
theorem l1_fourier_unique (h : ℝ → ℂ) (hh : Integrable h)
    (hz : ∀ ξ : ℝ, (∫ t, h t * character ξ t) = 0) : h =ᵐ[volume] 0 := by
  have hc (ξ : ℝ) : (∫ t, conj (h t) * character ξ t) = 0 := by
    rw [integral_conj_mul_character, hz, map_zero]
  have hi (ξ : ℝ) := integrable_mul_character hh ξ
  have hconj : Integrable (fun t => conj (h t)) :=
    (RCLike.conjLIE.integrable_comp_iff).mpr hh
  have hci (ξ : ℝ) := integrable_mul_character hconj ξ
  have hr : (fun t => (h t).re) =ᵐ[volume] 0 := by
    apply real_l1_fourier_unique _ hh.re
    intro ξ
    change (∫ t, ((h t).re : ℂ) * character ξ t) = 0
    have he : (∫ t, ((h t).re : ℂ) * character ξ t) =
        (2 : ℂ)⁻¹ * ((∫ t, h t * character ξ t) +
          ∫ t, conj (h t) * character ξ t) := by
      rw [← integral_add (hi ξ) (hci ξ), ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [← add_mul, Complex.add_conj]
      push_cast
      ring
    rw [he, hz, hc]
    simp
  have him : (fun t => (h t).im) =ᵐ[volume] 0 := by
    apply real_l1_fourier_unique _ hh.im
    intro ξ
    change (∫ t, ((h t).im : ℂ) * character ξ t) = 0
    have he : (∫ t, ((h t).im : ℂ) * character ξ t) =
        (2 * Complex.I)⁻¹ * ((∫ t, h t * character ξ t) -
          ∫ t, conj (h t) * character ξ t) := by
      rw [← integral_sub (hi ξ) (hci ξ), ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [← sub_mul, Complex.sub_conj]
      push_cast
      field_simp
    rw [he, hz, hc]
    simp
  filter_upwards [hr, him] with t ht ht'
  exact Complex.ext ht ht'

end SchauderTranslates
