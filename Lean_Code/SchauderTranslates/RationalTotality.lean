import Lean_Code.SchauderTranslates.FourierUniqueness

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate InnerProductSpace

namespace SchauderTranslates
open Construction

theorem continuous_character_integral (h : ℝ → ℂ) (hh : Integrable h) :
    Continuous (fun ξ : ℝ => ∫ t, h t * character ξ t) := by
  apply continuous_of_dominated (bound := fun t => ‖h t‖)
  · exact fun ξ => (integrable_mul_character hh ξ).1
  · intro ξ
    filter_upwards with t
    simp only [norm_mul, norm_character, mul_one, le_refl]
  · exact hh.norm
  · filter_upwards with t
    unfold character
    fun_prop

def weightedDensity (w : Weight) (f : WeightedL2 w) (t : ℝ) : ℂ :=
  (ENNReal.ofReal (w.density t)).toReal • f t

theorem weightedDensity_integrable (w : Weight) (f : WeightedL2 w) :
    Integrable (weightedDensity w f) := by
  apply (integrable_withDensity_iff_integrable_smul'
    w.measurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp
  exact (Lp.memLp f).integrable (by norm_num)

theorem weightedCharacter_inner (w : Weight) (f : WeightedL2 w) (ξ : ℝ) :
    ⟪weightedCharacter w (-ξ), f⟫_ℂ = ∫ t, weightedDensity w f t * character ξ t := by
  rw [L2.inner_def]
  calc
    (∫ t, ⟪(weightedCharacter w (-ξ) : ℝ → ℂ) t, f t⟫_ℂ ∂w.measure) =
        ∫ t, f t * character ξ t ∂w.measure := by
      apply integral_congr_ae
      filter_upwards [weightedCharacter_ae w (-ξ)] with t ht
      simp [ht, RCLike.inner_apply]
    _ = ∫ t, weightedDensity w f t * character ξ t := by
      change (∫ t, f t * character ξ t ∂volume.withDensity
        (fun t => ENNReal.ofReal (w.density t))) = _
      rw [integral_withDensity_eq_integral_toReal_smul
        w.measurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards with t
      simp only [weightedDensity, Complex.real_smul, mul_assoc]

theorem eq_zero_of_rational_character_orthogonal (w : Weight) (f : WeightedL2 w)
    (hf : ∀ q : ℚ, ⟪weightedCharacter w (q : ℝ), f⟫_ℂ = 0) : f = 0 := by
  have hh := weightedDensity_integrable w f
  have hz : ∀ ξ : ℝ, (∫ t, weightedDensity w f t * character ξ t) = 0 := by
    intro ξ
    refine Rat.denseRange_cast.induction_on ξ
      (isClosed_eq (continuous_character_integral _ hh) continuous_const) ?_
    intro q
    have he := hf (-q)
    simpa only [Rat.cast_neg, weightedCharacter_inner] using he
  have ha := l1_fourier_unique _ hh hz
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply w.ae_iff.mpr
  filter_upwards [ha, w.positive] with t ht hp
  have hn : (ENNReal.ofReal (w.density t)).toReal ≠ 0 := by
    rw [ENNReal.toReal_ofReal hp.le]
    exact hp.ne'
  exact (smul_eq_zero.mp ht).resolve_left hn

/-- Rational characters are total for every positive integrable full-line density. -/
theorem rational_characters_total (w : Weight) :
    Dense (↑(Submodule.span ℂ (Set.range (fun q : ℚ => weightedCharacter w (q : ℝ)))) :
      Set (WeightedL2 w)) := by
  let K := Submodule.span ℂ (Set.range (fun q : ℚ => weightedCharacter w (q : ℝ)))
  have hk : Kᗮ = ⊥ := by
    apply le_antisymm
    · intro f hf
      apply (Submodule.mem_bot ℂ).mpr
      apply eq_zero_of_rational_character_orthogonal w f
      intro q
      exact K.inner_right_of_mem_orthogonal (Submodule.subset_span ⟨q, rfl⟩) hf
    · exact bot_le
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← K.orthogonal_orthogonal_eq_closure, hk, Submodule.bot_orthogonal_eq_top]

end SchauderTranslates
