import Lean_Code.SchauderTranslates.AugmentedScalarPrefixes
import Lean_Code.SchauderTranslates.CenteredMetricGram

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

def centeredMetric (s : ScalarData d n) (i : Fin n) : EuclideanSpace ℂ (Unit ⊕ Fin n) :=
  (ℂ ∙ metricColumn s.rawGram (Sum.inl ()))ᗮ.starProjection (metricColumn s.rawGram (Sum.inr i))

theorem centeredMetric_gram (s : ScalarData d n) : Matrix.gram ℂ s.centeredMetric = s.rawCenteredGram := by
  have hn : ‖metricColumn s.rawGram (Sum.inl ())‖ ^ 2 = s.mass := by
    have h := congrArg Complex.re (metricColumn_inner s.rawGram_posDef.posSemidef (Sum.inl ()) (Sum.inl ()))
    rw [s.rawGram_diagonal] at h
    change RCLike.re (inner ℂ (metricColumn s.rawGram (Sum.inl ())) (metricColumn s.rawGram (Sum.inl ()))) = s.mass at h
    simpa only [inner_self_eq_norm_sq] using h
  ext i j
  rw [Matrix.gram_apply, centeredMetric, centeredMetric, orthogonal_centering_inner, hn,
    metricColumn_inner s.rawGram_posDef.posSemidef,
    metricColumn_inner s.rawGram_posDef.posSemidef,
    metricColumn_inner s.rawGram_posDef.posSemidef]
  have hj := s.rawGram_posDef.isHermitian.apply (Sum.inl ()) (Sum.inr j)
  change star (s.rawGram (Sum.inr j) (Sum.inl ())) = s.rawGram (Sum.inl ()) (Sum.inr j) at hj
  rw [← hj]
  simp only [rawCenteredGram, nonconstantGram, ScalarData.moment, Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Removing the initial constant by orthogonal projection retains the augmented prefix constant. -/
theorem centered_prefix_of_augmented (s : ScalarData d n) {q : ℝ} (hq : 0 ≤ q)
    (hp : s.AugmentedPrefixSqBound q) : s.CenteredPrefixSqBound q := by
  rw [CenteredPrefixSqBound, finitePrefixSqBound_iff_gram s.centeredVector s.centeredVectors_linearIndependent hq,
    s.centeredVector_gram]
  intro k
  let δ : Unit ⊕ Fin n → ℂ := fun i => if (scalarRowEquiv n i).val < k + 1 then 1 else 0
  let P := gramConjugate s.rawGram (Matrix.diagonal δ)
  let F := ℂ ∙ metricColumn s.rawGram (Sum.inl ())
  have hF : ∀ x ∈ F, P x ∈ F := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, metricColumn_diagonal_action s.rawGram_posDef]
    exact F.smul_mem _ (F.smul_mem _ (Submodule.mem_span_singleton_self _))
  have hP : ‖P‖ ^ 2 ≤ q := (s.augmentedPrefixSqBound_iff_gram hq).mp hp (k + 1)
  apply (gramConjugate_quadratic_bound_iff s.rawCenteredGram_posDef (finitePrefixMatrix n k) hq).mpr
  intro c
  have h := centeredSynthesis_norm_sq_le P F hF (fun i : Fin n => metricColumn s.rawGram (Sum.inr i))
    (fun i => δ (Sum.inr i)) c.ofLp (fun i => metricColumn_diagonal_action s.rawGram_posDef δ (Sum.inr i))
  have hn (a : EuclideanSpace ℂ (Fin n)) :
      ‖finiteSynthesis s.centeredMetric a.ofLp‖ ^ 2 = coefficientQuadratic s.rawCenteredGram a := by
    rw [synthesis_norm_sq, s.centeredMetric_gram]
    rfl
  have hm : (fun i : Fin n => δ (Sum.inr i) * c.ofLp i) = WithLp.ofLp
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (finitePrefixMatrix n k) c) := by
    ext i
    simp [δ, scalarRowEquiv_nonconstant, finitePrefixMatrix, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  change ‖finiteSynthesis s.centeredMetric (fun i => δ (Sum.inr i) * c.ofLp i)‖ ^ 2 ≤
    ‖P‖ ^ 2 * ‖finiteSynthesis s.centeredMetric c.ofLp‖ ^ 2 at h
  rw [hm, hn, hn] at h
  exact h.trans (mul_le_mul_of_nonneg_right hP
    ((matrix_posSemidef_iff_quadratic s.rawCenteredGram_posDef.isHermitian).mp s.rawCenteredGram_posDef.posSemidef c))

end ScalarData
end SchauderTranslates
