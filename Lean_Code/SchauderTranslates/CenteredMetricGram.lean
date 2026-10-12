import Lean_Code.SchauderTranslates.CenteredProjection
import Lean_Code.SchauderTranslates.MetricColumns
import Lean_Code.SchauderTranslates.MarkedScalarGram
import Lean_Code.SchauderTranslates.RealComplexQuadratic
import Lean_Code.SchauderTranslates.ScaledGramBound

noncomputable section
open ContinuousLinearMap Matrix
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual orthogonal representatives of metric columns after removing one distinguished column. -/
def centeredMetricColumn (B : Matrix ι ι ℂ) (q₀ : ι) (i : {q : ι // q ≠ q₀}) :
    EuclideanSpace ℂ ι := (ℂ ∙ metricColumn B q₀)ᗮ.starProjection (metricColumn B i)

theorem centeredMetricColumn_gram (B : Matrix ι ι ℂ) (hB : B.PosDef) (q₀ : ι)
    (m : ℝ) (hm : 0 < m) (hmass : B q₀ q₀ = (m : ℂ)) :
    Matrix.gram ℂ (centeredMetricColumn B q₀) =
      (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram := by
  have hn : ‖metricColumn B q₀‖ ^ 2 = m := by
    have hh := congrArg Complex.re (metricColumn_inner hB.posSemidef q₀ q₀)
    rw [hmass] at hh
    change RCLike.re (inner ℂ (metricColumn B q₀) (metricColumn B q₀)) = m at hh
    simpa only [inner_self_eq_norm_sq] using hh
  ext i j
  rw [Matrix.gram_apply, centeredMetricColumn, centeredMetricColumn,
    orthogonal_centering_inner, hn, metricColumn_inner hB.posSemidef,
    metricColumn_inner hB.posSemidef, metricColumn_inner hB.posSemidef]
  have hstar : star (B (j : ι) q₀) = B q₀ j := hB.isHermitian.apply q₀ j
  simp only [markedScalarGram, FiniteScalarGram.rawCenteredGram, FiniteScalarGram.nonconstantGram,
    FiniteScalarGram.moment, Matrix.submatrix_apply, splitConstantEquiv_inr, splitConstantEquiv_inl,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    hstar, div_eq_mul_inv]
  ring

theorem metricColumn_diagonal_action {B : Matrix ι ι ℂ} (hB : B.PosDef)
    (δ : ι → ℂ) (i : ι) :
    gramConjugate B (Matrix.diagonal δ) (metricColumn B i) = δ i • metricColumn B i := by
  have hi : gramRootInv B (gramRoot B (EuclideanSpace.single i 1)) = EuclideanSpace.single i 1 :=
    congrArg (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => T _) (gramRoot_inv_mul hB)
  have hd : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (Matrix.diagonal δ)
      (EuclideanSpace.single i 1) = δ i • EuclideanSpace.single i 1 := by
    ext j
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, Pi.single_apply]
    split_ifs <;> simp_all
  simp only [gramConjugate, metricColumn, ContinuousLinearMap.comp_apply, hi, hd, map_smul]

/-- The exact raw centered Gram inherits every diagonal coefficient bound from the augmented Gram. -/
theorem markedScalarGram_centered_prefix (B : Matrix ι ι ℂ) (hB : B.PosDef) (q₀ : ι)
    (m : ℝ) (hm : 0 < m) (hmass : B q₀ q₀ = (m : ℂ)) (δ : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ‖gramConjugate B (Matrix.diagonal δ)‖ ^ 2 ≤ C) :
    ‖gramConjugate (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram
      (Matrix.diagonal (fun i : {q : ι // q ≠ q₀} => δ i))‖ ^ 2 ≤ C := by
  let P := gramConjugate B (Matrix.diagonal δ)
  let F := ℂ ∙ metricColumn B q₀
  have hF : ∀ x ∈ F, P x ∈ F := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, metricColumn_diagonal_action hB]
    exact F.smul_mem _ (F.smul_mem _ (Submodule.mem_span_singleton_self _))
  apply (gramConjugate_quadratic_bound_iff
    (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram_posDef _ hC).mpr
  intro c
  have h := centeredSynthesis_norm_sq_le P F hF (fun i : {q : ι // q ≠ q₀} => metricColumn B i)
    (fun i => δ i) c.ofLp (fun i => metricColumn_diagonal_action hB δ i)
  have hn (a : EuclideanSpace ℂ {q : ι // q ≠ q₀}) :
      ‖finiteSynthesis (centeredMetricColumn B q₀) a.ofLp‖ ^ 2 =
        coefficientQuadratic (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram a := by
    rw [synthesis_norm_sq, centeredMetricColumn_gram B hB q₀ m hm hmass]
    rfl
  have hmask : (fun i : {q : ι // q ≠ q₀} => δ i * c.ofLp i) = WithLp.ofLp
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := {q : ι // q ≠ q₀}))
        (Matrix.diagonal (fun i : {q : ι // q ≠ q₀} => δ i)) c) := by
    ext i
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  change ‖finiteSynthesis (centeredMetricColumn B q₀) (fun i => δ i * c.ofLp i)‖ ^ 2 ≤
    ‖P‖ ^ 2 * ‖finiteSynthesis (centeredMetricColumn B q₀) c.ofLp‖ ^ 2 at h
  rw [hmask, hn, hn] at h
  exact h.trans (mul_le_mul_of_nonneg_right hbound
    ((matrix_posSemidef_iff_quadratic (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram_posDef.isHermitian).mp
      (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram_posDef.posSemidef c))

/-- The same bound holds for the normalized centered Gram used in the scalar construction. -/
theorem markedScalarGram_normalized_prefix (B : Matrix ι ι ℂ) (hB : B.PosDef) (q₀ : ι)
    (m : ℝ) (hm : 0 < m) (hmass : B q₀ q₀ = (m : ℂ)) (δ : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ‖gramConjugate B (Matrix.diagonal δ)‖ ^ 2 ≤ C) :
    ‖gramConjugate (markedScalarGram B hB q₀ m hm hmass).centeredGram
      (Matrix.diagonal (fun i : {q : ι // q ≠ q₀} => δ i))‖ ^ 2 ≤ C := by
  have hraw := markedScalarGram_centered_prefix B hB q₀ m hm hmass δ hC hbound
  have h := gramConjugate_scaled_bound (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram_posDef
    (Matrix.diagonal (fun i : {q : ι // q ≠ q₀} => δ i)) (r := m⁻¹) (inv_pos.mpr hm) hC hraw
  simpa only [FiniteScalarGram.centeredGram, markedScalarGram, Complex.ofReal_inv] using h

end SchauderTranslates
