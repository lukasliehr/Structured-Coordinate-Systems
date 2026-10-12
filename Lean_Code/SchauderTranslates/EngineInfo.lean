import Lean_Code.SchauderTranslates.InformationResolvent
import Lean_Code.SchauderTranslates.TagKernel

/-!
# Quadratic form of the information operator

For atoms with slow means `T` and positive definite centered Gram `C`, the information
operator `J = T C⁻¹ T*` has quadratic form `a* C⁻¹ a` with `a = (⟪T_p, x⟫)_p`. Hence
Cauchy–Schwarz bounds every mean pairing by `⟪J x, x⟫` times the centered norm, and an
eigenvector of `J` is realized exactly by explicit coefficients. These are the only
properties of a selective engine used by the replica argument (`tag:engines`).
-/

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The source coefficients of a vector. -/
def sourceCoeff (v : ι → H) (x : H) : ι → ℂ := fun p => inner ℂ (v p) x

theorem informationOperator_apply (v : ι → H) (C : Matrix ι ι ℂ) (x : H) :
    informationOperator v C x = ∑ p, (C⁻¹ *ᵥ sourceCoeff v x) p • v p := by
  simp only [informationOperator, informationSandwich, ContinuousLinearMap.comp_apply,
    hilbertSynthesis_adjoint_apply, hilbertSynthesis_apply]
  apply Finset.sum_congr rfl
  intro p _
  congr 1

theorem informationOperator_inner (v : ι → H) {C : Matrix ι ι ℂ} (hC : C.PosDef) (x : H) :
    inner ℂ (informationOperator v C x) x =
      star (sourceCoeff v x) ⬝ᵥ C⁻¹ *ᵥ sourceCoeff v x := by
  rw [informationOperator_apply, sum_inner]
  have hH : (C⁻¹)ᴴ = C⁻¹ := hC.inv.isHermitian
  calc (∑ p, inner ℂ ((C⁻¹ *ᵥ sourceCoeff v x) p • v p) x) =
      star (C⁻¹ *ᵥ sourceCoeff v x) ⬝ᵥ sourceCoeff v x := by
        simp only [inner_smul_left, dotProduct, Pi.star_apply, sourceCoeff, Complex.star_def]
    _ = _ := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]

/-- Cauchy–Schwarz for mean pairings through the information operator. -/
theorem mean_pairing_le_information {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → H) (R : ι → E) (hR : (Matrix.gram ℂ R).PosDef) (x : H) (b : ι → ℂ) :
    ‖inner ℂ x (∑ p, b p • v p)‖ ^ 2 ≤
      (inner ℂ (informationOperator v (Matrix.gram ℂ R) x) x).re * ‖∑ p, b p • R p‖ ^ 2 := by
  rw [informationOperator_inner v hR]
  have h := gram_cauchy_schwarz R hR (sourceCoeff v x) b
  have he : inner ℂ x (∑ p, b p • v p) = star (sourceCoeff v x) ⬝ᵥ b := by
    simp only [inner_sum, inner_smul_right, dotProduct, Pi.star_apply, sourceCoeff]
    apply Finset.sum_congr rfl
    intro p _
    rw [← inner_conj_symm, Complex.star_def]
    ring
  rw [he]
  exact h

/-- An eigenvector of the information operator is realized by explicit coefficients whose
centered synthesis has squared norm equal to the eigenvalue (for a unit vector). -/
theorem information_eigen_witness {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → H) (R : ι → E) (hR : (Matrix.gram ℂ R).PosDef) (e : H) (j : ℝ)
    (he : informationOperator v (Matrix.gram ℂ R) e = (j : ℂ) • e) (he1 : ‖e‖ = 1) :
    ∃ b : ι → ℂ, ∑ p, b p • v p = (j : ℂ) • e ∧ ‖∑ p, b p • R p‖ ^ 2 = j := by
  set C := Matrix.gram ℂ R
  set b := C⁻¹ *ᵥ sourceCoeff v e
  refine ⟨b, ?_, ?_⟩
  · rw [← he, informationOperator_apply]
  · have hdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hR.isUnit
    have hq : ‖∑ p, b p • R p‖ ^ 2 = (star b ⬝ᵥ C *ᵥ b).re := by
      rw [Matrix.star_dotProduct_gram_mulVec]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    have hCb : C *ᵥ b = sourceCoeff v e := by
      simp only [b, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hJ := informationOperator_inner v hR e
    rw [he, inner_smul_left, inner_self_eq_norm_sq_to_K, he1] at hJ
    have hH : (C⁻¹)ᴴ = C⁻¹ := hR.inv.isHermitian
    have hsb : star b ⬝ᵥ C *ᵥ b = star (sourceCoeff v e) ⬝ᵥ C⁻¹ *ᵥ sourceCoeff v e := by
      rw [hCb]
      simp only [b]
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
    rw [hq, hsb, ← hJ]
    simp

/-- Projections in an information formula: the quadratic form of
`c P₁ + j P_e` is at most `c ‖x‖² + j |⟪e, x⟫|²` when `e` is a unit vector. -/
theorem selective_information_quadratic_le (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (e : H) (he1 : ‖e‖ = 1) {c j : ℝ} (hc : 0 ≤ c) (hj : 0 ≤ j) (x : H) :
    (inner ℂ (((c : ℂ) • P.starProjection + (j : ℂ) • (ℂ ∙ e).starProjection) x) x).re ≤
      c * ‖x‖ ^ 2 + j * ‖inner ℂ e x‖ ^ 2 := by
  have hmem : P.starProjection x ∈ P := by
    rw [Submodule.starProjection_apply]
    exact (P.orthogonalProjectionOnto x).2
  have hPP : P.starProjection (P.starProjection x) = P.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  have h1 : (inner ℂ (P.starProjection x) x).re = ‖P.starProjection x‖ ^ 2 := by
    have he : inner ℂ (P.starProjection x) x =
        inner ℂ (P.starProjection x) (P.starProjection x) := by
      calc inner ℂ (P.starProjection x) x =
          inner ℂ (P.starProjection (P.starProjection x)) x := by rw [hPP]
        _ = _ := Submodule.inner_starProjection_left_eq_right P _ _
    rw [he]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h2 : (ℂ ∙ e).starProjection x = inner ℂ e x • e := by
    rw [Submodule.starProjection_singleton, he1]
    simp
  have h3 : (inner ℂ ((ℂ ∙ e).starProjection x) x).re = ‖inner ℂ e x‖ ^ 2 := by
    rw [h2, inner_smul_left, Complex.conj_mul']
    norm_cast
  have hP : ‖P.starProjection x‖ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le P x
  simp only [_root_.add_apply, _root_.smul_apply, inner_add_left,
    inner_smul_left, Complex.add_re, Complex.conj_ofReal, Complex.re_ofReal_mul, h1, h3]
  have := pow_le_pow_left₀ (norm_nonneg _) hP 2
  nlinarith

/-- The distinguished unit vector is an eigenvector of `c P_{V ∩ e⊥} + j P_e`. -/
theorem selective_information_eigen (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (e : H) (c j : ℝ) [(V ⊓ (ℂ ∙ e)ᗮ).HasOrthogonalProjection] :
    ((c : ℂ) • (V ⊓ (ℂ ∙ e)ᗮ).starProjection + (j : ℂ) • (ℂ ∙ e).starProjection) e =
      (j : ℂ) • e := by
  have h1 : (V ⊓ (ℂ ∙ e)ᗮ).starProjection e = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
    intro y hy
    exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self e)
      (Submodule.mem_inf.mp hy).2
  have h2 : (ℂ ∙ e).starProjection e = e :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self e)
  simp [h1, h2]

end SchauderTranslates
