import Lean_Code.SchauderTranslates.ScalarHilbertModel
import Lean_Code.SchauderTranslates.ScalarProducts
import Lean_Code.SchauderTranslates.IndependentCopies

noncomputable section
open Matrix ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Orthogonal-copy inner products, for the constant family of centered coefficient spaces. -/
theorem piLp_single_inner {L n : ℕ} (i j : Fin L) (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (PiLp.single 2 i x : PiLp 2 (fun _ : Fin L => EuclideanSpace ℂ (Fin n)))
      (PiLp.single 2 j y) = if i = j then inner ℂ x y else 0 := by
  rw [PiLp.inner_apply]
  by_cases hij : i = j
  · subst j
    simp [PiLp.single, -PiLp.toLp_single, Pi.single_apply, apply_ite₂]
  · simp only [hij, if_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · subst k
      simp [PiLp.single, -PiLp.toLp_single, hij]
    · simp [PiLp.single, -PiLp.toLp_single, hk]

namespace ScalarData
variable {d n : ℕ}

/-- The constant followed by copies of the scalar list, in copy-major order. -/
def copyHilbertModel (s : ScalarData d n) (L : ℕ) :
    Unit ⊕ Fin (L * n) → WithLp 2 (ℂ × PiLp 2 (fun _ : Fin L => EuclideanSpace ℂ (Fin n))) :=
  Sum.elim (fun _ => WithLp.toLp 2 (1, 0))
    (fun q => WithLp.toLp 2 (star (s.mean (finProdFinEquiv.symm q).2),
      PiLp.single 2 (finProdFinEquiv.symm q).1
        (metricColumn s.centeredGram (finProdFinEquiv.symm q).2)))

/-- The copy model realizes the exact normalized Gram of the independent product density. -/
theorem copyHilbertModel_gram (s : ScalarData d n) (L : ℕ) :
    Matrix.gram ℂ (s.copyHilbertModel L) = ((s.product L).mass : ℂ)⁻¹ • (s.product L).rawGram := by
  rw [← (s.product L).hilbertModel_gram]
  ext (u | q) (v | r)
  · cases u; cases v
    simp [Matrix.gram_apply, copyHilbertModel, hilbertModel]
  · cases u
    obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective r
    simp only [Matrix.gram_apply, copyHilbertModel, hilbertModel, Sum.elim_inl, Sum.elim_inr,
      Equiv.symm_apply_apply, WithLp.prod_inner_apply]
    simp only [product_mean]
    simp
  · cases v
    obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective q
    simp only [Matrix.gram_apply, copyHilbertModel, hilbertModel, Sum.elim_inl, Sum.elim_inr,
      Equiv.symm_apply_apply, WithLp.prod_inner_apply]
    simp only [product_mean]
    simp
  · obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective q
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective r
    simp only [Matrix.gram_apply, copyHilbertModel, hilbertModel, Sum.elim_inr,
      Equiv.symm_apply_apply, WithLp.prod_inner_apply]
    change inner ℂ (star (s.mean a)) (star (s.mean b)) +
        inner ℂ (PiLp.single 2 i (metricColumn s.centeredGram a) :
          PiLp 2 (fun _ : Fin L => EuclideanSpace ℂ (Fin n)))
          (PiLp.single 2 j (metricColumn s.centeredGram b)) = _
    rw [piLp_single_inner, metricColumn_inner s.centeredGram_posDef.posSemidef,
      metricColumn_inner (s.product L).centeredGram_posDef.posSemidef]
    simp only [product_mean, product_centeredGram_entry]

/-- The individual and total mean budgets for independent copies. -/
theorem meanFunctional_comp_adjoint_norm (s : ScalarData d n) :
    ‖s.meanFunctional.comp (s.meanFunctional†)‖ = s.gain := by
  have h := norm_adjoint_comp_self (s.meanFunctional†)
  rw [adjoint_adjoint] at h
  simpa only [LinearIsometryEquiv.norm_map, ← pow_two, s.meanFunctional_norm_sq] using h

theorem copy_mean_budget (s : ScalarData d n) (L : ℕ) :
    ‖∑ _ : Fin L, s.meanFunctional.comp (s.meanFunctional†)‖ ≤ L * s.gain := by
  calc
    _ ≤ ∑ _ : Fin L, ‖s.meanFunctional.comp (s.meanFunctional†)‖ := norm_sum_le _ _
    _ = _ := by simp [s.meanFunctional_comp_adjoint_norm]

end ScalarData
end SchauderTranslates
