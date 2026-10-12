import Lean_Code.SchauderTranslates.ScalarCopyCuts
import Lean_Code.SchauderTranslates.AugmentedScalarPrefixes
import Lean_Code.SchauderTranslates.ScalarRowNumerics

noncomputable section
open Matrix ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Copy-major flattening has the lexicographic order used by the concatenation estimate. -/
theorem finProdFinEquiv_lt_iff {L n : ℕ} (i k : Fin L) (a b : Fin n) :
    finProdFinEquiv (i, a) < finProdFinEquiv (k, b) ↔ i < k ∨ (i = k ∧ a < b) := by
  have hsep (i k : Fin L) (a b : Fin n) (hik : i < k) :
      finProdFinEquiv (i, a) < finProdFinEquiv (k, b) := by
    have hm := Nat.mul_le_mul_left n (show i.val + 1 ≤ k.val from hik)
    change a.val + n * i.val < b.val + n * k.val
    nlinarith [a.isLt]
  rcases lt_trichotomy i k with hik | hik | hik
  · simp [hik, hsep i k a b hik]
  · subst i
    have he : finProdFinEquiv (k, a) < finProdFinEquiv (k, b) ↔ a < b := by
      change a.val + n * k.val < b.val + n * k.val ↔ a.val < b.val
      omega
    simp [he]
  · have hnot : ¬finProdFinEquiv (i, a) < finProdFinEquiv (k, b) :=
      not_lt_of_ge (hsep k i b a hik).le
    simp [hnot, not_lt_of_ge hik.le, (ne_of_lt hik).symm]

/-- A mask after the constant, with a cut in one copy. -/
def copyPrefixMask (L n : ℕ) (k : Fin L) (r : ℕ) : Unit ⊕ Fin (L * n) → ℂ :=
  Sum.elim (fun _ => 1) (fun q =>
    if (finProdFinEquiv.symm q).1 < k ∨
      ((finProdFinEquiv.symm q).1 = k ∧ (finProdFinEquiv.symm q).2.val < r) then 1 else 0)

namespace ScalarData
variable {d n : ℕ}

/-- The linear cut acts on each model character by the required zero-one coefficient mask. -/
theorem copyCutLinear_model (s : ScalarData d n) (L : ℕ) (k : Fin L) (r : ℕ)
    (i : Unit ⊕ Fin (L * n)) :
    liftedCopyCutLinear (fun _ : Fin L => s.meanFunctional) k
      (gramConjugate s.centeredGram (finitePrefixMatrix n r)) (s.copyHilbertModel L i) =
      copyPrefixMask L n k r i • s.copyHilbertModel L i := by
  rw [liftedCopyCutLinear_apply]
  rcases i with (u | i)
  · cases u
    rw [s.copyCut_constant]
    simp [copyPrefixMask]
  · obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [s.copyCut_nonconstant]
    simp only [copyPrefixMask, Sum.elim_inr, Equiv.symm_apply_apply]
    split_ifs <;> simp

/-- The independent-copy estimate applies to the actual normalized product Gram. -/
theorem product_augmented_copy_cut (s : ScalarData d n) (L : ℕ) (k : Fin L) (r : ℕ)
    {q : ℝ} (hq : 1 + L * s.gain < q) (hp : s.CenteredPrefixSqBound q) :
    ‖gramConjugate (s.product L).rawGram (Matrix.diagonal (copyPrefixMask L n k r))‖ ^ 2 ≤
      q + q ^ 2 * s.gain / (q - 1 - L * s.gain) := by
  let C := q + q ^ 2 * s.gain / (q - 1 - L * s.gain)
  have hZ : 0 ≤ (L : ℝ) * s.gain := mul_nonneg (Nat.cast_nonneg _) s.gain_nonneg
  have hq0 : 0 ≤ q := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    have hd : 0 < q - 1 - L * s.gain := by linarith
    exact add_nonneg hq0 (div_nonneg (mul_nonneg (sq_nonneg q) s.gain_nonneg) hd.le)
  let P := gramConjugate s.centeredGram (finitePrefixMatrix n r)
  let F := liftedCopyCutLinear (fun _ : Fin L => s.meanFunctional) k P
  let U := s.copyHilbertModel L
  let D := Matrix.diagonal (copyPrefixMask L n k r)
  have hpoint (z) : ‖F z‖ ^ 2 ≤ C * ‖z‖ ^ 2 :=
    independent_copies_prefix (fun _ : Fin L => s.meanFunctional) k P
      (gramConjugate_idempotent s.centeredGram_posDef _ (finitePrefixMatrix_square n r))
      hZ s.gain_nonneg hq (s.copy_mean_budget L) s.meanFunctional_comp_adjoint_norm.le
      ((s.centeredPrefixSqBound_iff_gram hq0).mp hp r) z
  have hF (c : Unit ⊕ Fin (L * n) → ℂ) :
      F (finiteSynthesis U c) = finiteSynthesis U (D *ᵥ c) := by
    simp only [finiteSynthesis, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    change c i • (F (U i)) = (D *ᵥ c) i • U i
    rw [show F (U i) = copyPrefixMask L n k r i • U i from s.copyCutLinear_model L k r i]
    simp only [D, Matrix.mulVec_diagonal, smul_smul]
    rw [mul_comm]
  let B := ((s.product L).mass : ℂ)⁻¹ • (s.product L).rawGram
  have hB : B.PosDef := (s.product L).rawGram_posDef.smul
    (by exact_mod_cast inv_pos.mpr (s.product L).toTorusWeight.mass_pos)
  have hnorm : ‖gramConjugate B D‖ ^ 2 ≤ C := by
    apply (gramConjugate_quadratic_bound_iff hB D hC).mpr
    intro x
    have hz := hpoint (finiteSynthesis U x.ofLp)
    rw [hF, synthesis_norm_sq, synthesis_norm_sq, s.copyHilbertModel_gram] at hz
    exact hz
  have hb := gramConjugate_scaled_bound hB D (s.product L).toTorusWeight.mass_pos hC hnorm
  have hm : ((s.product L).mass : ℂ) ≠ 0 := by
    exact_mod_cast (s.product L).toTorusWeight.mass_pos.ne'
  simpa only [B, smul_smul, mul_inv_cancel₀ hm, one_smul] using hb

/-- All augmented prefixes of independent scalar copies have the small *individual* gain cost. -/
theorem product_augmented_prefix (s : ScalarData d n) (L : ℕ) {q : ℝ}
    (hq : 2 ≤ q) (hq3 : q < 3) (hZ : (L : ℝ) * s.gain ≤ 1 / 323)
    (hp : s.CenteredPrefixSqBound q) :
    (s.product L).AugmentedPrefixSqBound (q + 10 * s.gain) := by
  have hC : 1 ≤ q + 10 * s.gain := by linarith [s.gain_nonneg]
  apply ((s.product L).augmentedPrefixSqBound_iff_gram (zero_le_one.trans hC)).mpr
  intro K
  by_cases hK0 : K = 0
  · subst K
    have hzero : scalarRowPrefixMatrix (L * n) 0 = 0 := by simp [scalarRowPrefixMatrix]
    rw [hzero]
    simpa [gramConjugate] using zero_le_one.trans hC
  by_cases hKfull : L * n + 1 ≤ K
  · have hall : scalarRowPrefixMatrix (L * n) K = 1 := by
      have hi (i : Unit ⊕ Fin (L * n)) : (scalarRowEquiv (L * n) i).val < K :=
        lt_of_lt_of_le (scalarRowEquiv (L * n) i).isLt hKfull
      simp [scalarRowPrefixMatrix, hi]
    rw [hall]
    exact gramConjugate_one_sq_le (s.product L).rawGram_posDef hC
  have hjlt : K - 1 < L * n := by omega
  let j : Fin (L * n) := ⟨K - 1, hjlt⟩
  obtain ⟨⟨k, b⟩, hkb⟩ := finProdFinEquiv.surjective j
  have hmask : scalarRowPrefixMatrix (L * n) K = Matrix.diagonal (copyPrefixMask L n k b.val) := by
    apply congrArg Matrix.diagonal
    funext i
    rcases i with (u | i)
    · cases u
      simp [copyPrefixMask, show 0 < K by omega]
    · obtain ⟨⟨t, a⟩, rfl⟩ := finProdFinEquiv.surjective i
      have he : (finProdFinEquiv (t, a)).val + 1 < K ↔
          finProdFinEquiv (t, a) < finProdFinEquiv (k, b) := by
        rw [hkb]
        change _ ↔ (finProdFinEquiv (t, a)).val < K - 1
        omega
      change (if (finProdFinEquiv (t, a)).val + 1 < K then (1 : ℂ) else 0) = _
      simp only [he]
      simp only [finProdFinEquiv_lt_iff]
      simp only [copyPrefixMask, Sum.elim_inr, Equiv.symm_apply_apply, Fin.lt_def]
  rw [hmask]
  exact (s.product_augmented_copy_cut L k b.val (by linarith) hp).trans
    (scalar_copy_prefix_cost hq hq3 hZ s.gain_nonneg)

end ScalarData
end SchauderTranslates
