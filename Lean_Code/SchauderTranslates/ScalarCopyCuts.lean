import Lean_Code.SchauderTranslates.ScalarCopyModel
import Lean_Code.SchauderTranslates.CopyLinearMaps
import Lean_Code.SchauderTranslates.OrderedGramPrefixes
import Lean_Code.SchauderTranslates.CenteredMetricGram

noncomputable section
open Matrix ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A metric conjugate of a coefficient projection is again a projection. -/
theorem gramConjugate_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℂ} (hB : B.PosDef) (D : Matrix ι ι ℂ) (hD : D * D = D)
    (x : EuclideanSpace ℂ ι) : gramConjugate B D (gramConjugate B D x) = gramConjugate B D x := by
  have hi (y : EuclideanSpace ℂ ι) : gramRootInv B (gramRoot B y) = y :=
    congrArg (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => T y) (gramRoot_inv_mul hB)
  let Φ := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
  have hd : (Φ D).comp (Φ D) = Φ D := by
    change Φ D * Φ D = Φ D
    rw [← map_mul, hD]
  change gramRoot B (Φ D (gramRootInv B (gramRoot B (Φ D (gramRootInv B x))))) = _
  rw [hi]
  have hdx : Φ D (Φ D (gramRootInv B x)) = Φ D (gramRootInv B x) :=
    congrArg (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => T (gramRootInv B x)) hd
  rw [hdx]
  rfl

theorem finitePrefixMatrix_square (n r : ℕ) : finitePrefixMatrix n r * finitePrefixMatrix n r =
    finitePrefixMatrix n r := by
  rw [finitePrefixMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem copyHead_single {L n : ℕ} (k i : Fin L) (v : EuclideanSpace ℂ (Fin n)) :
    copyHead k (PiLp.single 2 i v : PiLp 2 (fun _ : Fin L => EuclideanSpace ℂ (Fin n))) =
      if i < k then PiLp.single 2 i v else 0 := by
  ext j
  by_cases hi : i < k <;> by_cases hj : j = i
    <;> simp [copyHead, PiLp.single, -PiLp.toLp_single, hi, hj]

namespace ScalarData
variable {d n : ℕ}

theorem copyHilbertModel_lifted (s : ScalarData d n) (L : ℕ) (i : Fin L) (a : Fin n) :
    s.copyHilbertModel L (Sum.inr (finProdFinEquiv (i, a))) =
      liftedCopyVector (fun _ : Fin L => s.meanFunctional)
        (PiLp.single 2 i (metricColumn s.centeredGram a)) := by
  simp only [copyHilbertModel, Sum.elim_inr, Equiv.symm_apply_apply,
    liftedCopyVector, liftCopies]
  change WithLp.toLp 2 (star (s.mean a), _) = WithLp.toLp 2
    (0 + copyMean (fun _ : Fin L => s.meanFunctional) (PiLp.single 2 i (metricColumn s.centeredGram a)), _)
  rw [copyMean_single, s.meanFunctional_column, zero_add]
  rfl

/-- A lifted copy cut fixes the initial constant. -/
theorem copyCut_constant (s : ScalarData d n) (L : ℕ) (k : Fin L) (r : ℕ) :
    liftedCopyCut (fun _ : Fin L => s.meanFunctional) k
      (gramConjugate s.centeredGram (finitePrefixMatrix n r))
      (s.copyHilbertModel L (Sum.inl ())) = s.copyHilbertModel L (Sum.inl ()) := by
  simp [copyHilbertModel, liftedCopyCut, liftCopies, unliftCopies, orthogonalCopyCut,
    copyHead, PiLp.single, -PiLp.toLp_single]
  rfl

/-- On each copied character, a cut selects exactly the preceding copies and current initial segment. -/
theorem copyCut_nonconstant (s : ScalarData d n) (L : ℕ) (k : Fin L) (r : ℕ)
    (i : Fin L) (a : Fin n) :
    liftedCopyCut (fun _ : Fin L => s.meanFunctional) k
      (gramConjugate s.centeredGram (finitePrefixMatrix n r))
      (s.copyHilbertModel L (Sum.inr (finProdFinEquiv (i, a)))) =
      if i < k ∨ (i = k ∧ a.val < r) then
        s.copyHilbertModel L (Sum.inr (finProdFinEquiv (i, a))) else 0 := by
  rw [s.copyHilbertModel_lifted, liftedCopyCut_vector, copyHead_single]
  have hp : gramConjugate s.centeredGram (finitePrefixMatrix n r) (metricColumn s.centeredGram a) =
      if a.val < r then metricColumn s.centeredGram a else 0 := by
    rw [finitePrefixMatrix, metricColumn_diagonal_action s.centeredGram_posDef]
    split_ifs <;> simp
  by_cases hik : i = k
  · subst i
    simp only [lt_self_iff_false, if_false, false_or, true_and,
      PiLp.single_apply, Pi.single_eq_same, zero_add, hp]
    by_cases ha : a.val < r
    · simp [ha, hp]
    · simp [ha, hp, liftedCopyVector, liftCopies, PiLp.single, -PiLp.toLp_single]
  · have hki : k ≠ i := Ne.symm hik
    simp only [hik, false_and, or_false, PiLp.single_apply, Pi.single_eq_of_ne hki, map_zero]
    by_cases hlt : i < k
    · simp [hlt, hki, PiLp.single, -PiLp.toLp_single]
    · simp [hlt, hki, liftedCopyVector, liftCopies, PiLp.single, -PiLp.toLp_single]

end ScalarData
end SchauderTranslates
