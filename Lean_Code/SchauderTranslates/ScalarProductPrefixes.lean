import Lean_Code.SchauderTranslates.ScalarProducts
import Lean_Code.SchauderTranslates.RepeatedQuadratic
import Lean_Code.SchauderTranslates.OrderedGramPrefixes

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A flat ordered prefix cuts each copy at its own offset, including empty and full copies. -/
theorem coefficientCopy_prefix {L n : ℕ} (x : EuclideanSpace ℂ (Fin (L * n)))
    (k : ℕ) (i : Fin L) :
    coefficientCopy ((Matrix.toEuclideanCLM (𝕜 := ℂ)) (finitePrefixMatrix (L * n) k) x) i =
      (Matrix.toEuclideanCLM (𝕜 := ℂ)) (finitePrefixMatrix n (k - i.val * n)) (coefficientCopy x i) := by
  ext a
  change (finitePrefixMatrix (L * n) k *ᵥ WithLp.ofLp x) (finProdFinEquiv (i, a)) =
    (finitePrefixMatrix n (k - i.val * n) *ᵥ WithLp.ofLp (coefficientCopy x i)) a
  rw [finitePrefixMatrix_mulVec, finitePrefixMatrix_mulVec]
  have hv : (finProdFinEquiv (i, a)).val = a.val + n * i.val := rfl
  have he : (finProdFinEquiv (i, a)).val < k ↔ a.val < k - i.val * n := by
    rw [hv, Nat.mul_comm n i.val]
    omega
  simp only [he]
  rfl

namespace ScalarData
variable {d n : ℕ}

/-- Concatenating independent centered copies preserves every ordered prefix bound. -/
theorem product_centered_prefix (s : ScalarData d n) (L : ℕ) {q : ℝ}
    (hq : 0 ≤ q) (h : s.CenteredPrefixSqBound q) :
    (s.product L).CenteredPrefixSqBound q := by
  apply ((s.product L).centeredPrefixSqBound_iff_gram hq).mpr
  intro k
  apply (gramConjugate_quadratic_bound_iff (s.product L).centeredGram_posDef _ hq).mpr
  intro x
  rw [s.product_centeredGram, repeatedMatrix_quadratic_sum, repeatedMatrix_quadratic_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [coefficientCopy_prefix]
  exact (gramConjugate_quadratic_bound_iff s.centeredGram_posDef _ hq).mp
    ((s.centeredPrefixSqBound_iff_gram hq).mp h _) _

end ScalarData
end SchauderTranslates
