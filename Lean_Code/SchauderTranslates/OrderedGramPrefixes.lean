import Lean_Code.SchauderTranslates.ScalarPrefixes
import Lean_Code.SchauderTranslates.ScaledGramBound

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The coefficient projection onto the first `k` entries, including both endpoints. -/
def finitePrefixMatrix (n k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if i.val < k then 1 else 0)

theorem finitePrefixMatrix_mulVec {n : ℕ} (k : ℕ) (c : Fin n → ℂ) :
    finitePrefixMatrix n k *ᵥ c = fun i => if i.val < k then c i else 0 := by
  ext i
  simp [finitePrefixMatrix, Matrix.mulVec_diagonal]

theorem finiteSynthesis_prefix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (u : Fin n → H) (k : ℕ) (c : Fin n → ℂ) :
    finiteSynthesis u (finitePrefixMatrix n k *ᵥ c) =
      ∑ i, if i.val < k then c i • u i else 0 := by
  rw [finitePrefixMatrix_mulVec]
  simp [finiteSynthesis, ite_smul]

/-- The matrix prefix estimate is exactly the finite ordered-synthesis predicate. -/
theorem finitePrefixSqBound_iff_gram {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (u : Fin n → H) (hu : LinearIndependent ℂ u) {q : ℝ} (hq : 0 ≤ q) :
    FinitePrefixSqBound u q ↔
      ∀ k, ‖gramConjugate (Matrix.gram ℂ u) (finitePrefixMatrix n k)‖ ^ 2 ≤ q := by
  have h (k : ℕ) := synthesis_gram_prefix_iff u hu (finitePrefixMatrix n k) (Real.sqrt q)
  simp only [Real.sq_sqrt hq, finiteSynthesis_prefix] at h
  simp only [finiteSynthesis] at h
  exact forall_congr' (fun k => (h k).symm)

theorem finitePrefixMatrix_all {n k : ℕ} (h : n ≤ k) : finitePrefixMatrix n k = 1 := by
  have hi (i : Fin n) : i.val < k := lt_of_lt_of_le i.isLt h
  simp [finitePrefixMatrix, hi]

theorem gramConjugate_one_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℂ} (hB : B.PosDef) {q : ℝ} (hq : 1 ≤ q) :
    ‖gramConjugate B 1‖ ^ 2 ≤ q := by
  apply (gramConjugate_quadratic_bound_iff hB 1 (zero_le_one.trans hq)).mpr
  intro x
  rw [map_one]
  change coefficientQuadratic B x ≤ q * coefficientQuadratic B x
  exact le_mul_of_one_le_left ((matrix_posSemidef_iff_quadratic hB.isHermitian).mp hB.posSemidef x) hq

namespace ScalarData
variable {d n : ℕ}

theorem rawCenteredGram_eq_mass_smul (s : ScalarData d n) :
    s.rawCenteredGram = (s.mass : ℂ) • s.centeredGram := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  rw [centeredGram, smul_smul, mul_inv_cancel₀ hm, one_smul]

/-- Ordered centered prefixes use the normalized Gram without changing their constant. -/
theorem centeredPrefixSqBound_iff_gram (s : ScalarData d n) {q : ℝ} (hq : 0 ≤ q) :
    s.CenteredPrefixSqBound q ↔
      ∀ k, ‖gramConjugate s.centeredGram (finitePrefixMatrix n k)‖ ^ 2 ≤ q := by
  rw [CenteredPrefixSqBound, finitePrefixSqBound_iff_gram _ s.centeredVectors_linearIndependent hq,
    s.centeredVector_gram]
  constructor
  · intro h k
    have hs := gramConjugate_scaled_bound s.rawCenteredGram_posDef (finitePrefixMatrix n k)
      (inv_pos.mpr s.toTorusWeight.mass_pos) hq (h k)
    simpa only [centeredGram, Complex.ofReal_inv] using hs
  · intro h k
    rw [s.rawCenteredGram_eq_mass_smul]
    exact gramConjugate_scaled_bound s.centeredGram_posDef (finitePrefixMatrix n k)
      s.toTorusWeight.mass_pos hq (h k)

end ScalarData
end SchauderTranslates
