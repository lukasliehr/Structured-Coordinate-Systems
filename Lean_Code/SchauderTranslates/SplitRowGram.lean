import Lean_Code.SchauderTranslates.HilbertSynthesis
import Lean_Code.SchauderTranslates.SplitRowModel

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The old columns, followed by the split column in one new orthogonal dimension. -/
def splitAtoms (u : ι → H) (x : H) (t : ℝ) : ι ⊕ Unit → WithLp 2 (H × ℝ)
  | .inl i => WithLp.toLp 2 (u i, 0)
  | .inr _ => WithLp.toLp 2 (Real.sqrt t • x, Real.sqrt (1 - t))

/-- The displayed selected Gram in the paper, including an empty old prefix. -/
def splitGram (B : Matrix ι ι ℝ) (b : ι → ℝ) (m t : ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks B (fun i _ => Real.sqrt t * b i) (fun _ i => Real.sqrt t * b i)
    (fun _ _ => 1 - t + t * m)

omit [Fintype ι] [DecidableEq ι] in
theorem splitAtoms_gram (u : ι → H) (x : H) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Matrix.gram ℝ (splitAtoms u x t) =
      splitGram (Matrix.gram ℝ u) (fun i => inner ℝ (u i) x) (‖x‖ ^ 2) t := by
  ext i j
  cases i <;> cases j
  · simp [splitAtoms, splitGram, Matrix.gram_apply, WithLp.prod_inner_apply]
  · simp [splitAtoms, splitGram, Matrix.gram_apply, WithLp.prod_inner_apply, real_inner_smul_right]
  · simp [splitAtoms, splitGram, Matrix.gram_apply, WithLp.prod_inner_apply,
      real_inner_comm x, real_inner_smul_left]
  · simp only [Matrix.gram_apply, splitAtoms, splitGram, Matrix.fromBlocks_apply₂₂,
      WithLp.prod_inner_apply, real_inner_self_eq_norm_sq]
    change ‖Real.sqrt t • x‖ ^ 2 + ‖Real.sqrt (1 - t)‖ ^ 2 = _
    rw [real_norm_smul_sq, Real.norm_eq_abs, sq_abs]
    nlinarith [Real.sq_sqrt ht, Real.sq_sqrt (sub_nonneg.mpr ht1)]

omit [DecidableEq ι] in
theorem splitAtoms_product (u v : ι → H) (x y : H) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ i, rankOne ℝ (splitAtoms u x t i) (splitAtoms v y t i)) =
      splitRowOperator (∑ i, rankOne ℝ (u i) (v i)) x y t (Real.sqrt (t * (1 - t))) := by
  have hprod : Real.sqrt t * Real.sqrt (1 - t) = Real.sqrt (t * (1 - t)) :=
    (Real.sqrt_mul ht _).symm
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  apply ContinuousLinearMap.ext
  intro z
  simp only [add_apply, sum_apply, splitAtoms, rankOne_apply,
    splitRowOperator_apply, WithLp.prod_inner_apply, real_inner_smul_left, Real.inner_apply]
  apply (WithLp.equiv 2 (H × ℝ)).injective
  apply Prod.ext
  · simp only [WithLp.equiv_apply, WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Prod.fst_add, Prod.fst_sum,
      zero_mul, add_zero, Prod.smul_mk, smul_zero]
    change (∑ i, inner ℝ (v i) z.fst • u i) +
        (Real.sqrt t * inner ℝ y z.fst + Real.sqrt (1 - t) * z.snd) • (Real.sqrt t • x) =
      (∑ i, inner ℝ (v i) z.fst • u i) +
        (t * inner ℝ y z.fst + Real.sqrt (t * (1 - t)) * z.snd) • x
    rw [smul_smul]
    congr 2
    calc
      _ = (Real.sqrt t) ^ 2 * inner ℝ y z.fst +
          (Real.sqrt t * Real.sqrt (1 - t)) * z.snd := by ring
      _ = _ := by rw [Real.sq_sqrt ht, hprod]
  · simp only [WithLp.equiv_apply, WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Prod.snd_add, Prod.snd_sum,
      zero_mul, add_zero, Prod.smul_mk, smul_zero]
    change (∑ _i : ι, (0 : ℝ)) +
        (Real.sqrt t * inner ℝ y z.fst + Real.sqrt (1 - t) * z.snd) * Real.sqrt (1 - t) =
      Real.sqrt (t * (1 - t)) * inner ℝ y z.fst + (1 - t) * z.snd
    simp only [Finset.sum_const_zero, zero_add]
    calc
      _ = (Real.sqrt t * Real.sqrt (1 - t)) * inner ℝ y z.fst +
          (Real.sqrt (1 - t)) ^ 2 * z.snd := by ring
      _ = _ := by rw [Real.sq_sqrt (sub_nonneg.mpr ht1), hprod]

/-- Both displayed Grams determine the exact norm of the split-row operator. -/
theorem splitRow_norm_gram [CompleteSpace H] (u v : ι → H) (x y : H)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖splitRowOperator (∑ i, rankOne ℝ (u i) (v i)) x y t (Real.sqrt (t * (1 - t)))‖ ^ 2 =
      ‖(gramRoot (splitGram (Matrix.gram ℝ u) (fun i => inner ℝ (u i) x) (‖x‖ ^ 2) t)).comp
        (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι ⊕ Unit))
          (splitGram (Matrix.gram ℝ v) (fun i => inner ℝ (v i) y) (‖y‖ ^ 2) t)).comp
            (gramRoot (splitGram (Matrix.gram ℝ u) (fun i => inner ℝ (u i) x) (‖x‖ ^ 2) t)))‖ := by
  have h := sum_rankOne_norm_sq (𝕜 := ℝ) (splitAtoms u x t) (splitAtoms v y t)
  rw [splitAtoms_product u v x y ht ht1, splitAtoms_gram u x ht ht1,
    splitAtoms_gram v y ht ht1] at h
  exact h

end SchauderTranslates
