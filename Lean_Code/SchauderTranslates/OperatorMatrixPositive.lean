import Lean_Code.SchauderTranslates.BasisOperatorMatrix

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [DecidableEq ι] in
theorem basisOperatorMatrix_hermitian (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) :
    (basisOperatorMatrix b T).IsHermitian := by
  ext i j
  change star (inner ℂ (b j) (T (b i))) = inner ℂ (b i) (T (b j))
  rw [Complex.star_def, inner_conj_symm]
  exact hs _ _

theorem basisOperatorMatrix_quadratic (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H)
    (c : EuclideanSpace ℂ ι) :
    inner ℂ ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b T) c) c =
      inner ℂ (T (b.repr.symm c)) (b.repr.symm c) := by
  rw [basisOperatorMatrix_apply]
  simpa only [b.repr.apply_symm_apply] using
    b.repr.inner_map_map (T (b.repr.symm c)) (b.repr.symm c)

/-- Coercivity of the compressed operator proves positivity of its coordinate Gram. -/
theorem basisOperatorMatrix_posDef (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H)
    {r : ℝ} (hr : 0 < r)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    (hq : ∀ x, r * ‖x‖ ^ 2 ≤ (inner ℂ (T x) x).re) :
    (basisOperatorMatrix b T).PosDef := by
  have hh := basisOperatorMatrix_hermitian b T hs
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hh
  intro x hx
  apply RCLike.pos_iff.mpr
  refine ⟨?_, hh.im_star_dotProduct_mulVec_self x⟩
  let c : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  have hc : c ≠ 0 := by
    intro he
    exact hx (congrArg WithLp.ofLp he)
  have hnorm : 0 < ‖b.repr.symm c‖ ^ 2 := by
    rw [b.repr.symm.norm_map]
    exact sq_pos_of_pos (norm_pos_iff.mpr hc)
  have hp := lt_of_lt_of_le (mul_pos hr hnorm) (hq (b.repr.symm c))
  rw [← basisOperatorMatrix_quadratic] at hp
  have hi : inner ℂ ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b T) c) c =
      star (star x ⬝ᵥ basisOperatorMatrix b T *ᵥ x) := by
    calc
      _ = (starRingEnd ℂ) (inner ℂ c
          ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b T) c)) :=
        (inner_conj_symm _ _).symm
      _ = _ := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
          c, dotProduct_comm]
        rfl
  rw [hi] at hp
  change 0 < (star x ⬝ᵥ basisOperatorMatrix b T *ᵥ x).re
  simpa only [Complex.star_def, Complex.conj_re] using hp

end SchauderTranslates
