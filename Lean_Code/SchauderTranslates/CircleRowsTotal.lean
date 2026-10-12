import Lean_Code.SchauderTranslates.CircleRows

noncomputable section
open MeasureTheory
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Completeness of the row-by-circle characters in vector-valued L². -/
theorem circleRows_eq_zero (f : Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1)))
    (hf : ∀ (i : ι) (k : ℤ), inner ℂ (circleRow (EuclideanSpace.single i 1) k) f = 0) :
    f = 0 := by
  let g (i : ι) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    ((Lp.memLp f).eval_piLp i).toLp (fun y => f y i)
  have hg_ae (i : ι) : (g i : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle] (fun y => f y i) :=
    ((Lp.memLp f).eval_piLp i).coeFn_toLp
  have hi (i : ι) (k : ℤ) : inner ℂ (fourierLp 2 k) (g i) =
      inner ℂ (circleRow (EuclideanSpace.single i 1) k) f := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 k, hg_ae i,
      circleRow_ae (EuclideanSpace.single i 1) k] with y hy hg hr
    rw [hy, hg, hr]
    simp [inner_smul_left, EuclideanSpace.inner_single_left, RCLike.inner_apply, mul_comm]
  have hz (i : ι) : g i = 0 := by
    apply (fourierBasis (T := 1)).repr.injective
    ext k
    rw [HilbertBasis.repr_apply_apply]
    simp only [coe_fourierBasis, hi, hf, map_zero, lp.coeFn_zero, Pi.zero_apply]
  have hzero (i : ι) : (fun y : UnitAddCircle => f y i) =ᵐ[AddCircle.haarAddCircle] 0 := by
    have hh := (hg_ae i).symm
    rw [hz i] at hh
    exact hh.trans (Lp.coeFn_zero ℂ 2 _)
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hzero,
    Lp.coeFn_zero (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1))] with y hy hz
  rw [hz]
  ext i
  exact hy i

/-- Consequently the full activated Gram is uniquely determined by its Fourier coordinates. -/
theorem circleRows_total :
    (Submodule.span ℂ (Set.range (fun q : ι × ℤ =>
      circleRow (EuclideanSpace.single q.1 1) q.2))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  apply circleRows_eq_zero
  intro i k
  exact (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨(i,k), rfl⟩)

/-- Equality of all row/Fourier coefficients determines a bounded operator uniquely. -/
theorem circleRows_operator_ext
    (A B : Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1)) →L[ℂ]
      Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1)))
    (h : ∀ (i j : ι) (k l : ℤ),
      inner ℂ (circleRow (EuclideanSpace.single i 1) k)
        (A (circleRow (EuclideanSpace.single j 1) l)) =
      inner ℂ (circleRow (EuclideanSpace.single i 1) k)
        (B (circleRow (EuclideanSpace.single j 1) l))) : A = B := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (circleRows_total (ι := ι)))
  rintro f ⟨⟨j,l⟩, rfl⟩
  apply sub_eq_zero.mp
  apply circleRows_eq_zero
  intro i k
  rw [inner_sub_right, h, sub_self]

end SchauderTranslates
