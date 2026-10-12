import Lean_Code.SchauderTranslates.CircleRowsTotal

noncomputable section
open MeasureTheory
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Tensor orthogonality, proved directly in the vector-valued L² representation. -/
theorem circleRow_inner (v w : EuclideanSpace ℂ ι) (k l : ℤ) :
    inner ℂ (circleRow v k) (circleRow w l) = inner ℂ v w * (if k = l then 1 else 0) := by
  have hkl : (∫ y : UnitAddCircle, star (fourier k y) * fourier l y
      ∂AddCircle.haarAddCircle) = if k = l then 1 else 0 := by
    have h := orthonormal_iff_ite.mp (orthonormal_fourier (T := 1)) k l
    rw [L2.inner_def] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 k, coeFn_fourierLp 2 l] with y hk hl
    rw [hk, hl]
    simp [RCLike.inner_apply, mul_comm]
  rw [← hkl, ← integral_const_mul, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleRow_ae v k, circleRow_ae w l] with y hv hw
  rw [hv, hw, inner_smul_left, inner_smul_right]
  rw [Complex.star_def]
  ring

/-- Every old coordinate crossed with every circle Fourier mode is orthonormal. -/
theorem circleRows_orthonormal : Orthonormal ℂ (fun q : ι × ℤ =>
    circleRow (EuclideanSpace.single q.1 1) q.2) := by
  apply orthonormal_iff_ite.mpr
  rintro ⟨i,k⟩ ⟨j,l⟩
  rw [circleRow_inner, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, PiLp.single_apply]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl, Prod.ext_iff]

/-- The complete Fourier basis for the coefficient model of rare activation. -/
def circleRowsBasis : HilbertBasis (ι × ℤ) ℂ
    (Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1))) :=
  HilbertBasis.mk circleRows_orthonormal circleRows_total.ge

@[simp] theorem circleRowsBasis_apply (q : ι × ℤ) :
    circleRowsBasis q = circleRow (EuclideanSpace.single q.1 1) q.2 :=
  congrFun (HilbertBasis.coe_mk _ _) q

end SchauderTranslates
