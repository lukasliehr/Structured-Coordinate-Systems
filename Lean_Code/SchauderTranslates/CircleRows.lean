import Lean_Code.SchauderTranslates.ActivationOperator
import Lean_Code.SchauderTranslates.ActivationSet
import Lean_Code.SchauderTranslates.HilbertSynthesis

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A row vector modulated by one circle Fourier character. -/
def circleRow (v : EuclideanSpace ℂ ι) (k : ℤ) :
    Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1)) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    ⟨fun y : UnitAddCircle => fourier k y • v, by fun_prop⟩

omit [DecidableEq ι] in
theorem circleRow_ae (v : EuclideanSpace ℂ ι) (k : ℤ) :
    (circleRow v k : UnitAddCircle → EuclideanSpace ℂ ι) =ᵐ[AddCircle.haarAddCircle]
      (fun y => fourier k y • v) :=
  ContinuousMap.coeFn_toLp (𝕜 := ℂ) AddCircle.haarAddCircle _

theorem matrix_inner_single (B : Matrix ι ι ℂ) (i j : ι) :
    inner ℂ (EuclideanSpace.single i 1)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B (EuclideanSpace.single j 1)) = B i j := by
  rw [EuclideanSpace.inner_single_left]
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, PiLp.single_apply]

/-- All Fourier matrix entries of the full activation operator. -/
theorem circleRow_activation_inner (B : Matrix ι ι ℂ) (p : ℝ) (i j : ι) (k l : ℤ) :
    inner ℂ (circleRow (EuclideanSpace.single i 1) k)
      (activationOperator (activationSet p) (activationSet_measurable p)
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B)
        (circleRow (EuclideanSpace.single j 1) l)) =
      ∫ y, (if y ∈ activationSet p then B i j else if i = j then 1 else 0) *
        star (fourier k y) * fourier l y ∂AddCircle.haarAddCircle := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleRow_ae (EuclideanSpace.single i 1) k,
    circleRow_ae (EuclideanSpace.single j 1) l,
    activationOperator_ae (activationSet p) (activationSet_measurable p)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B)
      (circleRow (EuclideanSpace.single j 1) l)] with y hi hj ha
  rw [ha, hi, hj]
  by_cases hy : y ∈ activationSet p
  · simp only [hy, if_true, map_smul, inner_smul_left, inner_smul_right, matrix_inner_single,
      Complex.star_def]
    ring
  · simp only [hy, if_false, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
      map_one, one_mul, PiLp.single_apply, Complex.star_def]
    ring

end SchauderTranslates
