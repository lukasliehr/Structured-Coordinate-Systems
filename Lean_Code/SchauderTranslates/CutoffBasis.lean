import Lean_Code.SchauderTranslates.CircleRowsBasis
import Lean_Code.SchauderTranslates.CircleCutoffs
import Lean_Code.SchauderTranslates.BasisOperatorMatrix

noncomputable section
open MeasureTheory Module
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite orthonormal family itself is the basis of its span. -/
def spanOrthonormalBasis {u : ι → H} (hu : Orthonormal ℂ u) :
    OrthonormalBasis ι ℂ (Submodule.span ℂ (Set.range u)) :=
  (Basis.span hu.linearIndependent).toOrthonormalBasis (by
    change Orthonormal ℂ (fun i => (Basis.span hu.linearIndependent) i)
    simp_rw [Basis.span_apply]
    exact orthonormal_span hu)

omit [DecidableEq ι] in
@[simp] theorem spanOrthonormalBasis_coe {u : ι → H} (hu : Orthonormal ℂ u) (i : ι) :
    (spanOrthonormalBasis hu i : H) = u i := by
  simp [spanOrthonormalBasis, Basis.coe_toOrthonormalBasis, Basis.span_apply]

/-- The inherited row/Fourier basis on a finite symmetric window. -/
def circleCutoffBasis (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    OrthonormalBasis (ι × CircleWindow N) ℂ (circleCutoffSpace ι N) :=
  spanOrthonormalBasis (circleRows_orthonormal.comp
    (fun q : ι × CircleWindow N => (q.1, q.2.1)) (by
      rintro ⟨i,k⟩ ⟨j,l⟩ he
      have hi := congrArg Prod.fst he
      have hk := congrArg Prod.snd he
      exact Prod.ext hi (Subtype.ext hk)))

@[simp] theorem circleCutoffBasis_coe (N : ℕ) (q : ι × CircleWindow N) :
    (circleCutoffBasis ι N q : Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1))) =
      circleRow (EuclideanSpace.single q.1 1) q.2.1 :=
  spanOrthonormalBasis_coe _ _

end SchauderTranslates
