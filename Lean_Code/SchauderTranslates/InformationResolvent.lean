import Lean_Code.SchauderTranslates.HilbertSynthesis

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lift a finite matrix between the mean synthesis and its adjoint. -/
def informationSandwich (v : ι → H) (B : Matrix ι ι ℂ) : H →L[ℂ] H :=
  (hilbertSynthesis v).comp (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B).comp ((hilbertSynthesis v)†))

theorem informationSandwich_add (v : ι → H) (A B : Matrix ι ι ℂ) :
    informationSandwich v (A + B) = informationSandwich v A + informationSandwich v B := by
  simp [informationSandwich, map_add, add_comp, comp_add]

theorem informationSandwich_mul (v : ι → H) (A B : Matrix ι ι ℂ) :
    informationSandwich v A * informationSandwich v B =
      informationSandwich v (A * Matrix.gram ℂ v * B) := by
  let T : EuclideanSpace ℂ ι →L[ℂ] H := hilbertSynthesis v
  let M := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
  change (T.comp ((M A).comp (T†))).comp (T.comp ((M B).comp (T†))) =
    T.comp ((M (A * Matrix.gram ℂ v * B)).comp (T†))
  rw [map_mul, map_mul]
  change (T.comp ((M A).comp (T†))).comp (T.comp ((M B).comp (T†))) =
    T.comp ((((M A).comp (M (Matrix.gram ℂ v))).comp (M B)).comp (T†))
  simp only [comp_assoc]
  rw [← comp_assoc (T†) T, hilbertSynthesis_gram]

/-- Both orders of the inverse-difference identity are retained for the operator inverse. -/
theorem matrix_inverse_add_split {C D : Matrix ι ι ℂ} (hC : C.PosDef)
    (hA : (C + D).PosDef) :
    C⁻¹ = (C + D)⁻¹ + C⁻¹ * D * (C + D)⁻¹ ∧
    C⁻¹ = (C + D)⁻¹ + (C + D)⁻¹ * D * C⁻¹ := by
  have hc := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have ha := (Matrix.isUnit_iff_isUnit_det (C + D)).mp hA.isUnit
  constructor
  · calc
      C⁻¹ = C⁻¹ * ((C + D) * (C + D)⁻¹) := by rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
        Matrix.nonsing_inv_mul _ hc, Matrix.one_mul]
  · calc
      C⁻¹ = ((C + D)⁻¹ * (C + D)) * C⁻¹ := by rw [Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_nonsing_inv _ hc, Matrix.mul_one, Matrix.mul_assoc]

/-- Information and raw capture, acting on the entire slow Hilbert space. -/
def informationOperator (v : ι → H) (C : Matrix ι ι ℂ) : H →L[ℂ] H := informationSandwich v C⁻¹

def captureOperator (v : ι → H) (C : Matrix ι ι ℂ) : H →L[ℂ] H :=
  informationSandwich v (C + Matrix.gram ℂ v)⁻¹

theorem information_capture_equations (v : ι → H) {C : Matrix ι ι ℂ} (hC : C.PosDef) :
    informationOperator v C = captureOperator v C + informationOperator v C * captureOperator v C ∧
    informationOperator v C = captureOperator v C + captureOperator v C * informationOperator v C := by
  have hA := hC.add_posSemidef (Matrix.posSemidef_gram ℂ v)
  have h := matrix_inverse_add_split hC hA
  constructor
  · simpa only [informationOperator, captureOperator, informationSandwich_add, ← informationSandwich_mul] using
      congrArg (informationSandwich v) h.1
  · simpa only [informationOperator, captureOperator, informationSandwich_add, ← informationSandwich_mul] using
      congrArg (informationSandwich v) h.2

/-- An explicit two-sided bounded inverse of `I + J`; no finite-dimensionality of the slow space is needed. -/
theorem information_resolvent_inverse (v : ι → H) {C : Matrix ι ι ℂ} (hC : C.PosDef) :
    (1 + informationOperator v C) * (1 - captureOperator v C) = 1 ∧
      (1 - captureOperator v C) * (1 + informationOperator v C) = 1 := by
  have h := information_capture_equations v hC
  constructor
  · calc
      _ = 1 + informationOperator v C - (captureOperator v C + informationOperator v C * captureOperator v C) := by noncomm_ring
      _ = 1 := by rw [← h.1]; abel
  · calc
      _ = 1 + informationOperator v C - (captureOperator v C + captureOperator v C * informationOperator v C) := by noncomm_ring
      _ = 1 := by rw [← h.2]; abel

/-- The precise resolvent identity in (I1), with a certified invertible denominator. -/
theorem information_capture_resolvent (v : ι → H) {C : Matrix ι ι ℂ} (hC : C.PosDef) :
    IsUnit (1 + informationOperator v C) ∧
      captureOperator v C = informationOperator v C * Ring.inverse (1 + informationOperator v C) := by
  have hi := information_resolvent_inverse v hC
  have hu : IsUnit (1 + informationOperator v C) := ⟨⟨_, _, hi.1, hi.2⟩, rfl⟩
  refine ⟨hu, ?_⟩
  have he : captureOperator v C * (1 + informationOperator v C) = informationOperator v C := by
    rw [mul_add, mul_one, ← (information_capture_equations v hC).2]
  calc
    captureOperator v C = captureOperator v C * ((1 + informationOperator v C) * Ring.inverse (1 + informationOperator v C)) := by
      rw [Ring.mul_inverse_cancel _ hu, mul_one]
    _ = _ := by rw [← mul_assoc, he]

end SchauderTranslates
