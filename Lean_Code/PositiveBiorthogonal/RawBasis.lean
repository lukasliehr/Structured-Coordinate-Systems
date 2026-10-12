import Lean_Code.PositiveBiorthogonal.MeshDensity

/-! Assembly of the raw Schauder basis from the closed biorthogonality, density and bounds. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace PositiveBiorthogonal
namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

def rawBasis : SchauderBasis 𝕜 p :=
  basisOfDenseSpan C.rawVector (fun n => representedFunctional (C.rawCoefficient n))
    (fun i j => by rw [representedFunctional_apply]; exact C.raw_biorthogonal i j)
    C.rawVector_dense (1 + C.δ + C.η) C.rawProjection_bound

theorem rawBasis_represents : Represents C.rawBasis C.rawCoefficient := by
  intro n f
  exact representedFunctional_apply _ _

theorem rawBasis_K_le : K C.rawBasis ≤ 1 + C.δ + C.η :=
  K_le_of_projection_bound C.rawBasis _ C.rawProjection_bound

@[simp] theorem rawBasis_vector (n : ℕ) : C.rawBasis.b n = C.rawVector n := rfl

@[simp] theorem rawBasis_projection (n : ℕ) : P C.rawBasis n = C.rawProjection n := rfl

end ConstructionData
end PositiveBiorthogonal
