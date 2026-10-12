import Lean_Code.SchauderTranslates.SelectiveIntegrals

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ} (s : ScalarData d n)

theorem nonconstantGram_integral (k l : Fin n) :
    s.nonconstantGram k l = ∫ t, (s.density t : ℂ) *
      star (UnitAddTorus.mFourier (s.frequencies k) t) * UnitAddTorus.mFourier (s.frequencies l) t
      ∂torusMeasure d := s.toTorusWeight.vector_inner _ _

end ScalarData

namespace SelectiveKernelData
open BoundedMeasurableComplex
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- Actual seed-weighted row Gram; it has not been replaced by a matrix model. -/
def rawSeedGram (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) : Matrix ι ι ℂ :=
  integralGram (ρ.prod (torusMeasure L))
    (fun p => seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2) (fun i => r i)

def rowColumnGram (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) :
    Matrix (Fin n × ι) (Fin n × ι) ℂ :=
  Matrix.gram ℂ (fun i : Fin n × ι =>
    (rowColumn (r i.2) (torusCharacterRepresentative (a.scalar.frequencies i.1))).toL2 (a.kernel.measure ρ))

/-- Full tensor Gram in auxiliary-column-first order. This retains the original
reference row Gram and is valid before orthonormalizing the carrier coordinates. -/
theorem rowColumnGram_eq (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) :
    a.rowColumnGram ρ r = (a.mass : ℂ)⁻¹ •
      (a.scalar.nonconstantGram ⊗ₖ (Matrix.gram ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L)))) +
        (1 - a.scalar.nonconstantGram) ⊗ₖ a.rawSeedGram ρ r) := by
  apply Matrix.ext
  intro i j
  change inner ℂ
    ((rowColumn (r i.2) (torusCharacterRepresentative (a.scalar.frequencies i.1))).toL2 (a.kernel.measure ρ))
    ((rowColumn (r j.2) (torusCharacterRepresentative (a.scalar.frequencies j.1))).toL2 (a.kernel.measure ρ)) = _
  rw [a.inner_rowColumn, torusCharacter_inner]
  simp only [a.scalar.injective.eq_iff, torusCharacterRepresentative,
    ← a.scalar.nonconstantGram_integral]
  change (_ * a.scalar.nonconstantGram i.1 j.1 +
      a.rawSeedGram ρ r i.2 j.2 * ((if i.1 = j.1 then 1 else 0) - a.scalar.nonconstantGram i.1 j.1)) / (a.mass : ℂ) =
    (a.mass : ℂ)⁻¹ * (a.scalar.nonconstantGram i.1 j.1 *
      inner ℂ ((r i.2).toL2 (ρ.prod (torusMeasure L))) ((r j.2).toL2 (ρ.prod (torusMeasure L))) +
        ((if i.1 = j.1 then 1 else 0) - a.scalar.nonconstantGram i.1 j.1) * a.rawSeedGram ρ r i.2 j.2)
  ring

/-- In orthonormal reference row coordinates the raw tensor Gram is
`G ⊗ I + (I-G) ⊗ B`; normalization contributes only the common `1/M`. -/
theorem rowColumnGram_orthonormal
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : Matrix.gram ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))) = 1) :
    a.rowColumnGram ρ r = (a.mass : ℂ)⁻¹ •
      (a.scalar.nonconstantGram ⊗ₖ (1 : Matrix ι ι ℂ) +
        (1 - a.scalar.nonconstantGram) ⊗ₖ a.rawSeedGram ρ r) := by
  rw [a.rowColumnGram_eq, hr]

end SelectiveKernelData
end SchauderTranslates
