import Lean_Code.SchauderTranslates.IntegralGramOrder
import Lean_Code.SchauderTranslates.SelectiveGram
import Lean_Code.SchauderTranslates.SelectiveTensorOrder
import Lean_Code.SchauderTranslates.ScalarReality
import Lean_Code.SchauderTranslates.AugmentedScalarPrefixes

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ} (s : ScalarData d n)

theorem rawGram_integral_star (k l : Unit ⊕ Fin n) :
    s.rawGram k l = ∫ t, (s.density t : ℂ) *
      star (UnitAddTorus.mFourier (s.augmentedFrequency k) t) *
      UnitAddTorus.mFourier (s.augmentedFrequency l) t ∂torusMeasure d :=
  s.toTorusWeight.vector_inner _ _

end ScalarData

namespace SelectiveKernelData
open BoundedMeasurableComplex
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

def referenceRowGram (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) : Matrix ι ι ℂ :=
  Matrix.gram ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L)))

theorem referenceRowGram_integral (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) :
    referenceRowGram ρ r = integralGram (ρ.prod (torusMeasure L)) (fun _ => 1) (fun i => r i) := by
  ext i j
  rw [referenceRowGram, Matrix.gram_apply, inner_toL2]
  simp only [integralGram, Complex.ofReal_one, one_mul]

theorem rawSeedGram_order (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) :
    (a.rawSeedGram ρ r).PosSemidef ∧ (referenceRowGram ρ r - a.rawSeedGram ρ r).PosSemidef := by
  let w := fun p : S × UnitAddTorus (Fin L) => seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2
  have hw : Measurable w := seedKernel_measurable a.e a.e.measurable L a.m a.κ
  have hb (p : S × UnitAddTorus (Fin L)) : 0 ≤ w p ∧ w p ≤ 1 :=
    ⟨(seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound p.1) p.2).1.le,
      (seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound p.1) p.2).2⟩
  have hr := fun i => (r i).measurable
  have hrb := fun i => (⟨(r i).bound, (r i).norm_le⟩ : ∃ B : ℝ, ∀ x, ‖r i x‖ ≤ B)
  refine ⟨integralGram_posSemidef _ hw (fun p => (hb p).1) (fun p => (hb p).2) hr hrb, ?_⟩
  have h := integralGram_posSemidef (ρ.prod (torusMeasure L)) (measurable_const.sub hw)
    (fun p => sub_nonneg.mpr (hb p).2) (C := 1) (fun p => by change 1 - w p ≤ 1; linarith [(hb p).1]) hr hrb
  change (integralGram (ρ.prod (torusMeasure L)) (fun p => 1 - w p) (fun i => r i)).PosSemidef at h
  rw [integralGram_sub _ measurable_const hw (fun _ => by norm_num : ∀ _ : S × UnitAddTorus (Fin L), |(1 : ℝ)| ≤ 1)
    (fun p => by rw [abs_of_nonneg (hb p).1]; exact (hb p).2) hr hrb,
    ← referenceRowGram_integral] at h
  exact h

/-- The temporary packet includes the auxiliary constant column and every seed row. -/
def augmentedRowColumn (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) :
    (Unit ⊕ Fin n) × ι → BoundedMeasurableComplex
      (S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) :=
  fun p => rowColumn (r p.2) (torusCharacterRepresentative (a.scalar.augmentedFrequency p.1))

def augmentedRawGram (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) :=
  mixedTensorGram a.scalar.rawGram (referenceRowGram ρ r) (a.rawSeedGram ρ r)

theorem augmentedRowColumn_gram (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L))) :
    Matrix.gram ℂ (a.kernel.atoms ρ (a.augmentedRowColumn r)) =
      (a.mass : ℂ)⁻¹ • a.augmentedRawGram ρ r := by
  ext i j
  change inner ℂ
    ((rowColumn (r i.2) (torusCharacterRepresentative (a.scalar.augmentedFrequency i.1))).toL2 (a.kernel.measure ρ))
    ((rowColumn (r j.2) (torusCharacterRepresentative (a.scalar.augmentedFrequency j.1))).toL2 (a.kernel.measure ρ)) = _
  rw [a.inner_rowColumn, torusCharacter_inner]
  simp only [a.scalar.augmentedFrequency_injective.eq_iff, torusCharacterRepresentative,
    ← a.scalar.rawGram_integral_star]
  change (_ * a.scalar.rawGram i.1 j.1 +
      a.rawSeedGram ρ r i.2 j.2 * ((if i.1 = j.1 then 1 else 0) - a.scalar.rawGram i.1 j.1)) / (a.mass : ℂ) =
    (a.mass : ℂ)⁻¹ * (a.scalar.rawGram i.1 j.1 *
      inner ℂ ((r i.2).toL2 (ρ.prod (torusMeasure L))) ((r j.2).toL2 (ρ.prod (torusMeasure L))) +
        ((if i.1 = j.1 then 1 else 0) - a.scalar.rawGram i.1 j.1) * a.rawSeedGram ρ r i.2 j.2)
  ring

theorem augmentedRawGram_posDef (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L)))) :
    (a.augmentedRawGram ρ r).PosDef :=
  mixedTensorGram_posDef a.scalar.rawGram_posDef (Matrix.le_iff.mp a.scalar.rawGram_le_one)
    (Matrix.posDef_gram_iff_linearIndependent.mpr hr) (a.rawSeedGram_order ρ r).1

theorem augmentedRawGram_column_upper (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (k : Unit ⊕ Fin n) :
    (referenceRowGram ρ r - (a.augmentedRawGram ρ r).submatrix
      (fun i => (k, i)) (fun i => (k, i))).PosSemidef :=
  mixedTensorGram_column_upper (Matrix.le_iff.mp a.scalar.rawGram_le_one) (a.rawSeedGram_order ρ r).2 k

theorem augmentedRawGram_inverse_column (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))))
    (k : Unit ⊕ Fin n) {C : ℝ} (hdiag : a.scalar.rawGram⁻¹ k k ≤ (C : ℂ)) :
    ((C : ℂ) • (referenceRowGram ρ r)⁻¹ - (a.augmentedRawGram ρ r)⁻¹.submatrix
      (fun i => (k, i)) (fun i => (k, i))).PosSemidef :=
  mixedTensorGram_inverse_column a.scalar.rawGram_posDef (Matrix.le_iff.mp a.scalar.rawGram_le_one)
    (Matrix.posDef_gram_iff_linearIndependent.mpr hr) (a.rawSeedGram_order ρ r).1 k hdiag

end SelectiveKernelData
end SchauderTranslates
