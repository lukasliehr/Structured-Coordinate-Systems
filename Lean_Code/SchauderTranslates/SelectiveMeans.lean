import Lean_Code.SchauderTranslates.SelectiveKernel
import Lean_Code.SchauderTranslates.MixedKernelPairing

noncomputable section
open MeasureTheory Filter
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open BoundedMeasurableComplex

def torusCharacterRepresentative {d : ℕ} (k : Fin d → ℤ) : BoundedMeasurableComplex (UnitAddTorus (Fin d)) where
  toFun := UnitAddTorus.mFourier k
  measurable := (UnitAddTorus.mFourier k).continuous.measurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := fun x => (torus_character_norm k x).le

def seedPhaseRepresentative {L : ℕ} (j : Fin L) : BoundedMeasurableComplex (UnitAddTorus (Fin L)) where
  toFun := fun z => fourier (1 : ℤ) (z j)
  measurable := (fourier (1 : ℤ)).continuous.measurable.comp (measurable_pi_apply j)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := fun z => by simp [fourier_apply]

theorem seedPhase_integral {L : ℕ} (j : Fin L) :
    (∫ z, seedPhaseRepresentative j z ∂torusMeasure L) = 0 := by
  have hj : (Pi.single j 1 : Fin L → ℤ) ≠ 0 := by
    intro h
    have := congrFun h j
    simp at this
  simpa only [seedPhaseRepresentative, UnitAddTorus.mFourier_single, hj, if_false] using
    integral_torus_character (Pi.single j 1)

namespace ScalarData
variable {d n : ℕ} (s : ScalarData d n)

def weightRepresentative : BoundedMeasurableComplex (UnitAddTorus (Fin d)) where
  toFun := fun t => (s.density t : ℂ)
  measurable := Complex.continuous_ofReal.measurable.comp s.measurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (s.positive t)]
    exact s.le_one t

/-- Actual expectation; the existing Gram-column `moment` is its conjugate. -/
def expectation (k : Fin n) : ℂ :=
  ∫ t, (s.density t : ℂ) * UnitAddTorus.mFourier (s.frequencies k) t ∂torusMeasure d

theorem expectation_eq_star_moment (k : Fin n) : s.expectation k = star (s.moment k) := by
  have h := s.toTorusWeight.vector_inner 0 (s.frequencies k)
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, star_one, mul_one] at h
  change inner ℂ (s.vector 0) (s.vector (s.frequencies k)) = s.expectation k at h
  exact h.symm.trans (s.rawGram_posDef.isHermitian.apply (Sum.inl ()) (Sum.inr k)).symm

theorem character_integral_zero (k : Fin n) :
    (∫ t, UnitAddTorus.mFourier (s.frequencies k) t ∂torusMeasure d) = 0 := by
  rw [integral_torus_character, if_neg (s.nonconstant k)]

end ScalarData

namespace SelectiveKernelData
variable {S : Type*} [MeasurableSpace S] {L d n : ℕ}
variable (a : SelectiveKernelData S L d n)

def seedRepresentative (x : S) : BoundedMeasurableComplex (UnitAddTorus (Fin L)) where
  toFun := fun z => (seedKernel L a.m ((a.κ : ℂ) * a.e x) z : ℂ)
  measurable := Complex.continuous_ofReal.measurable.comp (seedKernel_continuous _ _ _).measurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := fun z => by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound x) z).1]
    exact (seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound x) z).2

def rowColumn (r : BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (q : BoundedMeasurableComplex (UnitAddTorus (Fin d))) :
    BoundedMeasurableComplex (S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) :=
  (r.comp (fun p => (p.1, p.2.1)) (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
    (q.comp (fun p => p.2.2) (measurable_snd.comp measurable_snd))

/-- The general row/column mean formula, with the normalization kept explicit. -/
theorem mean_rowColumn (r : BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (q : BoundedMeasurableComplex (UnitAddTorus (Fin d))) (x : S) :
    a.kernel.mean (rowColumn r q) x =
      ((∫ z, r (x, z) ∂torusMeasure L) *
          (∫ t, (a.scalar.density t : ℂ) * q t ∂torusMeasure d) +
        (∫ z, (seedKernel L a.m ((a.κ : ℂ) * a.e x) z : ℂ) * r (x, z) ∂torusMeasure L) *
          ((∫ t, q t ∂torusMeasure d) - ∫ t, (a.scalar.density t : ℂ) * q t ∂torusMeasure d)) / (a.mass : ℂ) := by
  have h := mixed_kernel_pairing (torusMeasure L) (torusMeasure d) (a.seedRepresentative x)
    (r.comp (fun z => (x, z)) measurable_prodMk_left) a.scalar.weightRepresentative q
  dsimp only [seedRepresentative, BoundedMeasurableComplex.comp, ScalarData.weightRepresentative] at h
  change (∫ y, ((a.raw (x, y) / a.mass : ℝ) : ℂ) * (r (x, y.1) * q y.2)
    ∂(torusMeasure L).prod (torusMeasure d)) = _
  simp only [Complex.ofReal_div, div_mul_eq_mul_div, integral_div]
  congr 1
  simpa only [raw, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one] using h

def carrierAtom (φ : BoundedMeasurableComplex S) (k : Fin n) :=
  rowColumn (φ.pullbackFst (UnitAddTorus (Fin L))) (torusCharacterRepresentative (a.scalar.frequencies k))

def seedAtom (j : Fin L) (k : Fin n) :
    BoundedMeasurableComplex (S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) :=
  rowColumn ((seedPhaseRepresentative j).comp Prod.snd measurable_snd)
    (torusCharacterRepresentative (a.scalar.frequencies k))

theorem mean_carrier (φ : BoundedMeasurableComplex S) (k : Fin n) (x : S) :
    a.kernel.mean (a.carrierAtom φ k) x =
      (1 - (a.m : ℂ)) * a.scalar.expectation k * φ x / (a.mass : ℂ) := by
  rw [carrierAtom, mean_rowColumn]
  simp only [pullbackFst, torusCharacterRepresentative, integral_const, probReal_univ, one_smul,
    integral_mul_const, integral_complex_ofReal, seedKernel_integral, a.scalar.character_integral_zero]
  change (φ x * a.scalar.expectation k + ((a.m : ℂ) * φ x) * (0 - a.scalar.expectation k)) / _ = _
  ring

theorem mean_seed (j : Fin L) (k : Fin n) (x : S) :
    a.kernel.mean (a.seedAtom j k) x =
      -(a.m : ℂ) * a.κ * a.scalar.expectation k * a.e x / (a.mass : ℂ) := by
  rw [seedAtom, mean_rowColumn]
  simp only [BoundedMeasurableComplex.comp, torusCharacterRepresentative]
  rw [seedPhase_integral]
  simp only [seedPhaseRepresentative, seedKernel_first_moment, a.scalar.character_integral_zero, zero_mul, zero_add]
  change ((a.m : ℂ) * ((a.κ : ℂ) * a.e x) * (0 - a.scalar.expectation k)) / _ = _
  ring

end SelectiveKernelData
end SchauderTranslates
