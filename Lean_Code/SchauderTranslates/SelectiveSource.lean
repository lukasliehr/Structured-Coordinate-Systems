import Lean_Code.SchauderTranslates.SelectiveGram
import Lean_Code.SchauderTranslates.FiberSlowSpace

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProduct InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- The source pairing holds for every marginal L² function, not only bounded tests. -/
theorem atom_slowLift_inner (f : BoundedMeasurableComplex (S × Y)) (h : Lp ℂ 2 ρ) :
    inner ℂ (f.toL2 (K.measure ρ)) (K.slowLift ρ h) =
      inner ℂ ((K.meanRepresentative f).toL2 ρ) h := by
  have hmem : K.slowLift ρ h ∈ K.slowSpace ρ := by
    rw [K.slowSpace_eq_range]
    exact ⟨h, rfl⟩
  have hfix := Submodule.starProjection_eq_self_iff.mpr hmem
  calc
    _ = inner ℂ (f.toL2 (K.measure ρ)) ((K.slowSpace ρ).starProjection (K.slowLift ρ h)) := by rw [hfix]
    _ = inner ℂ ((K.slowSpace ρ).starProjection (f.toL2 (K.measure ρ))) (K.slowLift ρ h) :=
      (Submodule.inner_starProjection_left_eq_right _ _ _).symm
    _ = inner ℂ (K.slowLift ρ ((K.meanRepresentative f).toL2 ρ)) (K.slowLift ρ h) := by
      rw [K.mean_eq_starProjection, K.slowLift_bounded]
    _ = _ := (K.slowLift ρ).inner_map_map _ _

end FiberKernel

namespace SelectiveKernelData
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsProbabilityMeasure ρ]

theorem carrier_source_pairing (φ : BoundedMeasurableComplex S) (k : Fin n) (h : Lp ℂ 2 ρ) :
    inner ℂ ((a.carrierAtom φ k).toL2 (a.kernel.measure ρ)) (a.kernel.slowLift ρ h) =
      ((1 - (a.m : ℂ)) * a.scalar.moment k / (a.mass : ℂ)) * inner ℂ (φ.toL2 ρ) h := by
  rw [a.kernel.atom_slowLift_inner, a.mean_carrier_toL2, inner_smul_left,
    a.scalar.expectation_eq_star_moment]
  simp only [map_div₀, map_mul, map_sub, Complex.star_def, Complex.conj_ofReal, map_one, Complex.conj_conj]

theorem seed_source_pairing (j : Fin L) (k : Fin n) (h : Lp ℂ 2 ρ) :
    inner ℂ ((a.seedAtom j k).toL2 (a.kernel.measure ρ)) (a.kernel.slowLift ρ h) =
      (-(a.m : ℂ) * a.κ * a.scalar.moment k / (a.mass : ℂ)) * inner ℂ (a.e.toL2 ρ) h := by
  rw [a.kernel.atom_slowLift_inner, a.mean_seed_toL2, inner_smul_left,
    a.scalar.expectation_eq_star_moment]
  simp only [map_div₀, map_mul, map_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]

/-- Complete source column for the unchanged original carrier/seed rows. This is the
adjoint of actual atom synthesis applied to an arbitrary lifted slow L² vector. -/
theorem packet_source_adjoint (φ : ι → BoundedMeasurableComplex S) (h : Lp ℂ 2 ρ) :
    ((hilbertSynthesis (a.kernel.atoms ρ (a.packet φ)))†) (a.kernel.slowLift ρ h) =
      WithLp.toLp 2 (fun i : Fin n × (ι ⊕ Fin L) => a.scalar.moment i.1 / (a.mass : ℂ) *
        Sum.elim (fun j => (1 - (a.m : ℂ)) * inner ℂ ((φ j).toL2 ρ) h)
          (fun _ => -(a.m : ℂ) * a.κ * inner ℂ (a.e.toL2 ρ) h) i.2) := by
  rw [hilbertSynthesis_adjoint_apply]
  congr 1
  funext i
  rcases i with ⟨k, i | j⟩
  · change inner ℂ ((a.carrierAtom (φ i) k).toL2 (a.kernel.measure ρ)) (a.kernel.slowLift ρ h) = _
    rw [a.carrier_source_pairing]
    simp only [Sum.elim_inl]
    ring
  · change inner ℂ ((a.seedAtom j k).toL2 (a.kernel.measure ρ)) (a.kernel.slowLift ρ h) = _
    rw [a.seed_source_pairing]
    simp only [Sum.elim_inr]
    ring

end SelectiveKernelData
end SchauderTranslates
