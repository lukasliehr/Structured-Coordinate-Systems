import Lean_Code.SchauderTranslates.SelectiveReference
import Lean_Code.SchauderTranslates.FiberCenteredIndependence
import Lean_Code.SchauderTranslates.FiberSlowLift

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace SelectiveKernelData
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsProbabilityMeasure ρ]

theorem mean_carrier_toL2 (φ : BoundedMeasurableComplex S) (k : Fin n) :
    (a.kernel.meanRepresentative (a.carrierAtom φ k)).toL2 ρ =
      ((1 - (a.m : ℂ)) * a.scalar.expectation k / (a.mass : ℂ)) • φ.toL2 ρ := by
  let c := (1 - (a.m : ℂ)) * a.scalar.expectation k / (a.mass : ℂ)
  calc
    _ = (φ.scale c).toL2 ρ := by
      apply BoundedMeasurableComplex.toL2_congr
      filter_upwards [] with x
      change a.kernel.mean (a.carrierAtom φ k) x = c * φ x
      rw [a.mean_carrier]
      dsimp only [c]
      ring
    _ = _ := BoundedMeasurableComplex.toL2_scale c φ ρ

theorem mean_seed_toL2 (j : Fin L) (k : Fin n) :
    (a.kernel.meanRepresentative (a.seedAtom j k)).toL2 ρ =
      (-(a.m : ℂ) * a.κ * a.scalar.expectation k / (a.mass : ℂ)) • a.e.toL2 ρ := by
  let c := -(a.m : ℂ) * a.κ * a.scalar.expectation k / (a.mass : ℂ)
  calc
    _ = (a.e.scale c).toL2 ρ := by
      apply BoundedMeasurableComplex.toL2_congr
      filter_upwards [] with x
      change a.kernel.mean (a.seedAtom j k) x = c * a.e x
      rw [a.mean_seed]
      dsimp only [c]
      ring
    _ = _ := BoundedMeasurableComplex.toL2_scale c a.e ρ

theorem packet_mean_mem (φ : ι → BoundedMeasurableComplex S)
    (V : Submodule ℂ (Lp ℂ 2 ρ)) (hφV : ∀ i, (φ i).toL2 ρ ∈ V) (heV : a.e.toL2 ρ ∈ V)
    (i : Fin n × (ι ⊕ Fin L)) :
    (a.kernel.meanRepresentative (a.packet φ i)).toL2 ρ ∈ V := by
  rcases i with ⟨k, i | j⟩
  · change (a.kernel.meanRepresentative (a.carrierAtom (φ i) k)).toL2 ρ ∈ V
    rw [a.mean_carrier_toL2]
    exact V.smul_mem _ (hφV i)
  · change (a.kernel.meanRepresentative (a.seedAtom j k)).toL2 ρ ∈ V
    rw [a.mean_seed_toL2]
    exact V.smul_mem _ heV

theorem packet_lifted_mean_mem (φ : ι → BoundedMeasurableComplex S)
    (V : Submodule ℂ (Lp ℂ 2 ρ)) (hφV : ∀ i, (φ i).toL2 ρ ∈ V) (heV : a.e.toL2 ρ ∈ V)
    (i : Fin n × (ι ⊕ Fin L)) :
    a.kernel.means ρ (a.packet φ) i ∈ V.map (a.kernel.slowLift ρ).toLinearMap := by
  apply Submodule.mem_map.mpr
  refine ⟨(a.kernel.meanRepresentative (a.packet φ i)).toL2 ρ,
    a.packet_mean_mem ρ φ V hφV heV i, ?_⟩
  exact a.kernel.slowLift_bounded ρ _

theorem packet_centered_posDef (φ : ι → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ)) :
    (Matrix.gram ℂ (a.kernel.centered ρ (a.packet φ))).PosDef :=
  a.kernel.centered_posDef_of_reference ρ (a.packet φ) a.kernel_positive
    (a.packet_independent ρ φ hφ) (a.packet_reference_mean_zero φ)

end SelectiveKernelData

/-- Blueprint `select:means`: the actual selective kernel, every retained original
carrier and seed mean, their range, and strict centered positivity. Columns are indexed
first, followed by the unchanged carrier/seed rows. `expectation` is the integral of
the character against the scalar density, not its conjugate Gram-column moment. -/
theorem selective_kernel_means {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
    {L d n : ℕ} (a : SelectiveKernelData S L d n)
    (ρ : Measure S) [IsProbabilityMeasure ρ] (φ : ι → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
    (V : Submodule ℂ (Lp ℂ 2 ρ)) (hφV : ∀ i, (φ i).toL2 ρ ∈ V) (heV : a.e.toL2 ρ ∈ V)
    {ε : ℝ} (hε : a.scalar.mass = 1 - ε) :
    a.mass = 1 - (1 - a.m) * ε ∧
      (∀ x, (∫ y, a.raw (x, y) ∂(torusMeasure L).prod (torusMeasure d)) = a.mass) ∧
      (∀ p, 0 < a.raw p ∧ a.raw p ≤ 1) ∧
      (∀ i k x, a.kernel.mean (a.carrierAtom (φ i) k) x =
        (1 - (a.m : ℂ)) * a.scalar.expectation k * φ i x / (a.mass : ℂ)) ∧
      (∀ j k x, a.kernel.mean (a.seedAtom j k) x =
        -(a.m : ℂ) * a.κ * a.scalar.expectation k * a.e x / (a.mass : ℂ)) ∧
      (∀ i, a.kernel.means ρ (a.packet φ) i ∈ V.map (a.kernel.slowLift ρ).toLinearMap) ∧
      (Matrix.gram ℂ (a.kernel.centered ρ (a.packet φ))).PosDef := by
  exact ⟨a.mass_eq hε, a.raw_mass, a.raw_bounds, fun i => a.mean_carrier (φ i),
    a.mean_seed, a.packet_lifted_mean_mem ρ φ V hφV heV, a.packet_centered_posDef ρ φ hφ⟩

end SchauderTranslates
