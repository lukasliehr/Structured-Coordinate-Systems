import Lean_Code.SchauderTranslates.SelectiveAugmentedGram
import Lean_Code.SchauderTranslates.FiberSlowSpace

noncomputable section
open MeasureTheory Matrix
open scoped InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SelectiveKernelData
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsProbabilityMeasure ρ]

/-- The original carrier embedded isometrically in the actual weighted space. -/
def initialCarrier (φ : ι → BoundedMeasurableComplex S) (i : ι) : Lp ℂ 2 (a.kernel.measure ρ) :=
  a.kernel.slowLift ρ ((φ i).toL2 ρ)

theorem initialCarrier_span (φ : ι → BoundedMeasurableComplex S) :
    atomSpan (a.initialCarrier ρ φ) =
      (atomSpan (fun i => (φ i).toL2 ρ)).map (a.kernel.slowLift ρ).toLinearMap := by
  simp only [atomSpan, Submodule.map_span, ← Set.range_comp, initialCarrier]
  rfl

theorem initialCarrier_mem_slow (φ : ι → BoundedMeasurableComplex S) (i : ι) :
    a.initialCarrier ρ φ i ∈ a.kernel.slowSpace ρ := by
  rw [initialCarrier, a.kernel.slowLift_bounded]
  exact a.kernel.slow_mem ρ (φ i)

theorem initialCarrier_span_le_slow (φ : ι → BoundedMeasurableComplex S) :
    atomSpan (a.initialCarrier ρ φ) ≤ a.kernel.slowSpace ρ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact a.initialCarrier_mem_slow ρ φ i

/-- The retained carrier entries of the auxiliary constant column are exactly
the slow carrier, as actual weighted L² vectors. -/
theorem augmented_constant_carrier (φ : ι → BoundedMeasurableComplex S) (i : ι) :
    a.kernel.atoms ρ (a.augmentedRowColumn (packetRows φ)) (Sum.inl (), Sum.inl i) =
      a.initialCarrier ρ φ i := by
  rw [initialCarrier, a.kernel.slowLift_bounded]
  apply BoundedMeasurableComplex.toL2_congr
  exact Filter.Eventually.of_forall (fun p => by
    simp [augmentedRowColumn, packetRows, rowColumn, ScalarData.augmentedFrequency,
      torusCharacterRepresentative, UnitAddTorus.mFourier_zero, BoundedMeasurableComplex.pullbackFst,
      BoundedMeasurableComplex.comp, BoundedMeasurableComplex.mul])

theorem augmented_nonconstant_packet (φ : ι → BoundedMeasurableComplex S)
    (p : Fin n × (ι ⊕ Fin L)) :
    a.kernel.atoms ρ (a.augmentedRowColumn (packetRows φ)) (Sum.inr p.1, p.2) =
      a.kernel.atoms ρ (a.packet φ) p := rfl

theorem packet_means_mem_initial (φ : ι → BoundedMeasurableComplex S)
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ)) (p : Fin n × (ι ⊕ Fin L)) :
    a.kernel.means ρ (a.packet φ) p ∈ atomSpan (a.initialCarrier ρ φ) := by
  rw [a.initialCarrier_span]
  exact a.packet_lifted_mean_mem ρ φ _ (fun i => Submodule.subset_span (Set.mem_range_self i)) he p

theorem packet_centered_mem_initial_orthogonal (φ : ι → BoundedMeasurableComplex S)
    (p : Fin n × (ι ⊕ Fin L)) :
    a.kernel.centered ρ (a.packet φ) p ∈ (atomSpan (a.initialCarrier ρ φ))ᗮ :=
  Submodule.orthogonal_le (a.initialCarrier_span_le_slow ρ φ)
    (a.kernel.centered_mem_slow_orthogonal ρ (a.packet φ p))

end SchauderTranslates.SelectiveKernelData
