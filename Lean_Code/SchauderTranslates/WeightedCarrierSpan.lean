import Lean_Code.SchauderTranslates.BoundedSpan
import Lean_Code.SchauderTranslates.SelectivePacket
import Lean_Code.SchauderTranslates.FiberSlowLift

noncomputable section
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.FiberKernel
variable {S Y ι : Type*} [MeasurableSpace S] [MeasurableSpace Y] [Fintype ι]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- Multiplying a slow bounded function by a fixed bounded packet factor preserves
all linear relations, using the actual marginal of the weighted measure. -/
theorem multiply_slow_relation (f : ι → BoundedMeasurableComplex S)
    (g : BoundedMeasurableComplex S) (q : BoundedMeasurableComplex (S × Y))
    (c : ι → ℂ) (h : ∑ i, c i • (f i).toL2 ρ = g.toL2 ρ) :
    ∑ i, c i • (((f i).pullbackFst Y).mul q).toL2 (K.measure ρ) =
      ((g.pullbackFst Y).mul q).toL2 (K.measure ρ) := by
  have hae : (fun x => ∑ i, c i * f i x) =ᵐ[ρ] g := by
    have hh := (BoundedMeasurableComplex.sum_toL2_ae f ρ Finset.univ c).symm
    rw [h] at hh
    exact hh.trans (g.toL2_ae ρ)
  have hp := (K.measurePreserving_fst ρ).quasiMeasurePreserving.ae_eq_comp hae
  apply Lp.ext
  filter_upwards [BoundedMeasurableComplex.sum_toL2_ae
    (fun i => ((f i).pullbackFst Y).mul q) (K.measure ρ) Finset.univ c,
    ((g.pullbackFst Y).mul q).toL2_ae (K.measure ρ), hp] with p hs hg he
  rw [hs, hg]
  change (∑ i, c i * (f i p.1 * q p)) = g p.1 * q p
  calc
    _ = (∑ i, c i * f i p.1) * q p := by simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by simpa only [Function.comp_apply] using congrArg (fun z : ℂ => z * q p) he

theorem multiply_slow_mem_span (f : ι → BoundedMeasurableComplex S)
    (g : BoundedMeasurableComplex S) (q : BoundedMeasurableComplex (S × Y))
    (h : g.toL2 ρ ∈ atomSpan (fun i => (f i).toL2 ρ)) :
    ((g.pullbackFst Y).mul q).toL2 (K.measure ρ) ∈
      atomSpan (fun i => (((f i).pullbackFst Y).mul q).toL2 (K.measure ρ)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, K.multiply_slow_relation ρ f g q c hc⟩

end SchauderTranslates.FiberKernel

namespace SchauderTranslates.SelectiveKernelData
variable {S ι κ : Type*} [MeasurableSpace S] [Fintype ι] [Fintype κ]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsProbabilityMeasure ρ]

/-- A change of coordinates in the slow carrier preserves the span of the actual
weighted packet, column by column; all seed atoms remain in the packet. -/
theorem packet_span_mono (φ : ι → BoundedMeasurableComplex S)
    (ψ : κ → BoundedMeasurableComplex S)
    (h : atomSpan (fun i => (φ i).toL2 ρ) ≤ atomSpan (fun i => (ψ i).toL2 ρ)) :
    atomSpan (a.kernel.atoms ρ (a.packet φ)) ≤ atomSpan (a.kernel.atoms ρ (a.packet ψ)) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨k, r⟩, rfl⟩
  cases r with
  | inl i =>
    let q := (torusCharacterRepresentative (a.scalar.frequencies k)).comp
      (fun p : S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d)) => p.2.2)
      (measurable_snd.comp measurable_snd)
    have hi := h (Submodule.subset_span (Set.mem_range_self i))
    have hm := a.kernel.multiply_slow_mem_span ρ ψ (φ i) q hi
    apply Submodule.span_mono (s := Set.range (fun j =>
      (((ψ j).pullbackFst _).mul q).toL2 (a.kernel.measure ρ))) ?_ hm
    rintro _ ⟨j, rfl⟩
    exact ⟨(k, Sum.inl j), rfl⟩
  | inr j =>
    exact Submodule.subset_span ⟨(k, Sum.inr j), rfl⟩

theorem packet_span_eq (φ : ι → BoundedMeasurableComplex S)
    (ψ : κ → BoundedMeasurableComplex S)
    (h : atomSpan (fun i => (φ i).toL2 ρ) = atomSpan (fun i => (ψ i).toL2 ρ)) :
    atomSpan (a.kernel.atoms ρ (a.packet φ)) = atomSpan (a.kernel.atoms ρ (a.packet ψ)) :=
  le_antisymm (a.packet_span_mono ρ φ ψ h.le) (a.packet_span_mono ρ ψ φ h.ge)

end SchauderTranslates.SelectiveKernelData
