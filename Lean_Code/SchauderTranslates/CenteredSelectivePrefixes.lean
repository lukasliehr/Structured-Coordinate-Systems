import Lean_Code.SchauderTranslates.OrderedSelectivePrefixes
import Lean_Code.SchauderTranslates.SelectiveInitialCarrier
import Lean_Code.SchauderTranslates.PacketCoefficientExtension
import Lean_Code.SchauderTranslates.CenteredExtensionBound

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SelectiveKernelData
variable {S : Type*} [MeasurableSpace S] {L d n r : ℕ}
variable (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsProbabilityMeasure ρ]
variable (φ : Fin r → BoundedMeasurableComplex S)

theorem synthesis_extended_packet (b : Fin r → ℂ) (c : Fin n × (Fin r ⊕ Fin L) → ℂ) :
    finiteSynthesis (a.kernel.atoms ρ (a.augmentedRowColumn (packetRows φ))) (extendPacketCoefficients b c) =
      finiteSynthesis (a.initialCarrier ρ φ) b + finiteSynthesis (a.kernel.atoms ρ (a.packet φ)) c := by
  rw [synthesis_extendPacketCoefficients]
  simp only [a.augmented_constant_carrier, a.augmented_nonconstant_packet]

variable (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
variable {K : ℝ} (hK : 0 ≤ K) (hrow : FinitePrefixSqBound (fun i => (φ i).toL2 ρ) (K ^ 2))
variable (haux : a.scalar.AugmentedPrefixSqBound 4)
variable (hdiag : ∀ k, (a.scalar.rawGram⁻¹ k k).re ≤ 2)
include hφ hK hrow haux hdiag

/-- Zero extension deletes precisely the seed entries in the auxiliary constant
column. The full initial carrier is retained by every subsequent prefix. -/
theorem extended_packet_synthesis_bound (t : ℕ) (b : Fin r → ℂ)
    (c : Fin n × (Fin r ⊕ Fin L) → ℂ) :
    ‖finiteSynthesis (a.initialCarrier ρ φ) b +
      finiteSynthesis (a.kernel.atoms ρ (a.packet φ)) (fun p => if packetRank p < t then c p else 0)‖ ^ 2 ≤
      (selectivePrefixConstant K) ^ 2 *
        ‖finiteSynthesis (a.initialCarrier ρ φ) b + finiteSynthesis (a.kernel.atoms ρ (a.packet φ)) c‖ ^ 2 := by
  have h := a.augmented_ordered_synthesis_bound ρ φ hφ hK hrow haux hdiag
    ((r + L) + t) (extendPacketCoefficients b c)
  dsimp only at h
  rw [extendPacketCoefficients_prefix, a.synthesis_extended_packet, a.synthesis_extended_packet] at h
  exact h

/-- Every centered column-major prefix of the unchanged original atom list,
using its explicit conditional means in the actual weighted L² space. -/
theorem centered_packet_synthesis_bound
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ))
    (t : ℕ) (c : Fin n × (Fin r ⊕ Fin L) → ℂ) :
    ‖finiteSynthesis (a.kernel.centered ρ (a.packet φ)) (fun p => if packetRank p < t then c p else 0)‖ ^ 2 ≤
      (selectivePrefixConstant K) ^ 2 * ‖finiteSynthesis (a.kernel.centered ρ (a.packet φ)) c‖ ^ 2 := by
  have h := centered_extension_bound (a.initialCarrier ρ φ)
    (a.kernel.atoms ρ (a.packet φ)) (a.kernel.means ρ (a.packet φ))
    (a.packet_means_mem_initial ρ φ he) (a.packet_centered_mem_initial_orthogonal ρ φ)
    (fun p => if packetRank p < t then (1 : ℂ) else 0) (selectivePrefixConstant K) ?_ c
  · change ‖finiteSynthesis (fun i => a.kernel.atoms ρ (a.packet φ) i -
        a.kernel.means ρ (a.packet φ) i) (fun p => if packetRank p < t then c p else 0)‖ ^ 2 ≤
      (selectivePrefixConstant K) ^ 2 *
        ‖finiteSynthesis (fun i => a.kernel.atoms ρ (a.packet φ) i - a.kernel.means ρ (a.packet φ) i) c‖ ^ 2
    have hm : (fun p => (if packetRank p < t then (1 : ℂ) else 0) * c p) =
        (fun p => if packetRank p < t then c p else 0) := by
      funext p
      simp only [ite_mul, one_mul, zero_mul]
    rw [hm] at h
    exact h
  · intro b c
    simpa only [ite_mul, one_mul, zero_mul] using
      a.extended_packet_synthesis_bound ρ φ hφ hK hrow haux hdiag t b c

end SchauderTranslates.SelectiveKernelData
