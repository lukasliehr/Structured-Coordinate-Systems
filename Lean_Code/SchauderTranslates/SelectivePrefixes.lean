import Lean_Code.SchauderTranslates.CenteredSelectivePrefixes
import Lean_Code.SchauderTranslates.PacketEnumeration

noncomputable section
open MeasureTheory Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The actual centered packet, in the paper's auxiliary-column-major order. -/
def SelectiveKernelData.orderedCenteredPacket {S : Type*} [MeasurableSpace S]
    {L d n r : ℕ} (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsProbabilityMeasure ρ]
    (φ : Fin r → BoundedMeasurableComplex S) :
    Fin (n * (r + L)) → Lp ℂ 2 (a.kernel.measure ρ) :=
  fun i => a.kernel.centered ρ (a.packet φ) ((packetEquiv n r L).symm i)

/-- Blueprint `select:prefix`: every ordered centered prefix has norm at most
`2 + sqrt 2 * max K 1`, in the original carrier coordinates. The scalar
hypotheses are exactly the numerical consequences of `scalar_blocks`. -/
theorem selective_centered_prefix {S : Type*} [MeasurableSpace S] {L d n r : ℕ}
    (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsProbabilityMeasure ρ]
    (φ : Fin r → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ))
    {K : ℝ} (hK : 0 ≤ K) (hrow : FinitePrefixSqBound (fun i => (φ i).toL2 ρ) (K ^ 2))
    (haux : a.scalar.AugmentedPrefixSqBound 4)
    (hdiag : ∀ k, (a.scalar.rawGram⁻¹ k k).re ≤ 2) :
    FinitePrefixSqBound (a.orderedCenteredPacket ρ φ) (selectivePrefixConstant K ^ 2) := by
  apply finitePrefixSqBound_of_rank (packetEquiv n r L)
  intro t c
  simpa only [packetEquiv_val] using
    a.centered_packet_synthesis_bound ρ φ hφ hK hrow haux hdiag he t c

/-- Discharge the prefix hypotheses directly from the bounds exported by the
scalar supply, including the auxiliary constant diagonal. -/
theorem selective_centered_prefix_of_scalar_supply {S : Type*} [MeasurableSpace S]
    {L d n r : ℕ} (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsProbabilityMeasure ρ]
    (φ : Fin r → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ))
    {K : ℝ} (hK : 0 ≤ K) (hrow : FinitePrefixSqBound (fun i => (φ i).toL2 ρ) (K ^ 2))
    {ε A : ℝ} (hε : ε ≤ 1 / 10) (hA : 0 ≤ A) (hA2 : A < 2)
    (haux : a.scalar.AugmentedPrefixSqBound (A ^ 2))
    (hdiag : ∀ k : Fin n, (a.scalar.rawGram⁻¹ (Sum.inr k) (Sum.inr k)).re ≤ 1 + 2 * ε)
    (hconst : (a.scalar.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2) :
    FinitePrefixSqBound (a.orderedCenteredPacket ρ φ) (selectivePrefixConstant K ^ 2) := by
  apply selective_centered_prefix a ρ φ hφ he hK hrow
  · exact haux.mono (by nlinarith)
  · intro k
    rcases k with u | k
    · cases u
      exact hconst.le
    · linarith [hdiag k]

end SchauderTranslates
