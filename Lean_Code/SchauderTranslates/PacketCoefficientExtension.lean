import Lean_Code.SchauderTranslates.ColumnPrefixMasks

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

def packetRank {n r L : ℕ} (p : Fin n × (Fin r ⊕ Fin L)) : ℕ :=
  p.1.val * (r + L) + packetRowRank p.2

/-- Insert arbitrary initial carrier coefficients and zero coefficients for
all deleted seed rows at auxiliary frequency zero. -/
def extendPacketCoefficients {n r L : ℕ} (a : Fin r → ℂ)
    (c : Fin n × (Fin r ⊕ Fin L) → ℂ) : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L) → ℂ :=
  fun p => Sum.elim (fun _ => Sum.elim a 0 p.2) (fun k => c (k, p.2)) p.1

theorem synthesis_extendPacketCoefficients {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n r L : ℕ} (u : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L) → H)
    (a : Fin r → ℂ) (c : Fin n × (Fin r ⊕ Fin L) → ℂ) :
    finiteSynthesis u (extendPacketCoefficients a c) =
      finiteSynthesis (fun i => u (Sum.inl (), Sum.inl i)) a +
        finiteSynthesis (fun p : Fin n × (Fin r ⊕ Fin L) => u (Sum.inr p.1, p.2)) c := by
  simp [finiteSynthesis, Fintype.sum_prod_type, Fintype.sum_sum_type, extendPacketCoefficients]

theorem extendPacketCoefficients_prefix {n r L : ℕ} (a : Fin r → ℂ)
    (c : Fin n × (Fin r ⊕ Fin L) → ℂ) (t : ℕ) :
    (fun p => if augmentedPacketRank p < (r + L) + t then extendPacketCoefficients a c p else 0) =
      extendPacketCoefficients a (fun p => if packetRank p < t then c p else 0) := by
  classical
  funext p
  rcases p with ⟨u | k, i | j⟩
  · cases u
    have hi : i.val < (r + L) + t := by omega
    simp [augmentedPacketRank, packetRowRank, extendPacketCoefficients, hi]
  · cases u
    simp [augmentedPacketRank, packetRowRank, extendPacketCoefficients]
  · have hh : (k.val + 1) * (r + L) + i.val < (r + L) + t ↔
        k.val * (r + L) + i.val < t := by rw [Nat.add_mul, Nat.one_mul]; omega
    simp [augmentedPacketRank, packetRank, packetRowRank, extendPacketCoefficients, hh]
  · have hh : (k.val + 1) * (r + L) + (r + j.val) < (r + L) + t ↔
        k.val * (r + L) + (r + j.val) < t := by rw [Nat.add_mul, Nat.one_mul]; omega
    simp [augmentedPacketRank, packetRank, packetRowRank, extendPacketCoefficients, hh]

end SchauderTranslates
