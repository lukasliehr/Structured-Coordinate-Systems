import Lean_Code.SchauderTranslates.PacketCoefficientExtension

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The original packet order: auxiliary column first, then carrier and seed rows. -/
def packetEquiv (n r L : ℕ) : Fin n × (Fin r ⊕ Fin L) ≃ Fin (n * (r + L)) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) (packetRowEquiv r L)).trans finProdFinEquiv

@[simp] theorem packetEquiv_val {n r L : ℕ} (p : Fin n × (Fin r ⊕ Fin L)) :
    (packetEquiv n r L p).val = packetRank p := by
  rcases p with ⟨k, i | j⟩ <;>
    simp [packetEquiv, packetRank, packetRowEquiv, packetRowRank,
      finProdFinEquiv, finSumFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- Transfer an explicitly ranked prefix estimate to a finite ordered list. -/
theorem finitePrefixSqBound_of_rank {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}
    (e : ι ≃ Fin N) (u : ι → H) (q : ℝ)
    (h : ∀ t c, ‖finiteSynthesis u (fun p => if (e p).val < t then c p else 0)‖ ^ 2 ≤
      q * ‖finiteSynthesis u c‖ ^ 2) :
    FinitePrefixSqBound (fun i => u (e.symm i)) q := by
  classical
  intro t c
  have hp := e.sum_comp (fun i => if i.val < t then c i • u (e.symm i) else 0)
  have hf := e.sum_comp (fun i => c i • u (e.symm i))
  have hh := h t (fun p => c (e p))
  simp only [finiteSynthesis, ite_smul, zero_smul] at hh
  simp only [Equiv.symm_apply_apply] at hp hf
  rw [hp, hf] at hh
  exact hh

end SchauderTranslates
