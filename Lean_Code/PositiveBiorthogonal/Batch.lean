import Lean_Code.PositiveBiorthogonal.BatchAlgebra
import Lean_Code.PositiveBiorthogonal.Schedule

/-! A batch obtained from an actual refinement trace and a disjoint fresh block. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
namespace RefinementTrace
variable {N : ℕ} (T : RefinementTrace N)

theorem active_eq_initial (i : Fin (N + 1)) : (T.state i).active = (T.state 0).active := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [T.next, ActivePartition.refine_active]; exact ih

theorem parent_subset_initial (j : Fin N) : (T.split j).parent.carrier ⊆ (T.state 0).active := by
  rw [T.parent, ← T.active_eq_initial j.castSucc]
  rw [ActivePartition.active, ← (T.state j.castSucc).cover]
  exact subset_iUnion (fun i => ((T.state j.castSucc).cell i).carrier) (T.index j)

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

theorem haarH_supported_initial (j : Fin N) :
    ∀ᵐ x : ℝ, x ∉ (T.state 0).active → (T.split j).haarH (𝕜 := 𝕜) (p := p) x = 0 := by
  filter_upwards [(T.split j).haarH_supported (𝕜 := 𝕜) (p := p)] with x hx
  intro ha
  exact hx (fun hp => ha (T.parent_subset_initial j hp))

theorem haarPhi_supported_initial (j : Fin N) :
    ∀ᵐ x : ℝ, x ∉ (T.state 0).active → (T.split j).haarPhi (𝕜 := 𝕜) (p := p) x = 0 := by
  filter_upwards [(T.split j).haarPhi_supported (𝕜 := 𝕜) (p := p)] with x hx
  intro ha
  exact hx (fun hp => ha (T.parent_subset_initial j hp))

theorem transfer_pairing_haarPhi {m : ℕ} (F : UnitBlock m)
    (hF : Disjoint F.carrier (T.state 0).active) (x : FiniteLp 𝕜 p m) (j : Fin N) :
    pairing (F.transfer x) ((T.split j).haarPhi : L 𝕜 q) = 0 :=
  pairing_zero_disjoint_support _ _ _ _ hF (F.transfer_supported x) (T.haarPhi_supported_initial j)

theorem haarH_pairing_transfer {m : ℕ} (F : UnitBlock m)
    (hF : Disjoint F.carrier (T.state 0).active) (x : FiniteLp 𝕜 q m) (j : Fin N) :
    pairing ((T.split j).haarH : L 𝕜 p) (F.transfer x) = 0 :=
  pairing_zero_disjoint_support _ _ _ _ hF.symm (T.haarH_supported_initial j) (F.transfer_supported x)

end RefinementTrace

namespace AuxiliaryFamily
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  {δ : ℝ} (A : AuxiliaryFamily 𝕜 p q δ) {N : ℕ}

def batchVectors (T : RefinementTrace N) (F : UnitBlock (2 * N)) (a : 𝕜) : Fin (3 * N) → L 𝕜 p :=
  orderedBatchVector (fun j => F.transfer (A.d N j)) (fun j => (T.split j).haarH) a

def batchCoefficients (T : RefinementTrace N) (F : UnitBlock (2 * N)) (a : 𝕜) : Fin (3 * N) → L 𝕜 q :=
  orderedBatchCoefficient (fun j => F.transfer (A.s N j)) (fun j => (T.split j).haarPhi) a

theorem batch_biorthogonal (hN : 0 < N) (T : RefinementTrace N) (F : UnitBlock (2 * N))
    (hF : Disjoint F.carrier (T.state 0).active) (a : 𝕜) (i j : Fin (3 * N)) :
    pairing (A.batchVectors T F a i) (A.batchCoefficients T F a j) = if i = j then 1 else 0 := by
  apply orderedBatch_biorthogonal
  · intro i j
    rw [F.transfer_pairing, A.biorthogonal N hN]
  · exact T.haar_biorthogonal
  · exact fun i j => T.transfer_pairing_haarPhi F hF (A.d N i) j
  · exact fun i j => T.haarH_pairing_transfer F hF (A.s N j) i

theorem batchVectors_step (T : RefinementTrace N) (F : UnitBlock (2 * N)) (a : 𝕜) (i : Fin (3 * N)) :
    CompactlySupportedStep (A.batchVectors T F a i) :=
  batchVector_step _ _ a (fun j => F.transfer_step _) (fun j => (T.split j).haarH_step) _

theorem batchCoefficients_step (T : RefinementTrace N) (F : UnitBlock (2 * N)) (a : 𝕜) (i : Fin (3 * N)) :
    CompactlySupportedStep (A.batchCoefficients T F a i) :=
  batchCoefficient_step _ _ a (fun j => F.transfer_step _) (fun j => (T.split j).haarPhi_step) _

end AuxiliaryFamily
end PositiveBiorthogonal
