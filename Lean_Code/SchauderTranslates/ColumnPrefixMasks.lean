import Lean_Code.SchauderTranslates.PacketRowPrefixes
import Lean_Code.SchauderTranslates.SelectiveColumnCuts

noncomputable section
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Division and remainder identify the unique partially retained column. -/
theorem column_rank_lt_iff {w b : ℕ} (hw : 0 < w) (hb : b < w) (a t : ℕ) :
    a * w + b < t ↔ a < t / w ∨ a = t / w ∧ b < t % w := by
  have ht := Nat.mod_add_div t w
  rw [Nat.mul_comm w (t / w)] at ht
  have hm := Nat.mod_lt t hw
  rcases lt_trichotomy a (t / w) with ha | ha | ha
  · have hx := Nat.mul_le_mul_right w (show a + 1 ≤ t / w by omega)
    rw [Nat.add_mul, Nat.one_mul] at hx
    have hlt : a * w + b < t := by omega
    exact ⟨fun _ => Or.inl ha, fun _ => hlt⟩
  · subst a
    constructor <;> intro h <;> omega
  · have hx := Nat.mul_le_mul_right w (show t / w + 1 ≤ a by omega)
    rw [Nat.add_mul, Nat.one_mul] at hx
    have hge : t ≤ a * w + b := by omega
    constructor <;> intro h <;> omega

section Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Insert a diagonal row mask into exactly one column. -/
theorem selected_column_diagonal (k : ι) (δ : κ → ℂ) :
    selectionColumns (𝕜 := ℂ) (fun i : κ => (k, i)) * Matrix.diagonal δ *
      (selectionColumns (𝕜 := ℂ) (fun i : κ => (k, i))).conjTranspose =
      Matrix.diagonal (fun p : ι × κ => if p.1 = k then δ p.2 else 0) := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.mul_diagonal, selectionColumns,
    Matrix.submatrix_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases hp : p.1 = k
  · by_cases hq : q.1 = k
    · rcases p with ⟨p, i⟩; rcases q with ⟨q, j⟩
      dsimp at hp hq
      subst p; subst q
      by_cases hij : i = j <;> simp [Prod.mk.injEq, eq_comm, hij]
    · have hne (j : κ) : q ≠ (k, j) := fun h => hq (congrArg Prod.fst h)
      have hpq : p ≠ q := by intro h; exact hq (h ▸ hp)
      simp [hne, hpq, hp]
  · have hne (j : κ) : p ≠ (k, j) := fun h => hp (congrArg Prod.fst h)
    simp [hne, hp]

/-- Tensoring an auxiliary diagonal mask with the identity retains whole columns. -/
theorem diagonal_kronecker_identity (δ : ι → ℂ) :
    Matrix.diagonal δ ⊗ₖ (1 : Matrix κ κ ℂ) = Matrix.diagonal (fun p : ι × κ => δ p.1) := by
  ext ⟨k, i⟩ ⟨l, j⟩
  simp [Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

end Matrix

/-- The fixed carrier/seed row order enumerates each row exactly once. -/
def packetRowEquiv (r L : ℕ) : Fin r ⊕ Fin L ≃ Fin (r + L) := finSumFinEquiv

@[simp] theorem packetRowEquiv_val {r L : ℕ} (i : Fin r ⊕ Fin L) :
    (packetRowEquiv r L i).val = packetRowRank i := by
  cases i <;> rfl

def augmentedPacketRank {n r L : ℕ} (p : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L)) : ℕ :=
  (scalarRowEquiv n p.1).val * (r + L) + packetRowRank p.2

def augmentedPacketPrefixMatrix (n r L t : ℕ) :
    Matrix ((Unit ⊕ Fin n) × (Fin r ⊕ Fin L)) ((Unit ⊕ Fin n) × (Fin r ⊕ Fin L)) ℂ :=
  Matrix.diagonal (fun p => if augmentedPacketRank p < t then 1 else 0)

/-- An interior augmented prefix is precisely its complete columns plus one
partial column. This statement retains the original row order. -/
theorem augmentedPacketPrefixMatrix_split {n r L t : ℕ} (ht : t < (n + 1) * (r + L)) :
    let k : Unit ⊕ Fin n := (scalarRowEquiv n).symm ⟨t / (r + L), (Nat.div_lt_iff_lt_mul (by nlinarith : 0 < r + L)).mpr ht⟩
    augmentedPacketPrefixMatrix n r L t =
      scalarRowPrefixMatrix n (t / (r + L)) ⊗ₖ (1 : Matrix (Fin r ⊕ Fin L) (Fin r ⊕ Fin L) ℂ) +
        selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i)) *
          packetRowPrefixMatrix r L (t % (r + L)) *
          (selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i))).conjTranspose := by
  dsimp only
  rw [packetRowPrefixMatrix_diagonal, selected_column_diagonal, scalarRowPrefixMatrix,
    diagonal_kronecker_identity, Matrix.diagonal_add]
  apply congrArg Matrix.diagonal
  funext p
  have hw : 0 < r + L := by nlinarith
  have hb : packetRowRank p.2 < r + L := by
    simpa only [packetRowEquiv_val] using (packetRowEquiv r L p.2).isLt
  have he : p.1 = (scalarRowEquiv n).symm ⟨t / (r + L), (Nat.div_lt_iff_lt_mul hw).mpr ht⟩ ↔
      (scalarRowEquiv n p.1).val = t / (r + L) := by
    rw [Equiv.eq_symm_apply]
    exact Fin.ext_iff
  simp only [augmentedPacketPrefixMatrix, augmentedPacketRank, Pi.add_apply,
    column_rank_lt_iff hw hb, he]
  by_cases hlt : (scalarRowEquiv n p.1).val < t / (r + L)
  · have hne : ¬ (scalarRowEquiv n p.1).val = t / (r + L) := Nat.ne_of_lt hlt
    simp [hlt, hne]
  · by_cases heq : (scalarRowEquiv n p.1).val = t / (r + L) <;> simp [hlt, heq]

end SchauderTranslates
