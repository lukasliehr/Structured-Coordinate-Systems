import Lean_Code.SchauderTranslates.SoftCapture
import Mathlib.Analysis.Matrix.Order

noncomputable section
open Matrix
open scoped ComplexOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Auxiliary coordinate first, row coordinate second. -/
def tensorVector (y : ι → ℂ) (x : κ → ℂ) : ι × κ → ℂ := fun p => y p.1 * x p.2

theorem kronecker_mulVec_tensor (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (y : ι → ℂ) (x : κ → ℂ) :
    (A ⊗ₖ B) *ᵥ tensorVector y x = tensorVector (A *ᵥ y) (B *ᵥ x) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, tensorVector, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change (A p.1 j * B p.2 l) * (y j * x l) = (A p.1 j * y j) * (B p.2 l * x l)
  ring

def tensorGram (G : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  G ⊗ₖ (1 : Matrix κ κ ℂ) + (1 - G) ⊗ₖ B

theorem tensorGram_posDef {G : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hG : G.PosDef) (hB : B.PosDef) (hB1 : (1 - B).PosSemidef) : (tensorGram G B).PosDef := by
  have h := (Matrix.PosDef.one.kronecker hB).add_posSemidef (hG.posSemidef.kronecker hB1)
  have he : tensorGram G B = (1 : Matrix ι ι ℂ) ⊗ₖ B + G ⊗ₖ (1 - B) := by
    apply Matrix.ext
    intro i j
    change G i.1 j.1 * (1 : Matrix κ κ ℂ) i.2 j.2 +
      ((1 : Matrix ι ι ℂ) i.1 j.1 - G i.1 j.1) * B i.2 j.2 =
      (1 : Matrix ι ι ℂ) i.1 j.1 * B i.2 j.2 +
        G i.1 j.1 * ((1 : Matrix κ κ ℂ) i.2 j.2 - B i.2 j.2)
    ring
  rw [he]
  exact h

/-- The actual raw source matrix in orthonormal row coordinates. -/
def tensorSource (b : ι → ℂ) (B : Matrix κ κ ℂ) : Matrix (ι × κ) κ ℂ :=
  fun p j => b p.1 * (1 - B) p.2 j

def tensorCapture (G : Matrix ι ι ℂ) (b : ι → ℂ) (B : Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  (tensorSource b B)ᴴ * (tensorGram G B)⁻¹ * tensorSource b B

theorem tensorSource_mulVec (b : ι → ℂ) (B : Matrix κ κ ℂ) (x : κ → ℂ) :
    tensorSource b B *ᵥ x = tensorVector b ((1 - B) *ᵥ x) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, tensorSource, tensorVector, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Adjoint source action includes the conjugation on the scalar moment vector. -/
theorem tensorSource_adjoint_tensor (b y : ι → ℂ) {B : Matrix κ κ ℂ}
    (hB : B.IsHermitian) (x : κ → ℂ) :
    (tensorSource b B)ᴴ *ᵥ tensorVector y x = (star b ⬝ᵥ y) • ((1 - B) *ᵥ x) := by
  have hH : (1 - B : Matrix κ κ ℂ).IsHermitian := Matrix.isHermitian_one.sub hB
  funext j
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorVector,
    tensorSource, Matrix.conjTranspose_apply, star_mul, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have he : star ((1 - B : Matrix κ κ ℂ) l j) = (1 - B) j l := congrFun (congrFun hH j) l
  rw [he]
  ring

end SchauderTranslates
