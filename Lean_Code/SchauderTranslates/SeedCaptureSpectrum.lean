import Lean_Code.SchauderTranslates.TensorCaptureEigen
import Lean_Code.SchauderTranslates.SeedUpperProjection

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

def seedCaptureValue (G : Matrix α α ℂ) (b : α → ℂ) (κ m : ℝ) (L : ℕ) : ℝ :=
  seedOmega κ L * softCapture G b (m * seedGamma κ L) +
    (1 - seedOmega κ L) * softCapture G b (m * seedBigGamma κ L)

def seedCompressedCapture (G : Matrix α α ℂ) (b : α → ℂ) (i₀ : ι) (κ m : ℝ) (L : ℕ) : Matrix ι ι ℂ :=
  (tensorCapture G b ((m : ℂ) • seedBlock i₀ L κ)).submatrix Sum.inl Sum.inl

theorem seedLower_scaled_eigen (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) (m : ℝ) (x : ι ⊕ Fin L → ℂ) :
    ((m : ℂ) • seedBlock i₀ L κ) *ᵥ (seedFullLowerProjection i₀ κ L *ᵥ x) =
      (m * seedGamma κ L : ℝ) • (seedFullLowerProjection i₀ κ L *ᵥ x) := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, seedFullLowerProjection_eigen i₀ hκ0 hκ1 hL,
    Matrix.smul_mulVec, smul_smul]
  ext i
  simp [Complex.real_smul, Complex.ofReal_mul]

theorem seedUpper_scaled_eigen (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) (m : ℝ) (x : ι ⊕ Fin L → ℂ) :
    ((m : ℂ) • seedBlock i₀ L κ) *ᵥ (seedFullUpperProjection i₀ κ L *ᵥ x) =
      (m * seedBigGamma κ L : ℝ) • (seedFullUpperProjection i₀ κ L *ᵥ x) := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, seedFullUpperProjection_eigen i₀ hκ0 hκ1 hL,
    Matrix.smul_mulVec, smul_smul]
  ext i
  simp [Complex.real_smul, Complex.ofReal_mul]

/-- Exact compressed action on every original carrier coefficient vector. -/
theorem seed_compressed_capture_action {G : Matrix α α ℂ} (hG : G.PosDef) (b : α → ℂ)
    (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) {L : ℕ} (hL : 0 < L) (m : ℝ)
    (hB : ((m : ℂ) • seedBlock i₀ L κ).PosDef)
    (hB1 : (1 - (m : ℂ) • seedBlock i₀ L κ).PosSemidef) (v : ι → ℂ) (i : ι) :
    (seedCompressedCapture G b i₀ κ m L *ᵥ v) i =
      if i = i₀ then (seedCaptureValue G b κ m L : ℂ) * v i₀
      else (softCapture G b m : ℂ) * v i := by
  let x : ι ⊕ Fin L → ℂ := Sum.elim v 0
  let z : ι ⊕ Fin L → ℂ := Sum.elim (fun j => if j = i₀ then 0 else v j) 0
  let p := seedFullLowerProjection i₀ κ L *ᵥ x
  let q := seedFullUpperProjection i₀ κ L *ᵥ x
  let B := (m : ℂ) • seedBlock i₀ L κ
  let C := tensorCapture G b B
  have hsplit : x = z + p + q := seedFullProjections_carrier_split i₀ κ L v
  have hz : B *ᵥ z = (m : ℂ) • z := by
    dsimp only [B]
    rw [Matrix.smul_mulVec]
    congr 1
    exact seedBlock_carrier_perp i₀ L κ _ (by simp)
  have hp : B *ᵥ p = ((m * seedGamma κ L : ℝ) : ℂ) • p := by
    simpa only [B, p, Pi.smul_def, Complex.real_smul, smul_eq_mul] using seedLower_scaled_eigen i₀ hκ0 hκ1 hL m x
  have hq : B *ᵥ q = ((m * seedBigGamma κ L : ℝ) : ℂ) • q := by
    simpa only [B, q, Pi.smul_def, Complex.real_smul, smul_eq_mul] using seedUpper_scaled_eigen i₀ hκ0 hκ1 hL m x
  have hc : C *ᵥ x = (softCapture G b m : ℂ) • z +
      (softCapture G b (m * seedGamma κ L) : ℂ) • p +
      (softCapture G b (m * seedBigGamma κ L) : ℂ) • q := by
    rw [hsplit, Matrix.mulVec_add, Matrix.mulVec_add]
    rw [tensorCapture_eigen_of_contraction hG b hB hB1 hz,
      tensorCapture_eigen_of_contraction hG b hB hB1 hp,
      tensorCapture_eigen_of_contraction hG b hB hB1 hq]
  have hi := congrFun hc (Sum.inl i)
  have hleft : (seedCompressedCapture G b i₀ κ m L *ᵥ v) i = (C *ᵥ x) (Sum.inl i) := by
    simp [seedCompressedCapture, C, B, x, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hleft, hi]
  change (softCapture G b m : ℂ) * (if i = i₀ then 0 else v i) +
    (softCapture G b (m * seedGamma κ L) : ℂ) *
      (seedFullLowerProjection i₀ κ L *ᵥ Sum.elim v (0 : Fin L → ℂ)) (Sum.inl i) +
    (softCapture G b (m * seedBigGamma κ L) : ℂ) *
      (seedFullUpperProjection i₀ κ L *ᵥ Sum.elim v (0 : Fin L → ℂ)) (Sum.inl i) = _
  rw [seedFullLowerProjection_carrier, seedFullUpperProjection_carrier]
  by_cases hii : i = i₀
  · simp only [hii, if_true, mul_zero, zero_add, seedCaptureValue, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  · simp [hii]

/-- The compressed raw capture has exactly the two asserted diagonal values. -/
theorem seed_compressed_capture_diagonal {G : Matrix α α ℂ} (hG : G.PosDef) (b : α → ℂ)
    (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) {L : ℕ} (hL : 0 < L) (m : ℝ)
    (hB : ((m : ℂ) • seedBlock i₀ L κ).PosDef)
    (hB1 : (1 - (m : ℂ) • seedBlock i₀ L κ).PosSemidef) :
    seedCompressedCapture G b i₀ κ m L =
      Matrix.diagonal (fun i => if i = i₀ then (seedCaptureValue G b κ m L : ℂ) else (softCapture G b m : ℂ)) := by
  apply Matrix.ext
  intro i j
  have h := seed_compressed_capture_action hG b i₀ hκ0 hκ1 hL m hB hB1 (Pi.single j 1) i
  by_cases hi : i = i₀ <;> by_cases hij : i = j <;>
    simp_all [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.diagonal_apply,
      mul_ite, ite_mul, eq_comm]

end SchauderTranslates
