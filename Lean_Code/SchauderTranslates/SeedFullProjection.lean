import Lean_Code.SchauderTranslates.SeedPlaneInclusion
import Lean_Code.SchauderTranslates.SeedComplexProjection
import Lean_Code.SchauderTranslates.MatrixColumnIsometry

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lower-plane spectral projection on the full carrier-plus-seed coefficient space. -/
def seedFullLowerProjection (i₀ : ι) (κ : ℝ) (L : ℕ) : Matrix (ι ⊕ Fin L) (ι ⊕ Fin L) ℂ :=
  seedPlaneInclusion i₀ L * seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L) *
    (seedPlaneInclusion i₀ L)ᴴ

theorem seedFullLowerProjection_hermitian (i₀ : ι) (κ : ℝ) (L : ℕ) :
    (seedFullLowerProjection i₀ κ L).IsHermitian := by
  change (seedFullLowerProjection i₀ κ L)ᴴ = _
  simp only [seedFullLowerProjection, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (seedComplexLowerProjection_hermitian _ _).eq, Matrix.mul_assoc]

theorem seedFullLowerProjection_idempotent (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) :
    seedFullLowerProjection i₀ κ L * seedFullLowerProjection i₀ κ L = seedFullLowerProjection i₀ κ L := by
  let U := seedPlaneInclusion i₀ L
  let P := seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)
  have hU : Uᴴ * U = 1 := seedPlaneInclusion_gram i₀ hL
  have hP : P * P = P := seedComplexLowerProjection_idempotent
    (seed_a_bounds hκ0 hκ1).1 (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)
  change U * P * Uᴴ * (U * P * Uᴴ) = U * P * Uᴴ
  calc
    _ = U * (P * (Uᴴ * U) * P) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, hP]

theorem seedFullLowerProjection_eigen (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) :
    seedBlock i₀ L κ * seedFullLowerProjection i₀ κ L =
      (seedGamma κ L : ℂ) • seedFullLowerProjection i₀ κ L := by
  let U := seedPlaneInclusion i₀ L
  let P := seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)
  have hp : seedComplexPlane κ L * P = (seedGamma κ L : ℂ) • P :=
    seedComplexLowerProjection_eigen (seed_a_bounds hκ0 hκ1).1
      (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)
  change seedBlock i₀ L κ * (U * P * Uᴴ) = (seedGamma κ L : ℂ) • (U * P * Uᴴ)
  calc
    _ = (seedBlock i₀ L κ * U) * P * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = (U * seedComplexPlane κ L) * P * Uᴴ := by rw [seedBlock_plane i₀ hL]
    _ = U * (seedComplexPlane κ L * P) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hp, Matrix.mul_smul, Matrix.smul_mul]

theorem seedPlaneInclusion_first (i₀ : ι) (L : ℕ) :
    (seedPlaneInclusion i₀ L).toEuclideanLin (EuclideanSpace.single 0 (1 : ℂ)) =
      EuclideanSpace.single (Sum.inl i₀) 1 := by
  ext i
  cases i with
  | inl i => simp [Matrix.toEuclideanLin_apply, seedPlaneInclusion, EuclideanSpace.single]
  | inr j => simp [Matrix.toEuclideanLin_apply, seedPlaneInclusion, EuclideanSpace.single]

/-- Spectral mass computed in the full Euclidean coefficient space of the actual Gram. -/
theorem seedFullLowerProjection_mass (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) :
    ‖(seedFullLowerProjection i₀ κ L).toEuclideanLin (EuclideanSpace.single (Sum.inl i₀) (1 : ℂ))‖ ^ 2 =
      seedOmega κ L := by
  let U := seedPlaneInclusion i₀ L
  let P := seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)
  have hU : Uᴴ * U = 1 := seedPlaneInclusion_gram i₀ hL
  have hmul : seedFullLowerProjection i₀ κ L * U = U * P := by
    change U * P * Uᴴ * U = U * P
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  have hv (x : EuclideanSpace ℂ (Fin 2)) :
      (seedFullLowerProjection i₀ κ L).toEuclideanLin (U.toEuclideanLin x) =
        U.toEuclideanLin (P.toEuclideanLin x) := by
    simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
    rw [Matrix.mulVec_mulVec, hmul, ← Matrix.mulVec_mulVec]
  rw [← seedPlaneInclusion_first i₀ L]
  change ‖(seedFullLowerProjection i₀ κ L).toEuclideanLin (U.toEuclideanLin _)‖ ^ 2 = _
  rw [hv, matrix_orthonormal_columns_norm hU]
  exact seedComplexLowerProjection_mass (seed_a_bounds hκ0 hκ1).1
    (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)

end SchauderTranslates
