import Lean_Code.SchauderTranslates.SeedFullProjection

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem seedComplexPlane_spectral {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) {L : ℕ} (hL : 0 < L) :
    seedComplexPlane κ L =
      (seedGamma κ L : ℂ) • seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L) +
      (seedBigGamma κ L : ℂ) • (1 - seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)) := by
  have h := seedPlane_spectral_decomposition (seed_a_bounds hκ0 hκ1).1
    (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)
  apply Matrix.ext
  intro i j
  have he := congrArg Complex.ofReal (congrFun (congrFun h i) j)
  simpa only [seedComplexPlane, seedComplexLowerProjection, seedGamma, seedBigGamma,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Matrix.one_apply,
    apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using he

theorem seedComplexUpperProjection_eigen {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) :
    seedComplexPlane κ L * (1 - seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)) =
      (seedBigGamma κ L : ℂ) • (1 - seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)) := by
  have hp := seedComplexLowerProjection_eigen (seed_a_bounds hκ0 hκ1).1
    (seed_a_bounds hκ0 hκ1).2 (seedCoupling_pos hκ0 hL)
  change seedComplexPlane κ L * seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L) =
    (seedGamma κ L : ℂ) • seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L) at hp
  rw [Matrix.mul_sub, Matrix.mul_one, hp, seedComplexPlane_spectral hκ0 hκ1 hL, add_sub_cancel_left]

def seedFullUpperProjection (i₀ : ι) (κ : ℝ) (L : ℕ) : Matrix (ι ⊕ Fin L) (ι ⊕ Fin L) ℂ :=
  seedPlaneInclusion i₀ L * (1 - seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)) *
    (seedPlaneInclusion i₀ L)ᴴ

theorem seedFullUpperProjection_eigen (i₀ : ι) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {L : ℕ} (hL : 0 < L) :
    seedBlock i₀ L κ * seedFullUpperProjection i₀ κ L =
      (seedBigGamma κ L : ℂ) • seedFullUpperProjection i₀ κ L := by
  let U := seedPlaneInclusion i₀ L
  let Q := 1 - seedComplexLowerProjection (1 - κ ^ 2) (seedCoupling κ L)
  have hq : seedComplexPlane κ L * Q = (seedBigGamma κ L : ℂ) • Q :=
    seedComplexUpperProjection_eigen hκ0 hκ1 hL
  change seedBlock i₀ L κ * (U * Q * Uᴴ) = (seedBigGamma κ L : ℂ) • (U * Q * Uᴴ)
  calc
    _ = (seedBlock i₀ L κ * U) * Q * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = (U * seedComplexPlane κ L) * Q * Uᴴ := by rw [seedBlock_plane i₀ hL]
    _ = U * (seedComplexPlane κ L * Q) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hq, Matrix.mul_smul, Matrix.smul_mul]

theorem seedFullProjections_sum (i₀ : ι) (κ : ℝ) (L : ℕ) :
    seedFullLowerProjection i₀ κ L + seedFullUpperProjection i₀ κ L =
      seedPlaneInclusion i₀ L * (seedPlaneInclusion i₀ L)ᴴ := by
  simp only [seedFullLowerProjection, seedFullUpperProjection, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, add_sub_cancel]

theorem seedPlaneInclusion_adjoint_carrier (i₀ : ι) (L : ℕ) (v : ι → ℂ) :
    (seedPlaneInclusion i₀ L)ᴴ *ᵥ Sum.elim v (0 : Fin L → ℂ) = ![v i₀, 0] := by
  funext j
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, seedPlaneInclusion,
      Matrix.conjTranspose_apply, Complex.star_def]

/-- Compression of the lower spectral projection to the original carrier coordinates. -/
theorem seedFullLowerProjection_carrier (i₀ : ι) (κ : ℝ) (L : ℕ) (v : ι → ℂ) (i : ι) :
    (seedFullLowerProjection i₀ κ L *ᵥ Sum.elim v (0 : Fin L → ℂ)) (Sum.inl i) =
      if i = i₀ then (seedOmega κ L : ℂ) * v i₀ else 0 := by
  rw [seedFullLowerProjection, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    seedPlaneInclusion_adjoint_carrier, seedPlaneInclusion_carrier]
  by_cases hi : i = i₀
  · simp only [hi, if_true]
    simp [seedComplexLowerProjection, seedLowerProjection, seedOmega, seedSpectralMass,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Matrix.smul_apply,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  · simp [hi]

theorem seedFullUpperProjection_carrier (i₀ : ι) (κ : ℝ) (L : ℕ) (v : ι → ℂ) (i : ι) :
    (seedFullUpperProjection i₀ κ L *ᵥ Sum.elim v (0 : Fin L → ℂ)) (Sum.inl i) =
      if i = i₀ then (1 - (seedOmega κ L : ℂ)) * v i₀ else 0 := by
  have h := congrFun (congrArg (fun A : Matrix (ι ⊕ Fin L) (ι ⊕ Fin L) ℂ =>
    A *ᵥ Sum.elim v (0 : Fin L → ℂ)) (seedFullProjections_sum i₀ κ L)) (Sum.inl i)
  rw [Matrix.add_mulVec, Pi.add_apply, seedFullLowerProjection_carrier,
    ← Matrix.mulVec_mulVec, seedPlaneInclusion_adjoint_carrier, seedPlaneInclusion_carrier] at h
  by_cases hi : i = i₀
  · simp only [hi, if_true, Matrix.cons_val_zero] at h ⊢
    linear_combination h
  · simpa only [hi, if_false, zero_add] using h

/-- A carrier vector splits into its distinguished coordinate and the carrier complement. -/
theorem seedFullProjections_carrier_split (i₀ : ι) (κ : ℝ) (L : ℕ) (v : ι → ℂ) :
    Sum.elim v (0 : Fin L → ℂ) =
      Sum.elim (fun i => if i = i₀ then 0 else v i) (0 : Fin L → ℂ) +
        seedFullLowerProjection i₀ κ L *ᵥ Sum.elim v (0 : Fin L → ℂ) +
        seedFullUpperProjection i₀ κ L *ᵥ Sum.elim v (0 : Fin L → ℂ) := by
  rw [add_assoc, ← Matrix.add_mulVec, seedFullProjections_sum, ← Matrix.mulVec_mulVec,
    seedPlaneInclusion_adjoint_carrier]
  funext i
  cases i with
  | inl i =>
    simp only [Pi.add_apply, Sum.elim_inl, seedPlaneInclusion_carrier, Matrix.cons_val_zero]
    split_ifs <;> simp_all
  | inr j => simp [seedPlaneInclusion_seed]

end SchauderTranslates
