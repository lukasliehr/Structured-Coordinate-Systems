import Lean_Code.SchauderTranslates.SeedCarrierOrder
import Lean_Code.SchauderTranslates.SeedFullProjection
import Lean_Code.SchauderTranslates.SeedDecomposition

noncomputable section
open MeasureTheory Matrix Filter
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ]

/-- The seed-spectrum contract uses the actual weighted Gram and Euclidean coefficient space.
The asymptotic assertions keep `κ` fixed while the number of seed rows grows. -/
structure SeedSpectralData (c : SeedCarrier (ι := ι) ρ) (L : ℕ) (m κ : ℝ) : Prop where
  positive : (c.gram L m κ).PosDef
  contraction : (1 - c.gram L m κ).PosSemidef
  matrix : c.gram L m κ = (m : ℂ) • seedBlock c.distinguished L κ
  carrier : ∀ x : ι → ℂ, x c.distinguished = 0 →
    c.gram L m κ *ᵥ Sum.elim x (0 : Fin L → ℂ) = (m : ℂ) • Sum.elim x (0 : Fin L → ℂ)
  differences : ∀ y : Fin L → ℂ, (∑ j, y j) = 0 →
    c.gram L m κ *ᵥ Sum.elim (0 : ι → ℂ) y =
      ((m : ℂ) * (1 - (κ : ℂ) ^ 2)) • Sum.elim (0 : ι → ℂ) y
  plane_orthonormal : (seedPlaneInclusion c.distinguished L)ᴴ * seedPlaneInclusion c.distinguished L = 1
  plane_action : c.gram L m κ * seedPlaneInclusion c.distinguished L =
    (m : ℂ) • (seedPlaneInclusion c.distinguished L * seedComplexPlane κ L)
  decomposition : ∀ v : ι ⊕ Fin L → ℂ,
    ∃ (x : ι → ℂ) (y : Fin L → ℂ) (z : Fin 2 → ℂ),
      x c.distinguished = 0 ∧ (∑ j, y j) = 0 ∧
      v = Sum.elim x (0 : Fin L → ℂ) + Sum.elim (0 : ι → ℂ) y + seedPlaneInclusion c.distinguished L *ᵥ z
  projection_symmetric : (seedFullLowerProjection c.distinguished κ L).IsHermitian
  projection_idempotent : seedFullLowerProjection c.distinguished κ L * seedFullLowerProjection c.distinguished κ L =
    seedFullLowerProjection c.distinguished κ L
  projection_eigen : c.gram L m κ * seedFullLowerProjection c.distinguished κ L =
    ((m : ℂ) * (seedGamma κ L : ℂ)) • seedFullLowerProjection c.distinguished κ L
  projection_mass : ‖(seedFullLowerProjection c.distinguished κ L).toEuclideanLin
    (EuclideanSpace.single (Sum.inl c.distinguished) (1 : ℂ))‖ ^ 2 = seedOmega κ L
  eigen_product : seedGamma κ L * seedBigGamma κ L = 1 - κ ^ 2
  eigen_order : 0 < seedGamma κ L ∧ seedGamma κ L < 1 ∧ 1 < seedBigGamma κ L ∧ seedGamma κ L < seedBigGamma κ L
  big_bounds : κ ^ 2 / 2 * (L : ℝ) ≤ seedBigGamma κ L ∧ seedBigGamma κ L ≤ (κ ^ 2 + 2) * (L : ℝ)
  ratio_bounds : κ ^ 2 / (2 * (1 - κ ^ 2)) * (L : ℝ) ≤ seedRatio κ L ∧
    seedRatio κ L ≤ (κ ^ 2 + 2) / (1 - κ ^ 2) * (L : ℝ)
  gamma_limit : Tendsto (seedGamma κ) atTop (𝓝 0)
  big_limit : Tendsto (seedBigGamma κ) atTop atTop
  ratio_limit : Tendsto (seedRatio κ) atTop atTop
  mass_limit : Tendsto (seedOmega κ) atTop (𝓝 1)

/-- Blueprint `select:spectrum`: actual seed Gram, invariant decomposition,
Euclidean spectral mass, and explicit fixed-parameter asymptotics. -/
theorem seed_spectral_data (c : SeedCarrier (ι := ι) ρ) {L : ℕ} (hL : 0 < L)
    {m κ : ℝ} (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) :
    SeedSpectralData c L m κ := by
  have hB := c.gram_positive_contraction L hm hm1 hκ
  have hM := c.gram_eq_seedBlock L hm.le hκ
  refine {
    positive := hB.1
    contraction := hB.2.1
    matrix := hM
    carrier := ?_
    differences := ?_
    plane_orthonormal := seedPlaneInclusion_gram c.distinguished hL
    plane_action := ?_
    decomposition := ?_
    projection_symmetric := seedFullLowerProjection_hermitian c.distinguished κ L
    projection_idempotent := seedFullLowerProjection_idempotent c.distinguished hκ0 hκ1 hL
    projection_eigen := ?_
    projection_mass := seedFullLowerProjection_mass c.distinguished hκ0 hκ1 hL
    eigen_product := seedEigenvalues_product (1 - κ ^ 2) (seedCoupling_pos hκ0 hL)
    eigen_order := seed_spectral_order hκ0 hκ1 hL
    big_bounds := seedBigGamma_linear_bounds hκ0 hκ1 hL
    ratio_bounds := seedRatio_linear_bounds hκ0 hκ1 hL
    gamma_limit := seedGamma_tendsto_zero hκ0 hκ1
    big_limit := seedBigGamma_tendsto_atTop hκ0 hκ1
    ratio_limit := seedRatio_tendsto_atTop hκ0 hκ1
    mass_limit := seedOmega_tendsto_one hκ0 hκ1 }
  · intro x hx
    rw [hM, Matrix.smul_mulVec, seedBlock_carrier_perp c.distinguished L κ x hx]
  · intro y hy
    rw [hM, Matrix.smul_mulVec, seedBlock_seed_perp c.distinguished L κ y hy, smul_smul]
  · rw [hM, Matrix.smul_mul, seedBlock_plane c.distinguished hL]
  · intro v
    obtain ⟨x, y, z, hx, hy, hv, _⟩ := seedBlock_invariant_decomposition c.distinguished hL κ v
    exact ⟨x, y, z, hx, hy, hv⟩
  · rw [hM, Matrix.smul_mul, seedFullLowerProjection_eigen c.distinguished hκ0 hκ1 hL, smul_smul]

/-- The parameter prescribed in the seed construction satisfies every spectral hypothesis. -/
theorem seed_spectral_data_parameter (c : SeedCarrier (ι := ι) ρ) {L : ℕ} (hL : 0 < L)
    {m E : ℝ} (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L) (hE0 : 0 ≤ E)
    (hE : ∀ x, ‖c.e x‖ ≤ E) : SeedSpectralData c L m (seedParameter E) := by
  have hE1 := one_le_bound_of_unit_energy ρ c.e (c.measurable _) hE0 hE c.unit_energy
  have hκ := seedParameter_bounds hE1
  exact seed_spectral_data c hL hm hm1 hκ.1 (hκ.2.trans_lt (by norm_num))
    (fun x => seedParameter_scaled_bound hE1 (hE x))

end SchauderTranslates
