import Lean_Code.SchauderTranslates.TagPacket
import Lean_Code.SchauderTranslates.BoundedSpan

/-!
# Mean-one tags and lifted residuals (blueprint `tag:lift`, `tag:replicas`)

The minimum-variance polynomial of mean one in the nonconstant span of a scalar block of
gain `z` has variance `1/z`. Attaching it to every carrier row lifts a slow residual
`r = Σ_j c_j e_{λ_j}` to a packet vector with conditional mean `r` and squared norm
`‖r‖² + Σ_j |c_j|²/z`. Replicas in disjoint tag blocks have inner product `‖r‖²`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction



namespace ScalarData
variable {dt nt : ℕ} (s : ScalarData dt nt)

/-- Coefficients of the minimum-variance tag polynomial of mean one. -/
def liftCoefficients : Fin nt → ℂ := ((s.gain : ℂ)⁻¹) • (s.centeredGram⁻¹ *ᵥ s.mean)

theorem tagExpect_liftCoefficients (hz : 0 < s.gain) : s.tagExpect s.liftCoefficients = 1 := by
  rw [tagExpect_eq, liftCoefficients, dotProduct_smul, s.gain_quadratic_eq_real, smul_eq_mul]
  have : (s.gain : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  field_simp

theorem tagVariance_liftCoefficients (hz : 0 < s.gain) :
    s.tagVariance s.liftCoefficients = 1 / s.gain := by
  have hdet : IsUnit s.centeredGram.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp s.centeredGram_posDef.isUnit
  have hH : (s.centeredGram⁻¹)ᴴ = s.centeredGram⁻¹ := s.centeredGram_posDef.inv.isHermitian
  have hq : star (s.centeredGram⁻¹ *ᵥ s.mean) ⬝ᵥ s.centeredGram *ᵥ (s.centeredGram⁻¹ *ᵥ s.mean) =
      (s.gain : ℂ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
    exact s.gain_quadratic_eq_real
  rw [tagVariance, liftCoefficients, star_smul, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, hq]
  have hz' : (s.gain : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have he : (s.gain : ℂ)⁻¹ • star ((s.gain : ℂ)⁻¹) • (s.gain : ℂ) = ((1 / s.gain : ℝ) : ℂ) := by
    rw [smul_eq_mul, smul_eq_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  rw [he, Complex.ofReal_re]

theorem tagExpect_smul (a : ℂ) (x : Fin nt → ℂ) : s.tagExpect (a • x) = a * s.tagExpect x := by
  simp only [tagExpect, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem tagVariance_smul (a : ℂ) (x : Fin nt → ℂ) :
    s.tagVariance (a • x) = ‖a‖ ^ 2 * s.tagVariance x := by
  rw [tagVariance_eq_norm, tagVariance_eq_norm]
  have h : ∑ k, (a • x) k • s.normalizedCentered k = a • ∑ k, x k • s.normalizedCentered k := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  rw [h, norm_smul, mul_pow]

theorem tagVariance_eq_zero {x : Fin nt → ℂ} (hx : s.tagVariance x = 0) : x = 0 := by
  rw [tagVariance_eq_norm, sq_eq_zero_iff, norm_eq_zero] at hx
  have hli : LinearIndependent ℂ s.normalizedCentered := by
    apply Matrix.posDef_gram_iff_linearIndependent.mp
    rw [normalizedCentered_gram]
    exact s.centeredGram_posDef
  have h := linearIndependent_iff'.mp hli Finset.univ x (by simpa using hx)
  exact funext fun k => h k (Finset.mem_univ k)

end ScalarData

section Lift
variable {dt nt M J : ℕ} (s : ScalarData dt nt) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- The packet coefficients of the lifted residual. -/
def liftPacketCoeff (c : Fin J → ℂ) (q : Fin J × Fin nt) : ℂ := c q.1 * s.liftCoefficients q.2

/-- The lifted residual of `Σ_j c_j e_{λ_j}` in the tag blocks `blk`. -/
def liftVector (blk : Fin J → Fin M) (lam : Fin J → ℝ) (c : Fin J → ℂ) :
    BoundedMeasurableComplex (ℝ × (Fin M → UnitAddTorus (Fin dt))) :=
  BoundedMeasurableComplex.linearCombination (tagCarrier s blk lam) (liftPacketCoeff s c)

theorem liftVector_toL2 (blk : Fin J → Fin M) (lam : Fin J → ℝ) (c : Fin J → ℂ) :
    (liftVector s blk lam c).toL2 (tagLaw s ρ M) =
      ∑ q, liftPacketCoeff s c q • (tagCarrier s blk lam q).toL2 (tagLaw s ρ M) :=
  BoundedMeasurableComplex.toL2_linearCombination _ _ _

theorem liftPacketCoeff_row (c : Fin J → ℂ) (j : Fin J) :
    (fun k => liftPacketCoeff s c (j, k)) = c j • s.liftCoefficients := by
  funext k
  rfl

/-- The slow residual synthesized from the line characters. -/
def lineSynthesis (lam : Fin J → ℝ) (c : Fin J → ℂ) : Lp ℂ 2 ρ :=
  ∑ j, c j • (lineCharacter (lam j)).toL2 ρ

/-- Blueprint `tag:lift`: squared norm of the lifted residual. -/
theorem liftVector_norm_sq (hz : 0 < s.gain) (blk : Fin J → Fin M) (hblk : Function.Injective blk)
    (lam : Fin J → ℝ) (c : Fin J → ℂ) :
    ‖(liftVector s blk lam c).toL2 (tagLaw s ρ M)‖ ^ 2 =
      ‖lineSynthesis ρ lam c‖ ^ 2 + (∑ j, ‖c j‖ ^ 2) / s.gain := by
  rw [liftVector_toL2, tagPacket_norm_sq s ρ blk hblk]
  simp only [liftPacketCoeff_row, s.tagVariance_smul, s.tagExpect_smul,
    s.tagVariance_liftCoefficients hz, s.tagExpect_liftCoefficients hz, mul_one]
  rw [lineSynthesis, Finset.sum_div]
  simp only [mul_one_div]
  ring

theorem inner_sum_sum_eq {ι κ H : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a : ι → ℂ) (u : ι → H) (b : κ → ℂ) (v : κ → H) :
    inner ℂ (∑ q, a q • u q) (∑ q', b q' • v q') =
      ∑ q, ∑ q', star (a q) * b q' * inner ℂ (u q) (v q') := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro q _
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q' _
  rw [inner_smul_right, Complex.star_def]
  ring

theorem sum_prod_factor {J n : ℕ} (F : Fin J → Fin J → ℂ) (g h : Fin n → ℂ) :
    (∑ q : Fin J × Fin n, ∑ q' : Fin J × Fin n, F q.1 q'.1 * (g q.2 * h q'.2)) =
      ∑ j, ∑ j', F j j' * ((∑ k, g k) * ∑ k', h k') := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j' _
  rw [Finset.sum_comm]

/-- Lifts in disjoint tag blocks interact only through their common conditional mean. -/
theorem liftVector_inner_disjoint (hz : 0 < s.gain) (blk blk' : Fin J → Fin M)
    (hdisj : ∀ j j', blk j ≠ blk' j') (lam : Fin J → ℝ) (c : Fin J → ℂ) :
    inner ℂ ((liftVector s blk lam c).toL2 (tagLaw s ρ M))
        ((liftVector s blk' lam c).toL2 (tagLaw s ρ M)) =
      inner ℂ (lineSynthesis ρ lam c) (lineSynthesis ρ lam c) := by
  rw [liftVector_toL2, liftVector_toL2, lineSynthesis, inner_sum_sum_eq, inner_sum_sum_eq]
  have hE := s.tagExpect_liftCoefficients hz
  simp only [ScalarData.tagExpect] at hE
  have hE' : ∑ k, star (s.liftCoefficients k) * star (s.tagMean k) = 1 := by
    have := congrArg star hE
    rw [star_sum, star_one] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun k _ => by rw [star_mul', mul_comm])
  have hterm (q q' : Fin J × Fin nt) :
      star (liftPacketCoeff s c q) * liftPacketCoeff s c q' *
        inner ℂ ((tagCarrier s blk lam q).toL2 (tagLaw s ρ M))
          ((tagCarrier s blk' lam q').toL2 (tagLaw s ρ M)) =
      (star (c q.1) * c q'.1 *
          inner ℂ ((lineCharacter (lam q.1)).toL2 ρ) ((lineCharacter (lam q'.1)).toL2 ρ)) *
        ((star (s.liftCoefficients q.2) * star (s.tagMean q.2)) *
          (s.liftCoefficients q'.2 * s.tagMean q'.2)) := by
    rw [tagCarrier_inner, if_neg (hdisj _ _), zero_mul, zero_add]
    simp only [liftPacketCoeff, star_mul']
    ring
  simp_rw [hterm]
  have hf := sum_prod_factor (fun j j' => star (c j) * c j' *
      inner ℂ ((lineCharacter (lam j)).toL2 ρ) ((lineCharacter (lam j')).toL2 ρ))
    (fun k => star (s.liftCoefficients k) * star (s.tagMean k))
    (fun k => s.liftCoefficients k * s.tagMean k)
  rw [hf, hE']
  have hE2 : ∑ k', s.liftCoefficients k' * s.tagMean k' = 1 := by
    rw [← hE]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hE2]
  simp only [mul_one]

/-- Inner products of the lift with bounded slow functions see only the residual. -/
theorem liftVector_slow_inner (hz : 0 < s.gain) (blk : Fin J → Fin M) (lam : Fin J → ℝ)
    (c : Fin J → ℂ) (g : BoundedMeasurableComplex ℝ) :
    inner ℂ ((g.pullbackFst (Fin M → UnitAddTorus (Fin dt))).toL2 (tagLaw s ρ M))
        ((liftVector s blk lam c).toL2 (tagLaw s ρ M)) =
      inner ℂ (g.toL2 ρ) (lineSynthesis ρ lam c) := by
  rw [liftVector_toL2, lineSynthesis]
  simp only [inner_sum, inner_smul_right]
  have hmean (q : Fin J × Fin nt) :
      inner ℂ ((g.pullbackFst (Fin M → UnitAddTorus (Fin dt))).toL2 (tagLaw s ρ M))
        ((tagCarrier s blk lam q).toL2 (tagLaw s ρ M)) =
      s.tagMean q.2 * inner ℂ (g.toL2 ρ) ((lineCharacter (lam q.1)).toL2 ρ) := by
    rw [FiberKernel.slow_atom_inner, BoundedMeasurableComplex.inner_toL2,
      BoundedMeasurableComplex.inner_toL2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    change star (g t) * (tagKernel ℝ s M).mean (tagCarrier s blk lam q) t = _
    unfold tagCarrier
    rw [FiberKernel.mean_liftAt, scalarKernel_mean_tensor]
    change star (g t) * (character (lam q.1) t * s.tagMean q.2) = _
    simp only [lineCharacter_apply]
    ring
  simp_rw [hmean]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  have hE := s.tagExpect_liftCoefficients hz
  simp only [ScalarData.tagExpect] at hE
  simp only [liftPacketCoeff]
  calc (∑ k, c j * s.liftCoefficients k * (s.tagMean k *
        inner ℂ (g.toL2 ρ) ((lineCharacter (lam j)).toL2 ρ))) =
      c j * inner ℂ (g.toL2 ρ) ((lineCharacter (lam j)).toL2 ρ) *
        ∑ k, s.tagMean k * s.liftCoefficients k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = _ := by rw [hE, mul_one]

/-- The ordered carrier list of a replica is linearly independent. -/
theorem orderedCarrier_linearIndependent (blk : Fin J → Fin M) (hblk : Function.Injective blk)
    (lam : Fin J → ℝ) :
    LinearIndependent ℂ (fun i => (orderedCarrier s blk lam i).toL2 (tagLaw s ρ M)) := by
  rw [linearIndependent_iff']
  intro t g hg i hi
  classical
  set c : Fin (J * nt) → ℂ := fun i => if i ∈ t then g i else 0 with hc
  have hsum : ∑ i, c i • (orderedCarrier s blk lam i).toL2 (tagLaw s ρ M) = 0 := by
    rw [← hg, ← Finset.sum_subset (Finset.subset_univ t)]
    · apply Finset.sum_congr rfl
      intro i hit
      rw [hc]
      simp only [if_pos hit]
    · intro i _ hit
      rw [hc]
      simp only [if_neg hit, zero_smul]
  rw [orderedCarrier_sum] at hsum
  have hv := tagPacket_variance_le s ρ blk hblk lam (fun q => c (finProdFinEquiv q))
  rw [hsum, norm_zero, sq, mul_zero] at hv
  have hnn (j : Fin J) := s.tagVariance_nonneg (fun k => c (finProdFinEquiv (j, k)))
  have hzero (j : Fin J) : s.tagVariance (fun k => c (finProdFinEquiv (j, k))) = 0 := by
    have hs := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j) |>.mp
      (le_antisymm hv (Finset.sum_nonneg fun j _ => hnn j))
    exact hs j (Finset.mem_univ j)
  have hrow (j : Fin J) := s.tagVariance_eq_zero (hzero j)
  have hci : c i = 0 := by
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
    exact congrFun (hrow j) k
  rw [hc] at hci
  simpa only [if_pos hi] using hci

end Lift
end SchauderTranslates
