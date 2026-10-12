import Lean_Code.PositiveBiorthogonal.Haar

/-! The sharp estimate on the Haar vector, including the p = 1 endpoint. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
theorem holder_reciprocal_reals [ENNReal.HolderConjugate p q] :
    1 / p.toReal + 1 / q.toReal = 1 := by
  have hp0 := ENNReal.HolderConjugate.ne_zero p q
  have hq0 := ENNReal.HolderConjugate.ne_zero q p
  have he := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one p q)
  rw [ENNReal.toReal_add (by simpa using hp0) (by simpa using hq0)] at he
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_one, one_div] using he

theorem IntervalCell.normalizedIndicator_norm (D : IntervalCell) (hpfin : p ≠ ∞) :
    ‖(D.normalizedIndicator : L 𝕜 p)‖ = D.length ^ (1 / p.toReal - 1) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  rw [IntervalCell.normalizedIndicator, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos D.length_pos,
    D.indicator_norm hp0 hpfin, ← Real.rpow_neg_one, ← Real.rpow_add D.length_pos]
  congr 1
  ring

theorem IntervalCell.normalizedIndicator_norm_power (D : IntervalCell) (hpfin : p ≠ ∞) :
    ‖(D.normalizedIndicator : L 𝕜 p)‖ ^ p.toReal = D.length ^ (1 - p.toReal) := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hpfin
  rw [D.normalizedIndicator_norm hpfin, ← Real.rpow_mul D.length_pos.le]
  congr 1
  field_simp

omit [Fact (1 ≤ p)] in
theorem IntervalCell.normalizedIndicator_supported (D : IntervalCell) :
    ∀ᵐ x : ℝ, x ∉ D.carrier → (D.normalizedIndicator : L 𝕜 p) x = 0 := by
  filter_upwards [Lp.coeFn_smul ((D.length : 𝕜)⁻¹) (D.indicator : L 𝕜 p),
    D.coe_indicator (𝕜 := 𝕜) (p := p)] with x hs hi
  intro hx
  change (((D.length : 𝕜)⁻¹) • D.indicator : L 𝕜 p) x = 0
  rw [hs, Pi.smul_apply, hi]
  simp [hx]

theorem IntervalSplit.haarH_norm_power (S : IntervalSplit) (hpfin : p ≠ ∞) :
    ‖(S.haarH : L 𝕜 p)‖ ^ p.toReal =
      S.leftChild.length ^ (1 - p.toReal) + S.rightChild.length ^ (1 - p.toReal) := by
  have hd : ∀ᵐ x : ℝ, (S.leftChild.normalizedIndicator : L 𝕜 p) x = 0 ∨
      (-S.rightChild.normalizedIndicator : L 𝕜 p) x = 0 := by
    filter_upwards [S.leftChild.normalizedIndicator_supported (𝕜 := 𝕜) (p := p),
      S.rightChild.normalizedIndicator_supported (𝕜 := 𝕜) (p := p),
      Lp.coeFn_neg (S.rightChild.normalizedIndicator : L 𝕜 p)] with x hb hc hn
    by_cases hx : x ∈ S.leftChild.carrier
    · right
      have hxC : x ∉ S.rightChild.carrier := fun hc => Set.disjoint_left.mp S.children_disjoint hx hc
      rw [hn, Pi.neg_apply, hc hxC, neg_zero]
    · exact Or.inl (hb hx)
  rw [IntervalSplit.haarH, sub_eq_add_neg, norm_rpow_add_of_ae_disjoint hpfin _ _ hd, norm_neg,
    S.leftChild.normalizedIndicator_norm_power hpfin, S.rightChild.normalizedIndicator_norm_power hpfin]

theorem IntervalSplit.haarH_norm_power_le (S : IntervalSplit) (hpfin : p ≠ ∞)
    (hθ : S.ratio ≤ 1 / 2) :
    ‖(S.haarH : L 𝕜 p)‖ ^ p.toReal ≤ 2 * S.leftChild.length ^ (1 - p.toReal) := by
  have hr : 1 ≤ p.toReal := by
    have he := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpfin).mpr (Fact.out : 1 ≤ p)
    simpa only [ENNReal.toReal_one] using he
  have hlen : S.leftChild.length ≤ S.rightChild.length := by
    rw [S.left_length_eq, S.right_length_eq]
    exact mul_le_mul_of_nonneg_right (by linarith) S.parent.length_pos.le
  rw [S.haarH_norm_power hpfin]
  have he := Real.rpow_le_rpow_of_nonpos S.leftChild.length_pos hlen (by linarith : 1 - p.toReal ≤ 0)
  linarith

theorem haar_bound_power_identity (r s θ ℓ : ℝ) (hr : 0 < r)
    (hrec : 1 / r + 1 / s = 1) (hθ : 0 < θ) (hℓ : 0 < ℓ) :
    (2 * θ ^ (-(1 / s)) * ℓ ^ (-(1 / s))) ^ r = 2 * (θ * (ℓ / 2)) ^ (1 - r) := by
  have he : (-(1 / s)) * r = 1 - r := by
    have hh := congrArg (fun t : ℝ => t * r) hrec
    rw [add_mul, one_div_mul_cancel hr.ne', one_mul] at hh
    linarith
  have h2 : (2 : ℝ) ^ r = 2 / (2 : ℝ) ^ (1 - r) := by
    apply (eq_div_iff (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne').mpr
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show r + (1 - r) = 1 by ring, Real.rpow_one]
  rw [Real.mul_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hθ.le _)) (Real.rpow_nonneg hℓ.le _),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hθ.le _),
    ← Real.rpow_mul hθ.le, ← Real.rpow_mul hℓ.le, he,
    Real.mul_rpow hθ.le (by positivity : (0 : ℝ) ≤ ℓ / 2),
    Real.div_rpow hℓ.le (by norm_num : (0 : ℝ) ≤ 2), h2]
  ring

theorem IntervalSplit.haarH_norm_bound [ENNReal.HolderConjugate p q]
    (S : IntervalSplit) (hpfin : p ≠ ∞) (hθ : S.ratio ≤ 1 / 2)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hD : ℓ / 2 ≤ S.parent.length) :
    ‖(S.haarH : L 𝕜 p)‖ ≤ 2 * S.ratio ^ (-(1 / q.toReal)) * ℓ ^ (-(1 / q.toReal)) := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hpfin
  have hr1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpfin).mpr (Fact.out : 1 ≤ p)
  have hB : S.ratio * (ℓ / 2) ≤ S.leftChild.length := by
    rw [S.left_length_eq]
    exact mul_le_mul_of_nonneg_left hD S.ratio_pos.le
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg S.ratio_pos.le _))
      (Real.rpow_nonneg hℓ.le _)) hr).mp
  calc
    _ ≤ 2 * S.leftChild.length ^ (1 - p.toReal) := S.haarH_norm_power_le hpfin hθ
    _ ≤ 2 * (S.ratio * (ℓ / 2)) ^ (1 - p.toReal) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_nonpos (mul_pos S.ratio_pos (by positivity)) hB (by linarith)
    _ = _ := (haar_bound_power_identity p.toReal q.toReal S.ratio ℓ hr
      (holder_reciprocal_reals (p := p) (q := q)) S.ratio_pos hℓ).symm

theorem geometricSplit_ratio (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (geometricSplit D θ hθ hθ1 k).ratio = θ := by
  rw [IntervalSplit.ratio, geometricSplit_left_length,
    mul_div_cancel_right₀ _ (geometricSplit D θ hθ hθ1 k).parent.length_pos.ne']

end PositiveBiorthogonal
