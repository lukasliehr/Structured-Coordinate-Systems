import Lean_Code.SchauderTranslates.Arrowhead

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem real_norm_smul_sq (a : ℝ) (x : E) : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Rotation followed by the inclusion of a unit vector in the second copy. -/
def skewCompressionMap (u : E) (α β : ℝ) : WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((α • WithLp.fstL 2 ℝ E ℝ -
      (β • toSpanSingleton ℝ u).comp (WithLp.sndL 2 ℝ E ℝ)).prod
    (β • WithLp.fstL 2 ℝ E ℝ +
      (α • toSpanSingleton ℝ u).comp (WithLp.sndL 2 ℝ E ℝ)))

@[simp] theorem skewCompressionMap_apply (u : E) (α β : ℝ) (x : WithLp 2 (E × ℝ)) :
    skewCompressionMap u α β x = WithLp.toLp 2
      (α • x.fst - (β * x.snd) • u, β • x.fst + (α * x.snd) • u) := by
  simp [skewCompressionMap, smul_smul]

theorem skewCompressionMap_norm (u : E) (hu : ‖u‖ = 1) (α β : ℝ)
    (hab : α ^ 2 + β ^ 2 = 1) (x : WithLp 2 (E × ℝ)) :
    ‖skewCompressionMap u α β x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [skewCompressionMap_apply, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖α • x.fst - (β * x.snd) • u‖ ^ 2 +
    ‖β • x.fst + (α * x.snd) • u‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [real_norm_smul_sq, real_inner_smul_left, real_inner_smul_right, hu,
    one_pow, mul_one, Real.norm_eq_abs, sq_abs]
  nlinarith [congrArg (fun r : ℝ => r * (‖x.fst‖ ^ 2 + x.snd ^ 2)) hab]

def hilbertDiagonal (J₀ J₁ : E →L[ℝ] E) : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((J₀.comp (WithLp.fstL 2 ℝ E E)).prod (J₁.comp (WithLp.sndL 2 ℝ E E)))

@[simp] theorem hilbertDiagonal_apply (J₀ J₁ : E →L[ℝ] E) (x : WithLp 2 (E × E)) :
    hilbertDiagonal J₀ J₁ x = WithLp.toLp 2 (J₀ x.fst, J₁ x.snd) := rfl

theorem hilbertDiagonal_norm_sq_le (J₀ J₁ : E →L[ℝ] E) :
    ‖hilbertDiagonal J₀ J₁‖ ^ 2 ≤ max (‖J₀‖ ^ 2) (‖J₁‖ ^ 2) := by
  apply opNorm_sq_le_of_pointwise _ (le_max_of_le_left (sq_nonneg _))
  intro x
  rw [hilbertDiagonal_apply, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖J₀ x.fst‖ ^ 2 + ‖J₁ x.snd‖ ^ 2 ≤ _
  have h₀ := pow_le_pow_left₀ (norm_nonneg _) (J₀.le_opNorm x.fst) 2
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (J₁.le_opNorm x.snd) 2
  have hmax₀ := mul_le_mul_of_nonneg_right (le_max_left (‖J₀‖ ^ 2) (‖J₁‖ ^ 2))
    (sq_nonneg ‖x.fst‖)
  have hmax₁ := mul_le_mul_of_nonneg_right (le_max_right (‖J₀‖ ^ 2) (‖J₁‖ ^ 2))
    (sq_nonneg ‖x.snd‖)
  nlinarith

section Complete
variable [CompleteSpace E]

theorem skewCompressionMap_adjoint_apply (u : E) (α β : ℝ) (y : WithLp 2 (E × E)) :
    ((skewCompressionMap u α β)†) y = WithLp.toLp 2
      (α • y.fst + β • y.snd, -β * inner ℝ u y.fst + α * inner ℝ u y.snd) := by
  apply ext_inner_right ℝ
  intro x
  rw [adjoint_inner_left]
  simp only [skewCompressionMap_apply, WithLp.prod_inner_apply, inner_sub_right,
    inner_add_right, inner_add_left, real_inner_smul_right, real_inner_smul_left,
    Real.inner_apply]
  change α * inner ℝ y.fst x.fst - (β * x.snd) * inner ℝ y.fst u +
      (β * inner ℝ y.snd x.fst + (α * x.snd) * inner ℝ y.snd u) =
    (α * inner ℝ y.fst x.fst + β * inner ℝ y.snd x.fst) +
      (-β * inner ℝ u y.fst * x.snd + α * inner ℝ u y.snd * x.snd)
  rw [real_inner_comm u y.fst, real_inner_comm u y.snd]
  ring

theorem skewCompressionMap_compression_norm (u : E) (hu : ‖u‖ = 1) (α β : ℝ)
    (hab : α ^ 2 + β ^ 2 = 1) (D : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E)) :
    ‖((skewCompressionMap u α β)†).comp (D.comp (skewCompressionMap u α β))‖ ≤ ‖D‖ := by
  have hQ : ‖skewCompressionMap u α β‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro x
    rw [skewCompressionMap_norm u hu α β hab, one_mul]
  have hQadj : ‖(skewCompressionMap u α β)†‖ ≤ 1 := by simpa using hQ
  calc
    _ ≤ ‖(skewCompressionMap u α β)†‖ * (‖D‖ * ‖skewCompressionMap u α β‖) :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖D‖ * 1) := by gcongr
    _ = ‖D‖ := by ring

/-- The compression of the endpoint diagonal is the smaller arrowhead. -/
theorem skewCompressionMap_diagonal (J₀ J₁ : E →L[ℝ] E)
    (h₀ : ∀ x y, inner ℝ (J₀ x) y = -inner ℝ x (J₀ y))
    (h₁ : ∀ x y, inner ℝ (J₁ x) y = -inner ℝ x (J₁ y))
    (u : E) (α β : ℝ) :
    ((skewCompressionMap u α β)†).comp
      ((hilbertDiagonal J₀ J₁).comp (skewCompressionMap u α β)) =
    skewArrowhead (α ^ 2 • J₀ + β ^ 2 • J₁) ((J₁ - J₀) u) (α * β) := by
  have hself₀ : inner ℝ u (J₀ u) = 0 := by
    have h := h₀ u u
    rw [real_inner_comm u (J₀ u)] at h
    linarith
  have hself₁ : inner ℝ u (J₁ u) = 0 := by
    have h := h₁ u u
    rw [real_inner_comm u (J₁ u)] at h
    linarith
  ext x
  simp only [comp_apply, skewCompressionMap_adjoint_apply, hilbertDiagonal_apply,
    skewCompressionMap_apply, skewArrowhead_apply]
  apply (WithLp.equiv 2 (E × ℝ)).injective
  apply Prod.ext
  · change α • J₀ (α • x.fst - (β * x.snd) • u) +
        β • J₁ (β • x.fst + (α * x.snd) • u) =
      (α ^ 2 • J₀ + β ^ 2 • J₁) x.fst + (α * β * x.snd) • ((J₁ - J₀) u)
    simp only [map_sub, map_add, map_smul, add_apply, sub_apply, smul_apply]
    module
  · change -β * inner ℝ u (J₀ (α • x.fst - (β * x.snd) • u)) +
        α * inner ℝ u (J₁ (β • x.fst + (α * x.snd) • u)) =
      -(α * β) * inner ℝ ((J₁ - J₀) u) x.fst
    simp only [map_sub, map_add, map_smul, sub_apply, inner_sub_right, inner_add_right,
      real_inner_smul_right, inner_sub_left, hself₀, hself₁, mul_zero, add_zero, sub_zero,
      h₀, h₁]
    ring

theorem compressed_skew_arrowhead_bound (J₀ J₁ : E →L[ℝ] E)
    (h₀ : ∀ x y, inner ℝ (J₀ x) y = -inner ℝ x (J₀ y))
    (h₁ : ∀ x y, inner ℝ (J₁ x) y = -inner ℝ x (J₁ y))
    (u : E) (hu : ‖u‖ = 1) (α β : ℝ) (hab : α ^ 2 + β ^ 2 = 1) :
    ‖skewArrowhead (α ^ 2 • J₀ + β ^ 2 • J₁) ((J₁ - J₀) u) (α * β)‖ ^ 2 ≤
      max (‖J₀‖ ^ 2) (‖J₁‖ ^ 2) := by
  rw [← skewCompressionMap_diagonal J₀ J₁ h₀ h₁]
  have hc := skewCompressionMap_compression_norm u hu α β hab (hilbertDiagonal J₀ J₁)
  have hs := pow_le_pow_left₀ (norm_nonneg
    (((skewCompressionMap u α β)†).comp
      ((hilbertDiagonal J₀ J₁).comp (skewCompressionMap u α β)))) hc 2
  exact hs.trans (hilbertDiagonal_norm_sq_le J₀ J₁)

end Complete

/-- The skew rank-two operator generated by an ordered pair of vectors. -/
def rankTwoSkew (x y : E) : E →L[ℝ] E := rankOne ℝ x y - rankOne ℝ y x

@[simp] theorem rankTwoSkew_apply (x y z : E) :
    rankTwoSkew x y z = inner ℝ y z • x - inner ℝ x z • y := by
  simp [rankTwoSkew, rankOne_apply]

theorem rankTwoSkew_skew (x y z w : E) :
    inner ℝ (rankTwoSkew x y z) w = -inner ℝ z (rankTwoSkew x y w) := by
  simp only [rankTwoSkew_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm z x, real_inner_comm z y]
  ring

theorem rankTwoSkew_square_diff (x y : E) (hxy : inner ℝ x y = 1) :
    rankTwoSkew x y (rankTwoSkew x y (x - y)) =
      -(‖x‖ ^ 2 * ‖y‖ ^ 2 - 1) • (x - y) := by
  have hyx : inner ℝ y x = 1 := by rw [real_inner_comm, hxy]
  simp only [rankTwoSkew_apply, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hxy, hyx]
  module

theorem rankTwoSkew_zero_of_degenerate (x y : E) (hxy : inner ℝ x y = 1)
    (hd : ‖x‖ ^ 2 * ‖y‖ ^ 2 = 1) : rankTwoSkew x y = 0 := by
  have hn : ‖‖y‖ ^ 2 • x - y‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_norm_smul_sq, real_inner_smul_left, hxy]
    nlinarith [congrArg (fun r : ℝ => ‖y‖ ^ 2 * r) hd]
  have he : ‖y‖ ^ 2 • x = y := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  ext z
  change inner ℝ y z • x - inner ℝ x z • y = 0
  conv_lhs => rw [← he]
  simp only [real_inner_smul_left]
  module

theorem normalized_pair_geometry (x y : E) (hxy : inner ℝ x y = 1)
    (hm : ‖x‖ ^ 2 ≤ 1) :
    0 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 - 1 ∧ 1 ≤ ‖y‖ ^ 2 ∧
      ‖x - y‖ ^ 2 = (‖x‖ ^ 2 * ‖y‖ ^ 2 - 1) +
        (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) := by
  have hcs : 1 ≤ ‖x‖ * ‖y‖ := by simpa [hxy] using real_inner_le_norm x y
  have hd : 1 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ * ‖y‖ - 1)]
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith [sq_nonneg ‖y‖]
  · rw [norm_sub_sq_real, hxy]
    ring

/-- A unit preimage in a two-dimensional skew-invariant plane. -/
theorem skew_unit_preimage (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = -inner ℝ x (A y))
    (v : E) {a : ℝ} (ha : 0 < a) (hv : 0 < ‖v‖)
    (hAA : A (A v) = -(a ^ 2) • v) :
    ∃ u : E, ‖u‖ = 1 ∧ A u = (a / ‖v‖) • v := by
  have hn : ‖A v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hA, hAA, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖A v‖ = a * ‖v‖ := by
    nlinarith [norm_nonneg (A v), mul_pos ha hv]
  refine ⟨(-(a * ‖v‖)⁻¹) • A v, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr (mul_pos ha hv)),
      hnorm, inv_mul_cancel₀ (ne_of_gt (mul_pos ha hv))]
  · rw [map_smul, hAA, smul_smul]
    congr 1
    field_simp

theorem skewArrowhead_smul (J : E →L[ℝ] E) (v : E) (a s : ℝ) :
    skewArrowhead J (a • v) s = skewArrowhead J v (s * a) := by
  ext x
  simp [skewArrowhead_apply, real_inner_smul_left, smul_smul, mul_assoc, mul_left_comm,
    mul_comm]

theorem skewArrowhead_zero_norm_sq_le (J : E →L[ℝ] E) (v : E) :
    ‖skewArrowhead J v 0‖ ^ 2 ≤ ‖J‖ ^ 2 := by
  apply opNorm_sq_le_of_pointwise _ (sq_nonneg _)
  intro x
  simp only [skewArrowhead_apply, zero_mul, zero_smul, add_zero, neg_zero]
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖J x.fst‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2 ≤ ‖J‖ ^ 2 * (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2)
  have h := pow_le_pow_left₀ (norm_nonneg (J x.fst)) (J.le_opNorm x.fst) 2
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  nlinarith [mul_nonneg (sq_nonneg ‖J‖) (sq_nonneg ‖x.snd‖)]

theorem skewArrowhead_zero_norm (J : E →L[ℝ] E) (v : E) :
    ‖skewArrowhead J v 0‖ = ‖J‖ := by
  apply le_antisymm
  · have h := skewArrowhead_zero_norm_sq_le J v
    nlinarith [norm_nonneg (skewArrowhead J v 0), norm_nonneg J]
  · apply opNorm_le_bound J (norm_nonneg (skewArrowhead J v 0))
    intro z
    have h := (skewArrowhead J v 0).le_opNorm (WithLp.toLp 2 (z, (0 : ℝ)))
    simpa [skewArrowhead_apply, WithLp.norm_toLp_fst] using h

/-- Endpoint compression plus arrowhead growth gives the split-row skew bound. -/
theorem rankTwo_skew_interpolation_bound [CompleteSpace E] [FiniteDimensional ℝ E]
    (J₀ J₁ : E →L[ℝ] E)
    (h₀ : ∀ x y, inner ℝ (J₀ x) y = -inner ℝ x (J₀ y))
    (h₁ : ∀ x y, inner ℝ (J₁ x) y = -inner ℝ x (J₁ y))
    (x y : E) (hxy : inner ℝ x y = 1) (hm : ‖x‖ ^ 2 ≤ 1)
    (hdiff : J₁ - J₀ = rankTwoSkew x y)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : α ^ 2 + β ^ 2 = 1) :
    ‖skewArrowhead (α ^ 2 • J₀ + β ^ 2 • J₁) (x - y) (α * β)‖ ^ 2 ≤
      max (‖J₀‖ ^ 2) (‖J₁‖ ^ 2) +
        (α * β) ^ 2 * (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) := by
  obtain ⟨hd, hh, hvgeom⟩ := normalized_pair_geometry x y hxy hm
  have hcost : 0 ≤ (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) :=
    mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hh)
  have hq : 0 ≤ α * β := mul_nonneg hα hβ
  have hJ : ∀ z w, inner ℝ ((α ^ 2 • J₀ + β ^ 2 • J₁) z) w =
      -inner ℝ z ((α ^ 2 • J₀ + β ^ 2 • J₁) w) := by
    intro z w
    simp only [add_apply, smul_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, h₀, h₁]
    ring
  by_cases hz : ‖x‖ ^ 2 * ‖y‖ ^ 2 - 1 = 0
  · have hA := rankTwoSkew_zero_of_degenerate x y hxy (by linarith)
    have he : J₁ = J₀ := sub_eq_zero.mp (hdiff.trans hA)
    have hJe : α ^ 2 • J₀ + β ^ 2 • J₁ = J₀ := by rw [he, ← add_smul, hab, one_smul]
    have hg := skew_arrowhead_bound (α ^ 2 • J₀ + β ^ 2 • J₁) hJ (x - y)
      (r := 0) (s := α * β) le_rfl hq
    have hn := skewArrowhead_zero_norm_sq_le (α ^ 2 • J₀ + β ^ 2 • J₁) (x - y)
    rw [hJe] at hn
    have hmax := le_max_left (‖J₀‖ ^ 2) (‖J₁‖ ^ 2)
    rw [hz, zero_add] at hvgeom
    rw [hJe, hvgeom] at hg
    rw [hJe]
    nlinarith
  · have hdpos : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 1 := lt_of_le_of_ne hd (Ne.symm hz)
    let a := Real.sqrt (‖x‖ ^ 2 * ‖y‖ ^ 2 - 1)
    have ha : 0 < a := Real.sqrt_pos.mpr hdpos
    have ha2 : a ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - 1 := Real.sq_sqrt hd
    have hv : 0 < ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
    have hale : a ≤ ‖x - y‖ := by nlinarith
    obtain ⟨u, hu, hAu⟩ := skew_unit_preimage (rankTwoSkew x y)
      (rankTwoSkew_skew x y) (x - y) ha hv (by
        rw [ha2]; exact rankTwoSkew_square_diff x y hxy)
    have hc := compressed_skew_arrowhead_bound J₀ J₁ h₀ h₁ u hu α β hab
    rw [hdiff, hAu, skewArrowhead_smul] at hc
    have hr : 0 ≤ α * β * (a / ‖x - y‖) := mul_nonneg hq (div_nonneg ha.le hv.le)
    have hrs : α * β * (a / ‖x - y‖) ≤ α * β := by
      exact mul_le_of_le_one_right hq ((div_le_one hv).mpr hale)
    have hg := skew_arrowhead_bound (α ^ 2 • J₀ + β ^ 2 • J₁) hJ (x - y) hr hrs
    have hrem : ((α * β) ^ 2 - (α * β * (a / ‖x - y‖)) ^ 2) * ‖x - y‖ ^ 2 =
        (α * β) ^ 2 * (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) := by
      have hvne : ‖x - y‖ ≠ 0 := ne_of_gt hv
      field_simp
      nlinarith [hvgeom]
    rw [hrem] at hg
    linarith

end SchauderTranslates
