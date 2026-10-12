import Lean_Code.SchauderTranslates.TagKernel
import Lean_Code.SchauderTranslates.SelectiveMeans

/-!
# Well-conditioned carrier packets (blueprint `tag:packet`)

The carrier of one replica consists of the products `e_{λ_j}(t) ψ_k(y_{b(j)})` of a line
character with a tag character in its own tag block. Different carrier rows use
independent tag blocks, so the packet norm splits into the centered tag variances plus
the norm of the explicit mean `Σ_j E_j e_{λ_j}`. No conditioning of the line Gram enters
the resulting prefix bound.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction

/-- A line character as a bounded representative. -/
def lineCharacter (ξ : ℝ) : BoundedMeasurableComplex ℝ where
  toFun := character ξ
  measurable := (continuous_character ξ).measurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le t := (norm_character ξ t).le

@[simp] theorem lineCharacter_apply (ξ t : ℝ) : lineCharacter ξ t = character ξ t := rfl

/-- Synthesis of finitely many norm-one-bounded line representatives, for a probability law. -/
theorem lineCharacter_norm (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (ξ : ℝ) :
    ‖(lineCharacter ξ).toL2 ρ‖ = 1 := by
  have h := BoundedMeasurableComplex.inner_toL2 ρ (lineCharacter ξ) (lineCharacter ξ)
  have hone : (fun t => star (lineCharacter ξ t) * lineCharacter ξ t) = fun _ => (1 : ℂ) := by
    funext t
    rw [Complex.star_def]
    simpa only [lineCharacter_apply, norm_character, Complex.ofReal_one, one_pow] using
      Complex.conj_mul' (character ξ t)
  rw [hone, integral_const, probReal_univ, one_smul] at h
  have hn := inner_self_eq_norm_sq (𝕜 := ℂ) ((lineCharacter ξ).toL2 ρ)
  rw [h] at hn
  have hn' : ‖(lineCharacter ξ).toL2 ρ‖ ^ 2 = 1 := by
    rw [← hn]
    simp
  have h0 := norm_nonneg ((lineCharacter ξ).toL2 ρ)
  nlinarith [sq_nonneg (‖(lineCharacter ξ).toL2 ρ‖ - 1)]

section ScalarTensor
variable {dt nt : ℕ} (s : ScalarData dt nt) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

theorem scalarKernel_integral_tensor (F : ℝ → ℂ) (G : UnitAddTorus (Fin dt) → ℂ) :
    (∫ p, F p.1 * G p.2 ∂(scalarKernel ℝ s).measure ρ) =
      (∫ t, F t ∂ρ) * s.nIntegral G := by
  rw [FiberKernel.integral_measure]
  have he (p : ℝ × UnitAddTorus (Fin dt)) : ((scalarKernel ℝ s).density p : ℂ) * (F p.1 * G p.2) =
      F p.1 * (((s.density p.2 / s.mass : ℝ) : ℂ) * G p.2) := by
    simp only [scalarKernel]
    ring
  simp_rw [he]
  exact integral_prod_mul (μ := ρ) (ν := torusMeasure dt) F
    (fun y => ((s.density y / s.mass : ℝ) : ℂ) * G y)

/-- One tag block: inner products of tensors factor. -/
theorem scalarKernel_inner_tensor (f f' : BoundedMeasurableComplex ℝ)
    (g g' : BoundedMeasurableComplex (UnitAddTorus (Fin dt))) :
    inner ℂ ((f.tensor g).toL2 ((scalarKernel ℝ s).measure ρ))
        ((f'.tensor g').toL2 ((scalarKernel ℝ s).measure ρ)) =
      inner ℂ (f.toL2 ρ) (f'.toL2 ρ) * s.nIntegral (fun y => star (g y) * g' y) := by
  rw [BoundedMeasurableComplex.inner_toL2, BoundedMeasurableComplex.inner_toL2]
  have he (p : ℝ × UnitAddTorus (Fin dt)) : star ((f.tensor g) p) * (f'.tensor g') p =
      (star (f p.1) * f' p.1) * (star (g p.2) * g' p.2) := by
    change star (f p.1 * g p.2) * (f' p.1 * g' p.2) = _
    rw [star_mul']
    ring
  simp_rw [he]
  exact scalarKernel_integral_tensor s ρ (fun t => star (f t) * f' t) (fun y => star (g y) * g' y)

theorem scalarKernel_mean_tensor (f : BoundedMeasurableComplex ℝ)
    (g : BoundedMeasurableComplex (UnitAddTorus (Fin dt))) (t : ℝ) :
    (scalarKernel ℝ s).mean (f.tensor g) t = f t * s.nIntegral g := by
  simp only [FiberKernel.mean, ScalarData.nIntegral]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change ((scalarKernel ℝ s).density (t, y) : ℂ) * (f t * g y) = _
  simp only [scalarKernel]
  ring

end ScalarTensor

section Packet
variable {dt nt M J : ℕ} (s : ScalarData dt nt) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- The joint law of the line variable and all tag blocks. -/
abbrev tagLaw (M : ℕ) : Measure (ℝ × (Fin M → UnitAddTorus (Fin dt))) :=
  (tagKernel ℝ s M).measure ρ

/-- The carrier row `(j,k)`: line character `j` times tag character `k` in block `blk j`. -/
def tagCarrier (blk : Fin J → Fin M) (lam : Fin J → ℝ) (q : Fin J × Fin nt) :
    BoundedMeasurableComplex (ℝ × (Fin M → UnitAddTorus (Fin dt))) :=
  FiberKernel.liftAt (blk q.1)
    ((lineCharacter (lam q.1)).tensor (torusCharacterRepresentative (s.frequencies q.2)))

/-- The line Gram entry. -/
def lineGram (lam : Fin J → ℝ) (j j' : Fin J) : ℂ :=
  inner ℂ ((lineCharacter (lam j)).toL2 ρ) ((lineCharacter (lam j')).toL2 ρ)

theorem lineGram_self (lam : Fin J → ℝ) (j : Fin J) : lineGram ρ lam j j = 1 := by
  rw [lineGram, inner_self_eq_norm_sq_to_K, lineCharacter_norm]
  simp

/-- Inner products of carrier rows in arbitrary tag blocks. -/
theorem tagCarrier_inner (blk blk' : Fin J → Fin M) (lam lam' : Fin J → ℝ)
    (q q' : Fin J × Fin nt) :
    inner ℂ ((tagCarrier s blk lam q).toL2 (tagLaw s ρ M))
        ((tagCarrier s blk' lam' q').toL2 (tagLaw s ρ M)) =
      (if blk q.1 = blk' q'.1 then s.centeredGram q.2 q'.2 else 0) *
          inner ℂ ((lineCharacter (lam q.1)).toL2 ρ) ((lineCharacter (lam' q'.1)).toL2 ρ) +
        star (s.tagMean q.2) * s.tagMean q'.2 *
          inner ℂ ((lineCharacter (lam q.1)).toL2 ρ) ((lineCharacter (lam' q'.1)).toL2 ρ) := by
  by_cases hb : blk q.1 = blk' q'.1
  · rw [if_pos hb]
    unfold tagCarrier
    rw [hb, FiberKernel.inner_liftAt_same, scalarKernel_inner_tensor]
    have hs : s.nIntegral (fun y => star (torusCharacterRepresentative (s.frequencies q.2) y) *
        torusCharacterRepresentative (s.frequencies q'.2) y) = s.tagSecond q.2 q'.2 := rfl
    rw [hs, s.tagSecond_eq_centered]
    ring
  · rw [if_neg hb, zero_mul, zero_add]
    unfold tagCarrier
    rw [FiberKernel.inner_liftAt_ne _ ρ hb, BoundedMeasurableComplex.inner_toL2,
      BoundedMeasurableComplex.inner_toL2]
    have hm (f : BoundedMeasurableComplex ℝ) (k : Fin nt) (t : ℝ) :
        ((scalarKernel ℝ s).meanRepresentative
          (f.tensor (torusCharacterRepresentative (s.frequencies k)))) t = f t * s.tagMean k := by
      change (scalarKernel ℝ s).mean _ t = _
      rw [scalarKernel_mean_tensor]
      rfl
    simp_rw [hm, star_mul', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring

/-- Expansion of a finite synthesis norm through inner products. -/
theorem norm_sq_sum_eq_inner {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ι → H) (y : ι → ℂ) :
    ‖∑ q, y q • v q‖ ^ 2 = (∑ q, ∑ q', star (y q) * y q' * inner ℂ (v q) (v q')).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← Matrix.star_dotProduct_gram_mulVec]
  simp only [dotProduct, Matrix.mulVec, Matrix.gram_apply, Pi.star_apply, Finset.mul_sum]
  change Complex.re _ = Complex.re _
  congr 1
  refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun q' _ => ?_))
  ring

/-- The packet norm: centered variances plus the explicit mean. -/
theorem tagPacket_norm_sq (blk : Fin J → Fin M) (hblk : Function.Injective blk)
    (lam : Fin J → ℝ) (x : Fin J × Fin nt → ℂ) :
    ‖∑ q, x q • (tagCarrier s blk lam q).toL2 (tagLaw s ρ M)‖ ^ 2 =
      ∑ j, s.tagVariance (fun k => x (j, k)) +
        ‖∑ j, s.tagExpect (fun k => x (j, k)) • (lineCharacter (lam j)).toL2 ρ‖ ^ 2 := by
  have hgram (q q' : Fin J × Fin nt) : inner ℂ ((tagCarrier s blk lam q).toL2 (tagLaw s ρ M))
      ((tagCarrier s blk lam q').toL2 (tagLaw s ρ M)) =
      (if q.1 = q'.1 then s.centeredGram q.2 q'.2 else 0) +
        star (s.tagMean q.2) * s.tagMean q'.2 * lineGram ρ lam q.1 q'.1 := by
    rw [tagCarrier_inner]
    by_cases hj : q.1 = q'.1
    · have h1 : inner ℂ ((lineCharacter (lam q.1)).toL2 ρ) ((lineCharacter (lam q'.1)).toL2 ρ) = 1 := by
        rw [hj]
        exact lineGram_self ρ lam q'.1
      rw [if_pos (congrArg blk hj), if_pos hj, h1, mul_one, lineGram, h1]
    · rw [if_neg (fun h => hj (hblk h)), if_neg hj, zero_mul, zero_add, zero_add]
      rfl
  rw [norm_sq_sum_eq_inner, norm_sq_sum_eq_inner]
  simp_rw [hgram]
  have hsplit : (∑ q : Fin J × Fin nt, ∑ q' : Fin J × Fin nt, star (x q) * x q' *
      ((if q.1 = q'.1 then s.centeredGram q.2 q'.2 else 0) +
        star (s.tagMean q.2) * s.tagMean q'.2 * lineGram ρ lam q.1 q'.1)) =
      (∑ j, star (fun k => x (j, k)) ⬝ᵥ s.centeredGram *ᵥ (fun k => x (j, k))) +
        ∑ j, ∑ j', star (s.tagExpect (fun k => x (j, k))) * s.tagExpect (fun k => x (j', k)) *
          lineGram ρ lam j j' := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k' _
        rw [if_pos rfl]
        ring
      · intro j' _ hj'
        apply Finset.sum_eq_zero
        intro k' _
        rw [if_neg (Ne.symm hj'), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    · simp only [ScalarData.tagExpect, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum,
        Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j' _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro k' _
      ring
  rw [hsplit, Complex.add_re, Complex.re_sum]
  rfl

/-- Each line synthesis has squared norm at most `J` times the coefficient energy. -/
theorem line_synthesis_norm_sq_le (lam : Fin J → ℝ) (a : Fin J → ℂ) :
    ‖∑ j, a j • (lineCharacter (lam j)).toL2 ρ‖ ^ 2 ≤ J * ∑ j, ‖a j‖ ^ 2 := by
  have h1 : ‖∑ j, a j • (lineCharacter (lam j)).toL2 ρ‖ ≤ ∑ j, ‖a j‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, lineCharacter_norm, mul_one]
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin J => ‖a j‖)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  calc ‖∑ j, a j • (lineCharacter (lam j)).toL2 ρ‖ ^ 2 ≤ (∑ j, ‖a j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- The packet norm dominates the sum of centered variances. -/
theorem tagPacket_variance_le (blk : Fin J → Fin M) (hblk : Function.Injective blk)
    (lam : Fin J → ℝ) (x : Fin J × Fin nt → ℂ) :
    ∑ j, s.tagVariance (fun k => x (j, k)) ≤
      ‖∑ q, x q • (tagCarrier s blk lam q).toL2 (tagLaw s ρ M)‖ ^ 2 := by
  rw [tagPacket_norm_sq s ρ blk hblk]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The packet norm is at most `1 + J z` times the sum of centered variances. -/
theorem tagPacket_norm_sq_le (blk : Fin J → Fin M) (hblk : Function.Injective blk)
    (lam : Fin J → ℝ) (x : Fin J × Fin nt → ℂ) :
    ‖∑ q, x q • (tagCarrier s blk lam q).toL2 (tagLaw s ρ M)‖ ^ 2 ≤
      (1 + J * s.gain) * ∑ j, s.tagVariance (fun k => x (j, k)) := by
  rw [tagPacket_norm_sq s ρ blk hblk]
  have h := line_synthesis_norm_sq_le ρ lam (fun j => s.tagExpect (fun k => x (j, k)))
  have h2 : ∑ j, ‖s.tagExpect (fun k => x (j, k))‖ ^ 2 ≤
      s.gain * ∑ j, s.tagVariance (fun k => x (j, k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => s.tagExpect_sq_le _
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith [mul_le_mul_of_nonneg_left h2 hJ]

/-- The ordered carrier list of one replica, row-major in `(j,k)`. -/
def orderedCarrier (blk : Fin J → Fin M) (lam : Fin J → ℝ) (i : Fin (J * nt)) :
    BoundedMeasurableComplex (ℝ × (Fin M → UnitAddTorus (Fin dt))) :=
  tagCarrier s blk lam (finProdFinEquiv.symm i)

theorem orderedCarrier_sum (blk : Fin J → Fin M) (lam : Fin J → ℝ) (c : Fin (J * nt) → ℂ) :
    ∑ i, c i • (orderedCarrier s blk lam i).toL2 (tagLaw s ρ M) =
      ∑ q, c (finProdFinEquiv q) • (tagCarrier s blk lam q).toL2 (tagLaw s ρ M) := by
  rw [← finProdFinEquiv.sum_comp]
  simp [orderedCarrier]

/-- Blueprint `tag:packet`: every ordered prefix of the actual carrier list. -/
theorem tag_packet_prefix (blk : Fin J → Fin M) (hblk : Function.Injective blk)
    (lam : Fin J → ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq : s.CenteredPrefixSqBound q) :
    FinitePrefixSqBound (fun i => (orderedCarrier s blk lam i).toL2 (tagLaw s ρ M))
      ((1 + J * s.gain) * q) := by
  intro κ c
  set x : Fin J × Fin nt → ℂ := fun p => c (finProdFinEquiv p) with hx
  set xc : Fin J × Fin nt → ℂ := fun p => if (finProdFinEquiv p).val < κ then
    c (finProdFinEquiv p) else 0 with hxc
  have hfull : ∑ i, c i • (orderedCarrier s blk lam i).toL2 (tagLaw s ρ M) =
      ∑ p, x p • (tagCarrier s blk lam p).toL2 (tagLaw s ρ M) := orderedCarrier_sum s ρ blk lam c
  have hcut : (∑ i, if i.val < κ then c i • (orderedCarrier s blk lam i).toL2 (tagLaw s ρ M) else 0) =
      ∑ p, xc p • (tagCarrier s blk lam p).toL2 (tagLaw s ρ M) := by
    have h := orderedCarrier_sum s ρ blk lam (fun i => if i.val < κ then c i else 0)
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hfull, hcut]
  have hrow (j : Fin J) : (fun k => xc (j, k)) =
      fun k : Fin nt => if k.val < κ - nt * j.val then x (j, k) else 0 := by
    funext k
    simp only [hxc, hx, finProdFinEquiv_apply_val]
    congr 1
    apply propext
    omega
  have hvar : ∑ j, s.tagVariance (fun k => xc (j, k)) ≤ q * ∑ j, s.tagVariance (fun k => x (j, k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [hrow j]
    exact s.tagVariance_prefix hq _ _
  have hg : 0 ≤ 1 + J * s.gain := by
    have := s.gain_nonneg
    positivity
  calc ‖∑ p, xc p • (tagCarrier s blk lam p).toL2 (tagLaw s ρ M)‖ ^ 2
      ≤ (1 + J * s.gain) * ∑ j, s.tagVariance (fun k => xc (j, k)) :=
        tagPacket_norm_sq_le s ρ blk hblk lam xc
    _ ≤ (1 + J * s.gain) * (q * ∑ j, s.tagVariance (fun k => x (j, k))) :=
        mul_le_mul_of_nonneg_left hvar hg
    _ = (1 + J * s.gain) * q * ∑ j, s.tagVariance (fun k => x (j, k)) := by ring
    _ ≤ (1 + J * s.gain) * q * ‖∑ p, x p • (tagCarrier s blk lam p).toL2 (tagLaw s ρ M)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (tagPacket_variance_le s ρ blk hblk lam x)
          (mul_nonneg hg hq0)

end Packet
end SchauderTranslates
