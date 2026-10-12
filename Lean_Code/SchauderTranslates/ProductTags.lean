import Lean_Code.SchauderTranslates.ProductSlow

/-!
# Tag replicas for the product extension (blueprint `tag:lift`, `tag:replicas`)

The tag data of the finite extension: the residual coefficients of the target, one
scalar tag block of gain `z`, and `N` replicas of all carrier tags in disjoint blocks.
Each replica carries the normalized lift `e_i` of the residual. We prove the replica
relations `‖e_i‖ = 1`, `⟪e_i, e_{i'}⟫ = α²` and `⟪e_i, g⟫ = ⟪r, g⟫/√D` for slow `g`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction

/-- The discrete choices of the tag stage. -/
structure TagSetup where
  w : Weight
  d : ℕ
  μ : Fin d → ℝ
  ξ : ℝ
  c : Fin (d + 1) → ℂ
  dt : ℕ
  nt : ℕ
  st : ScalarData dt nt
  N : ℕ

namespace TagSetup
variable (T : TagSetup)

abbrev ρ : Measure ℝ := lineLaw T.w
abbrev lam : Fin (T.d + 1) → ℝ := Fin.cons T.ξ T.μ
abbrev Mt : ℕ := T.N * (T.d + 1)

def blk (i : Fin T.N) (j : Fin (T.d + 1)) : Fin T.Mt := finProdFinEquiv (i, j)

abbrev Slow := ℝ × (Fin T.Mt → UnitAddTorus (Fin T.dt))
abbrev ρS : Measure T.Slow := tagLaw T.st T.ρ T.Mt

def resid : Lp ℂ 2 T.ρ := (lineSum T.lam T.c).toL2 T.ρ

def D : ℝ := ‖T.resid‖ ^ 2 + (∑ j, ‖T.c j‖ ^ 2) / T.st.gain

def cn : Fin (T.d + 1) → ℂ := ((Real.sqrt T.D)⁻¹ : ℂ) • T.c

/-- The normalized lift of the residual in replica `i`. -/
def lift (i : Fin T.N) : BoundedMeasurableComplex T.Slow := liftVector T.st (T.blk i) T.lam T.cn

/-- The ordered carrier list of replica `i`. -/
def carrier (i : Fin T.N) : Fin ((T.d + 1) * T.nt) → BoundedMeasurableComplex T.Slow :=
  orderedCarrier T.st (T.blk i) T.lam

def α : ℝ := ‖T.resid‖ / Real.sqrt T.D

/-- Validity of the tag stage. -/
structure Valid : Prop where
  c0 : T.c 0 = 1
  orth : ∀ i, inner ℂ ((lineCharacter (T.μ i)).toL2 T.ρ) T.resid = 0
  diff : (lineCharacter T.ξ).toL2 T.ρ - T.resid ∈
    Submodule.span ℂ (Set.range fun i => (lineCharacter (T.μ i)).toL2 T.ρ)
  resid_pos : 0 < ‖T.resid‖
  gain_pos : 0 < T.st.gain
  tag_poly : T.st.IsPolynomial
  gain_small : ((T.d + 1 : ℕ) : ℝ) * T.st.gain ≤ 1
  prefix_tag : ∃ q : ℝ, 0 ≤ q ∧ q ≤ 4 ∧ T.st.CenteredPrefixSqBound q
  N_pos : 0 < T.N
  N_big : 20 ≤ (T.N : ℝ) * T.α ^ 2

variable {T}

theorem blk_injective (i : Fin T.N) : Function.Injective (T.blk i) := by
  intro j j' h
  have := finProdFinEquiv.injective h
  exact (Prod.ext_iff.mp this).2

theorem blk_disjoint {i i' : Fin T.N} (h : i ≠ i') (j j' : Fin (T.d + 1)) :
    T.blk i j ≠ T.blk i' j' := by
  intro he
  have := finProdFinEquiv.injective he
  exact h (Prod.ext_iff.mp this).1

theorem lineSynthesis_cn : lineSynthesis T.ρ T.lam T.cn = ((Real.sqrt T.D)⁻¹ : ℂ) • T.resid := by
  simp only [lineSynthesis, cn, resid, lineSum_toL2, Pi.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]

theorem D_pos (hT : T.Valid) : 0 < T.D := by
  have hc : 1 ≤ ∑ j, ‖T.c j‖ ^ 2 := by
    have h0 := Finset.single_le_sum (f := fun j => ‖T.c j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ 0)
    simp only [hT.c0, norm_one, one_pow] at h0
    exact h0
  have := hT.gain_pos
  unfold D
  positivity

theorem lift_norm (hT : T.Valid) (i : Fin T.N) : ‖(T.lift i).toL2 T.ρS‖ = 1 := by
  have hD := D_pos hT
  have h := liftVector_norm_sq (M := T.Mt) T.st T.ρ hT.gain_pos (T.blk i) (blk_injective i) T.lam T.cn
  rw [lineSynthesis_cn, norm_smul] at h
  have hs : ‖((Real.sqrt T.D)⁻¹ : ℂ)‖ ^ 2 = T.D⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt hD.le]
  have hc : ∑ j, ‖T.cn j‖ ^ 2 = T.D⁻¹ * ∑ j, ‖T.c j‖ ^ 2 := by
    simp only [cn, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hs, Finset.mul_sum]
  rw [mul_pow, hs, hc] at h
  have h1 : ‖(T.lift i).toL2 T.ρS‖ ^ 2 = 1 := by
    change ‖(liftVector T.st (T.blk i) T.lam T.cn).toL2 (tagLaw T.st T.ρ T.Mt)‖ ^ 2 = 1
    rw [h]
    unfold D at hD ⊢
    field_simp
  have h0 := norm_nonneg ((T.lift i).toL2 T.ρS)
  nlinarith [sq_nonneg (‖(T.lift i).toL2 T.ρS‖ - 1)]

theorem lift_inner_ne (hT : T.Valid) {i i' : Fin T.N} (h : i ≠ i') :
    inner ℂ ((T.lift i).toL2 T.ρS) ((T.lift i').toL2 T.ρS) = ((T.α ^ 2 : ℝ) : ℂ) := by
  have hD := D_pos hT
  have hi := liftVector_inner_disjoint (M := T.Mt) T.st T.ρ hT.gain_pos (T.blk i) (T.blk i')
    (blk_disjoint h) T.lam T.cn
  change inner ℂ ((liftVector T.st (T.blk i) T.lam T.cn).toL2 (tagLaw T.st T.ρ T.Mt))
    ((liftVector T.st (T.blk i') T.lam T.cn).toL2 (tagLaw T.st T.ρ T.Mt)) = _
  rw [hi, lineSynthesis_cn, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have hs : (starRingEnd ℂ) ((Real.sqrt T.D : ℂ)⁻¹) * ((Real.sqrt T.D : ℂ)⁻¹) =
      ((T.D⁻¹ : ℝ) : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hD.le, Complex.ofReal_inv]
  rw [← mul_assoc, hs, α, div_pow, Real.sq_sqrt hD.le]
  push_cast
  rw [div_eq_inv_mul]
  norm_cast
  rw [Complex.ofReal_mul]
  rfl

/-- Slow functions see only the residual. -/
theorem lift_slow_inner (hT : T.Valid) (i : Fin T.N) (g : BoundedMeasurableComplex ℝ) :
    inner ℂ ((g.pullbackFst (Fin T.Mt → UnitAddTorus (Fin T.dt))).toL2 T.ρS)
        ((T.lift i).toL2 T.ρS) =
      ((Real.sqrt T.D)⁻¹ : ℂ) * inner ℂ (g.toL2 T.ρ) T.resid := by
  have h := liftVector_slow_inner (M := T.Mt) T.st T.ρ hT.gain_pos (T.blk i) T.lam T.cn g
  change inner ℂ ((g.pullbackFst (Fin T.Mt → UnitAddTorus (Fin T.dt))).toL2 (tagLaw T.st T.ρ T.Mt))
    ((liftVector T.st (T.blk i) T.lam T.cn).toL2 (tagLaw T.st T.ρ T.Mt)) = _
  rw [h, lineSynthesis_cn, inner_smul_right]

theorem lift_mem_span (i : Fin T.N) :
    (T.lift i).toL2 T.ρS ∈ atomSpan (fun k => (T.carrier i k).toL2 T.ρS) := by
  change (liftVector T.st (T.blk i) T.lam T.cn).toL2 (tagLaw T.st T.ρ T.Mt) ∈ _
  rw [liftVector_toL2]
  apply Submodule.sum_mem
  intro q _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨finProdFinEquiv q, ?_⟩
  simp [carrier, orderedCarrier]

theorem carrier_independent (i : Fin T.N) :
    LinearIndependent ℂ (fun k => (T.carrier i k).toL2 T.ρS) :=
  orderedCarrier_linearIndependent (M := T.Mt) T.st T.ρ (T.blk i) (blk_injective i) T.lam

theorem carrier_prefix (hT : T.Valid) (i : Fin T.N) :
    FinitePrefixSqBound (fun k => (T.carrier i k).toL2 T.ρS) 8 := by
  obtain ⟨q, hq0, hq4, hq⟩ := hT.prefix_tag
  have h := tag_packet_prefix (M := T.Mt) T.st T.ρ (T.blk i) (blk_injective i) T.lam hq0 hq
  apply h.mono
  have hg := hT.gain_small
  have hg0 := hT.gain_pos.le
  nlinarith

/-- A common pointwise bound for all lifts. -/
def liftBound : ℝ := ∑ q : Fin (T.d + 1) × Fin T.nt, ‖liftPacketCoeff T.st T.cn q‖

theorem lift_bound_le (i : Fin T.N) (x : T.Slow) : ‖T.lift i x‖ ≤ T.liftBound := by
  refine ((T.lift i).norm_le x).trans (le_of_eq ?_)
  change (∑ q, ‖liftPacketCoeff T.st T.cn q‖ * (tagCarrier T.st (T.blk i) T.lam q).bound) = _
  apply Finset.sum_congr rfl
  intro q _
  have : (tagCarrier T.st (T.blk i) T.lam q).bound = 1 := by
    simp [tagCarrier, FiberKernel.liftAt, BoundedMeasurableComplex.comp,
      BoundedMeasurableComplex.tensor, BoundedMeasurableComplex.mul, lineCharacter,
      torusCharacterRepresentative]
  rw [this, mul_one]

/-- The coupling parameter of all engines. -/
def κ (T : TagSetup) : ℝ := seedParameter (max 1 T.liftBound)

theorem κ_pos : 0 < T.κ := (seedParameter_bounds (le_max_left 1 T.liftBound)).1

theorem κ_lt_one : T.κ < 1 :=
  (seedParameter_bounds (le_max_left 1 T.liftBound)).2.trans_lt (by norm_num)

theorem coupling (i : Fin T.N) (x : T.Slow) : ‖(T.κ : ℂ) * T.lift i x‖ ≤ 1 / 4 :=
  seedParameter_scaled_bound (le_max_left 1 T.liftBound)
    ((lift_bound_le i x).trans (le_max_right 1 T.liftBound))

end TagSetup
end SchauderTranslates
