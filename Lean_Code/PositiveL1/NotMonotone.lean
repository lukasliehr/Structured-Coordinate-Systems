import Lean_Code.Basis.Criterion

/-!
# A Schauder basis of `L¹(ℝ)` consisting of non-negative functions is never monotone

Let `b` be a Schauder basis of `L¹(ℝ; 𝕜)` (`𝕜 = ℝ` or `ℂ`) all of whose vectors are a.e.
non-negative.  We show that some partial sum projection `b.proj N` has norm `> 1`
(`StructuredBases.exists_one_lt_norm_proj_of_nonneg_L1`), so that the basis constant is not `1`
(`StructuredBases.nnnormProjBound_ne_one_of_nonneg_L1`).

## Outline of the proof

Suppose `‖b.proj N‖ ≤ 1` for all `N`.  All inequalities between functions are understood
almost everywhere, and `0 ≤ x ≤ y` for `𝕜`-valued functions means that `x` and `y - x` are real
and non-negative (the order of `ComplexOrder`).  The integral of `x : Lp 𝕜 1 μ` is written
`L1.integral x`; it equals `∫ a, x a ∂μ` by `MeasureTheory.L1.integral_eq_integral`.

The first three steps are statements about an arbitrary contraction `P` of `L¹` together with
a vector `u` such that `P u = u`.  For `P = b.proj N` every linear combination `u` of
`b 0, …, b (N - 1)` is admissible, for instance `u = t • (b 0 + ⋯ + b (N - 1))`; only multiples
of `b 0`, which are fixed by all `b.proj N` with `N ≥ 1`, are needed in Steps 4–6.

1. `PositiveL1.integral_apply_eq_of_le`: if `0 ≤ x ≤ u` then `∫ P x = ∫ x`.
2. `PositiveL1.apply_nonneg_of_le`: if `0 ≤ x ≤ u` then `0 ≤ P x`.
3. `PositiveL1.apply_le_of_le`: if `0 ≤ x ≤ u` then `P x ≤ u`.
4. `PositiveL1.proj_one_eq_of_proj_eq`: if `u` is a multiple of `b 0`, `0 ≤ h ≤ u` and
   `b.proj N h = h` for some `N ≥ 1`, then `b.proj 1 h = h`.
5. `PositiveL1.proj_one_eq_of_le`: if `u` is a multiple of `b 0` and `0 ≤ x ≤ u`, then
   `b.proj 1 x = x`, i.e. `x = b.coord 0 x • b 0` (`PositiveL1.eq_coord_smul_of_le`).
6. Applying Step 5 to `x = 1_S • b 0` shows that the set `A = {b 0 > 0}` cannot be split by a
   measurable set `S` into two parts of positive measure
   (`PositiveL1.measure_pos_inter_eq_zero_or_diff_eq_zero`).  On the real line with a measure
   without atoms every set of positive measure is split by a ray `S = (-∞, t]`
   (`PositiveL1.exists_measure_inter_Iic_ne_zero`), which is the desired contradiction
   (`PositiveL1.not_forall_norm_proj_le_one`).

Steps 1–5 and the first half of Step 6 hold over an arbitrary measure space.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexOrder

namespace StructuredBases

namespace PositiveL1

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Two facts about scalars -/

/-- A scalar whose norm is at most `r` and whose real part is at least `r` equals `r`. -/
theorem eq_ofReal_of_norm_le_of_le_re {z : 𝕜} {r : ℝ} (h₁ : ‖z‖ ≤ r) (h₂ : r ≤ RCLike.re z) :
    z = (r : 𝕜) := by
  have h₃ : ‖z‖ = r := le_antisymm h₁ (h₂.trans (RCLike.re_le_norm z))
  calc
    z = ((‖z‖ : ℝ) : 𝕜) := RCLike.norm_le_re_iff_eq_norm.mp (h₁.trans h₂)
    _ = (r : 𝕜) := by rw [h₃]

/-- A scalar whose norm is at most its real part is non-negative. -/
theorem nonneg_of_norm_le_re {z : 𝕜} (h : ‖z‖ ≤ RCLike.re z) : 0 ≤ z := by
  have h₁ : z = ((‖z‖ : ℝ) : 𝕜) := RCLike.norm_le_re_iff_eq_norm.mp h
  rw [h₁]
  exact RCLike.ofReal_nonneg.mpr (norm_nonneg z)

/-! ### Contractions of `L¹` fixing a function -/

section Contraction

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- The integral of a non-negative element of `L¹` is its norm. -/
theorem integral_eq_norm_of_nonneg (x : Lp 𝕜 1 μ) (hx : ∀ᵐ a ∂μ, 0 ≤ x a) :
    L1.integral x = ((‖x‖ : ℝ) : 𝕜) := by
  rw [L1.integral_eq_integral, L1.norm_eq_integral_norm, ← integral_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [hx] with a ha
  exact (RCLike.norm_of_nonneg' ha).symm

/-- If `x ≤ u` a.e., then `u - x` is a.e. non-negative. -/
theorem ae_sub_nonneg_of_le {u x : Lp 𝕜 1 μ} (hxu : ∀ᵐ a ∂μ, x a ≤ u a) :
    ∀ᵐ a ∂μ, 0 ≤ (u - x) a := by
  filter_upwards [Lp.coeFn_sub u x, hxu] with a ha h
  rw [ha, Pi.sub_apply]
  exact sub_nonneg.mpr h

/-- If `0 ≤ x` a.e., then `u - x ≤ u` a.e. -/
theorem ae_sub_le_of_nonneg {u x : Lp 𝕜 1 μ} (hx0 : ∀ᵐ a ∂μ, 0 ≤ x a) :
    ∀ᵐ a ∂μ, (u - x) a ≤ u a := by
  filter_upwards [Lp.coeFn_sub u x, hx0] with a ha h
  rw [ha, Pi.sub_apply]
  exact sub_le_self _ h

/-- **Step 1 (integral preservation).** A contraction `P` of `L¹` with `P u = u` preserves the
integral of every `x` with `0 ≤ x ≤ u`.

Indeed `y ↦ ∫ P y` is a functional of norm at most one; its values at the non-negative
functions `x` and `u - x` have modulus at most `∫ x` and `∫ (u - x)`, and they add up to
`∫ P u = ∫ u = ∫ x + ∫ (u - x)`. -/
theorem integral_apply_eq_of_le (P : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) (hP : ‖P‖ ≤ 1)
    {u x : Lp 𝕜 1 μ} (hu : P u = u) (hx0 : ∀ᵐ a ∂μ, 0 ≤ x a) (hxu : ∀ᵐ a ∂μ, x a ≤ u a) :
    L1.integral (P x) = L1.integral x := by
  have hPle : ∀ y, ‖P y‖ ≤ ‖y‖ := fun y => by simpa using P.le_of_opNorm_le hP y
  have e₁ : L1.integral x = ((‖x‖ : ℝ) : 𝕜) := integral_eq_norm_of_nonneg x hx0
  have e₂ : L1.integral (u - x) = ((‖u - x‖ : ℝ) : 𝕜) :=
    integral_eq_norm_of_nonneg _ (ae_sub_nonneg_of_le hxu)
  have hsum : L1.integral (P x) + L1.integral (P (u - x))
      = ((‖x‖ : ℝ) : 𝕜) + ((‖u - x‖ : ℝ) : 𝕜) := by
    rw [← L1.integral_add, ← map_add, add_sub_cancel, hu, ← e₁, ← e₂, ← L1.integral_add,
      add_sub_cancel]
  have b₁ : ‖L1.integral (P x)‖ ≤ ‖x‖ := (L1.norm_integral_le _).trans (hPle x)
  have b₂ : ‖L1.integral (P (u - x))‖ ≤ ‖u - x‖ := (L1.norm_integral_le _).trans (hPle _)
  rw [e₁]
  refine eq_ofReal_of_norm_le_of_le_re b₁ ?_
  have hre := congrArg RCLike.re hsum
  simp only [map_add, RCLike.ofReal_re] at hre
  have := (RCLike.re_le_norm (L1.integral (P (u - x)))).trans b₂
  linarith

/-- **Step 2 (positivity).** A contraction `P` of `L¹` with `P u = u` maps every `x` with
`0 ≤ x ≤ u` to a non-negative function.

Indeed `∫ ‖P x‖ = ‖P x‖ ≤ ‖x‖ = ∫ x = ∫ P x` by Step 1, so that the non-negative function
`‖P x‖ - re (P x)` has integral `≤ 0`. -/
theorem apply_nonneg_of_le (P : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) (hP : ‖P‖ ≤ 1)
    {u x : Lp 𝕜 1 μ} (hu : P u = u) (hx0 : ∀ᵐ a ∂μ, 0 ≤ x a) (hxu : ∀ᵐ a ∂μ, x a ≤ u a) :
    ∀ᵐ a ∂μ, 0 ≤ P x a := by
  have hI := integral_apply_eq_of_le P hP hu hx0 hxu
  have e₁ : L1.integral x = ((‖x‖ : ℝ) : 𝕜) := integral_eq_norm_of_nonneg x hx0
  have hn : ‖P x‖ ≤ ‖x‖ := by simpa using P.le_of_opNorm_le hP x
  have hi : Integrable (P x : α → 𝕜) μ := L1.integrable_coeFn _
  have key : ∫ a, (‖P x a‖ - RCLike.re (P x a)) ∂μ = ‖P x‖ - ‖x‖ := by
    rw [integral_sub hi.norm hi.re, integral_re hi, ← L1.norm_eq_integral_norm,
      ← L1.integral_eq_integral, hI, e₁, RCLike.ofReal_re]
  have hnn : 0 ≤ᵐ[μ] fun a => ‖P x a‖ - RCLike.re (P x a) :=
    ae_of_all _ fun a => sub_nonneg.mpr (RCLike.re_le_norm _)
  have hz : ∫ a, (‖P x a‖ - RCLike.re (P x a)) ∂μ = 0 :=
    le_antisymm (by rw [key]; linarith) (integral_nonneg_of_ae hnn)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (hi.norm.sub hi.re)).mp hz
  filter_upwards [hae] with a ha
  exact nonneg_of_norm_le_re (sub_nonpos.mp (le_of_eq ha))

/-- **Step 3 (domination).** A contraction `P` of `L¹` with `P u = u` maps every `x` with
`0 ≤ x ≤ u` to a function dominated by `u`: apply Step 2 to `u - x`. -/
theorem apply_le_of_le (P : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) (hP : ‖P‖ ≤ 1)
    {u x : Lp 𝕜 1 μ} (hu : P u = u) (hx0 : ∀ᵐ a ∂μ, 0 ≤ x a) (hxu : ∀ᵐ a ∂μ, x a ≤ u a) :
    ∀ᵐ a ∂μ, P x a ≤ u a := by
  have h := apply_nonneg_of_le P hP hu (ae_sub_nonneg_of_le hxu) (ae_sub_le_of_nonneg hx0)
  rw [map_sub, hu] at h
  filter_upwards [h, Lp.coeFn_sub u (P x)] with a ha hsub
  rw [hsub, Pi.sub_apply] at ha
  exact sub_nonneg.mp ha

end Contraction

/-! ### Monotone bases of non-negative functions -/

section Basis

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- A multiple of the first basis vector is fixed by all projections `b.proj N`, `N ≥ 1`. -/
theorem proj_eq_of_proj_one_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (b : SchauderBasis 𝕜 X) {u : X} (hu : b.proj 1 u = u) {N : ℕ} (hN : 1 ≤ N) :
    b.proj N u = u := by
  calc
    b.proj N u = b.proj N (b.proj 1 u) := by rw [hu]
    _ = b.proj 1 u := by rw [b.proj_comp, min_eq_right hN]
    _ = u := hu

/-- **Step 4.** Let `b` be a monotone basis of `L¹` consisting of non-negative functions and
let `u` be a multiple of `b 0`.  If `0 ≤ h ≤ u` and `h` is fixed by `b.proj N` for some
`N ≥ 1`, then `h` is fixed by `b.proj 1`.

By induction on `N`: Step 1 for `b.proj N` gives `∫ b.proj N h = ∫ h`, whereas
`h - b.proj N h = b.coord N h • b N` and `∫ b N = ‖b N‖ ≠ 0`; hence `b.coord N h = 0`. -/
theorem proj_one_eq_of_proj_eq (b : SchauderBasis 𝕜 (Lp 𝕜 1 μ))
    (hb : ∀ n, ∀ᵐ a ∂μ, 0 ≤ b n a) (hP : ∀ N, ‖b.proj N‖ ≤ 1) {u h : Lp 𝕜 1 μ}
    (hu : b.proj 1 u = u) (hh0 : ∀ᵐ a ∂μ, 0 ≤ h a) (hhu : ∀ᵐ a ∂μ, h a ≤ u a) :
    ∀ N, 1 ≤ N → b.proj N h = h → b.proj 1 h = h := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact id
  | succ N hN ih =>
    intro hfix
    have hI := integral_apply_eq_of_le (b.proj N) (hP N) (proj_eq_of_proj_one_eq b hu hN) hh0 hhu
    have hsub : h - b.proj N h = b.coord N h • b N := by
      have := DFunLike.congr_fun (proj_succ_sub b N) h
      rwa [sub_apply, ContinuousLinearMap.smulRight_apply, hfix] at this
    have hint : L1.integral (b.coord N h • b N) = 0 := by
      rw [← hsub, L1.integral_sub, hI, sub_self]
    rw [L1.integral_smul, integral_eq_norm_of_nonneg _ (hb N), smul_eq_mul, mul_eq_zero] at hint
    have hne : ((‖b N‖ : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (basis_ne_zero b N))
    have hc : b.coord N h = 0 := hint.resolve_right hne
    apply ih
    rw [hc, zero_smul, sub_eq_zero] at hsub
    exact hsub.symm

/-- **Step 5.** Let `b` be a monotone basis of `L¹` consisting of non-negative functions and
let `u` be a multiple of `b 0`.  Every `x` with `0 ≤ x ≤ u` is fixed by `b.proj 1`.

For `N ≥ 1` the function `b.proj N x` is fixed by `b.proj N` and lies between `0` and `u`
(Steps 2 and 3), so `b.proj N x = b.proj 1 (b.proj N x) = b.proj 1 x` by Step 4; now let
`N → ∞`. -/
theorem proj_one_eq_of_le (b : SchauderBasis 𝕜 (Lp 𝕜 1 μ))
    (hb : ∀ n, ∀ᵐ a ∂μ, 0 ≤ b n a) (hP : ∀ N, ‖b.proj N‖ ≤ 1) {u x : Lp 𝕜 1 μ}
    (hu : b.proj 1 u = u) (hx0 : ∀ᵐ a ∂μ, 0 ≤ x a) (hxu : ∀ᵐ a ∂μ, x a ≤ u a) :
    b.proj 1 x = x := by
  have hconst : ∀ N, 1 ≤ N → b.proj N x = b.proj 1 x := by
    intro N hN
    have huN : b.proj N u = u := proj_eq_of_proj_one_eq b hu hN
    have h0 := apply_nonneg_of_le (b.proj N) (hP N) huN hx0 hxu
    have h1 := apply_le_of_le (b.proj N) (hP N) huN hx0 hxu
    have hfix : b.proj N (b.proj N x) = b.proj N x := by rw [b.proj_comp, min_self]
    have h := proj_one_eq_of_proj_eq b hb hP hu h0 h1 N hN hfix
    rw [b.proj_comp, min_eq_left hN] at h
    exact h.symm
  have hlim : Tendsto (fun N => b.proj N x) atTop (𝓝 (b.proj 1 x)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hconst N hN).symm
  exact tendsto_nhds_unique hlim (b.tendsto_proj x)

/-- **Step 5, reformulated.** Every `x` with `0 ≤ x ≤ u`, `u` a multiple of `b 0`, is a scalar
multiple of `b 0`. -/
theorem eq_coord_smul_of_le (b : SchauderBasis 𝕜 (Lp 𝕜 1 μ))
    (hb : ∀ n, ∀ᵐ a ∂μ, 0 ≤ b n a) (hP : ∀ N, ‖b.proj N‖ ≤ 1) {u x : Lp 𝕜 1 μ}
    (hu : b.proj 1 u = u) (hx0 : ∀ᵐ a ∂μ, 0 ≤ x a) (hxu : ∀ᵐ a ∂μ, x a ≤ u a) :
    x = b.coord 0 x • b 0 := by
  have h := proj_one_eq_of_le b hb hP hu hx0 hxu
  rw [SchauderBasis.proj_apply, Finset.sum_range_one] at h
  exact h.symm

/-- **Step 6, first half.** Let `b` be a monotone basis of `L¹` consisting of non-negative
functions.  Then the set `A = {b 0 > 0}` is not split by any measurable set `S` into two parts
of positive measure.

Indeed `x = 1_S • b 0` satisfies `0 ≤ x ≤ b 0`, so `x = c • b 0` for a scalar `c` by Step 5.
On `A ∩ S` this reads `b 0 = c • b 0`, which forces `c = 1` unless `A ∩ S` is a null set, and
on `A \ S` it reads `0 = c • b 0`, which forces `c = 0` unless `A \ S` is a null set. -/
theorem measure_pos_inter_eq_zero_or_diff_eq_zero (b : SchauderBasis 𝕜 (Lp 𝕜 1 μ))
    (hb : ∀ n, ∀ᵐ a ∂μ, 0 ≤ b n a) (hP : ∀ N, ‖b.proj N‖ ≤ 1) {S : Set α}
    (hS : MeasurableSet S) :
    μ ({a | 0 < b 0 a} ∩ S) = 0 ∨ μ ({a | 0 < b 0 a} \ S) = 0 := by
  -- the function `x = 1_S • b 0`
  have hmem : MemLp (S.indicator (b 0 : α → 𝕜)) 1 μ := (Lp.memLp (b 0)).indicator hS
  set x : Lp 𝕜 1 μ := hmem.toLp _
  have hxae : ∀ᵐ a ∂μ, x a = S.indicator (b 0 : α → 𝕜) a := hmem.coeFn_toLp
  have hx0 : ∀ᵐ a ∂μ, 0 ≤ x a := by
    filter_upwards [hxae, hb 0] with a ha h0
    rw [ha]
    exact Set.indicator_apply_nonneg fun _ => h0
  have hxu : ∀ᵐ a ∂μ, x a ≤ b 0 a := by
    filter_upwards [hxae, hb 0] with a ha h0
    rw [ha]
    exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => h0)
  -- `x` is a scalar multiple `c • b 0`
  have hxc := eq_coord_smul_of_le b hb hP (proj_apply_basis_of_lt b one_pos) hx0 hxu
  set c : 𝕜 := b.coord 0 x
  have hcae : ∀ᵐ a ∂μ, S.indicator (b 0 : α → 𝕜) a = c * b 0 a := by
    have h1 : ∀ᵐ a ∂μ, x a = (c • b 0 : Lp 𝕜 1 μ) a := by
      rw [← hxc]
      exact ae_of_all _ fun _ => rfl
    filter_upwards [h1, hxae, Lp.coeFn_smul c (b 0)] with a ha hxa hs
    rw [← hxa, ha, hs, Pi.smul_apply, smul_eq_mul]
  by_cases hc1 : c = 1
  · -- `c = 1`: then `b 0 = 0` a.e. outside `S`
    right
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcae] with a ha hmem'
    rw [Set.indicator_of_notMem hmem'.2, hc1, one_mul] at ha
    exact (ne_of_gt hmem'.1) ha.symm
  · -- `c ≠ 1`: then `b 0 = 0` a.e. on `S`
    left
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcae] with a ha hmem'
    rw [Set.indicator_of_mem hmem'.2] at ha
    have h0 : (1 - c) * b 0 a = 0 := by rw [sub_mul, one_mul, ← ha, sub_self]
    exact (ne_of_gt hmem'.1) ((mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hc1)))

end Basis

/-! ### The contradiction on the line -/

/-- **Step 6, second half.** For a measure on the real line without atoms, every set `A` of
positive measure is split by some ray `(-∞, t]` into two parts of positive measure.

Otherwise choose for every rational `q` a null set `B q` among `A ∩ (-∞, q]` and
`A \ (-∞, q]`.  Two points `a < a'` of `A` cannot both lie outside all the `B q`, as one sees
by taking a rational `q` between them.  So `A` is contained in the union of the countably many
null sets `B q` and of a set with at most one point. -/
theorem exists_measure_inter_Iic_ne_zero {μ : Measure ℝ} [NullSingletonClass μ] {A : Set ℝ}
    (hA : μ A ≠ 0) :
    ∃ t : ℝ, μ (A ∩ Set.Iic t) ≠ 0 ∧ μ (A \ Set.Iic t) ≠ 0 := by
  classical
  by_contra hcon
  have h : ∀ t : ℝ, ¬ μ (A ∩ Set.Iic t) = 0 → μ (A \ Set.Iic t) = 0 := fun t ht =>
    by_contra fun ht' => hcon ⟨t, ht, ht'⟩
  let B : ℚ → Set ℝ := fun q =>
    if μ (A ∩ Set.Iic (q : ℝ)) = 0 then A ∩ Set.Iic (q : ℝ) else A \ Set.Iic (q : ℝ)
  have hB : ∀ q, μ (B q) = 0 := by
    intro q
    by_cases hq : μ (A ∩ Set.Iic (q : ℝ)) = 0
    · simp only [B, if_pos hq]
      exact hq
    · simp only [B, if_neg hq]
      exact h q hq
  have hlt : ∀ a ∈ A \ ⋃ q, B q, ∀ a' ∈ A \ ⋃ q, B q, ¬ a < a' := by
    intro a ha a' ha' haa'
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn haa'
    by_cases hq : μ (A ∩ Set.Iic (q : ℝ)) = 0
    · refine ha.2 (Set.mem_iUnion.mpr ⟨q, ?_⟩)
      simp only [B, if_pos hq]
      exact ⟨ha.1, hq₁.le⟩
    · refine ha'.2 (Set.mem_iUnion.mpr ⟨q, ?_⟩)
      simp only [B, if_neg hq]
      exact ⟨ha'.1, not_le.mpr hq₂⟩
  have hsub : (A \ ⋃ q, B q).Subsingleton := fun a ha a' ha' =>
    le_antisymm (not_lt.mp (hlt a' ha' a ha)) (not_lt.mp (hlt a ha a' ha'))
  have hcover : A ⊆ (⋃ q, B q) ∪ (A \ ⋃ q, B q) := fun a ha => by
    by_cases ha' : a ∈ ⋃ q, B q
    · exact Or.inl ha'
    · exact Or.inr ⟨ha, ha'⟩
  exact hA (measure_mono_null hcover
    (measure_union_null (measure_iUnion_null hB) (hsub.measure_zero μ)))

/-- **Step 6.** On the real line with a measure without atoms, there is no monotone basis of
`L¹` consisting of non-negative functions. -/
theorem not_forall_norm_proj_le_one {μ : Measure ℝ} [NullSingletonClass μ]
    (b : SchauderBasis 𝕜 (Lp 𝕜 1 μ)) (hb : ∀ n, ∀ᵐ a ∂μ, 0 ≤ b n a) :
    ¬ ∀ N, ‖b.proj N‖ ≤ 1 := by
  intro hP
  -- the set `A = {b 0 > 0}` has positive measure because `b 0 ≠ 0`
  have hA : μ {a | 0 < b 0 a} ≠ 0 := by
    intro hA0
    have hzero : ∀ᵐ a ∂μ, b 0 a = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hA0, hb 0] with a ha h0
      by_contra hne
      exact ha (lt_of_le_of_ne h0 (Ne.symm hne))
    exact basis_ne_zero b 0 (Lp.eq_zero_iff_ae_eq_zero.mpr hzero)
  -- split it by a ray `S = (-∞, t]`
  obtain ⟨t, ht₁, ht₂⟩ := exists_measure_inter_Iic_ne_zero hA
  rcases measure_pos_inter_eq_zero_or_diff_eq_zero b hb hP
    (measurableSet_Iic (a := t)) with h | h
  · exact ht₁ h
  · exact ht₂ h

end PositiveL1

/-! ### Main results -/

/-- A Schauder basis of `L¹(ℝ)` consisting of non-negative functions is never monotone:
some partial sum projection has norm `> 1`. -/
theorem exists_one_lt_norm_proj_of_nonneg_L1 {𝕜 : Type*} [RCLike 𝕜]
    (b : SchauderBasis 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)))
    (hb : ∀ n, ∀ᵐ x : ℝ, 0 ≤ b n x) :
    ∃ N, 1 < ‖b.proj N‖ := by
  by_contra hcon
  exact PositiveL1.not_forall_norm_proj_le_one b hb fun N => not_lt.mp fun h => hcon ⟨N, h⟩

/-- Consequently its basis constant is not `1`. -/
theorem nnnormProjBound_ne_one_of_nonneg_L1 {𝕜 : Type*} [RCLike 𝕜]
    (b : SchauderBasis 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)))
    (hb : ∀ n, ∀ᵐ x : ℝ, 0 ≤ b n x) :
    b.nnnormProjBound ≠ 1 := by
  obtain ⟨N, hN⟩ := exists_one_lt_norm_proj_of_nonneg_L1 b hb
  exact nnnormProjBound_ne_one_of_lt b hN

end StructuredBases
