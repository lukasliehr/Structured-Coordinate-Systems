import Lean_Code.SchauderTranslates.ScalarPrefixes

/-!
# Engine algebra

Abstract Hilbert-space core of `tag:engines`, `tag:angle` and the distance part of
`extend:product`.

The old vectors `x` lie in a slow space `Sl`. An engine atom is `T c p + R c p` with
`T c p ∈ Sl` and `R c p ⟂ Sl`, and the fast parts of different engines are orthogonal.
For engine coefficients `b` write `zT b = ∑ c, ∑ p, b c p • T c p` and
`zR b = ∑ c, ∑ p, b c p • R c p`.

* `EngineAlgebra.norm_sq_slow_le`: `‖zT b‖² ≤ lam ‖zR b‖²` (point (a)).
* `EngineAlgebra.inner_slow_le`: `‖⟪v, zT b⟫‖ ≤ ρ ‖v‖ ‖zR b‖` for slow `v` with small
  information (point (b)).
* `EngineAlgebra.old_engine_two_sided`: an old vector and an engine vector are
  `ρ`-almost orthogonal.

The main results are `engine_concat_prefix`, `engine_concat_independent`,
`engine_witness_residual` and `replica_witness_bound`. The Bessel bound for equiangular
families is `equiangular_bessel_of_nonneg` (and `equiangular_bessel_of_pos`); without an
extra hypothesis it fails for `N = 0` and `α ^ 2 > 1`, where the constant
`1 - α ^ 2 + N * α ^ 2` is negative.
-/

noncomputable section
open scoped InnerProductSpace BigOperators

namespace SchauderTranslates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Old vectors first, then the engine atoms, engine by engine (`finProdFinEquiv` order). -/
def engineConcat {d m q : ℕ} (x : Fin d → H) (U : Fin m → Fin q → H) : Fin (d + m * q) → H :=
  Fin.append x (fun k => U (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
@[simp] theorem engineConcat_castAdd {d m q : ℕ} (x : Fin d → H) (U : Fin m → Fin q → H)
    (i : Fin d) : engineConcat x U (Fin.castAdd (m * q) i) = x i := by
  simp only [engineConcat, Fin.append_left]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
@[simp] theorem engineConcat_natAdd {d m q : ℕ} (x : Fin d → H) (U : Fin m → Fin q → H)
    (c : Fin m) (p : Fin q) :
    engineConcat x U (Fin.natAdd d (finProdFinEquiv (c, p))) = U c p := by
  simp only [engineConcat, Fin.append_right, Equiv.symm_apply_apply]

namespace EngineAlgebra

/-! ### Index bookkeeping -/

/-- A sum over the concatenated index splits into the old block and the engine blocks. -/
theorem sum_split {M : Type*} [AddCommMonoid M] {d m q : ℕ} (g : Fin (d + m * q) → M) :
    ∑ k, g k = ∑ i, g (Fin.castAdd (m * q) i) +
      ∑ c, ∑ p, g (Fin.natAdd d (finProdFinEquiv (c, p))) := by
  rw [Fin.sum_univ_add, ← Fintype.sum_prod_type']
  congr 1
  exact (Equiv.sum_comp finProdFinEquiv (fun l => g (Fin.natAdd d l))).symm

/-- Engine coefficients read off a concatenated coefficient vector. -/
def coeffs {d m q : ℕ} (a : Fin (d + m * q) → ℂ) : Fin m → Fin q → ℂ :=
  fun c p => a (Fin.natAdd d (finProdFinEquiv (c, p)))

/-- Engine coefficients kept by a cut at position `k` of the engine block: engine `c`
keeps its first `k - q * c` atoms. -/
def cut {m q : ℕ} (b : Fin m → Fin q → ℂ) (k : ℕ) : Fin m → Fin q → ℂ :=
  fun c p => if p.val < k - q * c.val then b c p else 0

/-- The full synthesis of the concatenation: old part plus slow and fast engine parts. -/
theorem synthesis_eq {d m q : ℕ} (x : Fin d → H) (T R : Fin m → Fin q → H)
    (a : Fin (d + m * q) → ℂ) :
    ∑ k, a k • engineConcat x (fun c p => T c p + R c p) k =
      ∑ i, a (Fin.castAdd (m * q) i) • x i +
        (∑ c, ∑ p, coeffs a c p • T c p + ∑ c, ∑ p, coeffs a c p • R c p) := by
  rw [sum_split]
  simp only [engineConcat_castAdd, engineConcat_natAdd, smul_add, Finset.sum_add_distrib,
    coeffs]

/-- A cut synthesis of the concatenation: a cut of the old part plus the engine part with
cut coefficients. -/
theorem prefix_eq {d m q : ℕ} (x : Fin d → H) (T R : Fin m → Fin q → H)
    (a : Fin (d + m * q) → ℂ) (k : ℕ) :
    ∑ j, (if j.val < k then a j • engineConcat x (fun c p => T c p + R c p) j else 0) =
      ∑ i, (if i.val < k then a (Fin.castAdd (m * q) i) • x i else 0) +
        (∑ c, ∑ p, cut (coeffs a) (k - d) c p • T c p +
          ∑ c, ∑ p, cut (coeffs a) (k - d) c p • R c p) := by
  rw [sum_split]
  congr 1
  · simp only [engineConcat_castAdd, Fin.val_castAdd]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [engineConcat_natAdd, Fin.val_natAdd, finProdFinEquiv_apply_val, cut, coeffs]
    by_cases h : p.val < k - d - q * c.val
    · rw [if_pos (by omega), if_pos h, smul_add]
    · rw [if_neg (by omega), if_neg h, zero_smul, zero_smul, add_zero]

/-- Within one engine, cut coefficients give a prefix of that engine's synthesis. -/
theorem cut_sum_eq {m q : ℕ} (R : Fin m → Fin q → H) (b : Fin m → Fin q → ℂ) (k : ℕ)
    (c : Fin m) :
    ∑ p, cut b k c p • R c p = ∑ p, if p.val < k - q * c.val then b c p • R c p else 0 := by
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [cut, ite_smul, zero_smul]

/-! ### Orthogonality -/

theorem slow_mem (Sl : Submodule ℂ H) {m q : ℕ} {T : Fin m → Fin q → H}
    (hT : ∀ c p, T c p ∈ Sl) (b : Fin m → Fin q → ℂ) : ∑ c, ∑ p, b c p • T c p ∈ Sl :=
  Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hT c p)

theorem inner_fast_eq_zero (Sl : Submodule ℂ H) {m q : ℕ} {R : Fin m → Fin q → H}
    (hRS : ∀ c p, ∀ s ∈ Sl, ⟪s, R c p⟫_ℂ = 0) (b : Fin m → Fin q → ℂ) {s : H} (hs : s ∈ Sl) :
    ⟪s, ∑ c, ∑ p, b c p • R c p⟫_ℂ = 0 := by
  simp [hRS _ _ s hs]

theorem norm_sq_add_of_inner_eq_zero {s w : H} (h : ⟪s, w⟫_ℂ = 0) :
    ‖s + w‖ ^ 2 = ‖s‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), h]
  simp

theorem norm_sq_sub_of_inner_eq_zero {s w : H} (h : ⟪s, w⟫_ℂ = 0) :
    ‖s - w‖ ^ 2 = ‖s‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), h]
  simp

/-- Pythagoras for a pairwise orthogonal finite family. -/
theorem norm_sq_sum_of_pairwise {ι : Type*} [Fintype ι] (w : ι → H)
    (h : ∀ i j, i ≠ j → ⟪w i, w j⟫_ℂ = 0) : ‖∑ i, w i‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i (fun j _ hji => h i j (Ne.symm hji)) (by simp),
    inner_self_eq_norm_sq]

/-- The fast parts of different engines add orthogonally. -/
theorem norm_sq_fast {m q : ℕ} {R : Fin m → Fin q → H}
    (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0) (b : Fin m → Fin q → ℂ) :
    ‖∑ c, ∑ p, b c p • R c p‖ ^ 2 = ∑ c, ‖∑ p, b c p • R c p‖ ^ 2 := by
  refine norm_sq_sum_of_pairwise _ fun c c' hcc' => ?_
  simp [hRR c c' _ _ hcc']

/-- The engine part splits orthogonally into its slow and fast components. -/
theorem norm_sq_engine (Sl : Submodule ℂ H) {m q : ℕ} {T R : Fin m → Fin q → H}
    (hT : ∀ c p, T c p ∈ Sl) (hRS : ∀ c p, ∀ s ∈ Sl, ⟪s, R c p⟫_ℂ = 0)
    (b : Fin m → Fin q → ℂ) :
    ‖∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p‖ ^ 2 =
      ‖∑ c, ∑ p, b c p • T c p‖ ^ 2 + ‖∑ c, ∑ p, b c p • R c p‖ ^ 2 :=
  norm_sq_add_of_inner_eq_zero (inner_fast_eq_zero Sl hRS b (slow_mem Sl hT b))

/-! ### Information estimates -/

/-- Summing the engine information inequalities with Cauchy–Schwarz. -/
theorem inner_slow_sq_le (Sl : Submodule ℂ H) {m q : ℕ} {T R : Fin m → Fin q → H}
    (I : Fin m → H → ℝ) (hI0 : ∀ c v, 0 ≤ I c v)
    (hinfo : ∀ c v (b : Fin q → ℂ), v ∈ Sl →
      ‖⟪v, ∑ p, b p • T c p⟫_ℂ‖ ^ 2 ≤ I c v * ‖∑ p, b p • R c p‖ ^ 2)
    (b : Fin m → Fin q → ℂ) {v : H} (hv : v ∈ Sl) :
    ‖⟪v, ∑ c, ∑ p, b c p • T c p⟫_ℂ‖ ^ 2 ≤
      (∑ c, I c v) * ∑ c, ‖∑ p, b c p • R c p‖ ^ 2 := by
  have hsq : ∀ c, √(I c v) ^ 2 = I c v := fun c => Real.sq_sqrt (hI0 c v)
  have hc : ∀ c, ‖⟪v, ∑ p, b c p • T c p⟫_ℂ‖ ≤ √(I c v) * ‖∑ p, b c p • R c p‖ := by
    intro c
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
      mul_pow, hsq]
    exact hinfo c v (b c) hv
  have h1 : ‖⟪v, ∑ c, ∑ p, b c p • T c p⟫_ℂ‖ ≤
      ∑ c, √(I c v) * ‖∑ p, b c p • R c p‖ := by
    rw [inner_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hc c)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => √(I c v))
    (fun c => ‖∑ p, b c p • R c p‖)
  simp only [hsq] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- Point (b): a slow vector with total information at most `ρ ^ 2 * ‖v‖ ^ 2` pairs weakly
with the slow part. -/
theorem inner_slow_le (Sl : Submodule ℂ H) {m q : ℕ} {T R : Fin m → Fin q → H}
    (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0)
    (I : Fin m → H → ℝ) (hI0 : ∀ c v, 0 ≤ I c v)
    (hinfo : ∀ c v (b : Fin q → ℂ), v ∈ Sl →
      ‖⟪v, ∑ p, b p • T c p⟫_ℂ‖ ^ 2 ≤ I c v * ‖∑ p, b p • R c p‖ ^ 2)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (b : Fin m → Fin q → ℂ) {v : H} (hv : v ∈ Sl)
    (hvI : ∑ c, I c v ≤ ρ ^ 2 * ‖v‖ ^ 2) :
    ‖⟪v, ∑ c, ∑ p, b c p • T c p⟫_ℂ‖ ≤ ρ * ‖v‖ * ‖∑ c, ∑ p, b c p • R c p‖ := by
  have h := inner_slow_sq_le Sl I hI0 hinfo b hv
  rw [← norm_sq_fast hRR] at h
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity)]
  calc _ ≤ _ := h
    _ ≤ ρ ^ 2 * ‖v‖ ^ 2 * ‖∑ c, ∑ p, b c p • R c p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hvI (sq_nonneg _)
    _ = _ := by ring

/-- Point (a): the slow part of an engine vector is controlled by its fast part. -/
theorem norm_sq_slow_le (Sl : Submodule ℂ H) {m q : ℕ} {T R : Fin m → Fin q → H}
    (hT : ∀ c p, T c p ∈ Sl) (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0)
    (I : Fin m → H → ℝ) (hI0 : ∀ c v, 0 ≤ I c v)
    (hinfo : ∀ c v (b : Fin q → ℂ), v ∈ Sl →
      ‖⟪v, ∑ p, b p • T c p⟫_ℂ‖ ^ 2 ≤ I c v * ‖∑ p, b p • R c p‖ ^ 2)
    {lam : ℝ} (hlam : 0 ≤ lam) (htot : ∀ v ∈ Sl, ∑ c, I c v ≤ lam * ‖v‖ ^ 2)
    (b : Fin m → Fin q → ℂ) :
    ‖∑ c, ∑ p, b c p • T c p‖ ^ 2 ≤ lam * ‖∑ c, ∑ p, b c p • R c p‖ ^ 2 := by
  have hz : ∑ c, ∑ p, b c p • T c p ∈ Sl := slow_mem Sl hT b
  have h := inner_slow_sq_le Sl I hI0 hinfo b hz
  rw [← norm_sq_fast hRR] at h
  set zT := ∑ c, ∑ p, b c p • T c p
  set zR := ∑ c, ∑ p, b c p • R c p
  have hn : ‖⟪zT, zT⟫_ℂ‖ = ‖zT‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hn] at h
  have h' : ‖zT‖ ^ 2 * ‖zT‖ ^ 2 ≤ ‖zT‖ ^ 2 * (lam * ‖zR‖ ^ 2) := by
    calc ‖zT‖ ^ 2 * ‖zT‖ ^ 2 = (‖zT‖ ^ 2) ^ 2 := by ring
      _ ≤ (∑ c, I c zT) * ‖zR‖ ^ 2 := h
      _ ≤ lam * ‖zT‖ ^ 2 * ‖zR‖ ^ 2 := mul_le_mul_of_nonneg_right (htot _ hz) (sq_nonneg _)
      _ = _ := by ring
  rcases (sq_nonneg ‖zT‖).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_left h' hpos

/-- Two vectors with `‖⟪y, n⟫‖ ≤ ρ ‖y‖ ‖n‖` are `ρ`-almost orthogonal. -/
theorem two_sided {y n : H} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (h : ‖⟪y, n⟫_ℂ‖ ≤ ρ * ‖y‖ * ‖n‖) :
    (1 - ρ) * (‖y‖ ^ 2 + ‖n‖ ^ 2) ≤ ‖y + n‖ ^ 2 ∧
      ‖y + n‖ ^ 2 ≤ (1 + ρ) * (‖y‖ ^ 2 + ‖n‖ ^ 2) := by
  rw [norm_add_sq (𝕜 := ℂ)]
  have h1 := abs_le.mp ((RCLike.abs_re_le_norm (⟪y, n⟫_ℂ)).trans h)
  have h2 := mul_le_mul_of_nonneg_left (two_mul_le_add_sq ‖y‖ ‖n‖) hρ0
  constructor <;> nlinarith [h1.1, h1.2]

/-- An old vector and an engine vector are `ρ`-almost orthogonal. -/
theorem old_engine_two_sided (Sl : Submodule ℂ H) {d m q : ℕ} {x : Fin d → H}
    (hxS : ∀ i, x i ∈ Sl) {T R : Fin m → Fin q → H} (hT : ∀ c p, T c p ∈ Sl)
    (hRS : ∀ c p, ∀ s ∈ Sl, ⟪s, R c p⟫_ℂ = 0)
    (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0)
    (I : Fin m → H → ℝ) (hI0 : ∀ c v, 0 ≤ I c v)
    (hinfo : ∀ c v (b : Fin q → ℂ), v ∈ Sl →
      ‖⟪v, ∑ p, b p • T c p⟫_ℂ‖ ^ 2 ≤ I c v * ‖∑ p, b p • R c p‖ ^ 2)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hang : ∀ y ∈ Submodule.span ℂ (Set.range x), ∑ c, I c y ≤ ρ ^ 2 * ‖y‖ ^ 2)
    {y : H} (hy : y ∈ Submodule.span ℂ (Set.range x)) (b : Fin m → Fin q → ℂ) :
    (1 - ρ) * (‖y‖ ^ 2 + ‖∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p‖ ^ 2) ≤
        ‖y + (∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p)‖ ^ 2 ∧
      ‖y + (∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p)‖ ^ 2 ≤
        (1 + ρ) * (‖y‖ ^ 2 + ‖∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p‖ ^ 2) := by
  have hyS : y ∈ Sl := Submodule.span_le.mpr (Set.range_subset_iff.mpr hxS) hy
  apply two_sided hρ0
  rw [inner_add_right, inner_fast_eq_zero Sl hRS b hyS, add_zero]
  have hn : ‖∑ c, ∑ p, b c p • R c p‖ ≤
      ‖∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_engine Sl hT hRS b]
    nlinarith [sq_nonneg ‖∑ c, ∑ p, b c p • T c p‖]
  calc _ ≤ ρ * ‖y‖ * ‖∑ c, ∑ p, b c p • R c p‖ :=
        inner_slow_le Sl hRR I hI0 hinfo hρ0 b hyS (hang y hy)
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

end EngineAlgebra

-- `hKc` belongs to the agreed interface but is not needed: every engine cut is a prefix
-- cut of that engine, so `hRpre` applies to full engines as well.
set_option linter.unusedVariables false in
/-- Prefix bound for the concatenation. `T c p` is the slow part and `R c p` the part
orthogonal to the slow space; `R` of different engines are orthogonal. -/
theorem engine_concat_prefix
    (Sl : Submodule ℂ H) {d m q : ℕ}
    (x : Fin d → H) (hxS : ∀ i, x i ∈ Sl) {K : ℝ} (hK : 1 ≤ K)
    (hxpre : FinitePrefixSqBound x (K ^ 2))
    (T R : Fin m → Fin q → H) (hT : ∀ c p, T c p ∈ Sl)
    (hRS : ∀ c p, ∀ s ∈ Sl, ⟪s, R c p⟫_ℂ = 0)
    (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0)
    {Kc : ℝ} (hKc : 1 ≤ Kc) (hRpre : ∀ c, FinitePrefixSqBound (R c) (Kc ^ 2))
    (I : Fin m → H → ℝ) (hI0 : ∀ c v, 0 ≤ I c v)
    (hinfo : ∀ c v (b : Fin q → ℂ), v ∈ Sl →
      ‖⟪v, ∑ p, b p • T c p⟫_ℂ‖ ^ 2 ≤ I c v * ‖∑ p, b p • R c p‖ ^ 2)
    {lam ρ : ℝ} (hlam : 0 ≤ lam) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (htot : ∀ v ∈ Sl, ∑ c, I c v ≤ lam * ‖v‖ ^ 2)
    (hang : ∀ y ∈ Submodule.span ℂ (Set.range x), ∑ c, I c y ≤ ρ ^ 2 * ‖y‖ ^ 2) :
    FinitePrefixSqBound (engineConcat x (fun c p => T c p + R c p))
      ((1 + ρ) / (1 - ρ) * max (K ^ 2) ((1 + lam) * Kc ^ 2)) := by
  intro k a
  rw [EngineAlgebra.prefix_eq, EngineAlgebra.synthesis_eq]
  set ay : Fin d → ℂ := fun i => a (Fin.castAdd (m * q) i)
  set b := EngineAlgebra.coeffs a
  set b' := EngineAlgebra.cut b (k - d) with hb'
  set y := ∑ i, ay i • x i
  set y' := ∑ i, (if i.val < k then ay i • x i else 0)
  set n := ∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p with hn
  set n' := ∑ c, ∑ p, b' c p • T c p + ∑ c, ∑ p, b' c p • R c p with hn'
  set M := max (K ^ 2) ((1 + lam) * Kc ^ 2)
  have hymem : y ∈ Submodule.span ℂ (Set.range x) :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨ay, rfl⟩
  have hy'mem : y' ∈ Submodule.span ℂ (Set.range x) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    split_ifs
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    · exact Submodule.zero_mem _
  have hlow :=
    (EngineAlgebra.old_engine_two_sided Sl hxS hT hRS hRR I hI0 hinfo hρ0 hang hymem b).1
  have hup :=
    (EngineAlgebra.old_engine_two_sided Sl hxS hT hRS hRR I hI0 hinfo hρ0 hang hy'mem b').2
  -- the old part: a prefix of the old list
  have hyy : ‖y'‖ ^ 2 ≤ K ^ 2 * ‖y‖ ^ 2 := hxpre k ay
  -- the engine part: engine `c` is cut after `k - d - q * c` atoms
  have hRcut : ‖∑ c, ∑ p, b' c p • R c p‖ ^ 2 ≤ Kc ^ 2 * ‖∑ c, ∑ p, b c p • R c p‖ ^ 2 := by
    rw [EngineAlgebra.norm_sq_fast hRR, EngineAlgebra.norm_sq_fast hRR, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [hb', EngineAlgebra.cut_sum_eq]
    exact hRpre c (k - d - q * c.val) (b c)
  have hnn : ‖n'‖ ^ 2 ≤ (1 + lam) * Kc ^ 2 * ‖n‖ ^ 2 := by
    have h1 := EngineAlgebra.norm_sq_engine Sl hT hRS b'
    have h2 := EngineAlgebra.norm_sq_engine Sl hT hRS b
    have h3 := EngineAlgebra.norm_sq_slow_le Sl hT hRR I hI0 hinfo hlam htot b'
    rw [hn', h1, hn, h2]
    have hKc2 : 0 ≤ Kc ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg ‖∑ c, ∑ p, b c p • T c p‖, sq_nonneg ‖∑ c, ∑ p, b c p • R c p‖,
      mul_nonneg (mul_nonneg (add_nonneg zero_le_one hlam) hKc2)
        (sq_nonneg ‖∑ c, ∑ p, b c p • T c p‖)]
  have hM1 : K ^ 2 ≤ M := le_max_left _ _
  have hM2 : (1 + lam) * Kc ^ 2 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := (sq_nonneg K).trans hM1
  have hS : ‖y'‖ ^ 2 + ‖n'‖ ^ 2 ≤ M * (‖y‖ ^ 2 + ‖n‖ ^ 2) := by
    nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖n‖, mul_le_mul_of_nonneg_right hM1 (sq_nonneg ‖y‖),
      mul_le_mul_of_nonneg_right hM2 (sq_nonneg ‖n‖)]
  have h1ρ : 0 < 1 - ρ := by linarith
  have key : (1 - ρ) * ‖y' + n'‖ ^ 2 ≤ (1 + ρ) * M * ‖y + n‖ ^ 2 := by
    calc (1 - ρ) * ‖y' + n'‖ ^ 2 ≤ (1 - ρ) * ((1 + ρ) * (‖y'‖ ^ 2 + ‖n'‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hup h1ρ.le
      _ ≤ (1 - ρ) * ((1 + ρ) * (M * (‖y‖ ^ 2 + ‖n‖ ^ 2))) := by
          gcongr
      _ = (1 + ρ) * M * ((1 - ρ) * (‖y‖ ^ 2 + ‖n‖ ^ 2)) := by ring
      _ ≤ (1 + ρ) * M * ‖y + n‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ h1ρ]
  linarith

/-- The concatenation is linearly independent. -/
theorem engine_concat_independent
    (Sl : Submodule ℂ H) {d m q : ℕ}
    (x : Fin d → H) (hxS : ∀ i, x i ∈ Sl) (hxind : LinearIndependent ℂ x)
    (T R : Fin m → Fin q → H) (hT : ∀ c p, T c p ∈ Sl)
    (hRS : ∀ c p, ∀ s ∈ Sl, ⟪s, R c p⟫_ℂ = 0)
    (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0)
    (hRind : ∀ c, LinearIndependent ℂ (R c))
    (I : Fin m → H → ℝ) (hI0 : ∀ c v, 0 ≤ I c v)
    (hinfo : ∀ c v (b : Fin q → ℂ), v ∈ Sl →
      ‖⟪v, ∑ p, b p • T c p⟫_ℂ‖ ^ 2 ≤ I c v * ‖∑ p, b p • R c p‖ ^ 2)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hang : ∀ y ∈ Submodule.span ℂ (Set.range x), ∑ c, I c y ≤ ρ ^ 2 * ‖y‖ ^ 2) :
    LinearIndependent ℂ (engineConcat x (fun c p => T c p + R c p)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  rw [EngineAlgebra.synthesis_eq] at ha
  set ay : Fin d → ℂ := fun i => a (Fin.castAdd (m * q) i)
  set b := EngineAlgebra.coeffs a
  set y := ∑ i, ay i • x i
  set n := ∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p with hn
  have hymem : y ∈ Submodule.span ℂ (Set.range x) :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨ay, rfl⟩
  have hlow :=
    (EngineAlgebra.old_engine_two_sided Sl hxS hT hRS hRR I hI0 hinfo hρ0 hang hymem b).1
  rw [ha, norm_zero] at hlow
  have h1ρ : 0 < 1 - ρ := by linarith
  have hy0 : ‖y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖n‖]
  have hn0 : ‖n‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖n‖]
  -- the old coefficients vanish
  have hay0 : ∀ i, ay i = 0 :=
    (Fintype.linearIndependent_iff.mp hxind) ay
      (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hy0))
  -- every engine's fast synthesis vanishes, hence so do the engine coefficients
  have hR0 : ∑ c, ‖∑ p, b c p • R c p‖ ^ 2 = 0 := by
    rw [hn, EngineAlgebra.norm_sq_engine Sl hT hRS b, EngineAlgebra.norm_sq_fast hRR] at hn0
    have := sq_nonneg ‖∑ c, ∑ p, b c p • T c p‖
    have : 0 ≤ ∑ c, ‖∑ p, b c p • R c p‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
    linarith
  have hb0 : ∀ c p, b c p = 0 := by
    intro c
    have hc := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg _)).mp hR0 c
      (Finset.mem_univ c)
    exact (Fintype.linearIndependent_iff.mp (hRind c)) (b c)
      (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hc))
  intro k
  refine Fin.addCases (fun i => ?_) (fun l => ?_) k
  · exact hay0 i
  · obtain ⟨⟨c, p⟩, rfl⟩ := finProdFinEquiv.surjective l
    exact hb0 c p

/-- Any engine coefficients give an explicit approximant of a target whose residual
`r` is slow and whose old component lies in the old span. -/
theorem engine_witness_residual
    (Sl : Submodule ℂ H) {d m q : ℕ} (x : Fin d → H)
    (T R : Fin m → Fin q → H) (hT : ∀ c p, T c p ∈ Sl)
    (hRS : ∀ c p, ∀ s ∈ Sl, ⟪s, R c p⟫_ℂ = 0)
    (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0)
    (f r : H) (hr : r ∈ Sl) (hfr : f - r ∈ Submodule.span ℂ (Set.range x))
    (b : Fin m → Fin q → ℂ) :
    ∃ a : Fin (d + m * q) → ℂ,
      ‖f - ∑ k, a k • engineConcat x (fun c p => T c p + R c p) k‖ ^ 2 =
        ‖r - ∑ c, ∑ p, b c p • T c p‖ ^ 2 + ∑ c, ‖∑ p, b c p • R c p‖ ^ 2 := by
  obtain ⟨a0, ha0⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hfr
  refine ⟨Fin.append a0 (fun l => b (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2), ?_⟩
  rw [EngineAlgebra.synthesis_eq]
  have hco : EngineAlgebra.coeffs
      (Fin.append a0 (fun l => b (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2)) = b := by
    funext c p
    simp only [EngineAlgebra.coeffs, Fin.append_right, Equiv.symm_apply_apply]
  simp only [Fin.append_left, hco, ha0]
  have he : f - (f - r + (∑ c, ∑ p, b c p • T c p + ∑ c, ∑ p, b c p • R c p)) =
      (r - ∑ c, ∑ p, b c p • T c p) - ∑ c, ∑ p, b c p • R c p := by abel
  rw [he, EngineAlgebra.norm_sq_sub_of_inner_eq_zero, EngineAlgebra.norm_sq_fast hRR]
  exact EngineAlgebra.inner_fast_eq_zero Sl hRS b
    (Sl.sub_mem hr (EngineAlgebra.slow_mem Sl hT b))

/-! ### Equiangular families -/

/-- Gram entries of an equiangular unit family. -/
theorem equiangular_inner_eq {N : ℕ} (e : Fin N → H) {α : ℝ} (he1 : ∀ i, ‖e i‖ = 1)
    (he2 : ∀ i i', i ≠ i' → ⟪e i, e i'⟫_ℂ = ((α ^ 2 : ℝ) : ℂ)) (i i' : Fin N) :
    ⟪e i, e i'⟫_ℂ = ((α ^ 2 : ℝ) : ℂ) + if i = i' then ((1 - α ^ 2 : ℝ) : ℂ) else 0 := by
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K, he1]
    push_cast
    ring
  · rw [if_neg h, he2 i i' h, add_zero]

/-- Norm of a synthesis over an equiangular unit family. -/
theorem equiangular_norm_sq_sum {N : ℕ} (e : Fin N → H) {α : ℝ} (he1 : ∀ i, ‖e i‖ = 1)
    (he2 : ∀ i i', i ≠ i' → ⟪e i, e i'⟫_ℂ = ((α ^ 2 : ℝ) : ℂ)) (a : Fin N → ℂ) :
    ‖∑ i, a i • e i‖ ^ 2 = (1 - α ^ 2) * ∑ i, ‖a i‖ ^ 2 + α ^ 2 * ‖∑ i, a i‖ ^ 2 := by
  have hw : ⟪∑ i, a i • e i, ∑ i, a i • e i⟫_ℂ =
      ((((1 - α ^ 2) * ∑ i, ‖a i‖ ^ 2 + α ^ 2 * ‖∑ i, a i‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      equiangular_inner_eq e he1 he2, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    rw [← Complex.conj_mul' (∑ i, a i)]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, ← Complex.conj_mul']
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hw, RCLike.re_to_complex, Complex.ofReal_re]

/-- Bessel-type bound for unit vectors with constant pairwise inner product `α²`, provided
the constant `1 - α ^ 2 + N * α ^ 2` is nonnegative (automatic when `0 < N` or
`α ^ 2 ≤ 1`). Some such hypothesis is necessary: for `N = 0`, `α = 2` and `v ≠ 0` the
left side is `0` and the right side is `-3 * ‖v‖ ^ 2`. -/
theorem equiangular_bessel_of_nonneg {N : ℕ} (e : Fin N → H) {α : ℝ} (he1 : ∀ i, ‖e i‖ = 1)
    (he2 : ∀ i i', i ≠ i' → ⟪e i, e i'⟫_ℂ = ((α ^ 2 : ℝ) : ℂ))
    (hC : 0 ≤ 1 - α ^ 2 + N * α ^ 2) (v : H) :
    ∑ i, ‖⟪e i, v⟫_ℂ‖ ^ 2 ≤ (1 - α ^ 2 + N * α ^ 2) * ‖v‖ ^ 2 := by
  set a : Fin N → ℂ := fun i => ⟪e i, v⟫_ℂ
  set S := ∑ i, ‖a i‖ ^ 2 with hS
  set w := ∑ i, a i • e i with hw
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- `S = ⟪w, v⟫ ≤ ‖w‖ ‖v‖`
  have hwv : ⟪w, v⟫_ℂ = (S : ℂ) := by
    simp only [hw, sum_inner, inner_smul_left, hS]
    push_cast
    exact Finset.sum_congr rfl fun i _ => Complex.conj_mul' (a i)
  have hSw : S ≤ ‖w‖ * ‖v‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) w v
    rwa [hwv, Complex.norm_real, Real.norm_of_nonneg hS0] at h
  -- `‖w‖ ^ 2 ≤ (1 - α ^ 2 + N * α ^ 2) * S`
  have hA : ‖∑ i, a i‖ ^ 2 ≤ N * S := by
    calc ‖∑ i, a i‖ ^ 2 ≤ (∑ i, ‖a i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (Finset.univ.card : ℝ) * ∑ i, ‖a i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = N * S := by rw [Finset.card_univ, Fintype.card_fin]
  have hww : ‖w‖ ^ 2 ≤ (1 - α ^ 2 + N * α ^ 2) * S := by
    rw [hw, equiangular_norm_sq_sum e he1 he2 a]
    nlinarith [mul_le_mul_of_nonneg_left hA (sq_nonneg α)]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hC (sq_nonneg _)
  · have h2 : S * S ≤ S * ((1 - α ^ 2 + N * α ^ 2) * ‖v‖ ^ 2) := by
      calc S * S = S ^ 2 := by ring
        _ ≤ (‖w‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ hS0 hSw 2
        _ = ‖w‖ ^ 2 * ‖v‖ ^ 2 := by ring
        _ ≤ ((1 - α ^ 2 + N * α ^ 2) * S) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hww (sq_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2 hpos

/-- Bessel-type bound for a nonempty equiangular unit family. -/
theorem equiangular_bessel_of_pos {N : ℕ} (e : Fin N → H) {α : ℝ} (he1 : ∀ i, ‖e i‖ = 1)
    (he2 : ∀ i i', i ≠ i' → ⟪e i, e i'⟫_ℂ = ((α ^ 2 : ℝ) : ℂ)) (hN : 0 < N) (v : H) :
    ∑ i, ‖⟪e i, v⟫_ℂ‖ ^ 2 ≤ (1 - α ^ 2 + N * α ^ 2) * ‖v‖ ^ 2 := by
  refine equiangular_bessel_of_nonneg e he1 he2 ?_ v
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [sq_nonneg α]

-- `hF`, `hj` and `hRR` belong to the agreed interface but are not needed: the bound is
-- homogeneous in `F`, `hq1` already forces `0 < n * j`, and the conclusion only involves
-- the fast energies engine by engine.
set_option linter.unusedVariables false in
/-- The replica witness. With `n` engines per replica, each realizing `j • e_i` at
centered cost `j`, a common real multiple of the witnesses captures most of `r`. -/
theorem replica_witness_bound {N n q : ℕ} (e : Fin N → H) {α F j : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hF : 0 < F) (hj : 0 < j)
    (he1 : ∀ i, ‖e i‖ = 1) (he2 : ∀ i i', i ≠ i' → ⟪e i, e i'⟫_ℂ = ((α ^ 2 : ℝ) : ℂ))
    (r : H) (hr : ‖r‖ = F) (her : ∀ i, ⟪e i, r⟫_ℂ = ((α * F : ℝ) : ℂ))
    (T R : Fin (N * n) → Fin q → H)
    (hRR : ∀ c c' p p', c ≠ c' → ⟪R c p, R c' p'⟫_ℂ = 0)
    (hwit : ∀ c, ∃ b : Fin q → ℂ, ∑ p, b p • T c p = (j : ℂ) • e (finProdFinEquiv.symm c).1 ∧
      ‖∑ p, b p • R c p‖ ^ 2 = j)
    (hq1 : (1 / 10 : ℝ) ≤ n * j) (hq2 : n * j ≤ 11 / 100) (hN : 20 ≤ N * α ^ 2) :
    ∃ b : Fin (N * n) → Fin q → ℂ,
      ‖r - ∑ c, ∑ p, b c p • T c p‖ ^ 2 + ∑ c, ‖∑ p, b c p • R c p‖ ^ 2 ≤ (2 / 5) * F ^ 2 := by
  choose w hwT hwR using hwit
  -- the common real multiple `L = α F / (1 + n j (1 + (N - 1) α²))`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = α * F / (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) := ⟨_, rfl⟩
  refine ⟨fun c p => (L : ℂ) * w c p, ?_⟩
  -- the slow parts add up to `L j n • ∑ i, e i`: every replica has exactly `n` engines
  have hT1 : ∀ c, ∑ p, ((L : ℂ) * w c p) • T c p =
      ((L * j : ℝ) : ℂ) • e (finProdFinEquiv.symm c).1 := by
    intro c
    simp only [mul_smul, ← Finset.smul_sum, hwT c]
    rw [smul_smul, ← Complex.ofReal_mul]
  have hcount : ∑ c : Fin (N * n), e (finProdFinEquiv.symm c).1 = (n : ℂ) • ∑ i, e i := by
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun x : Fin N × Fin n => e x.1),
      Fintype.sum_prod_type, Finset.smul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hTsum : ∑ c, ∑ p, ((L : ℂ) * w c p) • T c p = ((L * j * n : ℝ) : ℂ) • ∑ i, e i := by
    simp only [hT1, ← Finset.smul_sum, hcount, smul_smul]
    push_cast
    rfl
  -- the fast parts have total energy `N n L² j`
  have hRsum : ∑ c, ‖∑ p, ((L : ℂ) * w c p) • R c p‖ ^ 2 = N * n * (L ^ 2 * j) := by
    have h1 : ∀ c, ‖∑ p, ((L : ℂ) * w c p) • R c p‖ ^ 2 = L ^ 2 * j := by
      intro c
      simp only [mul_smul, ← Finset.smul_sum, norm_smul, mul_pow, hwR c, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- geometry of `∑ i, e i`
  have hss : ‖∑ i, e i‖ ^ 2 = (1 - α ^ 2) * N + α ^ 2 * N ^ 2 := by
    have h := equiangular_norm_sq_sum e he1 he2 (fun _ => 1)
    simp only [one_smul, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Complex.norm_natCast] at h
    rw [h]
  have hrs : ⟪r, ∑ i, e i⟫_ℂ = ((N * (α * F) : ℝ) : ℂ) := by
    have h1 : ∀ i, ⟪r, e i⟫_ℂ = ((α * F : ℝ) : ℂ) := fun i => by
      rw [← inner_conj_symm, her, Complex.conj_ofReal]
    simp only [inner_sum, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  have hV : ‖r - ((L * j * n : ℝ) : ℂ) • ∑ i, e i‖ ^ 2 =
      F ^ 2 - 2 * ((L * j * n) * (N * (α * F))) +
        (L * j * n) ^ 2 * ((1 - α ^ 2) * N + α ^ 2 * N ^ 2) := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hrs, hr, norm_smul, mul_pow, hss,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_mul,
      RCLike.re_to_complex, Complex.ofReal_re]
  rw [hTsum, hRsum, hV]
  -- the scalar optimization: the value is `F ^ 2 * (1 - X / D)` with `5 X ≥ 3 D`
  have hα2 : 0 < α ^ 2 := by positivity
  have hα21 : α ^ 2 ≤ 1 := by nlinarith
  have hQ0 : 0 < (n : ℝ) * j := by linarith
  have hX : 2 ≤ n * j * (N * α ^ 2) := by nlinarith
  have hD : 0 < 1 + n * j * (1 - α ^ 2 + N * α ^ 2) := by nlinarith
  have hLD : L * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) = α * F := by
    rw [hL, div_mul_cancel₀ _ hD.ne']
  have hval : F ^ 2 - 2 * ((L * j * n) * (N * (α * F))) +
      (L * j * n) ^ 2 * ((1 - α ^ 2) * N + α ^ 2 * N ^ 2) + N * n * (L ^ 2 * j) =
      F ^ 2 - L * (n * j * N * α * F) := by
    linear_combination (L * j * n * N) * hLD
  rw [hval]
  have key : 3 * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) ≤ 5 * (n * j * (N * α ^ 2)) := by
    nlinarith
  have h3 : 3 / 5 * F ^ 2 * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) ≤
      L * (n * j * N * α * F) * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) := by
    calc 3 / 5 * F ^ 2 * (1 + n * j * (1 - α ^ 2 + N * α ^ 2))
        ≤ F ^ 2 * (n * j * (N * α ^ 2)) := by nlinarith [sq_nonneg F]
      _ = (L * (1 + n * j * (1 - α ^ 2 + N * α ^ 2))) * (n * j * N * α * F) := by
          rw [hLD]
          ring
      _ = _ := by ring
  have h4 := le_of_mul_le_mul_right h3 hD
  linarith

end SchauderTranslates
