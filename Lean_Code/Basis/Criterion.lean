import Mathlib

/-!
# Schauder bases: construction from coordinates and from finite prefix bounds

Everything here is stated for Mathlib's `SchauderBasis 𝕜 X`
(`Mathlib.Analysis.Normed.Module.Bases`).

* `StructuredBases.ofCoord`: a sequence with continuous biorthogonal coordinate
  functionals whose ordered expansions converge is a Schauder basis.
* `StructuredBases.exists_schauderBasis_of_prefix_bound`: the classical criterion
  (Grunblum): nonzero vectors with dense span whose finite prefixes satisfy
  `‖∑_{n<N} a_n e_n‖ ≤ C ‖∑_n a_n e_n‖` form a Schauder basis with all partial sum
  projections of norm at most `C`.
* `StructuredBases.nnnormProjBound_le_iff` and friends: the basis constant
  `SchauderBasis.nnnormProjBound` is the least upper bound of the norms `‖b.proj N‖`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators NNReal

namespace StructuredBases

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### Bases from continuous coordinates -/

/-- A sequence `e` with continuous biorthogonal coordinates `c` and convergent ordered
expansions, packaged as Mathlib's `SchauderBasis`. -/
def ofCoord (e : ℕ → X) (c : ℕ → X →L[𝕜] 𝕜)
    (hbi : ∀ n m, c n (e m) = if n = m then 1 else 0)
    (hexp : ∀ x, Tendsto (fun N => ∑ n ∈ Finset.range N, c n x • e n) atTop (𝓝 x)) :
    SchauderBasis 𝕜 X where
  basis := e
  coord := c
  ortho i j := by
    rw [hbi]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  expansion x := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    exact hexp x

@[simp] theorem ofCoord_coe (e : ℕ → X) (c : ℕ → X →L[𝕜] 𝕜)
    (hbi : ∀ n m, c n (e m) = if n = m then 1 else 0)
    (hexp : ∀ x, Tendsto (fun N => ∑ n ∈ Finset.range N, c n x • e n) atTop (𝓝 x)) :
    ⇑(ofCoord e c hbi hexp) = e := rfl

@[simp] theorem ofCoord_coord (e : ℕ → X) (c : ℕ → X →L[𝕜] 𝕜)
    (hbi : ∀ n m, c n (e m) = if n = m then 1 else 0)
    (hexp : ∀ x, Tendsto (fun N => ∑ n ∈ Finset.range N, c n x • e n) atTop (𝓝 x)) :
    (ofCoord e c hbi hexp).coord = c := rfl

theorem ofCoord_proj (e : ℕ → X) (c : ℕ → X →L[𝕜] 𝕜)
    (hbi : ∀ n m, c n (e m) = if n = m then 1 else 0)
    (hexp : ∀ x, Tendsto (fun N => ∑ n ∈ Finset.range N, c n x • e n) atTop (𝓝 x)) (N : ℕ) :
    (ofCoord e c hbi hexp).proj N = ∑ n ∈ Finset.range N, (c n).smulRight (e n) := rfl

/-! ### Elementary facts about a Schauder basis -/

section Basic

variable (b : SchauderBasis 𝕜 X)

/-- Biorthogonality in `if`-form. -/
theorem coord_apply_basis (i j : ℕ) : b.coord i (b j) = if i = j then 1 else 0 := by
  rw [b.ortho]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem proj_eq_sum (N : ℕ) :
    b.proj N = ∑ n ∈ Finset.range N, (b.coord n).smulRight (b n) := rfl

/-- The ordered expansion of `x`. -/
theorem tendsto_expansion (x : X) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, b.coord n x • b n) atTop (𝓝 x) := by
  simpa only [SchauderBasis.proj_apply] using b.tendsto_proj x

theorem basis_ne_zero (n : ℕ) : b n ≠ 0 := by
  intro h
  have := coord_apply_basis b n n
  rw [h, map_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem proj_succ_sub (n : ℕ) :
    b.proj (n + 1) - b.proj n = (b.coord n).smulRight (b n) := by
  simp [proj_eq_sum, Finset.sum_range_succ]

theorem proj_apply_basis_of_lt {n N : ℕ} (h : n < N) : b.proj N (b n) = b n := by
  rw [b.proj_apply_basis_mem, if_pos h]

theorem proj_apply_basis_of_le {n N : ℕ} (h : N ≤ n) : b.proj N (b n) = 0 := by
  rw [b.proj_apply_basis_mem, if_neg (by omega)]

/-- Uniqueness of expansions: the coefficients of any convergent ordered expansion of `x`
are the coordinates of `x`. -/
theorem coord_eq_of_tendsto {x : X} {a : ℕ → 𝕜}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n • b n) atTop (𝓝 x)) (n : ℕ) :
    b.coord n x = a n := by
  have ht := ((b.coord n).continuous.tendsto x).comp h
  have he : ∀ᶠ N : ℕ in atTop,
      (b.coord n ∘ fun N => ∑ m ∈ Finset.range N, a m • b m) N = a n := by
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [map_sum, coord_apply_basis, Finset.mem_range.mpr hN]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))

/-- Every vector has exactly one norm-convergent ordered expansion. -/
theorem existsUnique_expansion (x : X) :
    ∃! a : ℕ → 𝕜, Tendsto (fun N => ∑ n ∈ Finset.range N, a n • b n) atTop (𝓝 x) :=
  ⟨fun n => b.coord n x, tendsto_expansion b x,
    fun _ ha => funext fun n => (coord_eq_of_tendsto b ha n).symm⟩

/-- The first partial sum projection has norm at least one. -/
theorem one_le_norm_proj {N : ℕ} (hN : 0 < N) : 1 ≤ ‖b.proj N‖ := by
  have hfix : b.proj N (b 0) = b 0 := proj_apply_basis_of_lt b hN
  have hle := (b.proj N).le_opNorm (b 0)
  rw [hfix] at hle
  have hpos : 0 < ‖b 0‖ := norm_pos_iff.mpr (basis_ne_zero b 0)
  nlinarith

variable [CompleteSpace X]

theorem norm_proj_le_nnnormProjBound (N : ℕ) : ‖b.proj N‖ ≤ b.nnnormProjBound :=
  b.norm_proj_le_nnnormProjBound N

/-- The basis constant is at most `C` iff every partial sum projection has norm at most `C`. -/
theorem nnnormProjBound_le_iff {C : ℝ} : (b.nnnormProjBound : ℝ) ≤ C ↔ ∀ N, ‖b.proj N‖ ≤ C := by
  constructor
  · exact fun h N => (norm_proj_le_nnnormProjBound b N).trans h
  · intro h
    have hC : 0 ≤ C := (norm_nonneg _).trans (h 0)
    lift C to ℝ≥0 using hC
    rw [NNReal.coe_le_coe]
    exact ciSup_le fun N => by exact_mod_cast h N

/-- The basis constant is at least one. -/
theorem one_le_nnnormProjBound : (1 : ℝ) ≤ b.nnnormProjBound :=
  (one_le_norm_proj b one_pos).trans (norm_proj_le_nnnormProjBound b 1)

/-- A strict bound on the basis constant from a non-strict uniform bound below it. -/
theorem nnnormProjBound_lt_of_le {C D : ℝ} (h : ∀ N, ‖b.proj N‖ ≤ C) (hCD : C < D) :
    (b.nnnormProjBound : ℝ) < D :=
  ((nnnormProjBound_le_iff b).mpr h).trans_lt hCD

/-- If some partial sum projection has norm greater than one, the basis constant is not one. -/
theorem nnnormProjBound_ne_one_of_lt {N : ℕ} (h : 1 < ‖b.proj N‖) : b.nnnormProjBound ≠ 1 := by
  intro h1
  have := norm_proj_le_nnnormProjBound b N
  rw [h1] at this
  exact absurd (by exact_mod_cast this) (not_le.mpr h)

end Basic

/-! ### The finite prefix criterion -/

section Criterion

/-- The first `N` terms of a finitely supported combination. -/
def finitePrefix (e : ℕ → X) (N : ℕ) : (ℕ →₀ 𝕜) →ₗ[𝕜] X :=
  ∑ n ∈ Finset.range N, (Finsupp.lapply n).smulRight (e n)

@[simp] theorem finitePrefix_apply (e : ℕ → X) (N : ℕ) (a : ℕ →₀ 𝕜) :
    finitePrefix e N a = ∑ n ∈ Finset.range N, a n • e n := by
  simp [finitePrefix]

theorem finitePrefix_succ_sub (e : ℕ → X) (n : ℕ) (a : ℕ →₀ 𝕜) :
    finitePrefix e (n + 1) a - finitePrefix e n a = a n • e n := by
  simp [Finset.sum_range_succ]

theorem finitePrefix_eq_linearCombination (e : ℕ → X) (a : ℕ →₀ 𝕜) {N : ℕ}
    (hN : ∀ n ∈ a.support, n < N) :
    finitePrefix e N a = Finsupp.linearCombination 𝕜 e a := by
  rw [finitePrefix_apply, Finsupp.linearCombination_apply]
  symm
  apply a.sum_of_support_subset
  · exact fun n hn => Finset.mem_range.mpr (hN n hn)
  · simp

theorem finitePrefix_eventually (e : ℕ → X) (a : ℕ →₀ 𝕜) :
    ∀ᶠ N : ℕ in atTop, finitePrefix e N a = Finsupp.linearCombination 𝕜 e a := by
  filter_upwards [eventually_ge_atTop (a.support.sup id + 1)] with N hN
  apply finitePrefix_eq_linearCombination
  intro n hn
  have hn' : n ≤ a.support.sup id := Finset.le_sup (f := id) hn
  omega

variable (e : ℕ → X) {C : ℝ}

theorem coefficient_bound_of_prefix
    (hC : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖)
    (n : ℕ) (hn : e n ≠ 0) (a : ℕ →₀ 𝕜) :
    ‖a n‖ ≤ (2 * C / ‖e n‖) * ‖Finsupp.linearCombination 𝕜 e a‖ := by
  have hb : ‖a n‖ * ‖e n‖ ≤ 2 * C * ‖Finsupp.linearCombination 𝕜 e a‖ := by
    calc
      ‖a n‖ * ‖e n‖ = ‖a n • e n‖ := (norm_smul _ _).symm
      _ = ‖finitePrefix e (n + 1) a - finitePrefix e n a‖ := by rw [finitePrefix_succ_sub]
      _ ≤ ‖finitePrefix e (n + 1) a‖ + ‖finitePrefix e n a‖ := norm_sub_le _ _
      _ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖ + C * ‖Finsupp.linearCombination 𝕜 e a‖ :=
        add_le_add (hC _ _) (hC _ _)
      _ = 2 * C * ‖Finsupp.linearCombination 𝕜 e a‖ := by ring
  have hp : 0 < ‖e n‖ := norm_pos_iff.mpr hn
  calc
    ‖a n‖ ≤ (2 * C * ‖Finsupp.linearCombination 𝕜 e a‖) / ‖e n‖ := (le_div_iff₀ hp).mpr hb
    _ = (2 * C / ‖e n‖) * ‖Finsupp.linearCombination 𝕜 e a‖ := by ring

variable [CompleteSpace X] [CompleteSpace 𝕜]

variable (𝕜) in
/-- The prefix operators, extended from the dense span to the whole space. -/
def extendedPrefix (N : ℕ) : X →L[𝕜] X :=
  (finitePrefix e N).extendOfNorm (Finsupp.linearCombination 𝕜 e)

variable (𝕜) in
/-- The coordinate functionals, extended from the dense span to the whole space. -/
def extendedCoordinate (n : ℕ) : X →L[𝕜] 𝕜 :=
  (Finsupp.lapply n : (ℕ →₀ 𝕜) →ₗ[𝕜] 𝕜).extendOfNorm (Finsupp.linearCombination 𝕜 e)

variable {e}

omit [CompleteSpace 𝕜] in
theorem extendedPrefix_linearCombination
    (hd : DenseRange (Finsupp.linearCombination 𝕜 e))
    (hC : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖)
    (N : ℕ) (a : ℕ →₀ 𝕜) :
    extendedPrefix 𝕜 e N (Finsupp.linearCombination 𝕜 e a) = finitePrefix e N a :=
  LinearMap.extendOfNorm_eq hd ⟨C, hC N⟩ a

omit [CompleteSpace X] in
theorem extendedCoordinate_linearCombination
    (hd : DenseRange (Finsupp.linearCombination 𝕜 e))
    (hC : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖)
    (n : ℕ) (hn : e n ≠ 0) (a : ℕ →₀ 𝕜) :
    extendedCoordinate 𝕜 e n (Finsupp.linearCombination 𝕜 e a) = a n :=
  LinearMap.extendOfNorm_eq hd ⟨2 * C / ‖e n‖, coefficient_bound_of_prefix e hC n hn⟩ a

omit [CompleteSpace X] in
theorem extendedCoordinate_basis
    (hd : DenseRange (Finsupp.linearCombination 𝕜 e))
    (hC : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖)
    (n : ℕ) (hn : e n ≠ 0) (m : ℕ) :
    extendedCoordinate 𝕜 e n (e m) = if n = m then 1 else 0 := by
  have h := extendedCoordinate_linearCombination hd hC n hn (Finsupp.single m 1)
  rw [Finsupp.linearCombination_single, one_smul] at h
  rw [h, Finsupp.single_apply]
  by_cases hnm : n = m
  · simp [hnm]
  · simp [hnm, Ne.symm hnm]

theorem extendedPrefix_eq_sum (hn : ∀ n, e n ≠ 0)
    (hd : DenseRange (Finsupp.linearCombination 𝕜 e))
    (hC : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖) (N : ℕ) :
    extendedPrefix 𝕜 e N = ∑ n ∈ Finset.range N, (extendedCoordinate 𝕜 e n).smulRight (e n) := by
  ext x
  have hc : IsClosed {x : X | extendedPrefix 𝕜 e N x =
      (∑ n ∈ Finset.range N, (extendedCoordinate 𝕜 e n).smulRight (e n)) x} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  refine hd.induction_on x hc ?_
  intro a
  rw [extendedPrefix_linearCombination hd hC]
  simp [extendedCoordinate_linearCombination hd hC _ (hn _)]

omit [CompleteSpace 𝕜] in
theorem norm_extendedPrefix_le
    (hd : DenseRange (Finsupp.linearCombination 𝕜 e)) (hC0 : 0 ≤ C)
    (hC : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖) (N : ℕ) :
    ‖extendedPrefix 𝕜 e N‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le hd hC0 (hC N)

omit [CompleteSpace 𝕜] in
theorem extendedPrefix_tendsto
    (hd : DenseRange (Finsupp.linearCombination 𝕜 e)) (hC0 : 0 ≤ C)
    (hC : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖) (x : X) :
    Tendsto (fun N => extendedPrefix 𝕜 e N x) atTop (𝓝 x) := by
  have hb (N : ℕ) (y : X) : ‖extendedPrefix 𝕜 e N y‖ ≤ C * ‖y‖ :=
    LinearMap.norm_extendOfNorm_apply_le hd C (hC N) y
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp : 0 < C + 1 := by linarith
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x (div_pos hε hp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (finitePrefix_eventually e a)
  refine ⟨N, fun n hn => ?_⟩
  have hfix : extendedPrefix 𝕜 e n (Finsupp.linearCombination 𝕜 e a) =
      Finsupp.linearCombination 𝕜 e a := by
    rw [extendedPrefix_linearCombination hd hC, hN n hn]
  rw [dist_eq_norm] at ha ⊢
  calc
    ‖extendedPrefix 𝕜 e n x - x‖ =
        ‖extendedPrefix 𝕜 e n (x - Finsupp.linearCombination 𝕜 e a) +
          (Finsupp.linearCombination 𝕜 e a - x)‖ := by rw [map_sub, hfix]; congr 1; abel
    _ ≤ ‖extendedPrefix 𝕜 e n (x - Finsupp.linearCombination 𝕜 e a)‖ +
        ‖Finsupp.linearCombination 𝕜 e a - x‖ := norm_add_le _ _
    _ ≤ C * ‖x - Finsupp.linearCombination 𝕜 e a‖ + ‖x - Finsupp.linearCombination 𝕜 e a‖ := by
      rw [norm_sub_rev (Finsupp.linearCombination 𝕜 e a) x]
      exact add_le_add (hb _ _) le_rfl
    _ = (C + 1) * ‖x - Finsupp.linearCombination 𝕜 e a‖ := by ring
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hp).mp ha

/-- **Finite prefix criterion.** Nonzero vectors with dense linear span whose finite
prefixes are bounded by `C` times the full finite combination form a Schauder basis,
and all its partial sum projections have norm at most `C`. -/
theorem exists_schauderBasis_of_prefix_bound (e : ℕ → X) (hn : ∀ n, e n ≠ 0)
    (hd : Dense (Submodule.span 𝕜 (Set.range e) : Set X)) {C : ℝ}
    (hC : ∀ (N : ℕ) (a : ℕ →₀ 𝕜),
      ‖∑ n ∈ Finset.range N, a n • e n‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖) :
    ∃ b : SchauderBasis 𝕜 X, ⇑b = e ∧ ∀ N, ‖b.proj N‖ ≤ C := by
  have hC' : ∀ N a, ‖finitePrefix e N a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖ := by
    intro N a
    simpa using hC N a
  have hC0 : 0 ≤ C := by
    have h := hC 1 (Finsupp.single 0 1)
    simp only [Finset.range_one, Finset.sum_singleton, Finsupp.single_eq_same, one_smul,
      Finsupp.linearCombination_single] at h
    have hpos : 0 < ‖e 0‖ := norm_pos_iff.mpr (hn 0)
    nlinarith
  have hd' : DenseRange (Finsupp.linearCombination 𝕜 e) := by
    change Dense (↑(LinearMap.range (Finsupp.linearCombination 𝕜 e)) : Set X)
    rwa [Finsupp.range_linearCombination]
  have hexp : ∀ x, Tendsto
      (fun N => ∑ n ∈ Finset.range N, extendedCoordinate 𝕜 e n x • e n) atTop (𝓝 x) := by
    intro x
    have h := extendedPrefix_tendsto hd' hC0 hC' x
    simpa [extendedPrefix_eq_sum hn hd' hC'] using h
  refine ⟨ofCoord e (extendedCoordinate 𝕜 e)
    (fun n m => extendedCoordinate_basis hd' hC' n (hn n) m) hexp, rfl, fun N => ?_⟩
  rw [ofCoord_proj, ← extendedPrefix_eq_sum hn hd' hC']
  exact norm_extendedPrefix_le hd' hC0 hC' N

/-- The finite prefix criterion, with the hypothesis stated for plain sequences of
coefficients and two cut points `N ≤ M`. -/
theorem exists_schauderBasis_of_prefix_bound' (e : ℕ → X) (hn : ∀ n, e n ≠ 0)
    (hd : Dense (Submodule.span 𝕜 (Set.range e) : Set X)) {C : ℝ}
    (hC : ∀ (N M : ℕ) (a : ℕ → 𝕜), N ≤ M →
      ‖∑ n ∈ Finset.range N, a n • e n‖ ≤ C * ‖∑ n ∈ Finset.range M, a n • e n‖) :
    ∃ b : SchauderBasis 𝕜 X, ⇑b = e ∧ ∀ N, ‖b.proj N‖ ≤ C := by
  apply exists_schauderBasis_of_prefix_bound e hn hd
  intro N a
  set M := max N (a.support.sup id + 1) with hM
  have hfull : ∑ n ∈ Finset.range M, a n • e n = Finsupp.linearCombination 𝕜 e a := by
    rw [← finitePrefix_apply]
    apply finitePrefix_eq_linearCombination
    intro n hn'
    have hn'' : n ≤ a.support.sup id := Finset.le_sup (f := id) hn'
    omega
  rw [← hfull]
  exact hC N M a (le_max_left _ _)

end Criterion

end StructuredBases
