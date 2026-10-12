import Lean_Code.SchauderTranslates.Sharp.LimitStagesSharp
import Lean_Code.SchauderTranslates.LimitAssembly

/-!
# Assembly of the sharp infinite construction

This is the sharp counterpart of `LimitAssembly` (paper: Section "Assembling the basis",
Theorem `h2:thm:weighted`). Assuming the sharp finite extension
`Sharp.FiniteExtensionSharp Kstar` as a hypothesis (stored in `Assembly.Setup`), the
stages of `LimitStagesSharp` are passed to the limit:

* the limiting weight `w_∞ = w₀ ∏ₙ Wₙ` is positive almost everywhere, *even at every
  point* (an infinite product of even factors) and dominated by the Gaussian `w₀`;
* the stage errors of every rational target become arbitrarily small, so every rational
  character lies in the closed span of the installed characters in `L²(w_∞)`;
* the nested list lengths are unbounded, and reading the lists gives an injective
  frequency sequence whose characters have dense span;
* every finite prefix inequality passes to the limit weight with the uniform constant
  `K_∞ = K_* + ∑ₙ τ_n`.

The main results are `Assembly.weightedExponentialBasisSharp`
(`WeightedExponentialBasisSharp P.Kinf` for every parameter set `P`),
`weightedExponentialBasisSharp_of_step` (constant `Kstar + η` from one `Kstar`) and

`weightedExponentialBasisSharp_of_finiteExtension`:
if the sharp finite extension holds for every `Kstar > 1`, then for every `ε > 0` there is
`C < 1 + ε` with `WeightedExponentialBasisSharp C`.

Following the paper we use `K_* = 1 + ε/10` and prefix budgets with `∑ τ_n = ε/4`, so that
`C = K_∞ = 1 + ε/10 + ε/4 < 1 + ε`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
open SchauderTranslates SchauderTranslates.Construction SchauderTranslates.LimitAssembly

namespace SchauderTranslates.Sharp.Assembly

section Limit
variable (P : Setup)

/-! ### The limiting weight -/

theorem limit_facts :
    Integrable (limitWeight gaussWeight.density (factor P)) volume ∧
    (∀ᵐ x ∂volume, 0 < limitWeight gaussWeight.density (factor P) x ∧
      limitWeight gaussWeight.density (factor P) x ≤ gaussWeight.density x) ∧
    (∫ x, gaussWeight.density x) - ∑' n, lossBudget n ≤
      ∫ x, limitWeight gaussWeight.density (factor P) x ∧
    Tendsto (fun N => ∫ x, ‖partialWeight gaussWeight.density (factor P) N x -
      limitWeight gaussWeight.density (factor P) x‖) atTop (𝓝 0) :=
  positive_limit_weight (μ := volume) gaussWeight.density (factor P)
    gaussWeight.integrable gaussWeight.positive (factor_measurable P) (factor_pos P)
    (factor_le_one P) hasSum_lossBudget.summable (fun n => (lossBudget_pos n).le)
    (fun n => (factor_cost P n).le)

/-- The limiting weight `w_∞ = w₀ ∏ₙ Wₙ`. -/
def limitW : Weight where
  density := limitWeight gaussWeight.density (factor P)
  measurable := gaussWeight.measurable.mul (Measurable.tprod (factor_measurable P))
  integrable := (limit_facts P).1
  positive := (limit_facts P).2.1.mono (fun _ h => h.1)

theorem limitW_density (t : ℝ) :
    (limitW P).density t = gaussWeight.density t * ∏' n, factor P n t := rfl

/-- The limiting weight is even at *every* point: it is the even Gaussian times the
infinite product of the even factors. -/
theorem limitW_even (t : ℝ) : (limitW P).density (-t) = (limitW P).density t := by
  rw [limitW_density, limitW_density, gaussWeight_even]
  congr 1
  exact tprod_congr (fun n => factor_even P n t)

/-- The limiting weight is dominated by the Gaussian reference weight almost everywhere. -/
theorem limitW_le_gauss :
    ∀ᵐ t ∂volume, (limitW P).density t ≤ gaussWeight.density t :=
  (limit_facts P).2.1.mono (fun _ h => h.2)

/-- The infinite product of the factors is at most one at every point. -/
theorem tprod_factor_le_one (t : ℝ) : ∏' n, factor P n t ≤ 1 := by
  by_cases hm : Multipliable (fun n => factor P n t)
  · exact le_of_tendsto' hm.hasProd.tendsto_prod_nat (fun N =>
      Finset.prod_le_one (fun n _ => (factor_pos P n t).le) (fun n _ => factor_le_one P n t))
  · rw [tprod_eq_one_of_not_multipliable hm]

/-- The Gaussian majorant even holds at every point. -/
theorem limitW_le_gauss_everywhere (t : ℝ) :
    (limitW P).density t ≤ gaussWeight.density t := by
  rw [limitW_density]
  have h := mul_le_mul_of_nonneg_left (tprod_factor_le_one P t) (gaussWeight_density_pos t).le
  rwa [mul_one] at h

/-- The mass bound `∫ w_∞ ≥ 1 - ∑ δ_n = 7/8 > 1/2`. -/
theorem limitW_mass : (7 / 8 : ℝ) ≤ ∫ t, (limitW P).density t := by
  have h := (limit_facts P).2.2.1
  rw [gaussWeight_integral, hasSum_lossBudget.tsum_eq] at h
  have h' : (1 : ℝ) - 1 / 8 ≤ ∫ t, (limitW P).density t := h
  linarith

theorem stages_density_antitone (t : ℝ) :
    Antitone (fun m => (stages P m).w.density t) :=
  antitone_nat_of_succ_le (fun m => stages_density_succ_le P m t)

/-- `w_∞ ≤ w_n` almost everywhere, for every stage `n`. -/
theorem limitW_le (n : ℕ) :
    ∀ᵐ t ∂volume, (limitW P).density t ≤ (stages P n).w.density t := by
  have hs := ae_summable_deficits gaussWeight.density (factor P) gaussWeight.integrable
    gaussWeight.positive (factor_measurable P) (factor_pos P) (factor_le_one P)
    hasSum_lossBudget.summable (fun n => (factor_cost P n).le)
  filter_upwards [partialWeight_tendsto gaussWeight.density (factor P)
    (factor_le_one P) hs] with t ht
  show limitWeight gaussWeight.density (factor P) t ≤ _
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← stages_density]
  exact stages_density_antitone P t hm

theorem limitW_L1 :
    Tendsto (fun m => ∫ t, ‖(stages P m).w.density t - (limitW P).density t‖)
      atTop (𝓝 0) := by
  simp_rw [stages_density]
  exact (limit_facts P).2.2.2

/-- Raw weighted norms of bounded continuous functions converge to the limit weight. -/
theorem normSq_tendsto_limit {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) :
    Tendsto (fun m => normSq (stages P m).w f) atTop (𝓝 (normSq (limitW P) f)) :=
  tendsto_integral_sq_mul (fun m => (stages P m).w.integrable) (limitW P).integrable
    (limitW_L1 P) hf hB

/-! ### Completeness: the errors of the rational targets -/

/-- Every rational character lies in the closure of any submodule of `L²(w_∞)` containing
all installed characters. -/
theorem rational_mem_closure
    (Q : Submodule ℂ (WeightedL2 (limitW P)))
    (hQ : ∀ n, ∀ i < (stages P n).d,
      weightedCharacter (limitW P) ((stages P n).seq i) ∈ Q) (q : ℚ) :
    weightedCharacter (limitW P) (q : ℝ) ∈ Q.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := stageError_small P q (pow_pos hε 2)
  obtain ⟨c, hc⟩ := exists_normSq_lt_of_distanceSq_lt _ _ hn
  refine ⟨∑ i : Fin (stages P n).d,
    c i • weightedCharacter (limitW P) ((stages P n).seq i), ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hQ n i i.isLt))
  · rw [dist_eq_norm]
    have hae : ((weightedCharacter (limitW P) (q : ℝ) -
        ∑ i : Fin (stages P n).d,
          c i • weightedCharacter (limitW P) ((stages P n).seq i) :
            WeightedL2 (limitW P)) : ℝ → ℂ) =ᵐ[(limitW P).measure]
        fun t => character q t - synthesis (stages P n).μ c t := by
      filter_upwards [Lp.coeFn_sub (weightedCharacter (limitW P) (q : ℝ))
          (∑ i : Fin (stages P n).d,
            c i • weightedCharacter (limitW P) ((stages P n).seq i)),
        weightedCharacter_ae (limitW P) (q : ℝ),
        weightedCharacter_sum_ae (limitW P) (fun i : Fin (stages P n).d =>
          (stages P n).seq i) Finset.univ c] with t h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      rfl
    have hsq : ‖weightedCharacter (limitW P) (q : ℝ) -
        ∑ i : Fin (stages P n).d,
          c i • weightedCharacter (limitW P) ((stages P n).seq i)‖ ^ 2 < ε ^ 2 := by
      rw [norm_sq_eq_normSq _ _ hae]
      exact lt_of_le_of_lt (normSq_le_of_density_le (limitW_le P n)
        (continuous_residual _ c _) (norm_residual_le _ c _)) hc
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp hsq

/-! ### Enumeration of the installed frequencies -/

/-- The nested list lengths are unbounded. -/
theorem stages_unbounded (B : ℕ) : ∃ n, B < (stages P n).d := by
  by_contra hcon
  have hle : ∀ n, (stages P n).d ≤ B := fun n => not_lt.mp (fun h => hcon ⟨n, h⟩)
  have hbdd : BddAbove (Set.range fun n => (stages P n).d) :=
    ⟨B, by rintro _ ⟨n, rfl⟩; exact hle n⟩
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hn₀' : (stages P n₀).d = sSup (Set.range fun n => (stages P n).d) := hn₀
  have hmax : ∀ n, (stages P n).d ≤ (stages P n₀).d := by
    intro n
    rw [hn₀']
    exact le_csSup hbdd ⟨n, rfl⟩
  let A : Set (WeightedL2 (limitW P)) := Set.range fun i : Fin (stages P n₀).d =>
    weightedCharacter (limitW P) ((stages P n₀).seq i)
  let Q := Submodule.span ℂ A
  have hQ : ∀ n, ∀ i < (stages P n).d,
      weightedCharacter (limitW P) ((stages P n).seq i) ∈ Q := by
    intro n i hi
    have key : i < (stages P n₀).d ∧ (stages P n).seq i = (stages P n₀).seq i := by
      rcases le_total n n₀ with h | h
      · exact ⟨lt_of_lt_of_le hi (stages_mono P h).1, ((stages_mono P h).2 i hi).symm⟩
      · have hd : (stages P n).d = (stages P n₀).d :=
          le_antisymm (hmax n) (stages_mono P h).1
        have hi' : i < (stages P n₀).d := hd ▸ hi
        exact ⟨hi', (stages_mono P h).2 i hi'⟩
    rw [key.2]
    exact Submodule.subset_span ⟨⟨i, key.1⟩, rfl⟩
  have hAfin : A.Finite := Set.finite_range _
  have : FiniteDimensional ℂ Q := FiniteDimensional.span_of_finite ℂ hAfin
  have hcl : Q.topologicalClosure = Q :=
    IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional Q)
  have hmem : ∀ q : ℚ, weightedCharacter (limitW P) (q : ℝ) ∈ Q := by
    intro q
    have := rational_mem_closure P Q hQ q
    rwa [hcl] at this
  have hli := characters_linearIndependent (limitW P) (fun q : ℚ => (q : ℝ))
    Rat.cast_injective
  have : Finite A := hAfin.to_subtype
  have : Finite ℚ := hli.finite_of_le_span_finite _ A (by rintro _ ⟨q, rfl⟩; exact hmem q)
  exact not_finite ℚ

/-- The `i`-th installed frequency, read from any stage whose list is longer than `i`. -/
def muInf (i : ℕ) : ℝ :=
  (stages P (Classical.choose (stages_unbounded P i))).seq i

theorem stages_seq_eq_muInf {n i : ℕ} (hi : i < (stages P n).d) :
    (stages P n).seq i = muInf P i := by
  have hc := Classical.choose_spec (stages_unbounded P i)
  have h1 := (stages_mono P
    (le_max_left n (Classical.choose (stages_unbounded P i)))).2 i hi
  have h2 := (stages_mono P
    (le_max_right n (Classical.choose (stages_unbounded P i)))).2 i hc
  exact h1.symm.trans h2

theorem muInf_injective : Function.Injective (muInf P) := by
  intro i j hij
  obtain ⟨n, hn⟩ := stages_unbounded P (max i j)
  have hi : i < (stages P n).d := lt_of_le_of_lt (le_max_left i j) hn
  have hj : j < (stages P n).d := lt_of_le_of_lt (le_max_right i j) hn
  have he : (fun k : Fin (stages P n).d => (stages P n).seq k) ⟨i, hi⟩ =
      (fun k : Fin (stages P n).d => (stages P n).seq k) ⟨j, hj⟩ := by
    simp only
    rw [stages_seq_eq_muInf P hi, stages_seq_eq_muInf P hj, hij]
  exact congrArg Fin.val ((stages P n).inj he)

/-- The installed characters in the limiting weighted space. -/
def atoms (i : ℕ) : WeightedL2 (limitW P) :=
  weightedCharacter (limitW P) (muInf P i)

/-- The installed characters have dense span in `L²(w_∞)`. -/
theorem atoms_dense :
    Dense (↑(Submodule.span ℂ (Set.range (atoms P))) :
      Set (WeightedL2 (limitW P))) := by
  set Q := Submodule.span ℂ (Set.range (atoms P))
  have hQ : ∀ n, ∀ i < (stages P n).d,
      weightedCharacter (limitW P) ((stages P n).seq i) ∈ Q := by
    intro n i hi
    rw [stages_seq_eq_muInf P hi]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hR : Submodule.span ℂ (Set.range fun q : ℚ => weightedCharacter (limitW P) (q : ℝ))
      ≤ Q.topologicalClosure := by
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact rational_mem_closure P Q hQ q
  have htot := Submodule.dense_iff_topologicalClosure_eq_top.mp
    (rational_characters_total (limitW P))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff, ← htot]
  exact Submodule.topologicalClosure_minimal _ hR Q.isClosed_topologicalClosure

/-! ### Passing the prefix bounds to the limit -/

/-- A stage prefix inequality restricted to an old initial segment of length `M ≤ d_m`. -/
theorem stage_prefix_range (k M m : ℕ) (hMd : M ≤ (stages P m).d) (a : ℕ → ℂ) :
    normSq (stages P m).w (fun t => ∑ i ∈ Finset.range M,
        if i < k then a i * character (muInf P i) t else 0) ≤
      P.Kinf ^ 2 * normSq (stages P m).w
        (fun t => ∑ i ∈ Finset.range M, a i * character (muInf P i) t) := by
  let C : ℕ → ℂ := fun i => if i < M then a i else 0
  have hb := (stages P m).bound k (fun i => C i)
  have hPeq : (fun t => ∑ i : Fin (stages P m).d, if (i : ℕ) < k then
      C i * character ((stages P m).seq i) t else 0) =
      fun t => ∑ i ∈ Finset.range M,
        if i < k then a i * character (muInf P i) t else 0 := by
    rw [prefix_fun_eq_range (stages P m).d k C (stages P m).seq]
    funext t
    apply sum_range_extend hMd
    · intro i hi
      simp only [C, if_pos hi, stages_seq_eq_muInf P (lt_of_lt_of_le hi hMd)]
    · intro i hi _
      simp [C, not_lt.mpr hi]
  have hGeq : synthesis (fun i : Fin (stages P m).d => (stages P m).seq i)
      (fun i => C i) =
      fun t => ∑ i ∈ Finset.range M, a i * character (muInf P i) t := by
    funext t
    rw [synthesis_seq]
    apply sum_range_extend hMd
    · intro i hi
      simp only [C, if_pos hi, stages_seq_eq_muInf P (lt_of_lt_of_le hi hMd)]
    · intro i hi _
      simp [C, not_lt.mpr hi]
  rw [hPeq, hGeq] at hb
  have hK : (stages P m).K ^ 2 ≤ P.Kinf ^ 2 :=
    pow_le_pow_left₀ (by linarith [stages_one_le_K P m]) (stages_K_le P m) 2
  exact hb.trans (mul_le_mul_of_nonneg_right hK (normSq_nonneg _ _))

/-- The prefix inequality for an old initial segment passes to the limit weight. -/
theorem limit_prefix_range (k M : ℕ) (a : ℕ → ℂ) :
    normSq (limitW P) (fun t => ∑ i ∈ Finset.range M,
        if i < k then a i * character (muInf P i) t else 0) ≤
      P.Kinf ^ 2 * normSq (limitW P)
        (fun t => ∑ i ∈ Finset.range M, a i * character (muInf P i) t) := by
  obtain ⟨n, hn⟩ := stages_unbounded P M
  let F : ℝ → ℂ := fun t =>
    ∑ i ∈ Finset.range M, (if i < k then a i else 0) * character (muInf P i) t
  let G : ℝ → ℂ := fun t => ∑ i ∈ Finset.range M, a i * character (muInf P i) t
  have hFc : Continuous F := continuous_finsetSum_character _ _ _
  have hGc : Continuous G := continuous_finsetSum_character _ _ _
  have hFb : ∀ t, ‖F t‖ ≤ ∑ i ∈ Finset.range M, ‖(if i < k then a i else 0)‖ :=
    norm_finsetSum_character_le _ _ _
  have hGb : ∀ t, ‖G t‖ ≤ ∑ i ∈ Finset.range M, ‖a i‖ := norm_finsetSum_character_le _ _ _
  have hF : F = fun t => ∑ i ∈ Finset.range M,
      if i < k then a i * character (muInf P i) t else 0 :=
    prefix_sum_ite_mul M k a (muInf P)
  have hstage : ∀ m, n ≤ m →
      normSq (stages P m).w F ≤ P.Kinf ^ 2 * normSq (stages P m).w G := by
    intro m hm
    rw [hF]
    exact stage_prefix_range P k M m
      (lt_of_lt_of_le hn (stages_mono P hm).1).le a
  have hlim : normSq (limitW P) F ≤ P.Kinf ^ 2 * normSq (limitW P) G :=
    le_of_tendsto_of_tendsto (normSq_tendsto_limit P hFc hFb)
      ((normSq_tendsto_limit P hGc hGb).const_mul _)
      (by filter_upwards [eventually_ge_atTop n] with m hm using hstage m hm)
  rw [hF] at hlim
  exact hlim

/-- Every finite initial list of the installed frequencies has prefix constant `K_∞` in
`L²(w_∞)`, in the language of the contracts. -/
theorem limit_prefixBound (M : ℕ) :
    PrefixBound (limitW P) (fun i : Fin M => muInf P i) P.Kinf := by
  intro k c
  obtain ⟨a, rfl⟩ : ∃ a : ℕ → ℂ, c = fun i : Fin M => a i :=
    ⟨extendCoeff c, (extendCoeff_fin c).symm⟩
  have h := limit_prefix_range P k M a
  have h2 : synthesis (fun i : Fin M => muInf P i) (fun i => a i) =
      fun t => ∑ i ∈ Finset.range M, a i * character (muInf P i) t :=
    funext (synthesis_seq _ _ _)
  rw [← prefix_fun_eq_range M k a (muInf P), ← h2] at h
  exact h

/-- Every finite prefix inequality survives in `L²(w_∞)` with the constant `K_∞`. -/
theorem atoms_prefix_sum (N M : ℕ) (a : ℕ → ℂ) :
    ‖∑ i ∈ Finset.range M, (if i < N then a i else 0) • atoms P i‖ ≤
      P.Kinf * ‖∑ i ∈ Finset.range M, a i • atoms P i‖ := by
  have hlim := limit_prefix_range P N M a
  have h1 : ‖∑ i ∈ Finset.range M, (if i < N then a i else 0) • atoms P i‖ ^ 2 =
      normSq (limitW P) (fun t => ∑ i ∈ Finset.range M,
        (if i < N then a i else 0) * character (muInf P i) t) :=
    norm_sq_eq_normSq (limitW P) _ (weightedCharacter_sum_ae (limitW P)
      (muInf P) (Finset.range M) (fun i => if i < N then a i else 0))
  rw [prefix_sum_ite_mul] at h1
  have h2 : ‖∑ i ∈ Finset.range M, a i • atoms P i‖ ^ 2 =
      normSq (limitW P) (fun t => ∑ i ∈ Finset.range M,
        a i * character (muInf P i) t) :=
    norm_sq_eq_normSq (limitW P) _ (weightedCharacter_sum_ae (limitW P)
      (muInf P) (Finset.range M) a)
  have hsq : ‖∑ i ∈ Finset.range M, (if i < N then a i else 0) • atoms P i‖ ^ 2 ≤
      (P.Kinf * ‖∑ i ∈ Finset.range M, a i • atoms P i‖) ^ 2 := by
    rw [mul_pow, h1, h2]
    exact hlim
  have hK0 : 0 ≤ P.Kinf := by linarith [P.one_le_Kinf]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))
    two_ne_zero).mp hsq

/-- The uniform prefix bound in the form used by the Schauder criterion. -/
theorem atoms_prefix (N : ℕ) (c : ℕ →₀ ℂ) :
    ‖finitePrefix (atoms P) N c‖ ≤
      P.Kinf * ‖Finsupp.linearCombination ℂ (atoms P) c‖ := by
  set M := c.support.sup id + 1 with hM
  have hsupp : ∀ i, M ≤ i → c i = 0 := by
    intro i hi
    by_contra h
    have h' : i ≤ c.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr h)
    omega
  have hlc : Finsupp.linearCombination ℂ (atoms P) c =
      ∑ i ∈ Finset.range M, c i • atoms P i := by
    rw [Finsupp.linearCombination_apply]
    apply c.sum_of_support_subset
    · intro i hi
      have h' : i ≤ c.support.sup id := Finset.le_sup (f := id) hi
      exact Finset.mem_range.mpr (by omega)
    · intro i _
      simp
  have hpre : finitePrefix (atoms P) N c =
      ∑ i ∈ Finset.range M, (if i < N then c i else 0) • atoms P i := by
    rw [finitePrefix_apply]
    have e1 : ∑ i ∈ Finset.range N, c i • atoms P i =
        ∑ i ∈ Finset.range N, (if i < N then c i else 0) • atoms P i :=
      Finset.sum_congr rfl (fun i hi => by rw [if_pos (Finset.mem_range.mp hi)])
    have e2 : ∑ i ∈ Finset.range N, (if i < N then c i else 0) • atoms P i =
        ∑ i ∈ Finset.range (max N M), (if i < N then c i else 0) • atoms P i :=
      Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _))
        (fun i _ hi => by rw [if_neg (fun h => hi (Finset.mem_range.mpr h)), zero_smul])
    have e3 : ∑ i ∈ Finset.range M, (if i < N then c i else 0) • atoms P i =
        ∑ i ∈ Finset.range (max N M), (if i < N then c i else 0) • atoms P i :=
      Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) (fun i _ hi => by
        have hiM : M ≤ i := not_lt.mp (fun h => hi (Finset.mem_range.mpr h))
        rw [hsupp i hiM]
        simp)
    rw [e1, e2, e3]
  rw [hpre, hlc]
  exact atoms_prefix_sum P N M c

/-! ### Node-level statements -/

/-- The span of all installed characters in `L²(w_∞)`. -/
def installedSpan : Submodule ℂ (WeightedL2 (limitW P)) :=
  Submodule.span ℂ {x | ∃ n, ∃ i < (stages P n).d,
    x = weightedCharacter (limitW P) ((stages P n).seq i)}

theorem mem_installedSpan (n i : ℕ) (hi : i < (stages P n).d) :
    weightedCharacter (limitW P) ((stages P n).seq i) ∈ installedSpan P :=
  Submodule.subset_span ⟨n, i, hi, rfl⟩

/-- For every rational target the stage errors decrease to zero, and the rational
character lies in the closed span of the installed characters in `L²(w_∞)`. -/
theorem visited_target_errors (q : ℚ) :
    Antitone (fun n => stageError P n q) ∧
    Tendsto (fun n => stageError P n q) atTop (𝓝 0) ∧
    weightedCharacter (limitW P) (q : ℝ) ∈ (installedSpan P).topologicalClosure := by
  refine ⟨stageError_antitone P q, ?_,
    rational_mem_closure P (installedSpan P) (mem_installedSpan P) q⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := stageError_small P q hε
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (stageError_nonneg P n q)]
  exact lt_of_le_of_lt (stageError_antitone P q hn) hN

/-- The list lengths are unbounded, the installed entries define one injective sequence,
and its characters have dense span. -/
theorem enumerate_installed_atoms :
    (∀ B : ℕ, ∃ n, B < (stages P n).d) ∧
    (∀ n i, i < (stages P n).d → (stages P n).seq i = muInf P i) ∧
    Function.Injective (muInf P) ∧
    Dense (↑(Submodule.span ℂ (Set.range fun i =>
      weightedCharacter (limitW P) (muInf P i))) :
        Set (WeightedL2 (limitW P))) :=
  ⟨stages_unbounded P, fun _ _ hi => stages_seq_eq_muInf P hi,
    muInf_injective P, atoms_dense P⟩

/-- Every finite initial segment of the installed list is independent in `L²(w_∞)` and has
prefix constant `K_∞ = K_* + ∑ₙ τ_n`. -/
theorem limit_prefix_bounds (M : ℕ) :
    LinearIndependent ℂ (fun i : Fin M => weightedCharacter (limitW P) (muInf P i)) ∧
    PrefixBound (limitW P) (fun i : Fin M => muInf P i) P.Kinf :=
  ⟨characters_linearIndependent (limitW P) (fun i : Fin M => muInf P i)
      ((muInf_injective P).comp Fin.val_injective),
    limit_prefixBound P M⟩

/-- The installed characters form an ordered Schauder basis of `L²(w_∞)`: the partial sum
maps extend with norm at most `K_∞` and converge strongly by density (paper: subsection
"Completeness and convergence of the partial sums"). -/
theorem atoms_orderedSchauderBasis : OrderedSchauderBasis (atoms P) :=
  schauder_of_independent_dense_span (atoms P)
    (characters_linearIndependent (limitW P) (muInf P) (muInf_injective P))
    (atoms_dense P) (by linarith [P.one_le_Kinf]) (atoms_prefix P)

/-- The sharp weighted exponential basis for the parameters `P`: the limiting weight is
even and dominated by the Gaussian, the installed frequencies are injective with dense
span, and all finite prefixes are bounded by `K_∞ = K_* + ∑ₙ τ_n`. -/
theorem weightedExponentialBasisSharp : WeightedExponentialBasisSharp P.Kinf :=
  ⟨limitW P, muInf P, limitW_even P, limitW_le_gauss P, muInf_injective P,
    atoms_dense P, atoms_prefix P⟩

end Limit
end SchauderTranslates.Sharp.Assembly

namespace SchauderTranslates.Sharp
open Assembly

/-- From the sharp finite extension with one-step constant `Kstar ≥ 1`, the assembly gives
a sharp weighted exponential basis with constant `Kstar + η`, for every `η > 0`: the prefix
budgets are `τ_n = 4 η · prefixBudget n = (η/2) 2⁻ⁿ`, with total `η`. -/
theorem weightedExponentialBasisSharp_of_step {Kstar : ℝ} (hK : 1 ≤ Kstar)
    (hfe : FiniteExtensionSharp Kstar) {η : ℝ} (hη : 0 < η) :
    WeightedExponentialBasisSharp (Kstar + η) := by
  obtain ⟨s, hs, -⟩ := fair_schedule
  have hsum : HasSum (fun n => 4 * η * prefixBudget n) η := by
    have h := hasSum_prefixBudget.mul_left (4 * η)
    have he : 4 * η * (1 / 4) = η := by ring
    rwa [he] at h
  exact weightedExponentialBasisSharp
    { Kstar := Kstar
      one_le_Kstar := hK
      extension := hfe
      τ := fun n => 4 * η * prefixBudget n
      τ_pos := fun n => mul_pos (by linarith) (prefixBudget_pos n)
      τsum := η
      τ_hasSum := hsum
      s := s
      fair := hs }

/-- **Sharp weighted exponential basis** (paper: Theorem `h2:thm:weighted`, conditional on
the one-step extension Proposition `h2:prop:extension`). If the sharp finite extension
holds for every one-step constant `Kstar > 1`, then for every `ε > 0` there is a constant
`C < 1 + ε` and an even weight dominated by the Gaussian with an injective frequency
sequence whose characters have dense span and prefix constant `C`.

As in the paper, `K_* = 1 + ε/10` and `∑ₙ τ_n = ε/4`, so `C = K_∞ = 1 + ε/10 + ε/4`. -/
theorem weightedExponentialBasisSharp_of_finiteExtension
    (hfe : ∀ Kstar : ℝ, 1 < Kstar → FiniteExtensionSharp Kstar) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, C < 1 + ε ∧ WeightedExponentialBasisSharp C := by
  refine ⟨1 + ε / 10 + ε / 4, by linarith, ?_⟩
  exact weightedExponentialBasisSharp_of_step (by linarith) (hfe _ (by linarith))
    (by positivity)

end SchauderTranslates.Sharp
