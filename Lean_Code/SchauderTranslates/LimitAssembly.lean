import Lean_Code.SchauderTranslates.LimitStagesConstruct
import Lean_Code.SchauderTranslates.RationalTotality
import Lean_Code.SchauderTranslates.SchauderCriterion
import Lean_Code.SchauderTranslates.MainReduction

/-!
# Assembly of the infinite construction

Assuming the finite extension principle `Construction.FiniteExtensionPrinciple`
(blueprint `extend:line`) as a hypothesis, this file completes the blueprint nodes

* `limit:errors`: the stage errors of every rational target become arbitrarily small,
  so every rational character lies in the closed span of the installed characters in
  `L²(w_∞)`;
* `limit:enumerate`: the nested list lengths are unbounded, and reading the lists gives
  an injective frequency sequence whose characters have dense span;
* `limit:prefix`: every finite prefix inequality passes to the limit weight with the
  uniform constant `49/4 < 13`;
* `basis:weighted`: `Construction.WeightedExponentialBasisExists`.

The stage construction (`limit:stages`) is in `LimitStagesConstruct`, and the positive
infinite product (`limit:positive`) is `positive_limit_weight`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace SchauderTranslates.LimitAssembly
open SchauderTranslates.Construction

section Limit
variable (hfe : FiniteExtensionPrinciple) (s : ℕ → ℚ)

/-! ### The limiting weight (`limit:positive` applied to the stages) -/

theorem limit_facts :
    Integrable (limitWeight gaussWeight.density (factor hfe s)) volume ∧
    (∀ᵐ x ∂volume, 0 < limitWeight gaussWeight.density (factor hfe s) x ∧
      limitWeight gaussWeight.density (factor hfe s) x ≤ gaussWeight.density x) ∧
    (∫ x, gaussWeight.density x) - ∑' n, lossBudget n ≤
      ∫ x, limitWeight gaussWeight.density (factor hfe s) x ∧
    Tendsto (fun N => ∫ x, ‖partialWeight gaussWeight.density (factor hfe s) N x -
      limitWeight gaussWeight.density (factor hfe s) x‖) atTop (𝓝 0) :=
  positive_limit_weight (μ := volume) gaussWeight.density (factor hfe s)
    gaussWeight.integrable gaussWeight.positive (factor_measurable hfe s) (factor_pos hfe s)
    (factor_le_one hfe s) hasSum_lossBudget.summable (fun n => (lossBudget_pos n).le)
    (fun n => (factor_cost hfe s n).le)

/-- The limiting weight `w_∞ = w₀ ∏ₙ Wₙ`. -/
def limitW : Weight where
  density := limitWeight gaussWeight.density (factor hfe s)
  measurable := gaussWeight.measurable.mul (Measurable.tprod (factor_measurable hfe s))
  integrable := (limit_facts hfe s).1
  positive := (limit_facts hfe s).2.1.mono (fun _ h => h.1)

theorem stages_density_antitone (t : ℝ) :
    Antitone (fun m => (stages hfe s m).w.density t) :=
  antitone_nat_of_succ_le (fun m => stages_density_succ_le hfe s m t)

/-- `w_∞ ≤ w_n` almost everywhere, for every stage `n`. -/
theorem limitW_le (n : ℕ) :
    ∀ᵐ t ∂volume, (limitW hfe s).density t ≤ (stages hfe s n).w.density t := by
  have hs := ae_summable_deficits gaussWeight.density (factor hfe s) gaussWeight.integrable
    gaussWeight.positive (factor_measurable hfe s) (factor_pos hfe s) (factor_le_one hfe s)
    hasSum_lossBudget.summable (fun n => (factor_cost hfe s n).le)
  filter_upwards [partialWeight_tendsto gaussWeight.density (factor hfe s)
    (factor_le_one hfe s) hs] with t ht
  show limitWeight gaussWeight.density (factor hfe s) t ≤ _
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← stages_density]
  exact stages_density_antitone hfe s t hm

theorem limitW_L1 :
    Tendsto (fun m => ∫ t, ‖(stages hfe s m).w.density t - (limitW hfe s).density t‖)
      atTop (𝓝 0) := by
  simp_rw [stages_density]
  exact (limit_facts hfe s).2.2.2

/-- Raw weighted norms of bounded continuous functions converge to the limit weight. -/
theorem normSq_tendsto_limit {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) :
    Tendsto (fun m => normSq (stages hfe s m).w f) atTop (𝓝 (normSq (limitW hfe s) f)) :=
  tendsto_integral_sq_mul (fun m => (stages hfe s m).w.integrable) (limitW hfe s).integrable
    (limitW_L1 hfe s) hf hB

/-! ### `limit:errors` -/

/-- Every rational character lies in the closure of any submodule of `L²(w_∞)` containing
all installed characters. -/
theorem rational_mem_closure (hs : FairSchedule s)
    (P : Submodule ℂ (WeightedL2 (limitW hfe s)))
    (hP : ∀ n, ∀ i < (stages hfe s n).d,
      weightedCharacter (limitW hfe s) ((stages hfe s n).seq i) ∈ P) (q : ℚ) :
    weightedCharacter (limitW hfe s) (q : ℝ) ∈ P.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := stageError_small hfe s hs q (pow_pos hε 2)
  obtain ⟨c, hc⟩ := exists_normSq_lt_of_distanceSq_lt _ _ hn
  refine ⟨∑ i : Fin (stages hfe s n).d,
    c i • weightedCharacter (limitW hfe s) ((stages hfe s n).seq i), ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hP n i i.isLt))
  · rw [dist_eq_norm]
    have hae : ((weightedCharacter (limitW hfe s) (q : ℝ) -
        ∑ i : Fin (stages hfe s n).d,
          c i • weightedCharacter (limitW hfe s) ((stages hfe s n).seq i) :
            WeightedL2 (limitW hfe s)) : ℝ → ℂ) =ᵐ[(limitW hfe s).measure]
        fun t => character q t - synthesis (stages hfe s n).μ c t := by
      filter_upwards [Lp.coeFn_sub (weightedCharacter (limitW hfe s) (q : ℝ))
          (∑ i : Fin (stages hfe s n).d,
            c i • weightedCharacter (limitW hfe s) ((stages hfe s n).seq i)),
        weightedCharacter_ae (limitW hfe s) (q : ℝ),
        weightedCharacter_sum_ae (limitW hfe s) (fun i : Fin (stages hfe s n).d =>
          (stages hfe s n).seq i) Finset.univ c] with t h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      rfl
    have hsq : ‖weightedCharacter (limitW hfe s) (q : ℝ) -
        ∑ i : Fin (stages hfe s n).d,
          c i • weightedCharacter (limitW hfe s) ((stages hfe s n).seq i)‖ ^ 2 < ε ^ 2 := by
      rw [norm_sq_eq_normSq _ _ hae]
      exact lt_of_le_of_lt (normSq_le_of_density_le (limitW_le hfe s n)
        (continuous_residual _ c _) (norm_residual_le _ c _)) hc
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp hsq

/-! ### `limit:enumerate` -/

/-- The nested list lengths are unbounded. -/
theorem stages_unbounded (hs : FairSchedule s) (B : ℕ) : ∃ n, B < (stages hfe s n).d := by
  by_contra hcon
  have hle : ∀ n, (stages hfe s n).d ≤ B := fun n => not_lt.mp (fun h => hcon ⟨n, h⟩)
  have hbdd : BddAbove (Set.range fun n => (stages hfe s n).d) :=
    ⟨B, by rintro _ ⟨n, rfl⟩; exact hle n⟩
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hn₀' : (stages hfe s n₀).d = sSup (Set.range fun n => (stages hfe s n).d) := hn₀
  have hmax : ∀ n, (stages hfe s n).d ≤ (stages hfe s n₀).d := by
    intro n
    rw [hn₀']
    exact le_csSup hbdd ⟨n, rfl⟩
  let A : Set (WeightedL2 (limitW hfe s)) := Set.range fun i : Fin (stages hfe s n₀).d =>
    weightedCharacter (limitW hfe s) ((stages hfe s n₀).seq i)
  let P := Submodule.span ℂ A
  have hP : ∀ n, ∀ i < (stages hfe s n).d,
      weightedCharacter (limitW hfe s) ((stages hfe s n).seq i) ∈ P := by
    intro n i hi
    have key : i < (stages hfe s n₀).d ∧ (stages hfe s n).seq i = (stages hfe s n₀).seq i := by
      rcases le_total n n₀ with h | h
      · exact ⟨lt_of_lt_of_le hi (stages_mono hfe s h).1, ((stages_mono hfe s h).2 i hi).symm⟩
      · have hd : (stages hfe s n).d = (stages hfe s n₀).d :=
          le_antisymm (hmax n) (stages_mono hfe s h).1
        have hi' : i < (stages hfe s n₀).d := hd ▸ hi
        exact ⟨hi', (stages_mono hfe s h).2 i hi'⟩
    rw [key.2]
    exact Submodule.subset_span ⟨⟨i, key.1⟩, rfl⟩
  have hAfin : A.Finite := Set.finite_range _
  have : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ hAfin
  have hcl : P.topologicalClosure = P :=
    IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional P)
  have hmem : ∀ q : ℚ, weightedCharacter (limitW hfe s) (q : ℝ) ∈ P := by
    intro q
    have := rational_mem_closure hfe s hs P hP q
    rwa [hcl] at this
  have hli := characters_linearIndependent (limitW hfe s) (fun q : ℚ => (q : ℝ))
    Rat.cast_injective
  have : Finite A := hAfin.to_subtype
  have : Finite ℚ := hli.finite_of_le_span_finite _ A (by rintro _ ⟨q, rfl⟩; exact hmem q)
  exact not_finite ℚ

/-- The `i`-th installed frequency, read from any stage whose list is longer than `i`. -/
def muInf (hs : FairSchedule s) (i : ℕ) : ℝ :=
  (stages hfe s (Classical.choose (stages_unbounded hfe s hs i))).seq i

theorem stages_seq_eq_muInf (hs : FairSchedule s) {n i : ℕ} (hi : i < (stages hfe s n).d) :
    (stages hfe s n).seq i = muInf hfe s hs i := by
  have hc := Classical.choose_spec (stages_unbounded hfe s hs i)
  have h1 := (stages_mono hfe s
    (le_max_left n (Classical.choose (stages_unbounded hfe s hs i)))).2 i hi
  have h2 := (stages_mono hfe s
    (le_max_right n (Classical.choose (stages_unbounded hfe s hs i)))).2 i hc
  exact h1.symm.trans h2

theorem muInf_injective (hs : FairSchedule s) : Function.Injective (muInf hfe s hs) := by
  intro i j hij
  obtain ⟨n, hn⟩ := stages_unbounded hfe s hs (max i j)
  have hi : i < (stages hfe s n).d := lt_of_le_of_lt (le_max_left i j) hn
  have hj : j < (stages hfe s n).d := lt_of_le_of_lt (le_max_right i j) hn
  have he : (fun k : Fin (stages hfe s n).d => (stages hfe s n).seq k) ⟨i, hi⟩ =
      (fun k : Fin (stages hfe s n).d => (stages hfe s n).seq k) ⟨j, hj⟩ := by
    simp only
    rw [stages_seq_eq_muInf hfe s hs hi, stages_seq_eq_muInf hfe s hs hj, hij]
  exact congrArg Fin.val ((stages hfe s n).inj he)

/-- The installed characters in the limiting weighted space. -/
def atoms (hs : FairSchedule s) (i : ℕ) : WeightedL2 (limitW hfe s) :=
  weightedCharacter (limitW hfe s) (muInf hfe s hs i)

/-- The installed characters have dense span in `L²(w_∞)`. -/
theorem atoms_dense (hs : FairSchedule s) :
    Dense (↑(Submodule.span ℂ (Set.range (atoms hfe s hs))) :
      Set (WeightedL2 (limitW hfe s))) := by
  set P := Submodule.span ℂ (Set.range (atoms hfe s hs))
  have hP : ∀ n, ∀ i < (stages hfe s n).d,
      weightedCharacter (limitW hfe s) ((stages hfe s n).seq i) ∈ P := by
    intro n i hi
    rw [stages_seq_eq_muInf hfe s hs hi]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hR : Submodule.span ℂ (Set.range fun q : ℚ => weightedCharacter (limitW hfe s) (q : ℝ))
      ≤ P.topologicalClosure := by
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact rational_mem_closure hfe s hs P hP q
  have htot := Submodule.dense_iff_topologicalClosure_eq_top.mp
    (rational_characters_total (limitW hfe s))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff, ← htot]
  exact Submodule.topologicalClosure_minimal _ hR P.isClosed_topologicalClosure

/-! ### `limit:prefix` -/

/-- A prefix cut of a finite character sum, written over `Finset.range`. -/
theorem prefix_fun_eq_range (M k : ℕ) (a : ℕ → ℂ) (ξ : ℕ → ℝ) :
    (fun t => ∑ i : Fin M, if (i : ℕ) < k then a i * character (ξ i) t else 0) =
      fun t => ∑ i ∈ Finset.range M, if i < k then a i * character (ξ i) t else 0 :=
  funext fun t =>
    Fin.sum_univ_eq_sum_range (fun i => if i < k then a i * character (ξ i) t else 0) M

theorem prefix_sum_ite_mul (M k : ℕ) (a : ℕ → ℂ) (ξ : ℕ → ℝ) :
    (fun t => ∑ i ∈ Finset.range M, (if i < k then a i else 0) * character (ξ i) t) =
      fun t => ∑ i ∈ Finset.range M, if i < k then a i * character (ξ i) t else 0 := by
  funext t
  exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)

/-- A stage prefix inequality restricted to an old initial segment of length `M ≤ d_m`. -/
theorem stage_prefix_range (hs : FairSchedule s) (k M m : ℕ) (hMd : M ≤ (stages hfe s m).d)
    (a : ℕ → ℂ) :
    normSq (stages hfe s m).w (fun t => ∑ i ∈ Finset.range M,
        if i < k then a i * character (muInf hfe s hs i) t else 0) ≤
      (49 / 4) ^ 2 * normSq (stages hfe s m).w
        (fun t => ∑ i ∈ Finset.range M, a i * character (muInf hfe s hs i) t) := by
  let C : ℕ → ℂ := fun i => if i < M then a i else 0
  have hb := (stages hfe s m).bound k (fun i => C i)
  have hPeq : (fun t => ∑ i : Fin (stages hfe s m).d, if (i : ℕ) < k then
      C i * character ((stages hfe s m).seq i) t else 0) =
      fun t => ∑ i ∈ Finset.range M,
        if i < k then a i * character (muInf hfe s hs i) t else 0 := by
    rw [prefix_fun_eq_range (stages hfe s m).d k C (stages hfe s m).seq]
    funext t
    apply sum_range_extend hMd
    · intro i hi
      simp only [C, if_pos hi, stages_seq_eq_muInf hfe s hs (lt_of_lt_of_le hi hMd)]
    · intro i hi _
      simp [C, not_lt.mpr hi]
  have hGeq : synthesis (fun i : Fin (stages hfe s m).d => (stages hfe s m).seq i)
      (fun i => C i) =
      fun t => ∑ i ∈ Finset.range M, a i * character (muInf hfe s hs i) t := by
    funext t
    rw [synthesis_seq]
    apply sum_range_extend hMd
    · intro i hi
      simp only [C, if_pos hi, stages_seq_eq_muInf hfe s hs (lt_of_lt_of_le hi hMd)]
    · intro i hi _
      simp [C, not_lt.mpr hi]
  rw [hPeq, hGeq] at hb
  have hK : (stages hfe s m).K ^ 2 ≤ (49 / 4) ^ 2 :=
    pow_le_pow_left₀ (by linarith [stages_one_le_K hfe s m]) (stages_K_le hfe s m) 2
  exact hb.trans (mul_le_mul_of_nonneg_right hK (normSq_nonneg _ _))

/-- The prefix inequality for an old initial segment passes to the limit weight. -/
theorem limit_prefix_range (hs : FairSchedule s) (k M : ℕ) (a : ℕ → ℂ) :
    normSq (limitW hfe s) (fun t => ∑ i ∈ Finset.range M,
        if i < k then a i * character (muInf hfe s hs i) t else 0) ≤
      (49 / 4) ^ 2 * normSq (limitW hfe s)
        (fun t => ∑ i ∈ Finset.range M, a i * character (muInf hfe s hs i) t) := by
  obtain ⟨n, hn⟩ := stages_unbounded hfe s hs M
  let P : ℝ → ℂ := fun t =>
    ∑ i ∈ Finset.range M, (if i < k then a i else 0) * character (muInf hfe s hs i) t
  let G : ℝ → ℂ := fun t => ∑ i ∈ Finset.range M, a i * character (muInf hfe s hs i) t
  have hPc : Continuous P := continuous_finsetSum_character _ _ _
  have hGc : Continuous G := continuous_finsetSum_character _ _ _
  have hPb : ∀ t, ‖P t‖ ≤ ∑ i ∈ Finset.range M, ‖(if i < k then a i else 0)‖ :=
    norm_finsetSum_character_le _ _ _
  have hGb : ∀ t, ‖G t‖ ≤ ∑ i ∈ Finset.range M, ‖a i‖ := norm_finsetSum_character_le _ _ _
  have hP : P = fun t => ∑ i ∈ Finset.range M,
      if i < k then a i * character (muInf hfe s hs i) t else 0 :=
    prefix_sum_ite_mul M k a (muInf hfe s hs)
  have hstage : ∀ m, n ≤ m →
      normSq (stages hfe s m).w P ≤ (49 / 4) ^ 2 * normSq (stages hfe s m).w G := by
    intro m hm
    rw [hP]
    exact stage_prefix_range hfe s hs k M m
      (lt_of_lt_of_le hn (stages_mono hfe s hm).1).le a
  have hlim : normSq (limitW hfe s) P ≤ (49 / 4) ^ 2 * normSq (limitW hfe s) G :=
    le_of_tendsto_of_tendsto (normSq_tendsto_limit hfe s hPc hPb)
      ((normSq_tendsto_limit hfe s hGc hGb).const_mul _)
      (by filter_upwards [eventually_ge_atTop n] with m hm using hstage m hm)
  rw [hP] at hlim
  exact hlim

/-- `limit:prefix` in the language of the contracts: every finite initial list of the
installed frequencies has prefix constant `49/4 < 13` in `L²(w_∞)`. -/
theorem limit_prefixBound (hs : FairSchedule s) (M : ℕ) :
    PrefixBound (limitW hfe s) (fun i : Fin M => muInf hfe s hs i) (49 / 4) := by
  intro k c
  obtain ⟨a, rfl⟩ : ∃ a : ℕ → ℂ, c = fun i : Fin M => a i :=
    ⟨extendCoeff c, (extendCoeff_fin c).symm⟩
  have h := limit_prefix_range hfe s hs k M a
  have h2 : synthesis (fun i : Fin M => muInf hfe s hs i) (fun i => a i) =
      fun t => ∑ i ∈ Finset.range M, a i * character (muInf hfe s hs i) t :=
    funext (synthesis_seq _ _ _)
  rw [← prefix_fun_eq_range M k a (muInf hfe s hs), ← h2] at h
  exact h

/-- Every finite prefix inequality survives in `L²(w_∞)` with the constant `49/4`. -/
theorem atoms_prefix_sum (hs : FairSchedule s) (N M : ℕ) (a : ℕ → ℂ) :
    ‖∑ i ∈ Finset.range M, (if i < N then a i else 0) • atoms hfe s hs i‖ ≤
      49 / 4 * ‖∑ i ∈ Finset.range M, a i • atoms hfe s hs i‖ := by
  have hlim := limit_prefix_range hfe s hs N M a
  have h1 : ‖∑ i ∈ Finset.range M, (if i < N then a i else 0) • atoms hfe s hs i‖ ^ 2 =
      normSq (limitW hfe s) (fun t => ∑ i ∈ Finset.range M,
        (if i < N then a i else 0) * character (muInf hfe s hs i) t) :=
    norm_sq_eq_normSq (limitW hfe s) _ (weightedCharacter_sum_ae (limitW hfe s)
      (muInf hfe s hs) (Finset.range M) (fun i => if i < N then a i else 0))
  rw [prefix_sum_ite_mul] at h1
  have h2 : ‖∑ i ∈ Finset.range M, a i • atoms hfe s hs i‖ ^ 2 =
      normSq (limitW hfe s) (fun t => ∑ i ∈ Finset.range M,
        a i * character (muInf hfe s hs i) t) :=
    norm_sq_eq_normSq (limitW hfe s) _ (weightedCharacter_sum_ae (limitW hfe s)
      (muInf hfe s hs) (Finset.range M) a)
  have hsq : ‖∑ i ∈ Finset.range M, (if i < N then a i else 0) • atoms hfe s hs i‖ ^ 2 ≤
      (49 / 4 * ‖∑ i ∈ Finset.range M, a i • atoms hfe s hs i‖) ^ 2 := by
    rw [mul_pow, h1, h2]
    exact hlim
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The uniform prefix bound in the form used by the Schauder criterion. -/
theorem atoms_prefix (hs : FairSchedule s) (N : ℕ) (c : ℕ →₀ ℂ) :
    ‖finitePrefix (atoms hfe s hs) N c‖ ≤
      49 / 4 * ‖Finsupp.linearCombination ℂ (atoms hfe s hs) c‖ := by
  set M := c.support.sup id + 1 with hM
  have hsupp : ∀ i, M ≤ i → c i = 0 := by
    intro i hi
    by_contra h
    have h' : i ≤ c.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr h)
    omega
  have hlc : Finsupp.linearCombination ℂ (atoms hfe s hs) c =
      ∑ i ∈ Finset.range M, c i • atoms hfe s hs i := by
    rw [Finsupp.linearCombination_apply]
    apply c.sum_of_support_subset
    · intro i hi
      have h' : i ≤ c.support.sup id := Finset.le_sup (f := id) hi
      exact Finset.mem_range.mpr (by omega)
    · intro i _
      simp
  have hpre : finitePrefix (atoms hfe s hs) N c =
      ∑ i ∈ Finset.range M, (if i < N then c i else 0) • atoms hfe s hs i := by
    rw [finitePrefix_apply]
    have e1 : ∑ i ∈ Finset.range N, c i • atoms hfe s hs i =
        ∑ i ∈ Finset.range N, (if i < N then c i else 0) • atoms hfe s hs i :=
      Finset.sum_congr rfl (fun i hi => by rw [if_pos (Finset.mem_range.mp hi)])
    have e2 : ∑ i ∈ Finset.range N, (if i < N then c i else 0) • atoms hfe s hs i =
        ∑ i ∈ Finset.range (max N M), (if i < N then c i else 0) • atoms hfe s hs i :=
      Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _))
        (fun i _ hi => by rw [if_neg (fun h => hi (Finset.mem_range.mpr h)), zero_smul])
    have e3 : ∑ i ∈ Finset.range M, (if i < N then c i else 0) • atoms hfe s hs i =
        ∑ i ∈ Finset.range (max N M), (if i < N then c i else 0) • atoms hfe s hs i :=
      Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) (fun i _ hi => by
        have hiM : M ≤ i := not_lt.mp (fun h => hi (Finset.mem_range.mpr h))
        rw [hsupp i hiM]
        simp)
    rw [e1, e2, e3]
  rw [hpre, hlc]
  exact atoms_prefix_sum hfe s hs N M c

/-! ### Node-level statements -/

/-- The span of all installed characters in `L²(w_∞)`. -/
def installedSpan : Submodule ℂ (WeightedL2 (limitW hfe s)) :=
  Submodule.span ℂ {x | ∃ n, ∃ i < (stages hfe s n).d,
    x = weightedCharacter (limitW hfe s) ((stages hfe s n).seq i)}

theorem mem_installedSpan (n i : ℕ) (hi : i < (stages hfe s n).d) :
    weightedCharacter (limitW hfe s) ((stages hfe s n).seq i) ∈ installedSpan hfe s :=
  Submodule.subset_span ⟨n, i, hi, rfl⟩

/-- Blueprint `limit:errors`, conditional on `hfe`: for every rational target the stage
errors decrease to zero, and the rational character lies in the closed span of the
installed characters in `L²(w_∞)`. -/
theorem visited_target_errors (hs : FairSchedule s) (q : ℚ) :
    Antitone (fun n => stageError hfe s n q) ∧
    Tendsto (fun n => stageError hfe s n q) atTop (𝓝 0) ∧
    weightedCharacter (limitW hfe s) (q : ℝ) ∈ (installedSpan hfe s).topologicalClosure := by
  refine ⟨stageError_antitone hfe s q, ?_,
    rational_mem_closure hfe s hs (installedSpan hfe s) (mem_installedSpan hfe s) q⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := stageError_small hfe s hs q hε
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (stageError_nonneg hfe s n q)]
  exact lt_of_le_of_lt (stageError_antitone hfe s q hn) hN

/-- Blueprint `limit:enumerate`, conditional on `hfe`: the list lengths are unbounded, the
installed entries define one injective sequence, and its characters have dense span. -/
theorem enumerate_installed_atoms (hs : FairSchedule s) :
    (∀ B : ℕ, ∃ n, B < (stages hfe s n).d) ∧
    (∀ n i, i < (stages hfe s n).d → (stages hfe s n).seq i = muInf hfe s hs i) ∧
    Function.Injective (muInf hfe s hs) ∧
    Dense (↑(Submodule.span ℂ (Set.range fun i =>
      weightedCharacter (limitW hfe s) (muInf hfe s hs i))) :
        Set (WeightedL2 (limitW hfe s))) :=
  ⟨stages_unbounded hfe s hs, fun _ _ hi => stages_seq_eq_muInf hfe s hs hi,
    muInf_injective hfe s hs, atoms_dense hfe s hs⟩

/-- Blueprint `limit:prefix`, conditional on `hfe`: every finite initial segment of the
installed list is independent in `L²(w_∞)` and has prefix constant `49/4 < 13`. -/
theorem limit_prefix_bounds (hs : FairSchedule s) (M : ℕ) :
    LinearIndependent ℂ (fun i : Fin M => weightedCharacter (limitW hfe s) (muInf hfe s hs i)) ∧
    PrefixBound (limitW hfe s) (fun i : Fin M => muInf hfe s hs i) (49 / 4) ∧
    (49 / 4 : ℝ) < 13 :=
  ⟨characters_linearIndependent (limitW hfe s) (fun i : Fin M => muInf hfe s hs i)
      ((muInf_injective hfe s hs).comp Fin.val_injective),
    limit_prefixBound hfe s hs M, by norm_num⟩

end Limit
end SchauderTranslates.LimitAssembly

namespace SchauderTranslates
open Construction LimitAssembly

/-- Blueprint `basis:weighted`, conditional on the finite extension principle
(blueprint `extend:line`), which is a hypothesis here and not an assumption of the
library. -/
theorem weighted_basis_of_finite_extension (hfe : Construction.FiniteExtensionPrinciple) :
    Construction.WeightedExponentialBasisExists := by
  obtain ⟨s, hs, -⟩ := fair_schedule
  refine ⟨limitW hfe s, muInf hfe s hs, atoms hfe s hs, muInf_injective hfe s hs,
    fun n => weightedCharacter_ae _ _, ?_⟩
  exact schauder_of_independent_dense_span (atoms hfe s hs)
    (characters_linearIndependent (limitW hfe s) (muInf hfe s hs) (muInf_injective hfe s hs))
    (atoms_dense hfe s hs) (by norm_num) (atoms_prefix hfe s hs)

/-- The translate basis, conditional on the finite extension principle. -/
theorem translates_of_finite_extension (hfe : Construction.FiniteExtensionPrinciple) :
    ∃ (g : LebesgueL2) (Λ : ℕ → ℝ), g ≠ 0 ∧ Function.Injective Λ ∧
      Construction.OrderedSchauderBasis (fun n => translateL2 (Λ n) g) :=
  translates_of_weighted_exponential_basis (weighted_basis_of_finite_extension hfe)

end SchauderTranslates
