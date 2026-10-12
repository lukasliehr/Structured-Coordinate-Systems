import Lean_Code.SchauderTranslates.LimitStagesBasic
import Lean_Code.SchauderTranslates.LimitWeight
import Lean_Code.SchauderTranslates.PositiveProduct

/-!
# Limit stages: the recursive construction (blueprint `limit:stages`)

Assuming the finite extension principle `Construction.FiniteExtensionPrinciple`
(blueprint `extend:line`) as a hypothesis, we construct by recursion the nested
finite lists, weights `w_n = w₀ ∏_{k<n} W_k` and prefix constants of the infinite
construction. A stage stores its list as a sequence `ℕ → ℝ` together with its
length, so that the extension property is a statement about a common index type.

If the scheduled target already has distance zero, the stage is skipped: the list,
the weight and the constant are kept, and the factor is `W_n = 1`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace SchauderTranslates.LimitAssembly
open SchauderTranslates.Construction

/-- A finite stage: the list `seq 0, …, seq (d-1)`, its weight, and its prefix constant. -/
structure Stage where
  d : ℕ
  seq : ℕ → ℝ
  w : Weight
  K : ℝ
  inj : Function.Injective (fun i : Fin d => seq i)
  one_le : 1 ≤ K
  bound : PrefixBound w (fun i : Fin d => seq i) K

/-- The finite frequency list of a stage. -/
def Stage.μ (S : Stage) : Fin S.d → ℝ := fun i => S.seq i

/-- The data produced by one step of the construction, with target `ξ`, loss budget `δ`
measured against the fixed reference weight `w₀`, and prefix budget `τ`. -/
structure StepData (w₀ : Weight) (S : Stage) (ξ δ τ : ℝ) where
  T : Stage
  W : ℝ → ℝ
  d_le : S.d ≤ T.d
  seq_eq : ∀ i < S.d, T.seq i = S.seq i
  W_meas : Measurable W
  W_pos : ∀ t, 0 < W t
  W_le : ∀ t, W t ≤ 1
  density_eq : ∀ t, T.w.density t = S.w.density t * W t
  cost : (∫ t, w₀.density t * (1 - W t)) < δ
  halve : distanceSq T.w T.μ ξ ≤ (1 / 2 : ℝ) * distanceSq S.w S.μ ξ
  K_le : T.K ≤ max S.K 12 + τ
  skip : ¬ 0 < distanceSq S.w S.μ ξ → T = S ∧ W = fun _ => 1

theorem measurable_of_isTrigPolynomial {W : ℝ → ℝ} (h : IsTrigPolynomial W) :
    Measurable W := by
  obtain ⟨d, ξ, c, hW⟩ := h
  have he : W = fun t => (synthesis ξ c t).re := by
    funext t
    rw [← hW t, Complex.ofReal_re]
  rw [he]
  exact (Complex.continuous_re.comp (continuous_synthesis ξ c)).measurable

/-- One step: apply the finite extension principle when the distance is positive,
and skip the stage otherwise. -/
theorem exists_step (hfe : FiniteExtensionPrinciple) (w₀ : Weight)
    (hw₀ : (∫ t, w₀.density t) = 1) (S : Stage) (ξ δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) :
    Nonempty (StepData w₀ S ξ δ τ) := by
  by_cases hpos : 0 < distanceSq S.w S.μ ξ
  · obtain ⟨r, ν, W, w', hν, hext, htrig, hW, hdens, hcost, hhalf, hpre⟩ :=
      hfe S.w w₀ hw₀ S.d S.μ S.K ξ δ τ S.inj S.one_le S.bound hpos hδ hτ
    let seq' : ℕ → ℝ := fun i => if h : i < S.d + r then ν ⟨i, h⟩ else 0
    have hseq' : (fun i : Fin (S.d + r) => seq' i) = ν := by
      funext i
      simp [seq', i.isLt]
    have hK1 : 1 ≤ max S.K 12 + τ := by
      have := le_max_right S.K 12
      linarith
    let T : Stage :=
      { d := S.d + r
        seq := seq'
        w := w'
        K := max S.K 12 + τ
        inj := by rw [hseq']; exact hν
        one_le := hK1
        bound := by rw [hseq']; exact hpre }
    refine ⟨{
      T := T
      W := W
      d_le := Nat.le_add_right _ _
      seq_eq := ?_
      W_meas := measurable_of_isTrigPolynomial htrig
      W_pos := fun t => (hW t).1
      W_le := fun t => (hW t).2
      density_eq := hdens
      cost := hcost
      halve := ?_
      K_le := le_rfl
      skip := fun h => absurd hpos h }⟩
    · intro i hi
      have h1 : i < S.d + r := by omega
      change seq' i = S.seq i
      simp only [seq', dif_pos h1]
      exact hext ⟨i, hi⟩
    · change distanceSq w' (fun i : Fin (S.d + r) => seq' i) ξ ≤ _
      rw [hseq']
      exact hhalf
  · refine ⟨{
      T := S
      W := fun _ => 1
      d_le := le_rfl
      seq_eq := fun _ _ => rfl
      W_meas := measurable_const
      W_pos := fun _ => one_pos
      W_le := fun _ => le_rfl
      density_eq := fun t => (mul_one _).symm
      cost := ?_
      halve := ?_
      K_le := ?_
      skip := fun _ => ⟨rfl, rfl⟩ }⟩
    · simp only [sub_self, mul_zero, integral_zero]
      exact hδ
    · have := not_lt.mp hpos
      linarith
    · have := le_max_left S.K 12
      linarith

/-- The initial stage: the constant character, the Gaussian weight and constant one. -/
def initStage : Stage where
  d := 1
  seq := fun _ => 0
  w := gaussWeight
  K := 1
  inj := fun i j _ => Subsingleton.elim i j
  one_le := le_rfl
  bound := prefixBound_one _ _

section Stages
variable (hfe : FiniteExtensionPrinciple) (s : ℕ → ℚ)

/-- The step data chosen at stage `n` (target `s n`, budgets `lossBudget n`, `prefixBudget n`). -/
def stepData (n : ℕ) (S : Stage) :
    StepData gaussWeight S (s n) (lossBudget n) (prefixBudget n) :=
  Classical.choice (exists_step hfe gaussWeight gaussWeight_integral S (s n) (lossBudget n)
    (prefixBudget n) (lossBudget_pos n) (prefixBudget_pos n))

/-- The stages of the construction. -/
def stages : ℕ → Stage
  | 0 => initStage
  | n + 1 => (stepData hfe s n (stages n)).T

/-- The multiplicative factor `W_n` applied at stage `n`. -/
def factor (n : ℕ) : ℝ → ℝ :=
  (stepData hfe s n (stages hfe s n)).W

theorem stages_zero : stages hfe s 0 = initStage := rfl

theorem stages_succ (n : ℕ) :
    stages hfe s (n + 1) = (stepData hfe s n (stages hfe s n)).T := rfl

theorem stages_d_zero : (stages hfe s 0).d = 1 := rfl

theorem stages_seq_zero : (stages hfe s 0).seq 0 = 0 := rfl

theorem stages_w_zero : (stages hfe s 0).w = gaussWeight := rfl

theorem stages_d_le_succ (n : ℕ) : (stages hfe s n).d ≤ (stages hfe s (n + 1)).d :=
  (stepData hfe s n (stages hfe s n)).d_le

theorem stages_seq_succ (n : ℕ) :
    ∀ i < (stages hfe s n).d, (stages hfe s (n + 1)).seq i = (stages hfe s n).seq i :=
  (stepData hfe s n (stages hfe s n)).seq_eq

/-- The lists are nested. -/
theorem stages_mono {n m : ℕ} (h : n ≤ m) :
    (stages hfe s n).d ≤ (stages hfe s m).d ∧
      ∀ i < (stages hfe s n).d, (stages hfe s m).seq i = (stages hfe s n).seq i := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ m _ ih =>
    refine ⟨ih.1.trans (stages_d_le_succ hfe s m), fun i hi => ?_⟩
    rw [stages_seq_succ hfe s m i (lt_of_lt_of_le hi ih.1), ih.2 i hi]

theorem factor_measurable (n : ℕ) : Measurable (factor hfe s n) :=
  (stepData hfe s n (stages hfe s n)).W_meas

theorem factor_pos (n : ℕ) (t : ℝ) : 0 < factor hfe s n t :=
  (stepData hfe s n (stages hfe s n)).W_pos t

theorem factor_le_one (n : ℕ) (t : ℝ) : factor hfe s n t ≤ 1 :=
  (stepData hfe s n (stages hfe s n)).W_le t

theorem factor_cost (n : ℕ) :
    (∫ t, gaussWeight.density t * (1 - factor hfe s n t)) < lossBudget n :=
  (stepData hfe s n (stages hfe s n)).cost

theorem stages_density_succ (n : ℕ) (t : ℝ) :
    (stages hfe s (n + 1)).w.density t = (stages hfe s n).w.density t * factor hfe s n t :=
  (stepData hfe s n (stages hfe s n)).density_eq t

/-- `w_n = w₀ ∏_{k<n} W_k`. -/
theorem stages_density (n : ℕ) (t : ℝ) :
    (stages hfe s n).w.density t = partialWeight gaussWeight.density (factor hfe s) n t := by
  induction n with
  | zero => simp [partialWeight, stages_w_zero]
  | succ n ih =>
    rw [stages_density_succ, ih]
    simp only [partialWeight, Finset.prod_range_succ, mul_assoc]

theorem stages_density_pos (n : ℕ) (t : ℝ) : 0 < (stages hfe s n).w.density t := by
  rw [stages_density]
  exact mul_pos (gaussWeight_density_pos t)
    (Finset.prod_pos (fun k _ => factor_pos hfe s k t))

theorem stages_density_succ_le (n : ℕ) (t : ℝ) :
    (stages hfe s (n + 1)).w.density t ≤ (stages hfe s n).w.density t := by
  rw [stages_density_succ]
  have h1 := factor_le_one hfe s n t
  have h0 := stages_density_pos hfe s n t
  nlinarith

/-- At stage `n` the squared distance of the scheduled target is at least halved. -/
theorem stages_halve (n : ℕ) :
    distanceSq (stages hfe s (n + 1)).w (stages hfe s (n + 1)).μ (s n) ≤
      (1 / 2 : ℝ) * distanceSq (stages hfe s n).w (stages hfe s n).μ (s n) :=
  (stepData hfe s n (stages hfe s n)).halve

/-- A stage whose target already has distance zero is skipped. -/
theorem stages_skip (n : ℕ)
    (h : ¬ 0 < distanceSq (stages hfe s n).w (stages hfe s n).μ (s n)) :
    stages hfe s (n + 1) = stages hfe s n ∧ factor hfe s n = fun _ => 1 :=
  (stepData hfe s n (stages hfe s n)).skip h

theorem stages_one_le_K (n : ℕ) : 1 ≤ (stages hfe s n).K :=
  (stages hfe s n).one_le

theorem stages_K_le_sum (n : ℕ) :
    (stages hfe s n).K ≤ 12 + ∑ k ∈ Finset.range n, prefixBudget k := by
  induction n with
  | zero =>
    change (1 : ℝ) ≤ 12 + ∑ k ∈ Finset.range 0, prefixBudget k
    norm_num
  | succ n ih =>
    have h1 := (stepData hfe s n (stages hfe s n)).K_le
    rw [← stages_succ] at h1
    rw [Finset.sum_range_succ]
    have hs : 0 ≤ ∑ k ∈ Finset.range n, prefixBudget k :=
      Finset.sum_nonneg (fun k _ => (prefixBudget_pos k).le)
    have hm : max (stages hfe s n).K 12 ≤ 12 + ∑ k ∈ Finset.range n, prefixBudget k :=
      max_le ih (by linarith)
    linarith

/-- The uniform prefix constant `12 + ∑ τ_k ≤ 12 + 1/4 < 13`. -/
theorem stages_K_le (n : ℕ) : (stages hfe s n).K ≤ 49 / 4 := by
  have h := sum_le_hasSum (Finset.range n) (fun k _ => (prefixBudget_pos k).le)
    hasSum_prefixBudget
  have := stages_K_le_sum hfe s n
  linarith

/-- The squared distance of the target `ξ` at stage `n`. -/
def stageError (n : ℕ) (ξ : ℝ) : ℝ :=
  distanceSq (stages hfe s n).w (stages hfe s n).μ ξ

theorem stageError_nonneg (n : ℕ) (ξ : ℝ) : 0 ≤ stageError hfe s n ξ :=
  distanceSq_nonneg _ _ _

theorem stageError_succ_le (n : ℕ) (ξ : ℝ) :
    stageError hfe s (n + 1) ξ ≤ stageError hfe s n ξ :=
  distanceSq_anti_seq (stages_d_le_succ hfe s n) (stages_seq_succ hfe s n)
    (Eventually.of_forall (stages_density_succ_le hfe s n)) ξ

theorem stageError_antitone (ξ : ℝ) : Antitone (fun n => stageError hfe s n ξ) :=
  antitone_nat_of_succ_le (fun n => stageError_succ_le hfe s n ξ)

/-- Along a fair schedule, the errors of every rational target become arbitrarily small. -/
theorem stageError_small (hs : FairSchedule s) (q : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, stageError hfe s n q < ε := by
  have hk : ∀ k : ℕ, ∃ n, stageError hfe s n q ≤ stageError hfe s 0 q * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm, hsm⟩ := hs q n
      refine ⟨m + 1, ?_⟩
      have h1 : stageError hfe s (m + 1) q ≤ (1 / 2 : ℝ) * stageError hfe s m q := by
        have := stages_halve hfe s m
        rw [hsm] at this
        exact this
      have h2 := stageError_antitone hfe s q hm
      have h3 : 0 ≤ (1 / 2 : ℝ) := by norm_num
      calc
        stageError hfe s (m + 1) q ≤ (1 / 2 : ℝ) * stageError hfe s m q := h1
        _ ≤ (1 / 2 : ℝ) * stageError hfe s n q := mul_le_mul_of_nonneg_left h2 h3
        _ ≤ (1 / 2 : ℝ) * (stageError hfe s 0 q * (1 / 2) ^ k) :=
          mul_le_mul_of_nonneg_left hn h3
        _ = stageError hfe s 0 q * (1 / 2) ^ (k + 1) := by ring
  have ht : Tendsto (fun k : ℕ => stageError hfe s 0 q * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (stageError hfe s 0 q)
  obtain ⟨k, hk'⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨n, hn⟩ := hk k
  exact ⟨n, lt_of_le_of_lt hn hk'⟩

/-- Blueprint `limit:stages`, conditional on the finite extension principle `hfe`.
Starting from the Gaussian probability density and the constant character, the lists are
nested, `w_n = w₀ ∏_{k<n} W_k` with `0 < W_k ≤ 1`, every list is injective with prefix
constant `K_n < 13`, `∫ w₀ (1 - W_n) < δ_n`, the squared distance of the scheduled target
is at least halved, and a target at distance zero leads to a skipped stage. -/
theorem construct_stages :
    (stages hfe s 0).d = 1 ∧ (stages hfe s 0).seq 0 = 0 ∧
    (stages hfe s 0).w = gaussWeight ∧ (∫ t, gaussWeight.density t) = 1 ∧
    (∀ n, (stages hfe s n).d ≤ (stages hfe s (n + 1)).d ∧
      ∀ i < (stages hfe s n).d, (stages hfe s (n + 1)).seq i = (stages hfe s n).seq i) ∧
    (∀ n t, (stages hfe s n).w.density t =
      partialWeight gaussWeight.density (factor hfe s) n t) ∧
    (∀ n t, 0 < factor hfe s n t ∧ factor hfe s n t ≤ 1) ∧
    (∀ n, Function.Injective (stages hfe s n).μ ∧
      PrefixBound (stages hfe s n).w (stages hfe s n).μ (stages hfe s n).K ∧
      (stages hfe s n).K < 13) ∧
    (∀ n, (∫ t, gaussWeight.density t * (1 - factor hfe s n t)) < lossBudget n) ∧
    (∀ n, distanceSq (stages hfe s (n + 1)).w (stages hfe s (n + 1)).μ (s n) ≤
      (1 / 2 : ℝ) * distanceSq (stages hfe s n).w (stages hfe s n).μ (s n)) ∧
    (∀ n, ¬ 0 < distanceSq (stages hfe s n).w (stages hfe s n).μ (s n) →
      stages hfe s (n + 1) = stages hfe s n ∧ factor hfe s n = fun _ => 1) :=
  ⟨rfl, rfl, rfl, gaussWeight_integral,
    fun n => ⟨stages_d_le_succ hfe s n, stages_seq_succ hfe s n⟩,
    stages_density hfe s, fun n t => ⟨factor_pos hfe s n t, factor_le_one hfe s n t⟩,
    fun n => ⟨(stages hfe s n).inj, (stages hfe s n).bound,
      lt_of_le_of_lt (stages_K_le hfe s n) (by norm_num)⟩,
    factor_cost hfe s, stages_halve hfe s, stages_skip hfe s⟩

end Stages
end SchauderTranslates.LimitAssembly
