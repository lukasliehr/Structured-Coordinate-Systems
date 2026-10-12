import Lean_Code.SchauderTranslates.Sharp.Contracts
import Lean_Code.SchauderTranslates.LimitStagesConstruct

/-!
# Sharp limit stages: the recursive construction with even weights

This is the sharp counterpart of `LimitStagesConstruct` (paper: Section "Assembling the
basis", subsection "The stages and the positive limiting weight").

Assuming the sharp finite extension `Sharp.FiniteExtensionSharp Kstar` as a hypothesis, we
construct by recursion the nested finite lists, the even weights `w_n = w₀ ∏_{k<n} W_k`
and the prefix constants of the infinite construction. Compared with
`LimitStagesConstruct`:

* the absolute one-step constant `12` is replaced by the parameter `Kstar`;
* the prefix budgets `τ_n` are a parameter (a positive sequence with a sum `τsum`), so
  that every stage has prefix constant `K_n ≤ Kstar + ∑_{k<n} τ_k ≤ Kstar + τsum`;
* the evenness of the stage weight, *pointwise for every* `t`, is an invariant of a
  `Stage`: the Gaussian start weight is even, every factor `W_n` is even by
  `FiniteExtensionSharp`, and a skipped stage uses the factor `W_n = 1`.

All parameters are bundled in the structure `Setup`. Everything that does not mention the
one-step constant (`LimitStagesBasic`, `PositiveProduct`, `LimitWeight`) is reused
unchanged.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
open SchauderTranslates SchauderTranslates.Construction SchauderTranslates.LimitAssembly

namespace SchauderTranslates.Sharp.Assembly

/-! ### Evenness of the Gaussian reference weight -/

/-- The Gaussian reference density is even, pointwise. -/
theorem gaussWeight_even (t : ℝ) : gaussWeight.density (-t) = gaussWeight.density t := by
  rw [gaussWeight_density, gaussWeight_density, neg_sq]

/-! ### Stages and steps -/

/-- A finite stage: the list `seq 0, …, seq (d-1)`, its weight, its prefix constant, and
the evenness of the weight at every point. -/
structure Stage where
  d : ℕ
  seq : ℕ → ℝ
  w : Weight
  K : ℝ
  inj : Function.Injective (fun i : Fin d => seq i)
  one_le : 1 ≤ K
  bound : PrefixBound w (fun i : Fin d => seq i) K
  even : ∀ t, w.density (-t) = w.density t

/-- The finite frequency list of a stage. -/
def Stage.μ (S : Stage) : Fin S.d → ℝ := fun i => S.seq i

/-- The data produced by one step of the construction with one-step constant `Kstar`,
target `ξ`, loss budget `δ` measured against the fixed reference weight `w₀`, and prefix
budget `τ`. -/
structure StepData (Kstar : ℝ) (w₀ : Weight) (S : Stage) (ξ δ τ : ℝ) where
  T : Stage
  W : ℝ → ℝ
  d_le : S.d ≤ T.d
  seq_eq : ∀ i < S.d, T.seq i = S.seq i
  W_meas : Measurable W
  W_pos : ∀ t, 0 < W t
  W_le : ∀ t, W t ≤ 1
  W_even : ∀ t, W (-t) = W t
  density_eq : ∀ t, T.w.density t = S.w.density t * W t
  cost : (∫ t, w₀.density t * (1 - W t)) < δ
  halve : distanceSq T.w T.μ ξ ≤ (1 / 2 : ℝ) * distanceSq S.w S.μ ξ
  K_le : T.K ≤ max S.K Kstar + τ
  skip : ¬ 0 < distanceSq S.w S.μ ξ → T = S ∧ W = fun _ => 1

/-- One step: apply the sharp finite extension when the distance is positive, and skip the
stage otherwise. The evenness of the stage weight is what the extension needs, and it is
reproduced by the even factor. -/
theorem exists_step {Kstar : ℝ} (hfe : FiniteExtensionSharp Kstar) (w₀ : Weight)
    (hw₀ : (∫ t, w₀.density t) = 1) (S : Stage) (ξ δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) :
    Nonempty (StepData Kstar w₀ S ξ δ τ) := by
  by_cases hpos : 0 < distanceSq S.w S.μ ξ
  · obtain ⟨r, ν, W, w', hν, hext, htrig, hW, hWeven, hdens, hcost, hhalf, hpre⟩ :=
      hfe S.w w₀ hw₀ S.even S.d S.μ S.K ξ δ τ S.inj S.one_le S.bound hpos hδ hτ
    let seq' : ℕ → ℝ := fun i => if h : i < S.d + r then ν ⟨i, h⟩ else 0
    have hseq' : (fun i : Fin (S.d + r) => seq' i) = ν := by
      funext i
      simp [seq', i.isLt]
    have hK1 : 1 ≤ max S.K Kstar + τ := by
      have h1 := le_max_left S.K Kstar
      have h2 := S.one_le
      linarith
    let T : Stage :=
      { d := S.d + r
        seq := seq'
        w := w'
        K := max S.K Kstar + τ
        inj := by rw [hseq']; exact hν
        one_le := hK1
        bound := by rw [hseq']; exact hpre
        even := fun t => by rw [hdens, hdens, S.even, hWeven] }
    refine ⟨{
      T := T
      W := W
      d_le := Nat.le_add_right _ _
      seq_eq := ?_
      W_meas := measurable_of_isTrigPolynomial htrig
      W_pos := fun t => (hW t).1
      W_le := fun t => (hW t).2
      W_even := hWeven
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
      W_even := fun _ => rfl
      density_eq := fun t => (mul_one _).symm
      cost := ?_
      halve := ?_
      K_le := ?_
      skip := fun _ => ⟨rfl, rfl⟩ }⟩
    · simp only [sub_self, mul_zero, integral_zero]
      exact hδ
    · have := not_lt.mp hpos
      linarith
    · have := le_max_left S.K Kstar
      linarith

/-- The initial stage: the constant character, the (even) Gaussian weight and constant one. -/
def initStage : Stage where
  d := 1
  seq := fun _ => 0
  w := gaussWeight
  K := 1
  inj := fun i j _ => Subsingleton.elim i j
  one_le := le_rfl
  bound := prefixBound_one _ _
  even := gaussWeight_even

/-! ### The parameters of the construction -/

/-- The parameters of the sharp infinite construction: the one-step constant `Kstar`
together with the sharp finite extension for it, the positive prefix budgets `τ n` with
total `τsum`, and a fair schedule `s` of rational targets. The loss budgets are the fixed
`lossBudget n` of the first formalization (total `1/8 < 1/2`). -/
structure Setup where
  /-- The one-step constant `K_*`. -/
  Kstar : ℝ
  one_le_Kstar : 1 ≤ Kstar
  /-- The sharp finite extension for `K_*` (a hypothesis of the assembly). -/
  extension : FiniteExtensionSharp Kstar
  /-- The prefix budgets `τ_n`. -/
  τ : ℕ → ℝ
  τ_pos : ∀ n, 0 < τ n
  /-- The total prefix budget `∑ τ_n`. -/
  τsum : ℝ
  τ_hasSum : HasSum τ τsum
  /-- The schedule of rational targets. -/
  s : ℕ → ℚ
  fair : FairSchedule s

/-- The limiting prefix constant `K_∞ = K_* + ∑ₙ τ_n`. -/
def Setup.Kinf (P : Setup) : ℝ := P.Kstar + P.τsum

theorem Setup.τsum_nonneg (P : Setup) : 0 ≤ P.τsum :=
  P.τ_hasSum.nonneg (fun n => (P.τ_pos n).le)

theorem Setup.one_le_Kinf (P : Setup) : 1 ≤ P.Kinf := by
  have h1 := P.one_le_Kstar
  have h2 := P.τsum_nonneg
  unfold Setup.Kinf
  linarith

section Stages
variable (P : Setup)

/-- The step data chosen at stage `n` (target `P.s n`, budgets `lossBudget n`, `P.τ n`). -/
def stepData (n : ℕ) (S : Stage) :
    StepData P.Kstar gaussWeight S (P.s n) (lossBudget n) (P.τ n) :=
  Classical.choice (exists_step P.extension gaussWeight gaussWeight_integral S (P.s n)
    (lossBudget n) (P.τ n) (lossBudget_pos n) (P.τ_pos n))

/-- The stages of the construction. -/
def stages : ℕ → Stage
  | 0 => initStage
  | n + 1 => (stepData P n (stages n)).T

/-- The multiplicative factor `W_n` applied at stage `n`. -/
def factor (n : ℕ) : ℝ → ℝ :=
  (stepData P n (stages P n)).W

theorem stages_zero : stages P 0 = initStage := rfl

theorem stages_succ (n : ℕ) :
    stages P (n + 1) = (stepData P n (stages P n)).T := rfl

theorem stages_d_zero : (stages P 0).d = 1 := rfl

theorem stages_seq_zero : (stages P 0).seq 0 = 0 := rfl

theorem stages_w_zero : (stages P 0).w = gaussWeight := rfl

theorem stages_d_le_succ (n : ℕ) : (stages P n).d ≤ (stages P (n + 1)).d :=
  (stepData P n (stages P n)).d_le

theorem stages_seq_succ (n : ℕ) :
    ∀ i < (stages P n).d, (stages P (n + 1)).seq i = (stages P n).seq i :=
  (stepData P n (stages P n)).seq_eq

/-- The lists are nested. -/
theorem stages_mono {n m : ℕ} (h : n ≤ m) :
    (stages P n).d ≤ (stages P m).d ∧
      ∀ i < (stages P n).d, (stages P m).seq i = (stages P n).seq i := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ m _ ih =>
    refine ⟨ih.1.trans (stages_d_le_succ P m), fun i hi => ?_⟩
    rw [stages_seq_succ P m i (lt_of_lt_of_le hi ih.1), ih.2 i hi]

theorem factor_measurable (n : ℕ) : Measurable (factor P n) :=
  (stepData P n (stages P n)).W_meas

theorem factor_pos (n : ℕ) (t : ℝ) : 0 < factor P n t :=
  (stepData P n (stages P n)).W_pos t

theorem factor_le_one (n : ℕ) (t : ℝ) : factor P n t ≤ 1 :=
  (stepData P n (stages P n)).W_le t

/-- Every factor is even, pointwise. -/
theorem factor_even (n : ℕ) (t : ℝ) : factor P n (-t) = factor P n t :=
  (stepData P n (stages P n)).W_even t

theorem factor_cost (n : ℕ) :
    (∫ t, gaussWeight.density t * (1 - factor P n t)) < lossBudget n :=
  (stepData P n (stages P n)).cost

theorem stages_density_succ (n : ℕ) (t : ℝ) :
    (stages P (n + 1)).w.density t = (stages P n).w.density t * factor P n t :=
  (stepData P n (stages P n)).density_eq t

/-- `w_n = w₀ ∏_{k<n} W_k`. -/
theorem stages_density (n : ℕ) (t : ℝ) :
    (stages P n).w.density t = partialWeight gaussWeight.density (factor P) n t := by
  induction n with
  | zero => simp [partialWeight, stages_w_zero]
  | succ n ih =>
    rw [stages_density_succ, ih]
    simp only [partialWeight, Finset.prod_range_succ, mul_assoc]

/-- Every stage weight is even, pointwise for every `t`. -/
theorem stages_even (n : ℕ) (t : ℝ) :
    (stages P n).w.density (-t) = (stages P n).w.density t :=
  (stages P n).even t

theorem stages_density_pos (n : ℕ) (t : ℝ) : 0 < (stages P n).w.density t := by
  rw [stages_density]
  exact mul_pos (gaussWeight_density_pos t)
    (Finset.prod_pos (fun k _ => factor_pos P k t))

theorem stages_density_succ_le (n : ℕ) (t : ℝ) :
    (stages P (n + 1)).w.density t ≤ (stages P n).w.density t := by
  rw [stages_density_succ]
  have h1 := factor_le_one P n t
  have h0 := stages_density_pos P n t
  nlinarith

/-- At stage `n` the squared distance of the scheduled target is at least halved. -/
theorem stages_halve (n : ℕ) :
    distanceSq (stages P (n + 1)).w (stages P (n + 1)).μ (P.s n) ≤
      (1 / 2 : ℝ) * distanceSq (stages P n).w (stages P n).μ (P.s n) :=
  (stepData P n (stages P n)).halve

/-- A stage whose target already has distance zero is skipped. -/
theorem stages_skip (n : ℕ)
    (h : ¬ 0 < distanceSq (stages P n).w (stages P n).μ (P.s n)) :
    stages P (n + 1) = stages P n ∧ factor P n = fun _ => 1 :=
  (stepData P n (stages P n)).skip h

theorem stages_one_le_K (n : ℕ) : 1 ≤ (stages P n).K :=
  (stages P n).one_le

/-- The finite list at stage `n` has prefix constant at most `K_* + ∑_{k<n} τ_k`. -/
theorem stages_K_le_sum (n : ℕ) :
    (stages P n).K ≤ P.Kstar + ∑ k ∈ Finset.range n, P.τ k := by
  induction n with
  | zero =>
    change (1 : ℝ) ≤ P.Kstar + ∑ k ∈ Finset.range 0, P.τ k
    rw [Finset.range_zero, Finset.sum_empty, add_zero]
    exact P.one_le_Kstar
  | succ n ih =>
    have h1 := (stepData P n (stages P n)).K_le
    rw [← stages_succ] at h1
    rw [Finset.sum_range_succ]
    have hs : 0 ≤ ∑ k ∈ Finset.range n, P.τ k :=
      Finset.sum_nonneg (fun k _ => (P.τ_pos k).le)
    have hm : max (stages P n).K P.Kstar ≤ P.Kstar + ∑ k ∈ Finset.range n, P.τ k :=
      max_le ih (by linarith)
    linarith

/-- The uniform prefix constant `K_∞ = K_* + ∑ τ_k`. -/
theorem stages_K_le (n : ℕ) : (stages P n).K ≤ P.Kinf := by
  have h := sum_le_hasSum (Finset.range n) (fun k _ => (P.τ_pos k).le) P.τ_hasSum
  have := stages_K_le_sum P n
  unfold Setup.Kinf
  linarith

/-- The squared distance of the target `ξ` at stage `n`. -/
def stageError (n : ℕ) (ξ : ℝ) : ℝ :=
  distanceSq (stages P n).w (stages P n).μ ξ

theorem stageError_nonneg (n : ℕ) (ξ : ℝ) : 0 ≤ stageError P n ξ :=
  distanceSq_nonneg _ _ _

theorem stageError_succ_le (n : ℕ) (ξ : ℝ) :
    stageError P (n + 1) ξ ≤ stageError P n ξ :=
  distanceSq_anti_seq (stages_d_le_succ P n) (stages_seq_succ P n)
    (Eventually.of_forall (stages_density_succ_le P n)) ξ

theorem stageError_antitone (ξ : ℝ) : Antitone (fun n => stageError P n ξ) :=
  antitone_nat_of_succ_le (fun n => stageError_succ_le P n ξ)

/-- Along the fair schedule, the errors of every rational target become arbitrarily small. -/
theorem stageError_small (q : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, stageError P n q < ε := by
  have hk : ∀ k : ℕ, ∃ n, stageError P n q ≤ stageError P 0 q * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm, hsm⟩ := P.fair q n
      refine ⟨m + 1, ?_⟩
      have h1 : stageError P (m + 1) q ≤ (1 / 2 : ℝ) * stageError P m q := by
        have := stages_halve P m
        rw [hsm] at this
        exact this
      have h2 := stageError_antitone P q hm
      have h3 : 0 ≤ (1 / 2 : ℝ) := by norm_num
      calc
        stageError P (m + 1) q ≤ (1 / 2 : ℝ) * stageError P m q := h1
        _ ≤ (1 / 2 : ℝ) * stageError P n q := mul_le_mul_of_nonneg_left h2 h3
        _ ≤ (1 / 2 : ℝ) * (stageError P 0 q * (1 / 2) ^ k) :=
          mul_le_mul_of_nonneg_left hn h3
        _ = stageError P 0 q * (1 / 2) ^ (k + 1) := by ring
  have ht : Tendsto (fun k : ℕ => stageError P 0 q * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (stageError P 0 q)
  obtain ⟨k, hk'⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨n, hn⟩ := hk k
  exact ⟨n, lt_of_le_of_lt hn hk'⟩

/-- The stage construction of the sharp assembly, conditional on the sharp finite
extension stored in `P`. Starting from the even Gaussian probability density and the
constant character, the lists are nested, `w_n = w₀ ∏_{k<n} W_k` with even factors
`0 < W_k ≤ 1`, every stage weight is even, every list is injective with prefix constant
`K_n ≤ K_* + ∑_{k<n} τ_k ≤ K_∞`, `∫ w₀ (1 - W_n) < δ_n`, the squared distance of the
scheduled target is at least halved, and a target at distance zero leads to a skipped
stage. -/
theorem construct_stages :
    (stages P 0).d = 1 ∧ (stages P 0).seq 0 = 0 ∧
    (stages P 0).w = gaussWeight ∧ (∫ t, gaussWeight.density t) = 1 ∧
    (∀ n, (stages P n).d ≤ (stages P (n + 1)).d ∧
      ∀ i < (stages P n).d, (stages P (n + 1)).seq i = (stages P n).seq i) ∧
    (∀ n t, (stages P n).w.density t =
      partialWeight gaussWeight.density (factor P) n t) ∧
    (∀ n t, 0 < factor P n t ∧ factor P n t ≤ 1 ∧ factor P n (-t) = factor P n t) ∧
    (∀ n t, (stages P n).w.density (-t) = (stages P n).w.density t) ∧
    (∀ n, Function.Injective (stages P n).μ ∧
      PrefixBound (stages P n).w (stages P n).μ (stages P n).K ∧
      (stages P n).K ≤ P.Kstar + ∑ k ∈ Finset.range n, P.τ k ∧
      (stages P n).K ≤ P.Kinf) ∧
    (∀ n, (∫ t, gaussWeight.density t * (1 - factor P n t)) < lossBudget n) ∧
    (∀ n, distanceSq (stages P (n + 1)).w (stages P (n + 1)).μ (P.s n) ≤
      (1 / 2 : ℝ) * distanceSq (stages P n).w (stages P n).μ (P.s n)) ∧
    (∀ n, ¬ 0 < distanceSq (stages P n).w (stages P n).μ (P.s n) →
      stages P (n + 1) = stages P n ∧ factor P n = fun _ => 1) :=
  ⟨rfl, rfl, rfl, gaussWeight_integral,
    fun n => ⟨stages_d_le_succ P n, stages_seq_succ P n⟩,
    stages_density P,
    fun n t => ⟨factor_pos P n t, factor_le_one P n t, factor_even P n t⟩,
    stages_even P,
    fun n => ⟨(stages P n).inj, (stages P n).bound, stages_K_le_sum P n, stages_K_le P n⟩,
    factor_cost P, stages_halve P, stages_skip P⟩

end Stages
end SchauderTranslates.Sharp.Assembly
