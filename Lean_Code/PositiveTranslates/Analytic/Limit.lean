import Lean_Code.PositiveTranslates.Analytic.Run

/-!
# Passing to a single generator: limits and bookkeeping

* `exists_entire_limit`: entire functions whose increments are geometrically small on
  growing discs converge locally uniformly to an entire function; if their classes on the
  real line converge in `Lᵖ`, the `Lᵖ` limit is the restriction of the limit function.
* `MachineRun`: a run of a stage machine driven by admissible inputs, the enumeration
  `MachineRun.birth` of its births (parameters and reference vectors), and the total error
  `MachineRun.err t g = ∑_{m < L_t} ‖T_{λ_m} g - b_m‖`.
* `MachineRun.summable_translate_error`: the estimate
  `∑_m ‖T_{λ_m} g - b_m‖ ≤ 6 κ` for the limit `g` of the classes `g_t` (paper, equation
  `tr:eq:total-error`, with slightly different numerical budgets).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ComplexOrder BigOperators Real

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

/-! ### Limits of entire functions -/

/-- Functions with geometrically small increments on growing discs converge pointwise,
with an explicit rate on each disc. -/
theorem exists_limit_of_disc_increments {G : ℕ → ℂ → ℂ}
    (hinc : ∀ (t : ℕ) (z : ℂ), ‖z‖ ≤ (t : ℝ) + 1 → ‖G (t + 1) z - G t z‖ ≤ (1 / 2) ^ (t + 1)) :
    ∃ Glim : ℂ → ℂ, (∀ z, Tendsto (fun t => G t z) atTop (𝓝 (Glim z))) ∧
      ∀ (t : ℕ) (z : ℂ), ‖z‖ ≤ (t : ℝ) + 1 → ‖G t z - Glim z‖ ≤ (1 / 2) ^ t := by
  have hshift : ∀ (t : ℕ) (z : ℂ), ‖z‖ ≤ (t : ℝ) + 1 → ∀ s : ℕ,
      dist (G (t + s) z) (G (t + s + 1) z) ≤ (1 / 2 : ℝ) ^ (t + 1) * (1 / 2) ^ s := by
    intro t z hz s
    rw [dist_comm, dist_eq_norm, ← pow_add]
    have h := hinc (t + s) z (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
    rwa [show t + 1 + s = t + s + 1 by ring]
  have hconv : ∀ z : ℂ, ∃ ℓ, Tendsto (fun t => G t z) atTop (𝓝 ℓ) := by
    intro z
    have hz : ‖z‖ ≤ ((⌈‖z‖⌉₊ : ℕ) : ℝ) + 1 := (Nat.le_ceil _).trans (by linarith)
    have hc : CauchySeq (fun s => G (⌈‖z‖⌉₊ + s) z) :=
      cauchySeq_of_le_geometric (1 / 2) ((1 / 2) ^ (⌈‖z‖⌉₊ + 1)) (by norm_num)
        (hshift ⌈‖z‖⌉₊ z hz)
    obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨ℓ, (tendsto_add_atTop_iff_nat ⌈‖z‖⌉₊).mp ?_⟩
    simpa only [add_comm] using hℓ
  choose Glim hGlim using hconv
  refine ⟨Glim, hGlim, fun t z hz => ?_⟩
  have hlim : Tendsto (fun s => G (t + s) z) atTop (𝓝 (Glim z)) := by
    have h := (tendsto_add_atTop_iff_nat t).mpr (hGlim z)
    simpa only [add_comm] using h
  have h := dist_le_of_le_geometric_of_tendsto (1 / 2) ((1 / 2) ^ (t + 1)) (by norm_num)
    (hshift t z hz) hlim 0
  have h2 : (1 / 2 : ℝ) ^ (t + 1) * (1 / 2) ^ 0 / (1 - 1 / 2) = (1 / 2) ^ t := by
    rw [pow_succ]
    ring
  rw [dist_eq_norm, h2] at h
  simpa using h

theorem tendstoLocallyUniformly_of_disc_bound {G : ℕ → ℂ → ℂ} {Glim : ℂ → ℂ}
    (hb : ∀ (t : ℕ) (z : ℂ), ‖z‖ ≤ (t : ℝ) + 1 → ‖G t z - Glim z‖ ≤ (1 / 2) ^ t) :
    TendstoLocallyUniformly G Glim atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (max n₀ ⌈‖x‖⌉₊)] with n hn y hy
  have hy' : ‖y‖ ≤ (n : ℝ) + 1 := by
    have h1 : ‖y‖ ≤ ‖x‖ + 1 := by
      have h := norm_sub_norm_le y x
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith
    have h2 : ‖x‖ ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
    linarith
  rw [dist_comm, dist_eq_norm]
  calc
    ‖G n y - Glim y‖ ≤ (1 / 2) ^ n := hb n y hy'
    _ ≤ (1 / 2) ^ n₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) ((le_max_left _ _).trans hn)
    _ < ε := hn₀

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Γ : Set ℝ}

/-- **The limit generator.** -/
theorem exists_entire_limit {G : ℕ → ℂ → ℂ} {g : ℕ → LebesgueLp p}
    (hGdiff : ∀ t, Differentiable ℂ (G t)) (hGpos : ∀ t (x : ℝ), 0 ≤ G t x)
    (hgG : ∀ t, (g t : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => G t x)
    (hinc : ∀ (t : ℕ) (z : ℂ), ‖z‖ ≤ (t : ℝ) + 1 → ‖G (t + 1) z - G t z‖ ≤ (1 / 2) ^ (t + 1))
    {glim : LebesgueLp p} (hg : Tendsto g atTop (𝓝 glim)) :
    ∃ Glim : ℂ → ℂ, Differentiable ℂ Glim ∧ (∀ x : ℝ, 0 ≤ Glim x) ∧
      (glim : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => Glim x := by
  obtain ⟨Glim, hpt, hb⟩ := exists_limit_of_disc_increments hinc
  have hloc : TendstoLocallyUniformly G Glim atTop := tendstoLocallyUniformly_of_disc_bound hb
  have hdiff : Differentiable ℂ Glim := by
    have h := (tendstoLocallyUniformlyOn_univ.mpr hloc).differentiableOn
      (Eventually.of_forall fun n => (hGdiff n).differentiableOn) isOpen_univ
    exact differentiableOn_univ.mp h
  have hpos : ∀ x : ℝ, 0 ≤ Glim x := fun x => ge_of_tendsto' (hpt x) (fun t => hGpos t x)
  refine ⟨Glim, hdiff, hpos, ?_⟩
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ t, g t x = G t x := ae_all_iff.mpr hgG
  filter_upwards [hae, hall] with x hx hxall
  have h1 : Tendsto (fun i => G (ns i) x) atTop (𝓝 (glim x)) := by
    simpa only [hxall] using hx
  have h2 : Tendsto (fun i => G (ns i) x) atTop (𝓝 (Glim x)) :=
    (hpt x).comp hns.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

theorem isometry_translate (a : ℝ) : Isometry (translate p a) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, dist_eq_norm, ← translate_sub, norm_translate]

/-! ### Index bookkeeping for births -/

/-- An induction principle over the indices of the births of a run. -/
theorem birth_index_induction {L N : ℕ → ℕ} (hL0 : L 0 = 1) (hL : ∀ t, L (t + 1) = L t + N t)
    {Q : ℕ → Prop} (h0 : Q 0) (hnew : ∀ t i, i < N t → Q (L t + i)) :
    ∀ t m, m < L t → Q m := by
  intro t
  induction t with
  | zero =>
    intro m hm
    rw [hL0] at hm
    obtain rfl : m = 0 := by omega
    exact h0
  | succ t ih =>
    intro m hm
    rw [hL] at hm
    by_cases h : m < L t
    · exact ih m h
    · obtain ⟨i, rfl⟩ : ∃ i, m = L t + i := ⟨m - L t, by omega⟩
      exact hnew t i (by omega)

/-- A run of a stage machine driven by admissible inputs. -/
structure MachineRun (M : StageMachine p Γ) where
  /-- the states -/
  S : ℕ → M.State
  /-- the packet sizes -/
  N : ℕ → ℕ
  /-- the admissible inputs -/
  v : ℕ → LebesgueLp p
  /-- the requested lower bounds for the new parameters -/
  Λ₀ : ℕ → ℝ
  init : S 0 = M.init
  next : ∀ t, S (t + 1) = M.next (S t) (N t) (v t) (Λ₀ t)
  size : ∀ t, M.minSize (S t) ≤ N t
  adm : ∀ t, Admissible (v t)

namespace MachineRun

variable {M : StageMachine p Γ} (R : MachineRun M)

/-- The number of births before step `t`. -/
def L (t : ℕ) : ℕ := (M.births (R.S t)).length

/-- The parameters chosen at step `t`. -/
def lam (t : ℕ) : Fin (R.N t) → ℝ := M.params (R.S t) (R.N t) (R.v t) (R.Λ₀ t)

/-- The reference function of step `t`. -/
def V (t : ℕ) : LebesgueLp p := referenceFunction p (R.v t) (M.target (R.S t)) (R.lam t)

/-- The enumeration of all births (parameter, reference vector) of the run. -/
def birth (m : ℕ) : ℝ × LebesgueLp p := (M.births (R.S m)).getD m (0, 0)

theorem births_succ (t : ℕ) :
    M.births (R.S (t + 1)) = M.births (R.S t) ++
      List.ofFn fun i : Fin (R.N t) => (R.lam t i, translate p (R.lam t i) (R.V t)) := by
  rw [R.next t]
  exact M.births_next (R.S t) (R.N t) (R.v t) (R.Λ₀ t) (R.size t) (R.adm t)

theorem L_zero : R.L 0 = 1 := by
  unfold L
  rw [R.init, M.births_init]
  rfl

theorem L_succ (t : ℕ) : R.L (t + 1) = R.L t + R.N t := by
  unfold L
  rw [R.births_succ]
  simp

theorem one_le_N (t : ℕ) : 1 ≤ R.N t := (M.minSize_pos (R.S t)).trans (R.size t)

theorem L_mono : Monotone R.L :=
  monotone_nat_of_le_succ fun t => by
    rw [R.L_succ]
    omega

theorem lt_L (t : ℕ) : t < R.L t := by
  induction t with
  | zero =>
    rw [R.L_zero]
    exact Nat.zero_lt_one
  | succ t ih =>
    rw [R.L_succ]
    have := R.one_le_N t
    omega

theorem getD_births_add (t k m : ℕ) (d : ℝ × LebesgueLp p) (h : m < R.L t) :
    (M.births (R.S (t + k))).getD m d = (M.births (R.S t)).getD m d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, R.births_succ, List.getD_append _ _ _ _ ?_, ih]
    exact lt_of_lt_of_le h (R.L_mono (Nat.le_add_right t k))

theorem birth_eq {t m : ℕ} (h : m < R.L t) :
    R.birth m = (M.births (R.S t)).getD m (0, 0) := by
  unfold birth
  rcases le_total t m with htm | hmt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htm
    exact R.getD_births_add t k (t + k) _ h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmt
    exact (R.getD_births_add m k m _ (R.lt_L m)).symm

theorem birth_zero : R.birth 0 = (0, intervalAtom p (0, 1)) := by
  unfold birth
  rw [R.init, M.births_init]
  rfl

theorem birth_new (t : ℕ) (i : Fin (R.N t)) :
    R.birth (R.L t + i) = (R.lam t i, translate p (R.lam t i) (R.V t)) := by
  have hlt : R.L t + i < R.L (t + 1) := by
    rw [R.L_succ]
    omega
  have hlen : (i : ℕ) < (List.ofFn fun i : Fin (R.N t) =>
      (R.lam t i, translate p (R.lam t i) (R.V t))).length := by simp
  rw [R.birth_eq hlt, R.births_succ, List.getD_append_right _ _ _ _
      (show (M.births (R.S t)).length ≤ R.L t + i from Nat.le_add_right _ _),
    show R.L t + (i : ℕ) - (M.births (R.S t)).length = i from Nat.add_sub_cancel_left ..,
    List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]

theorem birth_mem {t m : ℕ} (h : m < R.L t) : R.birth m ∈ M.births (R.S t) := by
  rw [R.birth_eq h, List.getD_eq_getElem _ _ h]
  exact List.getElem_mem _

/-- Every statement about births can be checked on the initial birth and on the births of
each step. -/
theorem forall_birth {Q : ℕ → Prop} (h0 : Q 0)
    (hnew : ∀ t (i : Fin (R.N t)), Q (R.L t + i)) (m : ℕ) : Q m :=
  birth_index_induction R.L_zero R.L_succ h0 (fun t i hi => hnew t ⟨i, hi⟩) m m (R.lt_L m)

theorem birth_fst_mem (h0 : (0 : ℝ) ∈ Γ) (m : ℕ) : (R.birth m).1 ∈ Γ := by
  refine R.forall_birth (Q := fun m => (R.birth m).1 ∈ Γ) ?_ (fun t i => ?_) m
  · rw [R.birth_zero]
    exact h0
  · rw [R.birth_new]
    exact M.params_mem _ _ _ _ i

theorem half_le_norm_birth (hp' : p ≠ ∞) (m : ℕ) : 1 / 2 ≤ ‖(R.birth m).2‖ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  refine R.forall_birth (Q := fun m => 1 / 2 ≤ ‖(R.birth m).2‖) ?_ (fun t i => ?_) m
  · rw [R.birth_zero, initial_generator_unit p hp0 hp']
    norm_num
  · rw [R.birth_new, norm_translate]
    exact (R.adm t).lower.trans (M.reference_norm_ge _ _ _ _ (R.size t) (R.adm t))

theorem birth_fst_injOn (t : ℕ) : ∀ m m', m < R.L t → m' < R.L t →
    (R.birth m).1 = (R.birth m').1 → m = m' := by
  induction t with
  | zero =>
    intro m m' hm hm' _
    rw [R.L_zero] at hm hm'
    omega
  | succ t ih =>
    have hold_new : ∀ m (i : Fin (R.N t)), m < R.L t →
        (R.birth m).1 < (R.birth (R.L t + i)).1 := by
      intro m i hm
      rw [R.birth_new]
      exact M.params_gt_old (R.S t) (R.N t) (R.v t) (R.Λ₀ t) i _ (R.birth_mem hm)
    intro m m' hm hm' heq
    rw [R.L_succ] at hm hm'
    by_cases h : m < R.L t
    · by_cases h' : m' < R.L t
      · exact ih m m' h h' heq
      · obtain ⟨i, rfl⟩ : ∃ i, m' = R.L t + i := ⟨m' - R.L t, by omega⟩
        have hlt := hold_new m ⟨i, by omega⟩ h
        exact absurd heq (ne_of_lt hlt)
    · obtain ⟨i, rfl⟩ : ∃ i, m = R.L t + i := ⟨m - R.L t, by omega⟩
      by_cases h' : m' < R.L t
      · have hlt := hold_new m' ⟨i, by omega⟩ h'
        exact absurd heq.symm (ne_of_lt hlt)
      · obtain ⟨j, rfl⟩ : ∃ j, m' = R.L t + j := ⟨m' - R.L t, by omega⟩
        have hi : i < R.N t := by omega
        have hj : j < R.N t := by omega
        have h1 := R.birth_new t ⟨i, hi⟩
        have h2 := R.birth_new t ⟨j, hj⟩
        simp only at h1 h2
        rw [h1, h2] at heq
        have hij := M.params_injective (R.S t) (R.N t) (R.v t) (R.Λ₀ t) heq
        have : i = j := by simpa using congrArg Fin.val hij
        rw [this]

/-- The parameters of the run are pairwise distinct. -/
theorem birth_fst_injective : Function.Injective fun m => (R.birth m).1 := by
  intro m m' h
  exact R.birth_fst_injOn (max m m') m m'
    (lt_of_lt_of_le (R.lt_L m) (R.L_mono (le_max_left m m')))
    (lt_of_lt_of_le (R.lt_L m') (R.L_mono (le_max_right m m'))) h

/-- The basis produced by the machine is the enumeration of the reference vectors. -/
theorem basis_eq {B : SchauderBasis ℂ (LebesgueLp p)}
    (hB : ∀ t n (h : n < (M.births (R.S t)).length), B n = ((M.births (R.S t)).get ⟨n, h⟩).2)
    (m : ℕ) : B m = (R.birth m).2 := by
  unfold birth
  rw [List.getD_eq_getElem _ _ (R.lt_L m)]
  exact hB m m (R.lt_L m)

/-! ### The total error -/

/-- The total distance between the translates of `g` and the reference vectors born
before step `t`. -/
def err (t : ℕ) (g : LebesgueLp p) : ℝ :=
  ∑ m ∈ Finset.range (R.L t), ‖translate p (R.birth m).1 g - (R.birth m).2‖

theorem err_zero (g : LebesgueLp p) : R.err 0 g = ‖g - intervalAtom p (0, 1)‖ := by
  unfold err
  rw [R.L_zero]
  simp [R.birth_zero]

theorem err_succ_le (t : ℕ) (g g' : LebesgueLp p) :
    R.err (t + 1) g' ≤ R.err t g + R.L t * ‖g' - g‖ + R.N t * ‖g' - R.V t‖ := by
  unfold err
  rw [R.L_succ, Finset.sum_range_add]
  have h1 : ∑ m ∈ Finset.range (R.L t), ‖translate p (R.birth m).1 g' - (R.birth m).2‖ ≤
      ∑ m ∈ Finset.range (R.L t), ‖translate p (R.birth m).1 g - (R.birth m).2‖ +
        R.L t * ‖g' - g‖ := by
    calc
      ∑ m ∈ Finset.range (R.L t), ‖translate p (R.birth m).1 g' - (R.birth m).2‖
          ≤ ∑ m ∈ Finset.range (R.L t),
              (‖translate p (R.birth m).1 g - (R.birth m).2‖ + ‖g' - g‖) := by
        apply Finset.sum_le_sum
        intro m _
        have h : translate p (R.birth m).1 g' - (R.birth m).2 =
            (translate p (R.birth m).1 g - (R.birth m).2) +
              translate p (R.birth m).1 (g' - g) := by
          rw [translate_sub]
          abel
        rw [h]
        exact (norm_add_le _ _).trans (by rw [norm_translate])
      _ = ∑ m ∈ Finset.range (R.L t), ‖translate p (R.birth m).1 g - (R.birth m).2‖ +
            R.L t * ‖g' - g‖ := by
        rw [Finset.sum_add_distrib]
        simp
  have h2 : ∑ i ∈ Finset.range (R.N t),
      ‖translate p (R.birth (R.L t + i)).1 g' - (R.birth (R.L t + i)).2‖ =
        R.N t * ‖g' - R.V t‖ := by
    rw [Finset.sum_range]
    simp only [R.birth_new, ← translate_sub, norm_translate]
    simp
  linarith

/-- The total error stays below `6 κ` along the run. -/
theorem err_le {κ : ℝ} {g : ℕ → LebesgueLp p}
    (hg0 : ‖g 0 - intervalAtom p (0, 1)‖ ≤ κ)
    (hgL : ∀ t, ((R.L t : ℝ) + 1) * ‖g (t + 1) - g t‖ ≤ 3 / 2 * κ * (1 / 2) ^ t)
    (hgV : ∀ t, (R.N t : ℝ) * ‖g (t + 1) - R.V t‖ ≤ κ * (1 / 2) ^ t) (t : ℕ) :
    R.err t (g t) ≤ κ * (6 - 5 * (1 / 2) ^ t) := by
  induction t with
  | zero =>
    rw [R.err_zero]
    norm_num
    exact hg0
  | succ t ih =>
    have h1 := R.err_succ_le t (g t) (g (t + 1))
    have h2 : (R.L t : ℝ) * ‖g (t + 1) - g t‖ ≤ 3 / 2 * κ * (1 / 2) ^ t := by
      refine le_trans ?_ (hgL t)
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h3 := hgV t
    rw [pow_succ]
    linarith

/-- **The total error of the limit generator.** -/
theorem summable_translate_error {κ : ℝ} (hκ : 0 ≤ κ) {g : ℕ → LebesgueLp p}
    {glim : LebesgueLp p}
    (hg0 : ‖g 0 - intervalAtom p (0, 1)‖ ≤ κ)
    (hgL : ∀ t, ((R.L t : ℝ) + 1) * ‖g (t + 1) - g t‖ ≤ 3 / 2 * κ * (1 / 2) ^ t)
    (hgV : ∀ t, (R.N t : ℝ) * ‖g (t + 1) - R.V t‖ ≤ κ * (1 / 2) ^ t)
    (hg : Tendsto g atTop (𝓝 glim)) :
    Summable (fun m => ‖translate p (R.birth m).1 glim - (R.birth m).2‖) ∧
      ∑' m, ‖translate p (R.birth m).1 glim - (R.birth m).2‖ ≤ 6 * κ := by
  have hpart : ∀ n : ℕ,
      ∑ m ∈ Finset.range n, ‖translate p (R.birth m).1 glim - (R.birth m).2‖ ≤ 6 * κ := by
    intro n
    have hlim : Tendsto
        (fun t => ∑ m ∈ Finset.range n, ‖translate p (R.birth m).1 (g t) - (R.birth m).2‖)
        atTop (𝓝 (∑ m ∈ Finset.range n, ‖translate p (R.birth m).1 glim - (R.birth m).2‖)) := by
      refine tendsto_finsetSum _ fun m _ => ?_
      have hT : Tendsto (fun t => translate p (R.birth m).1 (g t)) atTop
          (𝓝 (translate p (R.birth m).1 glim)) :=
        ((isometry_translate (p := p) (R.birth m).1).continuous.tendsto glim).comp hg
      exact (hT.sub_const _).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop n] with t ht
    calc
      ∑ m ∈ Finset.range n, ‖translate p (R.birth m).1 (g t) - (R.birth m).2‖
          ≤ R.err t (g t) := by
        unfold err
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (ht.trans (R.lt_L t).le)) (fun _ _ _ => norm_nonneg _)
      _ ≤ κ * (6 - 5 * (1 / 2) ^ t) := R.err_le hg0 hgL hgV t
      _ ≤ 6 * κ := by
        have : 0 ≤ κ * (5 * (1 / 2 : ℝ) ^ t) := by positivity
        linarith
  exact ⟨summable_of_sum_range_le (fun _ => norm_nonneg _) hpart,
    Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) hpart⟩

end MachineRun

end StructuredBases.PositiveTranslates
