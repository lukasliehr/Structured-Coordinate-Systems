import Lean_Code.PositiveTranslates.Analytic.GaussianLp
import Lean_Code.PositiveTranslates.Analytic.StepDensity

/-!
# The analytic run driving a stage machine

Given a stage machine `M` (the reference construction) and a budget `0 < κ ≤ 1/100`, we
construct recursively machine states `S t`, admissible inputs `v t`, entire functions `G t`
(non-negative on `ℝ`) and their `Lᵖ` classes `g t` on the real line (paper, subsection
"Choosing the stages").

Step `t` (from `S t` to `S (t+1)`), with `L = (M.births (S t)).length`:

1. `N ≥ M.minSize (S t)` with `8 N^{2/p-1} ≤ κ 2^{-t} / (L+1)`;
2. `ρ = κ 2^{-t} / (N (L+1))` and an admissible `v` with `‖v - g_t‖ ≤ ρ/2`;
3. the scale `d ≤ 4` and amplitude `a` of the machine, so `‖V - v‖ = a N^{1/p} ≤ κ 2^{-t}/(L+1)`;
4. an entire smoothing `H` of the target with `a N ‖H - h‖ ≤ ρ/2`;
5. `Λ₀` with `a N sup_{|z| ≤ t+1} |H(z + λ)| ≤ 2^{-(t+1)}` for `λ > Λ₀`.

Then `G_{t+1} = G_t + a ∑ᵢ H(· + λᵢ)`.  The result is `exists_analytic_run`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ComplexOrder BigOperators Real

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

/-! ### Numerical facts about the packet scales -/

theorem posScale_bounds {r V : ℝ} {N : ℕ} (hr : 1 ≤ r) (hV0 : 0 ≤ V) (hV : V ≤ 2)
    (hdef : posDeficit r N ≤ 1 / 2) : 0 ≤ posScale r V N ∧ posScale r V N ≤ 4 := by
  have h1 : (1 / 2 : ℝ) ≤ (1 - posDeficit r N) ^ (1 / r) := by
    have ha : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / r) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (show 1 / r ≤ 1 by rw [div_le_one (by linarith)]; exact hr)
      simpa using h
    exact ha.trans (Real.rpow_le_rpow (by norm_num) (by linarith) (by positivity))
  unfold posScale
  constructor
  · exact div_nonneg hV0 (by linarith)
  · rw [div_le_iff₀ (by linarith)]
    linarith

theorem posAmplitude_mul_rpow_analytic {r d : ℝ} {N : ℕ} (hr : 0 < r) (hN : 1 ≤ N) :
    posAmplitude r d N * (N : ℝ) ^ (1 / r) = 2 * d * (N : ℝ) ^ (2 / r - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold posAmplitude
  rw [mul_assoc, ← Real.rpow_add hNpos]
  congr 2
  field_simp
  ring

/-- Packet sizes with small edit cost exist because `2/p - 1 < 0`. -/
theorem exists_analytic_packet_size {r : ℝ} (hr : 2 < r) {η : ℝ} (hη : 0 < η) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 1 ≤ N ∧ 8 * (N : ℝ) ^ (2 / r - 1) ≤ η := by
  have hy : 0 < 1 - 2 / r := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hr
  have ht : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-(1 - 2 / r))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < η / 8 by positivity))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  refine ⟨max N₁ (max N₀ 1), le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  have h := hN₁ _ (le_max_left N₁ (max N₀ 1))
  have hexp : 2 / r - 1 = -(1 - 2 / r) := by ring
  rw [hexp]
  linarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Γ : Set ℝ}

omit [Fact (1 ≤ p)] in
theorem isNonneg_intervalAtom_analytic (ab : ℝ × ℝ) : IsNonneg (intervalAtom p ab) := by
  filter_upwards [intervalAtom_ae p ab] with x hx
  rw [hx]
  by_cases h : x ∈ Ico ab.1 ab.2 <;> simp [h]

/-! ### Stages -/

/-- A finite stage of the analytic construction: the stage counter, the machine state, the
entire function, and its `Lᵖ` class on the real line. -/
structure Stage (M : StageMachine p Γ) where
  /-- the number of steps performed so far -/
  t : ℕ
  /-- the state of the reference machine -/
  S : M.State
  /-- the entire function -/
  G : ℂ → ℂ
  /-- its class on the real line -/
  g : LebesgueLp p

/-- The invariants of a stage. -/
abbrev Stage.Good {M : StageMachine p Γ} (κ : ℝ) (d : Stage M) : Prop :=
  Differentiable ℂ d.G ∧ (∀ x : ℝ, 0 ≤ d.G x) ∧
    (d.g : ℝ → ℂ) =ᵐ[volume] (fun x : ℝ => d.G x) ∧
    ‖d.g - intervalAtom p (0, 1)‖ ≤ κ * (4 - 3 * (1 / 2) ^ d.t)

/-- `d'` is obtained from `d` by one analytic step with budget `κ`. -/
abbrev Stage.Next {M : StageMachine p Γ} (κ : ℝ) (d d' : Stage M) : Prop :=
  ∃ (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ),
    d'.t = d.t + 1 ∧ M.minSize d.S ≤ N ∧ Admissible v ∧ d'.S = M.next d.S N v Λ₀ ∧
    (∀ z : ℂ, ‖z‖ ≤ (d.t : ℝ) + 1 → ‖d'.G z - d.G z‖ ≤ (1 / 2) ^ (d.t + 1)) ∧
    (((M.births d.S).length : ℝ) + 1) * ‖d'.g - d.g‖ ≤ 3 / 2 * κ * (1 / 2) ^ d.t ∧
    (N : ℝ) * ‖d'.g - referenceFunction p v (M.target d.S) (M.params d.S N v Λ₀)‖ ≤
      κ * (1 / 2) ^ d.t

theorem exists_initial_stage (hp' : p ≠ ∞) (M : StageMachine p Γ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ d : Stage M, d.t = 0 ∧ d.S = M.init ∧ d.Good κ := by
  obtain ⟨H, Hlp, hHdiff, hHpos, hHlp, hHh, -⟩ := exists_entire_smoothing hp'
    (intervalAtom_isCompactStep p (0, 1)) (isNonneg_intervalAtom_analytic (0, 1)) hκ
  have h : κ * (4 - 3 * (1 / 2 : ℝ) ^ 0) = κ := by norm_num
  exact ⟨⟨0, M.init, H, Hlp⟩, rfl, rfl, hHdiff, hHpos, hHlp, hHh.trans (le_of_eq h.symm)⟩

/-- **One analytic stage.** -/
theorem exists_next_stage (hp : 2 < p) (hp' : p ≠ ∞) (M : StageMachine p Γ) {κ : ℝ}
    (hκ : 0 < κ) (hκ' : κ ≤ 1 / 100) (d : Stage M) (hd : d.Good κ) :
    ∃ d' : Stage M, d'.Good κ ∧ d.Next κ d' := by
  obtain ⟨hGdiff, hGpos, hgG, hgnorm⟩ := hd
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hP : 2 < p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal (by norm_num) hp').mpr hp
  set L : ℝ := ((M.births d.S).length : ℝ) + 1 with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    linarith [Nat.cast_nonneg (α := ℝ) (M.births d.S).length]
  set q : ℝ := (1 / 2 : ℝ) ^ d.t with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  -- Step 1: the packet size
  obtain ⟨N, hNmin, hN1, hNη⟩ :=
    exists_analytic_packet_size hP (η := κ * q / L) (by positivity) (M.minSize d.S)
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- Step 2: the admissible input
  set ρ : ℝ := κ * q / (N * L) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρκ : ρ ≤ κ := by
    rw [hρ, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ N * L := one_le_mul_of_one_le_of_one_le hNpos hL1
    nlinarith
  have hgnonneg : IsNonneg d.g := by
    filter_upwards [hgG] with x hx
    rw [hx]
    exact hGpos x
  obtain ⟨v, hvstep, hvpos, hvg⟩ :=
    exists_nonneg_compactStep_near hp' d.g hgnonneg (half_pos hρ0)
  have hone : ‖intervalAtom p (0, 1)‖ = 1 := initial_generator_unit p hp0 hp'
  have hv1 : ‖v - intervalAtom p (0, 1)‖ ≤ 5 * κ := by
    calc
      ‖v - intervalAtom p (0, 1)‖ ≤ ‖v - d.g‖ + ‖d.g - intervalAtom p (0, 1)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ρ / 2 + κ * (4 - 3 * q) := add_le_add hvg hgnorm
      _ ≤ 5 * κ := by nlinarith
  have hvadm : Admissible v := by
    refine ⟨hvstep, hvpos, ?_, ?_⟩
    · have h := norm_sub_norm_le (intervalAtom p (0, 1)) v
      rw [hone, norm_sub_rev] at h
      linarith
    · have h := norm_add_le (v - intervalAtom p (0, 1)) (intervalAtom p (0, 1))
      rw [sub_add_cancel, hone] at h
      linarith
  -- Step 3: scale and amplitude
  have hdef := M.deficit_le d.S N hNmin
  obtain ⟨hd0, hd4⟩ := posScale_bounds (r := p.toReal) (N := N) (by linarith)
    (norm_nonneg v) hvadm.upper hdef
  set a : ℝ := posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N with ha
  have ha0 : 0 ≤ a := by
    rw [ha]
    unfold posAmplitude
    exact mul_nonneg (mul_nonneg zero_le_two hd0) (Real.rpow_nonneg (by linarith) _)
  have hrpow0 : 0 ≤ (N : ℝ) ^ (2 / p.toReal - 1) := Real.rpow_nonneg (by linarith) _
  have haN : a * (N : ℝ) ^ (1 / p.toReal) ≤ κ * q / L := by
    rw [ha, posAmplitude_mul_rpow_analytic (by linarith) hN1]
    calc
      2 * posScale p.toReal ‖v‖ N * (N : ℝ) ^ (2 / p.toReal - 1)
          ≤ 2 * 4 * (N : ℝ) ^ (2 / p.toReal - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hrpow0
      _ = 8 * (N : ℝ) ^ (2 / p.toReal - 1) := by ring
      _ ≤ κ * q / L := hNη
  -- Step 4: the entire smoothing of the target
  have haN0 : 0 ≤ a * N := mul_nonneg ha0 (by linarith)
  have haN1 : 0 < a * N + 1 := by linarith
  obtain ⟨H, Hlp, hHdiff, hHpos, hHlp, hHh, hHtail⟩ := exists_entire_smoothing hp'
    (M.target_step d.S) (M.target_nonneg d.S) (ε := ρ / (2 * (a * N + 1))) (by positivity)
  -- Step 5: the lower bound for the parameters
  obtain ⟨Λ₀, hΛ₀⟩ := hHtail ((d.t : ℝ) + 1) ((1 / 2 : ℝ) ^ (d.t + 1) / (a * N + 1))
    (by positivity)
  set lam : Fin N → ℝ := M.params d.S N v Λ₀ with hlam
  set V : LebesgueLp p := referenceFunction p v (M.target d.S) lam with hV
  -- the smoothing error of the increment
  set E : LebesgueLp p := a • ∑ i : Fin N, translate p (-(lam i)) (Hlp - M.target d.S) with hE
  have hfrac : a * N / (a * N + 1) ≤ 1 := (div_le_one haN1).mpr (by linarith)
  have hEnorm : ‖E‖ ≤ ρ / 2 := by
    calc
      ‖E‖ = a * ‖∑ i : Fin N, translate p (-(lam i)) (Hlp - M.target d.S)‖ := by
        rw [hE, norm_smul, Real.norm_of_nonneg ha0]
      _ ≤ a * ∑ i : Fin N, ‖translate p (-(lam i)) (Hlp - M.target d.S)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) ha0
      _ = a * N * ‖Hlp - M.target d.S‖ := by
        simp only [norm_translate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      _ ≤ a * N * (ρ / (2 * (a * N + 1))) := mul_le_mul_of_nonneg_left hHh haN0
      _ = ρ / 2 * (a * N / (a * N + 1)) := by
        field_simp
      _ ≤ ρ / 2 := mul_le_of_le_one_right (by positivity) hfrac
  set g' : LebesgueLp p := d.g + a • ∑ i : Fin N, translate p (-(lam i)) Hlp with hg'
  have hVdef : V = v + a • ∑ i : Fin N, translate p (-(lam i)) (M.target d.S) := rfl
  have hg'V : g' - V = (d.g - v) + E := by
    rw [hg', hVdef, hE]
    simp only [translate_sub, Finset.sum_sub_distrib, smul_sub]
    abel
  have hg'g : g' - d.g = (V - v) + E := by
    rw [hg', hVdef, hE]
    simp only [translate_sub, Finset.sum_sub_distrib, smul_sub]
    abel
  have hVv : ‖V - v‖ ≤ κ * q / L := by
    rw [hV, hlam, M.reference_edit_norm d.S N v Λ₀ hNmin hvadm]
    exact haN
  have hstep2 : ‖g' - d.g‖ ≤ κ * q / L + ρ / 2 := by
    rw [hg'g]
    exact (norm_add_le _ _).trans (add_le_add hVv hEnorm)
  have hstep3 : ‖g' - V‖ ≤ ρ := by
    rw [hg'V]
    calc
      ‖d.g - v + E‖ ≤ ‖d.g - v‖ + ‖E‖ := norm_add_le _ _
      _ ≤ ρ / 2 + ρ / 2 := add_le_add (by rw [norm_sub_rev]; exact hvg) hEnorm
      _ = ρ := add_halves ρ
  have hL2 : L * ‖g' - d.g‖ ≤ 3 / 2 * κ * q := by
    calc
      L * ‖g' - d.g‖ ≤ L * (κ * q / L + ρ / 2) :=
        mul_le_mul_of_nonneg_left hstep2 (by linarith)
      _ = κ * q + κ * q / (2 * N) := by
        rw [hρ]
        field_simp
      _ ≤ κ * q + κ * q / 2 := by
        have h : κ * q / (2 * N) ≤ κ * q / 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
        linarith
      _ = 3 / 2 * κ * q := by ring
  have hN3 : (N : ℝ) * ‖g' - V‖ ≤ κ * q := by
    calc
      (N : ℝ) * ‖g' - V‖ ≤ N * ρ := mul_le_mul_of_nonneg_left hstep3 (by linarith)
      _ = κ * q / L := by
        rw [hρ]
        field_simp
      _ ≤ κ * q := div_le_self (by positivity) hL1
  refine ⟨⟨d.t + 1, M.next d.S N v Λ₀,
      fun z => d.G z + (a : ℂ) * ∑ i : Fin N, H (z + lam i), g'⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨N, v, Λ₀, rfl, hNmin, hvadm, rfl, ?_, hL2, hN3⟩⟩
  · -- the new function is entire
    exact hGdiff.add ((differentiable_const _).mul
      (Differentiable.fun_sum fun i _ => hHdiff.comp (differentiable_id.add_const _)))
  · -- and non-negative on the real line
    intro x
    refine add_nonneg (hGpos x)
      (mul_nonneg (Complex.zero_le_real.mpr ha0) (Finset.sum_nonneg fun i _ => ?_))
    rw [← Complex.ofReal_add]
    exact hHpos _
  · -- its class on the real line
    have hT : ∀ᵐ x ∂(volume : Measure ℝ), ∀ i : Fin N,
        translate p (-(lam i)) Hlp x = H ((x : ℂ) + lam i) := by
      rw [ae_all_iff]
      intro i
      have h1 := translate_ae p (-(lam i)) Hlp
      have h2 := (measurePreserving_sub_right volume (-(lam i))).quasiMeasurePreserving.ae hHlp
      filter_upwards [h1, h2] with x hx1 hx2
      rw [hx1, hx2]
      congr 1
      push_cast
      ring
    filter_upwards [Lp.coeFn_add d.g (a • ∑ i : Fin N, translate p (-(lam i)) Hlp),
      Lp.coeFn_smul a (∑ i : Fin N, translate p (-(lam i)) Hlp),
      Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin N => translate p (-(lam i)) Hlp),
      hgG, hT] with x h1 h2 h3 h4 h5
    show g' x = d.G x + (a : ℂ) * ∑ i : Fin N, H ((x : ℂ) + lam i)
    rw [hg', h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]
    congr 2
    exact Finset.sum_congr rfl fun i _ => h5 i
  · -- the norm invariant
    show ‖g' - intervalAtom p (0, 1)‖ ≤ κ * (4 - 3 * (1 / 2) ^ (d.t + 1))
    have hgg : ‖g' - d.g‖ ≤ 3 / 2 * κ * q :=
      le_trans (le_mul_of_one_le_left (norm_nonneg _) hL1) hL2
    calc
      ‖g' - intervalAtom p (0, 1)‖ ≤ ‖g' - d.g‖ + ‖d.g - intervalAtom p (0, 1)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3 / 2 * κ * q + κ * (4 - 3 * q) := add_le_add hgg hgnorm
      _ = κ * (4 - 3 * (1 / 2) ^ (d.t + 1)) := by
        rw [pow_succ, ← hq]
        ring
  · -- the increment is small on the disc of radius `t + 1`
    intro z hz
    show ‖(d.G z + (a : ℂ) * ∑ i : Fin N, H (z + lam i)) - d.G z‖ ≤ (1 / 2) ^ (d.t + 1)
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
    calc
      a * ‖∑ i : Fin N, H (z + lam i)‖ ≤ a * ∑ i : Fin N, ‖H (z + lam i)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) ha0
      _ ≤ a * ∑ _i : Fin N, (1 / 2 : ℝ) ^ (d.t + 1) / (a * N + 1) := by
        apply mul_le_mul_of_nonneg_left _ ha0
        exact Finset.sum_le_sum fun i _ => hΛ₀ (lam i) (M.params_gt d.S N v Λ₀ i) z hz
      _ = a * N / (a * N + 1) * (1 / 2 : ℝ) ^ (d.t + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ (1 / 2 : ℝ) ^ (d.t + 1) := mul_le_of_le_one_left (by positivity) hfrac

/-! ### The run -/

/-- **The analytic run.** For every budget `0 < κ ≤ 1/100` there is a run of the machine
driven by admissible inputs together with entire functions `G t`, non-negative on `ℝ`, with
`Lᵖ` classes `g t`, such that the increments of `G` are summable on discs, the increments
of `g` are summable with the weights `L_t + 1`, and each new reference function `V_t` is
within `κ 2^{-t} / N_t` of `g_{t+1}`. -/
theorem exists_analytic_run (hp : 2 < p) (hp' : p ≠ ∞) (M : StageMachine p Γ) {κ : ℝ}
    (hκ : 0 < κ) (hκ' : κ ≤ 1 / 100) :
    ∃ (S : ℕ → M.State) (N : ℕ → ℕ) (v : ℕ → LebesgueLp p) (Λ₀ : ℕ → ℝ)
      (G : ℕ → ℂ → ℂ) (g : ℕ → LebesgueLp p),
      S 0 = M.init ∧ (∀ t, S (t + 1) = M.next (S t) (N t) (v t) (Λ₀ t)) ∧
      (∀ t, M.minSize (S t) ≤ N t) ∧ (∀ t, Admissible (v t)) ∧
      (∀ t, Differentiable ℂ (G t)) ∧ (∀ t (x : ℝ), 0 ≤ G t x) ∧
      (∀ t, (g t : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => G t x) ∧
      (∀ t, ‖g t - intervalAtom p (0, 1)‖ ≤ κ * (4 - 3 * (1 / 2) ^ t)) ∧
      (∀ (t : ℕ) (z : ℂ), ‖z‖ ≤ (t : ℝ) + 1 → ‖G (t + 1) z - G t z‖ ≤ (1 / 2) ^ (t + 1)) ∧
      (∀ t, (((M.births (S t)).length : ℝ) + 1) * ‖g (t + 1) - g t‖ ≤
        3 / 2 * κ * (1 / 2) ^ t) ∧
      (∀ t, (N t : ℝ) * ‖g (t + 1) - referenceFunction p (v t) (M.target (S t))
        (M.params (S t) (N t) (v t) (Λ₀ t))‖ ≤ κ * (1 / 2) ^ t) := by
  obtain ⟨d₀, hd₀t, hd₀S, hd₀⟩ := exists_initial_stage hp' M hκ
  let step : {d : Stage M // d.Good κ} → {d : Stage M // d.Good κ} :=
    fun d : {d : Stage M // d.Good κ} =>
      ⟨Classical.choose (exists_next_stage hp hp' M hκ hκ' d.1 d.2),
        (Classical.choose_spec (exists_next_stage hp hp' M hκ hκ' d.1 d.2)).1⟩
  have hstep : ∀ d : {d : Stage M // d.Good κ}, d.1.Next κ (step d).1 := fun d =>
    (Classical.choose_spec (exists_next_stage hp hp' M hκ hκ' d.1 d.2)).2
  let seq : ℕ → {d : Stage M // d.Good κ} := fun n => step^[n] ⟨d₀, hd₀⟩
  have hseq : ∀ n, seq (n + 1) = step (seq n) := fun n =>
    Function.iterate_succ_apply' step n _
  have hnext : ∀ n, ∃ (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ),
      (seq (n + 1)).1.t = (seq n).1.t + 1 ∧ M.minSize (seq n).1.S ≤ N ∧ Admissible v ∧
      (seq (n + 1)).1.S = M.next (seq n).1.S N v Λ₀ ∧
      (∀ z : ℂ, ‖z‖ ≤ ((seq n).1.t : ℝ) + 1 →
        ‖(seq (n + 1)).1.G z - (seq n).1.G z‖ ≤ (1 / 2) ^ ((seq n).1.t + 1)) ∧
      (((M.births (seq n).1.S).length : ℝ) + 1) * ‖(seq (n + 1)).1.g - (seq n).1.g‖ ≤
        3 / 2 * κ * (1 / 2) ^ (seq n).1.t ∧
      (N : ℝ) * ‖(seq (n + 1)).1.g - referenceFunction p v (M.target (seq n).1.S)
        (M.params (seq n).1.S N v Λ₀)‖ ≤ κ * (1 / 2) ^ (seq n).1.t := by
    intro n
    rw [hseq]
    exact hstep (seq n)
  have ht : ∀ n, (seq n).1.t = n := by
    intro n
    induction n with
    | zero => exact hd₀t
    | succ n ih =>
      obtain ⟨_, _, _, h1, -⟩ := hnext n
      rw [h1, ih]
  choose N v Λ₀ hN using hnext
  refine ⟨fun n => (seq n).1.S, N, v, Λ₀, fun n => (seq n).1.G, fun n => (seq n).1.g,
    hd₀S, fun t => (hN t).2.2.2.1, fun t => (hN t).2.1, fun t => (hN t).2.2.1,
    fun t => (seq t).2.1, fun t => (seq t).2.2.1, fun t => (seq t).2.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro t
    have h := (seq t).2.2.2.2
    rwa [ht t] at h
  · intro t z hz
    have h := (hN t).2.2.2.2.1 z (by rwa [ht t])
    rwa [ht t] at h
  · intro t
    have h := (hN t).2.2.2.2.2.1
    rwa [ht t] at h
  · intro t
    have h := (hN t).2.2.2.2.2.2
    rwa [ht t] at h

end StructuredBases.PositiveTranslates
