import Lean_Code.PositiveTranslates.StageMachine

/-!
# The scales of the positive packet

Elementary facts about the three numbers of `StageMachine.lean` (paper, proof of
`thm:translate-properties`(iii), lines 3364–3377):

* `posDeficit r N = 2^r (N-1) N^{-(r-1)}`,
* `posScale r V N = V / (1 - posDeficit r N)^{1/r}`   (the scale `d`),
* `posAmplitude r d N = 2 d N^{-(r-1)/r}`             (the amplitude `a`).

Main statements:

* `posDeficit_tendsto`, `exists_posDeficit_le_half` : the deficit tends to `0` for `r > 2`;
* `posScale_rpow`, `posScale_balance` : `d^r (1 - deficit) = V^r`;
* `pos_noise_power` : `V^r + (N-1) a^r = d^r` (the remainders are unit vectors);
* `posScale_le` : `d ≤ 2^{1/r} V` when the deficit is at most `1/2`; `le_posScale` : `V ≤ d`;
* `posAmplitude_mul_rpow` : `a N^{1/r} = 2 d N^{2/r-1}` (the cost of the edit);
* `posCost_tendsto`, `exists_packet_size` : the cost tends to `0`, uniformly for bounded `V`.
-/

noncomputable section
open Filter
open scoped Topology ENNReal

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

/-- The real exponent of `2 < p < ∞` is larger than `2`. -/
theorem two_lt_toReal {p : ℝ≥0∞} (hp : 2 < p) (hpfin : p ≠ ∞) : 2 < p.toReal := by
  simpa only [ENNReal.toReal_ofNat] using
    (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp

/-! ### The deficit -/

theorem posDeficit_eq (r : ℝ) (N : ℕ) : posDeficit r N = 2 ^ r * packetDeficit r N := by
  unfold posDeficit packetDeficit
  ring

theorem posDeficit_nonneg (r : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ posDeficit r N := by
  have hcast : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold posDeficit
  have h1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-(r - 1)) := Real.rpow_nonneg (by linarith) _
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ r := Real.rpow_nonneg (by norm_num) _
  exact mul_nonneg (mul_nonneg h3 h1) h2

/-- For `r > 2` the deficit `2^r (N-1) N^{-(r-1)}` tends to `0`. -/
theorem posDeficit_tendsto {r : ℝ} (hr : 2 < r) : Tendsto (posDeficit r) atTop (𝓝 0) := by
  have h := (packet_deficit_tendsto hr).const_mul ((2 : ℝ) ^ r)
  rw [mul_zero] at h
  exact h.congr (fun N => (posDeficit_eq r N).symm)

/-- For `r > 2` the deficit is at most `1/2` for all large `N`. -/
theorem exists_posDeficit_le_half {r : ℝ} (hr : 2 < r) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N → posDeficit r N ≤ 1 / 2 := by
  have h := (posDeficit_tendsto hr).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  exact ⟨max N₀ 1, le_max_right _ _, fun N hN => hN₀ N ((le_max_left _ _).trans hN)⟩

/-! ### The scale `d` -/

theorem posScale_pos {r V : ℝ} {N : ℕ} (hV : 0 < V) (hdef : posDeficit r N < 1) :
    0 < posScale r V N := by
  unfold posScale
  exact div_pos hV (Real.rpow_pos_of_pos (sub_pos.mpr hdef) _)

theorem posScale_nonneg {r V : ℝ} {N : ℕ} (hV : 0 ≤ V) (hdef : posDeficit r N < 1) :
    0 ≤ posScale r V N := by
  unfold posScale
  exact div_nonneg hV (Real.rpow_nonneg (sub_pos.mpr hdef).le _)

/-- `d^r = V^r / (1 - 2^r (N-1) N^{-(r-1)})`: the displayed definition of the paper. -/
theorem posScale_rpow {r V : ℝ} {N : ℕ} (hr : 0 < r) (hV : 0 ≤ V)
    (hdef : posDeficit r N < 1) :
    posScale r V N ^ r = V ^ r / (1 - posDeficit r N) := by
  have hden : 0 < 1 - posDeficit r N := sub_pos.mpr hdef
  unfold posScale
  rw [Real.div_rpow hV (Real.rpow_nonneg hden.le _), one_div,
    Real.rpow_inv_rpow hden.le (ne_of_gt hr)]

theorem posScale_balance {r V : ℝ} {N : ℕ} (hr : 0 < r) (hV : 0 ≤ V)
    (hdef : posDeficit r N < 1) :
    posScale r V N ^ r * (1 - posDeficit r N) = V ^ r := by
  rw [posScale_rpow hr hV hdef, div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hdef))]

/-- `V ≤ d`. -/
theorem le_posScale {r V : ℝ} {N : ℕ} (hr : 0 < r) (hV : 0 ≤ V) (hN : 1 ≤ N)
    (hdef : posDeficit r N < 1) : V ≤ posScale r V N := by
  have hden : 0 < 1 - posDeficit r N := sub_pos.mpr hdef
  have hle : (1 - posDeficit r N) ^ (1 / r) ≤ 1 :=
    Real.rpow_le_one hden.le (by linarith [posDeficit_nonneg r hN]) (by positivity)
  unfold posScale
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hden _)]
  exact mul_le_of_le_one_right hV hle

/-- `d ≤ 2^{1/r} V` as soon as the deficit is at most `1/2`. -/
theorem posScale_le {r V : ℝ} {N : ℕ} (hr : 0 < r) (hV : 0 ≤ V)
    (hdef : posDeficit r N ≤ 1 / 2) : posScale r V N ≤ 2 ^ (1 / r) * V := by
  have hhalf : (1 / 2 : ℝ) ≤ 1 - posDeficit r N := by linarith
  have hpow : (1 / 2 : ℝ) ^ (1 / r) ≤ (1 - posDeficit r N) ^ (1 / r) :=
    Real.rpow_le_rpow (by norm_num) hhalf (by positivity)
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (1 / r) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (1 / 2 : ℝ) ^ (1 / r) = ((2 : ℝ) ^ (1 / r))⁻¹ := by
    rw [one_div (2 : ℝ), Real.inv_rpow (by norm_num)]
  unfold posScale
  calc V / (1 - posDeficit r N) ^ (1 / r) ≤ V / (1 / 2 : ℝ) ^ (1 / r) :=
        div_le_div_of_nonneg_left hV hpos hpow
    _ = 2 ^ (1 / r) * V := by rw [hinv, div_inv_eq_mul, mul_comm]

/-- The scale tends to `V` as `N → ∞`. -/
theorem posScale_tendsto {r : ℝ} (hr : 2 < r) (V : ℝ) :
    Tendsto (posScale r V) atTop (𝓝 V) := by
  have hden : Tendsto (fun N => 1 - posDeficit r N) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (posDeficit_tendsto hr)
  have hpow : Tendsto (fun N => (1 - posDeficit r N) ^ (1 / r)) atTop
      (𝓝 ((1 : ℝ) ^ (1 / r))) := hden.rpow_const (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hpow
  have hdiv := (tendsto_const_nhds (x := V)).div hpow one_ne_zero
  rw [div_one] at hdiv
  exact hdiv

/-! ### The amplitude `a` -/

theorem posAmplitude_eq (r d : ℝ) (N : ℕ) :
    posAmplitude r d N = packetAmplitude r (2 * d) N := rfl

theorem posAmplitude_eq_mul (r d : ℝ) (N : ℕ) :
    posAmplitude r d N = d * (2 * (N : ℝ) ^ (-(r - 1) / r)) := by
  unfold posAmplitude
  ring

theorem posAmplitude_pos {r d : ℝ} {N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    0 < posAmplitude r d N := by
  rw [posAmplitude_eq]
  exact packet_amplitude_pos (by linarith) hN

theorem posAmplitude_nonneg {r d : ℝ} {N : ℕ} (hd : 0 ≤ d) : 0 ≤ posAmplitude r d N := by
  unfold posAmplitude
  exact mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- `a^r = 2^r d^r N^{-(r-1)}`. -/
theorem posAmplitude_rpow {r d : ℝ} {N : ℕ} (hr : 0 < r) (hd : 0 ≤ d) (hN : 1 ≤ N) :
    posAmplitude r d N ^ r = 2 ^ r * d ^ r * (N : ℝ) ^ (-(r - 1)) := by
  rw [posAmplitude_eq, packet_amplitude_rpow hr (by linarith) hN,
    Real.mul_rpow (by norm_num) hd]

/-- `(N-1) a^r = d^r · deficit`. -/
theorem posAmplitude_rpow_mul {r d : ℝ} {N : ℕ} (hr : 0 < r) (hd : 0 ≤ d) (hN : 1 ≤ N) :
    ((N - 1 : ℕ) : ℝ) * posAmplitude r d N ^ r = d ^ r * posDeficit r N := by
  rw [posAmplitude_rpow hr hd hN, Nat.cast_sub hN, Nat.cast_one]
  unfold posDeficit
  ring

/-- The balance that makes the remainders unit vectors: `V^r + (N-1) a^r = d^r`. -/
theorem pos_noise_power {r V : ℝ} {N : ℕ} (hr : 0 < r) (hV : 0 ≤ V) (hN : 1 ≤ N)
    (hdef : posDeficit r N < 1) :
    V ^ r + ((N - 1 : ℕ) : ℝ) * posAmplitude r (posScale r V N) N ^ r =
      posScale r V N ^ r := by
  rw [posAmplitude_rpow_mul hr (posScale_nonneg hV hdef) hN]
  have hbal := posScale_balance hr hV hdef
  linear_combination -hbal

/-! ### The cost of the edit -/

/-- `(a N^{1/r})^r = N a^r`. -/
theorem mul_rpow_one_div_rpow {r a : ℝ} {N : ℕ} (hr : 0 < r) (ha : 0 ≤ a) :
    (a * (N : ℝ) ^ (1 / r)) ^ r = (N : ℝ) * a ^ r := by
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Real.mul_rpow ha (Real.rpow_nonneg hNR _), one_div,
    Real.rpow_inv_rpow hNR (ne_of_gt hr), mul_comm]

/-- The cost of the edit (paper: `‖v' - v‖ = 2 d N^{2/p-1}`):
`a N^{1/r} = 2 d N^{2/r-1}`. -/
theorem posAmplitude_mul_rpow {r d : ℝ} {N : ℕ} (hr : r ≠ 0) (hN : 1 ≤ N) :
    posAmplitude r d N * (N : ℝ) ^ (1 / r) = 2 * d * (N : ℝ) ^ (2 / r - 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold posAmplitude
  rw [mul_assoc, ← Real.rpow_add hNR]
  congr 2
  field_simp
  ring

theorem rpow_two_div_sub_one_tendsto {r : ℝ} (hr : 2 < r) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (2 / r - 1)) atTop (𝓝 0) := by
  have hneg : 0 < 1 - 2 / r := by
    have hpos : 0 < r := by linarith
    have hlt : 2 / r < 1 := (div_lt_one hpos).mpr hr
    linarith
  simpa only [Function.comp_def, neg_sub] using
    (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop

/-- The cost `a N^{1/r} = 2 d N^{2/r-1}` of the edit tends to `0` as `N → ∞` (`r > 2`). -/
theorem posCost_tendsto {r : ℝ} (hr : 2 < r) (V : ℝ) :
    Tendsto (fun N : ℕ => posAmplitude r (posScale r V N) N * (N : ℝ) ^ (1 / r))
      atTop (𝓝 0) := by
  have hr0 : r ≠ 0 := by linarith
  have hlim : Tendsto (fun N : ℕ => 2 * posScale r V N * (N : ℝ) ^ (2 / r - 1))
      atTop (𝓝 0) := by
    have h := ((posScale_tendsto hr V).const_mul 2).mul (rpow_two_div_sub_one_tendsto hr)
    rwa [mul_zero] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (posAmplitude_mul_rpow hr0 hN).symm

/-- The cost of the edit is at most `2 · 2^{1/r} V N^{2/r-1}` when the deficit is at
most `1/2`. -/
theorem posCost_le {r V : ℝ} {N : ℕ} (hr : 0 < r) (hV : 0 ≤ V) (hN : 1 ≤ N)
    (hdef : posDeficit r N ≤ 1 / 2) :
    posAmplitude r (posScale r V N) N * (N : ℝ) ^ (1 / r) ≤
      2 * (2 ^ (1 / r) * V) * (N : ℝ) ^ (2 / r - 1) := by
  rw [posAmplitude_mul_rpow (ne_of_gt hr) hN]
  have hpow : (0 : ℝ) ≤ (N : ℝ) ^ (2 / r - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hle := posScale_le hr hV hdef
  exact mul_le_mul_of_nonneg_right (by linarith) hpow

/-- Choice of the packet size, uniformly for inputs of bounded norm: for `r > 2`, a bound
`C` and `ε > 0` there is `N₀ ≥ 1` such that for every `N ≥ N₀` the deficit is at most `1/2`
and the cost `a N^{1/r}` of the edit is at most `ε` for every `0 ≤ V ≤ C`. -/
theorem exists_packet_size {r : ℝ} (hr : 2 < r) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N → posDeficit r N ≤ 1 / 2 ∧
      ∀ V : ℝ, 0 ≤ V → V ≤ C →
        posAmplitude r (posScale r V N) N * (N : ℝ) ^ (1 / r) ≤ ε := by
  have hr0 : 0 < r := by linarith
  obtain ⟨N₁, hN₁, hdef⟩ := exists_posDeficit_le_half hr
  have hlim : Tendsto (fun N : ℕ => 2 * (2 ^ (1 / r) * C) * (N : ℝ) ^ (2 / r - 1))
      atTop (𝓝 0) := by
    have h := (rpow_two_div_sub_one_tendsto hr).const_mul (2 * (2 ^ (1 / r) * C))
    rwa [mul_zero] at h
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds hε))
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), fun N hN => ?_⟩
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  refine ⟨hdef N hNN₁, fun V hV hVC => ?_⟩
  have hpow : (0 : ℝ) ≤ (N : ℝ) ^ (2 / r - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / r) := Real.rpow_nonneg (by norm_num) _
  calc posAmplitude r (posScale r V N) N * (N : ℝ) ^ (1 / r)
      ≤ 2 * (2 ^ (1 / r) * V) * (N : ℝ) ^ (2 / r - 1) :=
        posCost_le hr0 hV (hN₁.trans hNN₁) (hdef N hNN₁)
    _ ≤ 2 * (2 ^ (1 / r) * C) * (N : ℝ) ^ (2 / r - 1) := by
        apply mul_le_mul_of_nonneg_right _ hpow
        have := mul_le_mul_of_nonneg_left hVC h2
        linarith
    _ ≤ ε := hN₂ N hNN₂

end StructuredBases.PositiveTranslates
