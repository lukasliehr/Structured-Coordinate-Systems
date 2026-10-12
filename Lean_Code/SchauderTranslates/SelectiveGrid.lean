import Lean_Code.SchauderTranslates.Contracts

noncomputable section
namespace SchauderTranslates

theorem first_crossing_exists (v : ℕ → ℝ) (A : ℝ) (N : ℕ) (hN : v N ≤ A) :
    ∃ k ≤ N, v k ≤ A ∧ ∀ i < k, A < v i := by
  classical
  let h : ∃ k, v k ≤ A := ⟨N, hN⟩
  exact ⟨Nat.find h, Nat.find_min' h hN, Nat.find_spec h,
    fun i hi => lt_of_not_ge (Nat.find_min h hi)⟩

theorem telescope_growth_bound (v : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ k, a < k → k ≤ b → v (k - 1) ≤ r * v k) :
    v a ≤ r ^ (b - a) * v b := by
  have h : ∀ m, a + m ≤ b → v a ≤ r ^ m * v (a + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have hi := ih (by omega)
      have hs := hstep (a + (m + 1)) (by omega) hm
      have hk : a + (m + 1) - 1 = a + m := by omega
      rw [hk] at hs
      calc
        v a ≤ r ^ m * v (a + m) := hi
        _ ≤ r ^ m * (r * v (a + (m + 1))) :=
          mul_le_mul_of_nonneg_left hs (pow_nonneg hr _)
        _ = r ^ (m + 1) * v (a + (m + 1)) := by rw [pow_succ]; ring
  simpa [Nat.add_sub_of_le hab] using h (b - a) (by omega)

/-- The crossing argument isolated from the analytic definition of the capture function. -/
theorem finite_grid_drop_general (v : ℕ → ℝ) {N a b : ℕ} {A B D r : ℝ}
    (hpos : ∀ k ≤ N, 0 < v k)
    (hmono : ∀ i j, i ≤ j → j ≤ N → v j ≤ v i)
    (hstep : ∀ k, 0 < k → k ≤ N → v (k - 1) / D ≤ v k)
    (hD : 0 < D) (hr : 1 ≤ r) (hB : 0 < B)
    (h0 : A < v 0) (haN : a ≤ N) (hbN : b ≤ N)
    (ha : v a ≤ A) (haMin : ∀ i < a, A < v i)
    (hb : v b ≤ B) (hbMin : ∀ i < b, B < v i)
    (hgap : r ^ N * B < A / D) :
    ∃ k, a < k ∧ k ≤ b ∧ v k / v (k - 1) ≤ 1 / r ∧ B < v (k - 1) ∧ v (k - 1) ≤ A := by
  have ha0 : 0 < a := by
    by_contra h
    have : a = 0 := by omega
    subst a
    linarith
  have hcross : A / D < v a :=
    (div_lt_div_of_pos_right (haMin (a - 1) (by omega)) hD).trans_le (hstep a ha0 haN)
  have hAB : B < v a := by
    have hpow := one_le_pow₀ hr (n := N)
    nlinarith
  have hab : a < b := by
    by_contra h
    have := hmono b a (by omega) haN
    linarith
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  by_contra hn
  have hs (k : ℕ) (hak : a < k) (hkb : k ≤ b) : v (k - 1) ≤ r * v k := by
    have hp : 0 < v (k - 1) := hpos _ (by omega)
    have hlow := hbMin (k - 1) (by omega)
    have hupp : v (k - 1) ≤ A :=
      (hmono a (k - 1) (by omega) (by omega)).trans ha
    have hn' : ¬v k / v (k - 1) ≤ 1 / r :=
      fun hk => hn ⟨k, hak, hkb, hk, hlow, hupp⟩
    have hd := (lt_div_iff₀ hp).mp (lt_of_not_ge hn')
    have hd' : v (k - 1) / r < v k := by simpa [div_eq_mul_inv, mul_comm] using hd
    have hm := (div_lt_iff₀ hr0).mp hd'
    linarith
  have ht := telescope_growth_bound v hr0.le hab.le hs
  have hp : r ^ (b - a) ≤ r ^ N := pow_le_pow_right₀ hr (by omega)
  have hc : v a ≤ r ^ N * B := by
    calc
      v a ≤ r ^ (b - a) * v b := ht
      _ ≤ r ^ N * v b := mul_le_mul_of_nonneg_right hp (hpos b hbN).le
      _ ≤ r ^ N * B := mul_le_mul_of_nonneg_left hb (pow_nonneg hr0.le _)
  linarith

/-- The exact finite-grid estimate used in the soft-capture window. -/
theorem finite_grid_drop (v : ℕ → ℝ) {N a b : ℕ} {A B R : ℝ}
    (hR : 1 < R) (hB : 0 < B)
    (hpos : ∀ k ≤ N, 0 < v k)
    (hmono : ∀ i j, i ≤ j → j ≤ N → v j ≤ v i)
    (hstep : ∀ k, 0 < k → k ≤ N → v (k - 1) / (4 * R) ≤ v k)
    (h0 : A < v 0) (haN : a ≤ N) (hbN : b ≤ N)
    (ha : v a ≤ A) (haMin : ∀ i < a, A < v i)
    (hb : v b ≤ B) (hbMin : ∀ i < b, B < v i)
    (hgap : R ^ ((N : ℝ) / 16) < A / (4 * R * B)) :
    ∃ k, a < k ∧ k ≤ b ∧ v k / v (k - 1) ≤ R ^ (-(1 / 16 : ℝ)) ∧
      B < v (k - 1) ∧ v (k - 1) ≤ A := by
  have hR0 : 0 < R := by linarith
  have hr : 1 ≤ R ^ (1 / 16 : ℝ) := Real.one_le_rpow hR.le (by norm_num)
  have hpower : (R ^ (1 / 16 : ℝ)) ^ N = R ^ ((N : ℝ) / 16) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    congr 1
    ring
  have hmargin : (R ^ (1 / 16 : ℝ)) ^ N * B < A / (4 * R) := by
    rw [hpower]
    have hd : 0 < 4 * R * B := by positivity
    have ht := (lt_div_iff₀ hd).mp hgap
    apply (lt_div_iff₀ (by positivity : 0 < 4 * R)).mpr
    nlinarith
  have ht := finite_grid_drop_general v hpos hmono hstep (by positivity) hr hB
    h0 haN hbN ha haMin hb hbMin hmargin
  simpa only [Real.rpow_neg hR0.le, one_div] using ht

end SchauderTranslates
