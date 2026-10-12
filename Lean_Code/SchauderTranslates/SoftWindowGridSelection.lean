import Lean_Code.SchauderTranslates.SoftGeometricGrid

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The finite selection argument depends only on the soft-capture inequalities,
with all numerical margins supplied before the function is chosen. -/
theorem soft_window_on_grid {X R : ℝ} (hX : 0 < X) (hR : 1 < R)
    (hA : Real.exp (-X / 4) < 1 / 4000)
    (hhalf : R * Real.exp (-X / 2) < 1 / 2)
    (hmargin : Real.log 4 + (17 / 16 : ℝ) * Real.log R < (5 / 32 : ℝ) * X)
    (g : ℝ → ℝ) (hmono : AntitoneOn g (Set.Icc 0 1))
    (hstart : (1 / 4000 : ℝ) ≤ g (Real.exp (-2 * X)))
    (hend : g (Real.exp (-X / 2)) ≤ Real.exp (-X / 2))
    (hstep : ∀ t : ℝ, 0 ≤ t → R * t ≤ 1 / 2 → g t / (4 * R) ≤ g (R * t)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ R * Real.exp (-X / 2) ∧
      Real.exp (-X / 2) < g (m / R) ∧ g (m / R) ≤ Real.exp (-X / 4) ∧
      g m / g (m / R) ≤ R ^ (-(1 / 16 : ℝ)) := by
  let N := softGridCount X R
  let v : ℕ → ℝ := fun k => g (softGrid X R k)
  have hR0 := zero_lt_one.trans hR
  have hN := softGrid_end_bounds hX hR
  have hgrid (k : ℕ) (hk : k ≤ N) : softGrid X R k ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(softGrid_pos X hR0 k).le, ?_⟩
    have hle := (softGrid_mono X hR.le hk).trans hN.2
    linarith
  have hprev (k : ℕ) (hk : 0 < k) : R * softGrid X R (k - 1) = softGrid X R k := by
    rw [← softGrid_step, Nat.sub_add_cancel hk]
  have hvstep (k : ℕ) (hk : 0 < k) (hkN : k ≤ N) : v (k - 1) / (4 * R) ≤ v k := by
    have ht : R * softGrid X R (k - 1) ≤ 1 / 2 := by
      rw [hprev k hk]
      exact ((softGrid_mono X hR.le hkN).trans hN.2).trans hhalf.le
    have h := hstep (softGrid X R (k - 1)) (softGrid_pos X hR0 _).le ht
    simpa only [hprev k hk] using h
  have hv0 : (1 / 4000 : ℝ) ≤ v 0 := by simpa [v, softGrid] using hstart
  have hvpos (k : ℕ) : k ≤ N → 0 < v k := by
    induction k with
    | zero => intro _; exact lt_of_lt_of_le (by norm_num) hv0
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hs := hvstep (k + 1) (by omega) hk
      simp only [Nat.add_sub_cancel] at hs
      exact (div_pos hp (by positivity)).trans_le hs
  have hvmono (i j : ℕ) (hij : i ≤ j) (hjN : j ≤ N) : v j ≤ v i :=
    hmono (hgrid i (hij.trans hjN)) (hgrid j hjN) (softGrid_mono X hR.le hij)
  have hB : 0 < Real.exp (-X / 2) := Real.exp_pos _
  have hAB : Real.exp (-X / 2) < Real.exp (-X / 4) := Real.exp_lt_exp.mpr (by linarith)
  have hvN : v N ≤ Real.exp (-X / 2) := by
    apply le_trans (hmono _ (hgrid N le_rfl) hN.1) hend
    exact ⟨hB.le, (Real.exp_le_one_iff.mpr (by linarith))⟩
  obtain ⟨a, haN, ha, haMin⟩ := first_crossing_exists v (Real.exp (-X / 4)) N (hvN.trans hAB.le)
  obtain ⟨b, hbN, hb, hbMin⟩ := first_crossing_exists v (Real.exp (-X / 2)) N hvN
  obtain ⟨k, hak, hkb, hratio, hlow, hhigh⟩ := finite_grid_drop v hR hB hvpos hvmono hvstep
    (hA.trans_le hv0) haN hbN ha haMin hb hbMin (softGrid_gap hX hR hmargin)
  have hk : 0 < k := by omega
  have he : softGrid X R k / R = softGrid X R (k - 1) := by
    rw [← hprev k hk]
    field_simp
  refine ⟨softGrid X R k, softGrid_pos X hR0 k, (softGrid_mono X hR.le (hkb.trans hbN)).trans hN.2, ?_⟩
  rw [he]
  exact ⟨hlow, hhigh, hratio⟩

end SchauderTranslates
