import Lean_Code.SchauderTranslates.Lp.HaarSpanning

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haarDyadicStep_ae (p : ℝ≥0∞) (n : ℕ) (c : Fin (2 ^ n) → ℂ) :
    (haarDyadicStep p n c : ℝ → ℂ) =ᵐ[haarMeasure]
      (fun x => ∑ k : Fin (2 ^ n), c k * (dyadicInterval n k).indicator (fun _ => (1 : ℂ)) x) := by
  have hc : ∀ᵐ x ∂haarMeasure, ∀ k : Fin (2 ^ n), haarIntervalAtom p n k x =
      (dyadicInterval n k).indicator (fun _ => (1 : ℂ)) x :=
    Filter.eventually_all.mpr (fun k => haarIntervalAtom_ae p n k)
  have hs : ∀ᵐ x ∂haarMeasure, ∀ k : Fin (2 ^ n),
      (c k • haarIntervalAtom p n k) x = c k • haarIntervalAtom p n k x := by
    apply Filter.eventually_all.mpr
    intro k
    filter_upwards [Lp.coeFn_smul (c k) (haarIntervalAtom p n k)] with x hx
    simpa only [Pi.smul_apply] using hx
  filter_upwards [hc, hs, Lp.coeFn_fun_finsetSum Finset.univ (fun k : Fin (2 ^ n) =>
    c k • haarIntervalAtom p n k)] with x hc hs hsum
  change (∑ k : Fin (2 ^ n), c k • haarIntervalAtom p n k) x = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hs k, smul_eq_mul, hc k]

theorem haarDyadicStep_value (n : ℕ) (c : Fin (2 ^ n) → ℂ) (k : Fin (2 ^ n))
    {x : ℝ} (hx : x ∈ dyadicInterval n k) :
    (∑ l : Fin (2 ^ n), c l * (dyadicInterval n l).indicator (fun _ => (1 : ℂ)) x) = c k := by
  classical
  rw [Finset.sum_eq_single k]
  · simp [hx]
  · intro l _ hlk
    have hne : (l : ℕ) ≠ k := fun h => hlk (Fin.ext h)
    have hxl : x ∉ dyadicInterval n l := fun hl =>
      Set.disjoint_left.mp (dyadicInterval_disjoint_same n hne) hl hx
    simp [hxl]
  · simp

theorem dyadic_mesh_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  simpa only [one_div_pow] using
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)

theorem dyadic_cell_left_in_unit (n : ℕ) (k : Fin (2 ^ n)) :
    dyadicEndpoint n k ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨dyadicEndpoint_nonneg n k, ?_⟩
  rw [← dyadicEndpoint_top n]
  exact dyadicEndpoint_mono n k.isLt.le

theorem dyadic_cell_left_distance (n : ℕ) (k : Fin (2 ^ n)) {x : ℝ}
    (hx : x ∈ dyadicInterval n k) : dist x (dyadicEndpoint n k) < 1 / (2 : ℝ) ^ n := by
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
  linarith [hx.2, dyadicEndpoint_length n k]

theorem haar_approximation_norm_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : BoundedContinuousFunction ℝ ℂ) (n : ℕ) {ε δ : ℝ} (hε : 0 ≤ ε) (hmesh : 1 / (2 : ℝ) ^ n < δ)
    (hclose : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      dist x y < δ → dist (g x) (g y) < ε) :
    ‖haarDyadicStep p n (fun k => g (dyadicEndpoint n k)) -
      BoundedContinuousFunction.toLp p haarMeasure ℂ g‖ ≤ ε := by
  have hm : ∀ᵐ x ∂haarMeasure, x ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  have hb : ∀ᵐ x ∂haarMeasure,
      ‖(haarDyadicStep p n (fun k => g (dyadicEndpoint n k)) -
        BoundedContinuousFunction.toLp p haarMeasure ℂ g) x‖ ≤ ε := by
    filter_upwards [hm, haarDyadicStep_ae p n (fun k => g (dyadicEndpoint n k)),
      BoundedContinuousFunction.coeFn_toLp p haarMeasure ℂ g,
      Lp.coeFn_sub (haarDyadicStep p n (fun k => g (dyadicEndpoint n k)))
        (BoundedContinuousFunction.toLp p haarMeasure ℂ g)] with x hxm hstep hg hsub
    obtain ⟨k, hk, hxk⟩ := dyadicInterval_unit_cover n hxm
    let i : Fin (2 ^ n) := ⟨k, hk⟩
    have hxclose := hclose x ⟨hxm.1, hxm.2.le⟩ (dyadicEndpoint n i)
      (dyadic_cell_left_in_unit n i) ((dyadic_cell_left_distance n i hxk).trans hmesh)
    rw [hsub, Pi.sub_apply, hstep, hg, haarDyadicStep_value n _ i hxk, norm_sub_rev]
    exact (by simpa only [dist_eq_norm] using hxclose.le)
  have h := Lp.norm_le_of_ae_bound hε hb
  simpa [measureUnivNNReal] using h

/-- Uniform dyadic approximation of bounded continuous functions gives
ordered norm convergence in every Banach Lᵖ on the unit interval. -/
theorem haar_approximation_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun n : ℕ => haarDyadicStep p n (fun k => g (dyadicEndpoint n k)))
      atTop (𝓝 (BoundedContinuousFunction.toLp p haarMeasure ℂ g)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu : UniformContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous g.continuous.continuousOn
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp dyadic_mesh_tendsto_zero).2 δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact (haar_approximation_norm_bound g n (by positivity) (hN n hn) hclose).trans_lt (by linarith)

end SchauderTranslates.LpConstruction
