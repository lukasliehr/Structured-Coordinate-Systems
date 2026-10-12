import Lean_Code.SchauderTranslates.Contracts

noncomputable section
open Filter
open scoped BigOperators Topology

namespace SchauderTranslates
open Construction

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The initial N coordinates synthesized from a finitely supported family. -/
def finitePrefix (u : ℕ → H) (N : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] H :=
  ∑ n ∈ Finset.range N, (Finsupp.lapply n).smulRight (u n)

@[simp] theorem finitePrefix_apply (u : ℕ → H) (N : ℕ) (c : ℕ →₀ ℂ) :
    finitePrefix u N c = ∑ n ∈ Finset.range N, c n • u n := by
  simp [finitePrefix]

theorem finitePrefix_succ (u : ℕ → H) (n : ℕ) (c : ℕ →₀ ℂ) :
    finitePrefix u (n + 1) c - finitePrefix u n c = c n • u n := by
  simp [Finset.sum_range_succ]

theorem finitePrefix_eventually (u : ℕ → H) (c : ℕ →₀ ℂ) :
    ∀ᶠ N : ℕ in atTop,
      finitePrefix u N c = Finsupp.linearCombination ℂ u c := by
  filter_upwards [eventually_ge_atTop (c.support.sup id + 1)] with N hN
  rw [finitePrefix_apply, Finsupp.linearCombination_apply]
  symm
  apply c.sum_of_support_subset
  · intro n hn
    apply Finset.mem_range.mpr
    have hn' : n ≤ c.support.sup id := Finset.le_sup (f := id) hn
    omega
  · intro n hn
    simp

/-- Bound each individual coordinate by two adjacent prefix bounds. -/
theorem coefficient_bound_of_prefix
    (u : ℕ → H) {K : ℝ}
    (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖)
    (n : ℕ) (hn : u n ≠ 0) (c : ℕ →₀ ℂ) :
    ‖c n‖ ≤ (2 * K / ‖u n‖) * ‖Finsupp.linearCombination ℂ u c‖ := by
  have hb : ‖c n‖ * ‖u n‖ ≤ 2 * K * ‖Finsupp.linearCombination ℂ u c‖ := by
    calc
      ‖c n‖ * ‖u n‖ = ‖c n • u n‖ := (norm_smul _ _).symm
      _ = ‖finitePrefix u (n + 1) c - finitePrefix u n c‖ := by
        rw [finitePrefix_succ]
      _ ≤ ‖finitePrefix u (n + 1) c‖ + ‖finitePrefix u n c‖ := norm_sub_le _ _
      _ ≤ K * ‖Finsupp.linearCombination ℂ u c‖ +
          K * ‖Finsupp.linearCombination ℂ u c‖ := add_le_add (hK _ _) (hK _ _)
      _ = 2 * K * ‖Finsupp.linearCombination ℂ u c‖ := by ring
  have hp : 0 < ‖u n‖ := norm_pos_iff.mpr hn
  calc
    ‖c n‖ ≤ (2 * K * ‖Finsupp.linearCombination ℂ u c‖) / ‖u n‖ :=
      (le_div_iff₀ hp).mpr hb
    _ = (2 * K / ‖u n‖) * ‖Finsupp.linearCombination ℂ u c‖ := by ring

/-- Continuous biorthogonal coefficients and ordered convergence give uniqueness. -/
theorem schauder_of_continuous_coordinates
    (u : ℕ → H) (coord : ℕ → H →L[ℂ] ℂ)
    (hcoord : ∀ n m, coord n (u m) = if n = m then 1 else 0)
    (hconv : ∀ f : H,
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, coord n f • u n) atTop (𝓝 f)) :
    OrderedSchauderBasis u := by
  intro f
  refine ⟨fun n => coord n f, hconv f, ?_⟩
  intro c hc
  funext n
  have ht := (coord n).continuous.continuousAt.tendsto.comp hc
  have he : ∀ᶠ N : ℕ in atTop,
      coord n (∑ m ∈ Finset.range N, c m • u m) = c n := by
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [map_sum, map_smul, hcoord, Finset.mem_range.mpr hN]
  apply tendsto_nhds_unique ?_ ht
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => c n) atTop (𝓝 (c n))).congr'
  filter_upwards [he] with N hN using hN.symm

section Complete
variable [CompleteSpace H]

/-- Extensions of finite coordinate prefixes to the ambient Banach space. -/
def extendedPrefix (u : ℕ → H) (N : ℕ) : H →L[ℂ] H :=
  (finitePrefix u N).extendOfNorm (Finsupp.linearCombination ℂ u)

def extendedCoordinate (u : ℕ → H) (n : ℕ) : H →L[ℂ] ℂ :=
  (Finsupp.lapply n : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ).extendOfNorm (Finsupp.linearCombination ℂ u)

theorem extendedPrefix_on_synthesis
    (u : ℕ → H) (hd : DenseRange (Finsupp.linearCombination ℂ u))
    {K : ℝ} (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖)
    (N : ℕ) (c : ℕ →₀ ℂ) :
    extendedPrefix u N (Finsupp.linearCombination ℂ u c) = finitePrefix u N c :=
  LinearMap.extendOfNorm_eq hd ⟨K, hK N⟩ c

omit [CompleteSpace H] in
theorem extendedCoordinate_on_synthesis
    (u : ℕ → H) (hd : DenseRange (Finsupp.linearCombination ℂ u))
    {K : ℝ} (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖)
    (n : ℕ) (hn : u n ≠ 0) (c : ℕ →₀ ℂ) :
    extendedCoordinate u n (Finsupp.linearCombination ℂ u c) = c n :=
  LinearMap.extendOfNorm_eq hd
    ⟨2 * K / ‖u n‖, coefficient_bound_of_prefix u hK n hn⟩ c

omit [CompleteSpace H] in
theorem extendedCoordinate_on_atom
    (u : ℕ → H) (hd : DenseRange (Finsupp.linearCombination ℂ u))
    {K : ℝ} (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖)
    (n : ℕ) (hn : u n ≠ 0) (m : ℕ) :
    extendedCoordinate u n (u m) = if n = m then 1 else 0 := by
  simpa [Finsupp.single_apply, eq_comm] using
    extendedCoordinate_on_synthesis u hd hK n hn (Finsupp.single m 1)

theorem extendedPrefix_eq_sum
    (u : ℕ → H) (hn : ∀ n, u n ≠ 0)
    (hd : DenseRange (Finsupp.linearCombination ℂ u))
    {K : ℝ} (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖)
    (N : ℕ) (f : H) :
    extendedPrefix u N f = ∑ n ∈ Finset.range N, extendedCoordinate u n f • u n := by
  have hc : IsClosed {x : H | extendedPrefix u N x =
      ∑ n ∈ Finset.range N, extendedCoordinate u n x • u n} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  refine hd.induction_on f hc ?_
  intro c
  rw [extendedPrefix_on_synthesis u hd hK]
  simp [extendedCoordinate_on_synthesis u hd hK _ (hn _)]

theorem extendedPrefix_tendsto
    (u : ℕ → H) (hd : DenseRange (Finsupp.linearCombination ℂ u))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖)
    (f : H) : Tendsto (fun N => extendedPrefix u N f) atTop (𝓝 f) := by
  have hb (N : ℕ) (x : H) : ‖extendedPrefix u N x‖ ≤ K * ‖x‖ :=
    LinearMap.norm_extendOfNorm_apply_le hd K (hK N) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp : 0 < K + 1 := by linarith
  obtain ⟨c, hc⟩ := hd.exists_dist_lt f (div_pos hε hp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (finitePrefix_eventually u c)
  refine ⟨N, fun n hn => ?_⟩
  have hfix : extendedPrefix u n (Finsupp.linearCombination ℂ u c) =
      Finsupp.linearCombination ℂ u c := by
    rw [extendedPrefix_on_synthesis u hd hK, hN n hn]
  rw [dist_eq_norm] at hc ⊢
  calc
    ‖extendedPrefix u n f - f‖ =
        ‖extendedPrefix u n (f - Finsupp.linearCombination ℂ u c) +
          (Finsupp.linearCombination ℂ u c - f)‖ := by rw [map_sub, hfix]; congr 1; abel
    _ ≤ ‖extendedPrefix u n (f - Finsupp.linearCombination ℂ u c)‖ +
        ‖Finsupp.linearCombination ℂ u c - f‖ := norm_add_le _ _
    _ ≤ K * ‖f - Finsupp.linearCombination ℂ u c‖ +
        ‖f - Finsupp.linearCombination ℂ u c‖ := by
      rw [norm_sub_rev (Finsupp.linearCombination ℂ u c) f]
      exact add_le_add (hb _ _) le_rfl
    _ = (K + 1) * ‖f - Finsupp.linearCombination ℂ u c‖ := by ring
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hp).mp hc

/-- Finite-prefix criterion, in the equivalent dense-synthesis formulation.
Independence is implied by the prefix bounds and nonzero atoms. -/
theorem schauder_of_prefix_dense
    (u : ℕ → H) (hn : ∀ n, u n ≠ 0)
    (hd : DenseRange (Finsupp.linearCombination ℂ u))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖) :
    OrderedSchauderBasis u := by
  apply schauder_of_continuous_coordinates u (extendedCoordinate u)
  · exact fun n m => extendedCoordinate_on_atom u hd hK n (hn n) m
  · intro f
    simpa only [extendedPrefix_eq_sum u hn hd hK] using
      extendedPrefix_tendsto u hd hK0 hK f

/-- The customary formulation using independence and a dense linear span. -/
theorem schauder_of_independent_dense_span
    (u : ℕ → H) (hi : LinearIndependent ℂ u)
    (hd : Dense (↑(Submodule.span ℂ (Set.range u)) : Set H))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ N c, ‖finitePrefix u N c‖ ≤ K * ‖Finsupp.linearCombination ℂ u c‖) :
    OrderedSchauderBasis u := by
  apply schauder_of_prefix_dense u (fun n => LinearIndependent.ne_zero n hi) ?_ hK0 hK
  change Dense (↑(LinearMap.range (Finsupp.linearCombination ℂ u)) : Set H)
  rwa [Finsupp.range_linearCombination]

end Complete
end SchauderTranslates
