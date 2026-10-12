import Lean_Code.SchauderTranslates.Lp.CoordinateCriterion

noncomputable section
open Filter
open scoped BigOperators Topology

namespace SchauderTranslates.LpConstruction

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem indexed_coordinate_on_synthesis (u : ι → E) (coord : ι → E →L[ℂ] ℂ)
    (hcoord : ∀ i j, coord i (u j) = if i = j then 1 else 0)
    (c : ι →₀ ℂ) (i : ι) : coord i (Finsupp.linearCombination ℂ u c) = c i := by
  classical
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul, hcoord, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp [Finsupp.sum, Finsupp.mem_support_iff]
  exact fun h => h.symm

/-- A uniform bound over every finite subcollection gives convergence
of the finite-subset net, without changing the ordered public contract. -/
theorem indexed_coordinate_finset_tendsto (u : ι → E) (coord : ι → E →L[ℂ] ℂ)
    (hcoord : ∀ i j, coord i (u j) = if i = j then 1 else 0)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set E))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (s : Finset ι) (x : E), ‖∑ i ∈ s, coord i x • u i‖ ≤ K * ‖x‖)
    (x : E) : Tendsto (fun s : Finset ι => ∑ i ∈ s, coord i x • u i) atTop (𝓝 x) := by
  classical
  have hd' : DenseRange (Finsupp.linearCombination ℂ u) := by
    change Dense (LinearMap.range (Finsupp.linearCombination ℂ u) : Set E)
    rwa [Finsupp.range_linearCombination]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp : 0 < K + 1 := by linarith
  obtain ⟨c, hc⟩ := hd'.exists_dist_lt x (div_pos hε hp)
  let y := Finsupp.linearCombination ℂ u c
  refine ⟨c.support, fun s hs => ?_⟩
  have hfix : ∑ i ∈ s, coord i y • u i = y := by
    simp only [y, indexed_coordinate_on_synthesis u coord hcoord]
    rw [Finsupp.linearCombination_apply]
    exact (c.sum_of_support_subset hs (fun i a => a • u i) (by simp)).symm
  let T : E →L[ℂ] E := ∑ i ∈ s, (coord i).smulRight (u i)
  have hT (z : E) : T z = ∑ i ∈ s, coord i z • u i := by simp [T]
  rw [dist_eq_norm] at hc ⊢
  calc
    ‖∑ i ∈ s, coord i x • u i - x‖ = ‖T (x - y) + (y - x)‖ := by
      rw [map_sub, hT, hT, hfix]
      congr 1
      abel
    _ ≤ ‖T (x - y)‖ + ‖y - x‖ := norm_add_le _ _
    _ ≤ K * ‖x - y‖ + ‖x - y‖ := by
      rw [hT, norm_sub_rev y x]
      exact add_le_add (hK s (x - y)) le_rfl
    _ = (K + 1) * ‖x - y‖ := by ring
    _ < ε := by
      have hc' : ‖x - y‖ < ε / (K + 1) := hc
      exact (mul_lt_mul_of_pos_left hc' hp).trans_eq (by field_simp)

end SchauderTranslates.LpConstruction
