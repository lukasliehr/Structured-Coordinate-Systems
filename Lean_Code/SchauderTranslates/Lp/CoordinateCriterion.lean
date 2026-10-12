import Lean_Code.SchauderTranslates.SchauderCriterion

noncomputable section
open scoped BigOperators

namespace SchauderTranslates.LpConstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem coordinate_on_synthesis (u : ℕ → E) (coord : ℕ → E →L[ℂ] ℂ)
    (hcoord : ∀ n m, coord n (u m) = if n = m then 1 else 0)
    (c : ℕ →₀ ℂ) (n : ℕ) : coord n (Finsupp.linearCombination ℂ u c) = c n := by
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul, hcoord, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp [Finsupp.sum, Finsupp.mem_support_iff]
  exact fun h => h.symm

/-- Reuse the existing finite-prefix criterion when continuous biorthogonal
coordinates and their global prefix bounds are already available. -/
theorem schauder_of_bounded_coordinate_prefix [CompleteSpace E]
    (u : ℕ → E) (coord : ℕ → E →L[ℂ] ℂ)
    (hcoord : ∀ n m, coord n (u m) = if n = m then 1 else 0)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set E))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ m x, ‖∑ n ∈ Finset.range m, coord n x • u n‖ ≤ K * ‖x‖) :
    Construction.OrderedSchauderBasis u := by
  refine schauder_of_prefix_dense u ?_ ?_ hK0 ?_
  · intro n he
    have h := hcoord n n
    simp [he] at h
  · change Dense (LinearMap.range (Finsupp.linearCombination ℂ u) : Set E)
    rwa [Finsupp.range_linearCombination]
  · intro m c
    have hb := hK m (Finsupp.linearCombination ℂ u c)
    simpa only [finitePrefix_apply, coordinate_on_synthesis u coord hcoord] using hb

end SchauderTranslates.LpConstruction
