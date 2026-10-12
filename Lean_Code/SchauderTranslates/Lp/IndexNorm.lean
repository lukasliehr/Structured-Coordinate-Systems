import Lean_Code.SchauderTranslates.Lp.IndexMaps

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem lp_norm_sum_power_disjoint {α ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (s : Finset α) (f : α → lp (fun _ : ι => ℂ) p)
    (hdis : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ i, f a i = 0 ∨ f b i = 0) :
    ‖∑ a ∈ s, f a‖ ^ p.toReal = ∑ a ∈ s, ‖f a‖ ^ p.toReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp.ne']
  | @insert a s ha ih =>
    have hdis' : ∀ i, f a i = 0 ∨ (∑ b ∈ s, f b) i = 0 := by
      intro i
      by_cases hfi : f a i = 0
      · exact Or.inl hfi
      · right
        simp only [lp.coeFn_sum, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro b hb
        have hab : a ≠ b := by intro he; subst b; exact ha hb
        exact (hdis a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) hab i).resolve_left hfi
    have hs := ih (fun b hb c hc hbc =>
      hdis b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc)
    rw [Finset.sum_insert ha, lp_norm_add_power_disjoint hp _ _ hdis', hs, Finset.sum_insert ha]

end SchauderTranslates.LpConstruction
