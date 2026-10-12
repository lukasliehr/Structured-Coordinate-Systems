import Lean_Code.PositiveBiorthogonal.DisjointOperators

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} [Countable ι]

theorem ae_disjoint_sum (s : Finset ι) (A : ι → Set ℝ)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (f : ι → L 𝕜 p)
    (hf : ∀ i, ∀ᵐ x : ℝ, x ∉ A i → f i x = 0) (a : ι) (ha : a ∉ s) :
    ∀ᵐ x : ℝ, f a x = 0 ∨ (∑ i ∈ s, f i) x = 0 := by
  classical
  filter_upwards [hf a, (ae_all_iff.mpr hf), Lp.coeFn_fun_finsetSum s f] with x hx hall hsum
  by_cases hxa : x ∈ A a
  · right
    rw [hsum]
    apply Finset.sum_eq_zero
    intro i hi
    have hai : a ≠ i := fun he => ha (he.symm ▸ hi)
    exact hall i (fun hxi => Set.disjoint_left.mp (hA hai) hxa hxi)
  · exact Or.inl (hx hxa)

theorem norm_rpow_sum_of_disjoint (hpfin : p ≠ ∞) (s : Finset ι) (A : ι → Set ℝ)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (f : ι → L 𝕜 p)
    (hf : ∀ i, ∀ᵐ x : ℝ, x ∉ A i → f i x = 0) :
    ‖∑ i ∈ s, f i‖ ^ p.toReal = ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  classical
  induction s using Finset.induction with
  | empty => simp [Real.zero_rpow (p.toReal_pos_iff_ne_top.mpr hpfin).ne']
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      norm_rpow_add_of_ae_disjoint hpfin _ _ (ae_disjoint_sum s A hA f hf a ha), ih]

theorem norm_top_sum_of_disjoint_le (s : Finset ι) (A : ι → Set ℝ)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (f : ι → L 𝕜 ∞)
    (hf : ∀ i, ∀ᵐ x : ℝ, x ∉ A i → f i x = 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hC
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (norm_top_add_le_max_of_ae_disjoint _ _ (ae_disjoint_sum s A hA f hf a ha)).trans
      (max_le (hbound a) ih)

end PositiveBiorthogonal
