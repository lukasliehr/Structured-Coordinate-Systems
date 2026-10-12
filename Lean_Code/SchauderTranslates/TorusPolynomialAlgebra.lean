import Lean_Code.SchauderTranslates.TorusPolynomial

noncomputable section
namespace SchauderTranslates
variable {d : ℕ}

theorem IsTorusPolynomial.const (a : ℂ) : IsTorusPolynomial (fun _ : UnitAddTorus (Fin d) => a) := by
  classical
  refine ⟨{0}, fun _ => a, ?_⟩
  intro x
  simp [UnitAddTorus.mFourier_zero]

theorem IsTorusPolynomial.const_mul {f : UnitAddTorus (Fin d) → ℂ}
    (hf : IsTorusPolynomial f) (a : ℂ) : IsTorusPolynomial (fun x => a * f x) := by
  obtain ⟨K, c, hc⟩ := hf
  refine ⟨K, fun k => a * c k, ?_⟩
  intro x
  simp_rw [hc, Finset.mul_sum, mul_assoc]

theorem IsTorusPolynomial.add {f g : UnitAddTorus (Fin d) → ℂ}
    (hf : IsTorusPolynomial f) (hg : IsTorusPolynomial g) : IsTorusPolynomial (fun x => f x + g x) := by
  classical
  obtain ⟨K, a, ha⟩ := hf
  obtain ⟨L, b, hb⟩ := hg
  refine ⟨K ∪ L, fun k => (if k ∈ K then a k else 0) + (if k ∈ L then b k else 0), ?_⟩
  intro x
  change f x + g x = _
  rw [ha, hb]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  · rw [← Finset.sum_subset (Finset.subset_union_left : K ⊆ K ∪ L)
      (fun k _ hk => by simp [hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [hk]
  · rw [← Finset.sum_subset (Finset.subset_union_right : L ⊆ K ∪ L)
      (fun k _ hk => by simp [hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [hk]

end SchauderTranslates
