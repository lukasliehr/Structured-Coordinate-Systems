import Lean_Code.SchauderTranslates.Lp.BranchElimination

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (hp : 1 < p.toReal) (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n)

include hp hN in
theorem branch_normalized_sum (n : ℕ) :
    (∑ i, (layerPrimalScale p.toReal (N n) : ℂ) • branchAtom p N n i) =
      branchMeanVector p N n + branchResidual p N n := by
  have hc : (layerDualScale p.toReal (N n) : ℂ) *
      (∑ _ : Fin (N n), (layerPrimalScale p.toReal (N n) : ℂ)) = 1 := by
    have hc : (N n : ℂ) * (layerPrimalScale p.toReal (N n) : ℂ) *
        (layerDualScale p.toReal (N n) : ℂ) = 1 := by
      exact_mod_cast layer_scale_product (by linarith : 0 < p.toReal) (hN n)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  rw [branch_synthesis, hc, one_smul]
  congr 1
  apply lp.ext
  funext k
  simp [branchLayer, branchMeanVector, lp.coeFn_sum, lp.coeFn_smul, Finset.mul_sum]

include hp hN in
theorem branch_root_recovery (n : ℕ) :
    branchResidual p N n =
      (1 / 2 : ℂ) • (∑ i, (layerPrimalScale p.toReal (N n) : ℂ) • branchAtom p N n i) +
        (branchRatio p.toReal : ℂ) • branchResidual p N (n + 1) := by
  have hb : (branchBeta p.toReal : ℂ) * (branchRatio p.toReal : ℂ) = 1 / 2 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ))
        (branch_beta_ratio (by linarith : 0 < p.toReal))
  rw [branch_normalized_sum hp N hN]
  apply lp.ext
  funext k
  simp only [branchResidual, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]
  linear_combination -(branchResidual p N n k - branchMeanVector p N n k) * hb

def branchAtomSpan (p : ℝ≥0∞) (N : ℕ → ℕ) : Submodule ℂ (BranchSpace p N) :=
  Submodule.span ℂ (Set.range fun s : Σ n, Fin (N n) => branchAtom p N s.1 s.2)

include hp hN in
theorem branch_recovery_difference_mem (n : ℕ) :
    branchResidual p N n - (branchRatio p.toReal : ℂ) • branchResidual p N (n + 1) ∈
      branchAtomSpan p N := by
  have he : branchResidual p N n - (branchRatio p.toReal : ℂ) • branchResidual p N (n + 1) =
      (1 / 2 : ℂ) • (∑ i, (layerPrimalScale p.toReal (N n) : ℂ) • branchAtom p N n i) := by
    rw [branch_root_recovery hp N hN n]
    abel
  rw [he]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(⟨n, i⟩ : Σ n, Fin (N n)), rfl⟩

include hp hN in
theorem branch_recovery_remainder_mem (n L : ℕ) :
    branchResidual p N n - (branchRatio p.toReal : ℂ) ^ L • branchResidual p N (n + L) ∈
      branchAtomSpan p N := by
  induction L with
  | zero => simp [Submodule.zero_mem]
  | succ L ih =>
    have he : branchResidual p N n -
        (branchRatio p.toReal : ℂ) ^ (L + 1) • branchResidual p N (n + (L + 1)) =
        (branchResidual p N n - (branchRatio p.toReal : ℂ) ^ L • branchResidual p N (n + L)) +
          (branchRatio p.toReal : ℂ) ^ L •
            (branchResidual p N (n + L) -
              (branchRatio p.toReal : ℂ) • branchResidual p N (n + L + 1)) := by
      rw [smul_sub, smul_smul, pow_succ]
      simp only [Nat.add_assoc]
      abel
    rw [he]
    exact Submodule.add_mem _ ih
      (Submodule.smul_mem _ _ (branch_recovery_difference_mem hp N hN (n + L)))

include hp hN in
theorem branch_recovery_remainder_tendsto (n : ℕ) :
    Tendsto (fun L : ℕ => (branchRatio p.toReal : ℂ) ^ L • branchResidual p N (n + L))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (branch_ratio_pos p.toReal).le
    (branch_ratio_lt_one hp)
  simpa [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (branch_ratio_pos _), branchResidual_norm (by linarith : 0 < p.toReal) N hN] using ht

include hp hN in
theorem branchResidual_mem_closure (n : ℕ) :
    branchResidual p N n ∈ (branchAtomSpan p N).topologicalClosure := by
  have ht0 : Tendsto (fun _ : ℕ => branchResidual p N n) atTop
      (𝓝 (branchResidual p N n)) := tendsto_const_nhds
  have ht := ht0.sub (branch_recovery_remainder_tendsto hp N hN n)
  have ht' : Tendsto (fun L : ℕ => branchResidual p N n -
      (branchRatio p.toReal : ℂ) ^ L • branchResidual p N (n + L))
        atTop (𝓝 (branchResidual p N n)) := by simpa using ht
  exact (branchAtomSpan p N).isClosed_topologicalClosure.mem_of_tendsto ht'
    (Eventually.of_forall fun L => (branchAtomSpan p N).le_topologicalClosure
      (branch_recovery_remainder_mem hp N hN n L))

include hp hN in
theorem branchUnit_mem_closure (n : ℕ) (i : Fin (N n)) :
    branchUnit p N n i ∈ (branchAtomSpan p N).topologicalClosure := by
  have he : branchUnit p N n i = branchAtom p N n i -
      layerDualScale p.toReal (N n) • branchResidual p N n := by rw [branchAtom]; abel
  rw [he]
  apply Submodule.sub_mem
  · exact (branchAtomSpan p N).le_topologicalClosure
      (Submodule.subset_span ⟨(⟨n, i⟩ : Σ n, Fin (N n)), rfl⟩)
  · exact (branchAtomSpan p N).topologicalClosure.smul_mem
      (layerDualScale p.toReal (N n)) (branchResidual_mem_closure hp N hN n)

include hp hN in
/-- Blueprint `lp:branch-density`: the closed atom span is the entire actual ℓᵖ branch. -/
theorem branch_dense_span : Dense (branchAtomSpan p N : Set (BranchSpace p N)) := by
  have hpfin : p ≠ ∞ := by intro he; norm_num [he] at hp
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro z _
  have hs (k : BranchIndex N) : lp.single p k (z k) ∈ (branchAtomSpan p N).topologicalClosure := by
    have he : lp.single p k (z k) = z k • (lp.single p k (1 : ℂ) : BranchSpace p N) := by
      rw [← lp.single_smul]; simp
    rw [he]
    apply Submodule.smul_mem
    rcases k with _ | ⟨n, i⟩
    · exact branchResidual_mem_closure hp N hN 0
    · exact branchUnit_mem_closure hp N hN n i
  exact (branchAtomSpan p N).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single hpfin z) (Eventually.of_forall fun s => Submodule.sum_mem _ fun k _ => hs k)

end SchauderTranslates.LpConstruction
