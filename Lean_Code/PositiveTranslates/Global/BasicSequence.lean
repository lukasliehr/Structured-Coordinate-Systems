import Lean_Code.Basis.Criterion

/-!
# Basic sequences

A sequence of nonzero vectors satisfying the finite prefix inequality is a Schauder basis
of its closed linear span.  We record the consequence in the form used by the global
splitting: continuous coordinate functionals on the closed span, biorthogonal to the
sequence, with uniformly bounded and strongly convergent partial sums.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace StructuredBases

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **Basic sequence criterion.** Nonzero vectors whose finite prefixes are bounded by `C`
times the full finite combination form a Schauder basis of their closed linear span, all of
whose partial sum projections have norm at most `C`. -/
theorem exists_schauderBasis_closedSpan_of_prefix_bound (e : ℕ → X) (hn : ∀ n, e n ≠ 0) {C : ℝ}
    (hC : ∀ (N : ℕ) (a : ℕ →₀ 𝕜),
      ‖∑ n ∈ Finset.range N, a n • e n‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖) :
    ∃ b : SchauderBasis 𝕜 (Submodule.span 𝕜 (Set.range e)).topologicalClosure,
      (∀ n, (b n : X) = e n) ∧ ∀ N, ‖b.proj N‖ ≤ C := by
  classical
  set S : Submodule 𝕜 X := (Submodule.span 𝕜 (Set.range e)).topologicalClosure with hS
  have hmem : ∀ n, e n ∈ S := fun n =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  let e' : ℕ → S := fun n => ⟨e n, hmem n⟩
  have hn' : ∀ n, e' n ≠ 0 := fun n h => hn n (congrArg Subtype.val h)
  have hcoe : ∀ a : ℕ →₀ 𝕜,
      ((Finsupp.linearCombination 𝕜 e' a : S) : X) = Finsupp.linearCombination 𝕜 e a := by
    intro a
    have h := Finsupp.apply_linearCombination 𝕜 S.subtype e' a
    simpa [Function.comp_def, e'] using h
  have hd : Dense (Submodule.span 𝕜 (Set.range e') : Set S) := by
    intro x
    rw [closure_subtype]
    have himg : Subtype.val '' (Submodule.span 𝕜 (Set.range e') : Set S) =
        (Submodule.span 𝕜 (Set.range e) : Set X) := by
      have h := Submodule.map_span S.subtype (Set.range e')
      have hr : S.subtype '' Set.range e' = Set.range e := by
        rw [← Set.range_comp]
        rfl
      rw [hr] at h
      rw [← h]
      rfl
    rw [himg]
    exact x.2
  have hC' : ∀ (N : ℕ) (a : ℕ →₀ 𝕜),
      ‖∑ n ∈ Finset.range N, a n • e' n‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e' a‖ := by
    intro N a
    have h1 : ((∑ n ∈ Finset.range N, a n • e' n : S) : X) =
        ∑ n ∈ Finset.range N, a n • e n := by
      rw [Submodule.coe_sum]
      rfl
    rw [Submodule.coe_norm, Submodule.coe_norm, h1, hcoe a]
    exact hC N a
  obtain ⟨b, hb, hproj⟩ := exists_schauderBasis_of_prefix_bound e' hn' hd hC'
  exact ⟨b, fun n => by rw [hb], hproj⟩

/-- Coordinate functionals of a basic sequence on its closed span: biorthogonality, the
uniform bound on partial sums and their strong convergence. -/
theorem exists_coord_closedSpan_of_prefix_bound (e : ℕ → X) (hn : ∀ n, e n ≠ 0) {C : ℝ}
    (hC : ∀ (N : ℕ) (a : ℕ →₀ 𝕜),
      ‖∑ n ∈ Finset.range N, a n • e n‖ ≤ C * ‖Finsupp.linearCombination 𝕜 e a‖) :
    ∃ φ : ℕ → (Submodule.span 𝕜 (Set.range e)).topologicalClosure →L[𝕜] 𝕜,
      (∀ (n m : ℕ) (x : (Submodule.span 𝕜 (Set.range e)).topologicalClosure),
        (x : X) = e m → φ n x = if n = m then 1 else 0) ∧
      (∀ (N : ℕ) (x : (Submodule.span 𝕜 (Set.range e)).topologicalClosure),
        ‖∑ n ∈ Finset.range N, φ n x • e n‖ ≤ C * ‖x‖) ∧
      (∀ x : (Submodule.span 𝕜 (Set.range e)).topologicalClosure,
        Tendsto (fun N => ∑ n ∈ Finset.range N, φ n x • e n) atTop (𝓝 (x : X))) := by
  obtain ⟨b, hb, hproj⟩ := exists_schauderBasis_closedSpan_of_prefix_bound e hn hC
  have hsum : ∀ (N : ℕ) (x : (Submodule.span 𝕜 (Set.range e)).topologicalClosure),
      ((b.proj N x : (Submodule.span 𝕜 (Set.range e)).topologicalClosure) : X) =
        ∑ n ∈ Finset.range N, b.coord n x • e n := by
    intro N x
    rw [SchauderBasis.proj_apply]
    simp [hb]
  refine ⟨b.coord, ?_, ?_, ?_⟩
  · intro n m x hx
    have hxm : x = b m := Subtype.ext (by rw [hx, hb])
    rw [hxm, coord_apply_basis]
  · intro N x
    rw [← hsum N x, ← Submodule.coe_norm]
    refine ((b.proj N).le_opNorm x).trans ?_
    exact mul_le_mul_of_nonneg_right (hproj N) (norm_nonneg x)
  · intro x
    have h := (continuous_subtype_val.tendsto x).comp (b.tendsto_proj x)
    refine h.congr fun N => ?_
    exact hsum N x

end StructuredBases
