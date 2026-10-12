import Mathlib
import Lean_Code.Basis.Criterion

/-!
# Banach's theorem: unique expansions give a Schauder basis

Textbooks define a Schauder basis of a Banach space `X` as a sequence `(eₙ)` such that every
`x : X` has a *unique* sequence of scalars `(aₙ)` with `x = ∑ₙ aₙ eₙ` (norm convergence of the
ordered partial sums).  Mathlib's `SchauderBasis 𝕜 X` asks in addition for *continuous*
biorthogonal coordinate functionals.  By a theorem of Banach the two notions agree: the
coefficient functionals of a sequence with unique expansions are automatically continuous.

## Main results

* `StructuredBases.exists_schauderBasis_of_existsUnique_expansion`: **Banach's theorem**.
* `StructuredBases.schauderBasis_iff_existsUnique_expansion`: Mathlib's `SchauderBasis` agrees
  with the textbook definition.

## Proof

* `StructuredBases.expansionSpace`: the space of convergent expansions in `e`, realised as the
  subspace of `(ℕ →ᵇ X) × X` of pairs (bounded sequence of partial sums, limit).  Its norm is
  the supremum of the norms of the partial sums, and it is closed
  (`StructuredBases.isClosed_expansionSpace`), hence a Banach space.
* `StructuredBases.exists_partialSum_bound_of_existsUnique_expansion`: the limit map from the
  expansion space to `X` is continuous, linear and (by hypothesis) surjective, so by the open
  mapping theorem the partial sums of the expansion of `x` are bounded by `C * ‖x‖`.
* Consequently the `n`-th coefficient of `x` is bounded by `2 * C / ‖e n‖ * ‖x‖`.  Linearity of
  the coefficients and biorthogonality follow from uniqueness, and
  `StructuredBases.ofCoord` packages everything as a `SchauderBasis`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace StructuredBases

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The space of convergent expansions -/

section ExpansionSpace

variable (𝕜) in
/-- The space of convergent expansions in the sequence `e`: the pairs `(s, x)` such that `s` is
the (bounded) sequence of partial sums `s N = ∑ n < N, a n • e n` of some sequence of scalars `a`
and `s N → x`.  As a subspace of `(ℕ →ᵇ X) × X` it carries the norm `max (sup_N ‖s N‖) ‖x‖`,
which is `sup_N ‖s N‖` since `s N → x`. -/
def expansionSpace (e : ℕ → X) : Submodule 𝕜 ((ℕ →ᵇ X) × X) where
  carrier := {p | p.1 0 = 0 ∧ (∀ n, p.1 (n + 1) - p.1 n ∈ Submodule.span 𝕜 {e n}) ∧
    Tendsto p.1 atTop (𝓝 p.2)}
  add_mem' := by
    rintro p q ⟨hp0, hp1, hp2⟩ ⟨hq0, hq1, hq2⟩
    refine ⟨?_, fun n => ?_, hp2.add hq2⟩
    · simp [hp0, hq0]
    · have hsplit : (p + q).1 (n + 1) - (p + q).1 n =
          (p.1 (n + 1) - p.1 n) + (q.1 (n + 1) - q.1 n) := by
        simp only [Prod.fst_add, BoundedContinuousFunction.add_apply]
        abel
      rw [hsplit]
      exact Submodule.add_mem _ (hp1 n) (hq1 n)
  zero_mem' := ⟨rfl, fun n => by simp, tendsto_const_nhds⟩
  smul_mem' := by
    rintro c p ⟨hp0, hp1, hp2⟩
    refine ⟨?_, fun n => ?_, hp2.const_smul c⟩
    · simp [hp0]
    · have hsplit : (c • p).1 (n + 1) - (c • p).1 n = c • (p.1 (n + 1) - p.1 n) := by
        simp only [Prod.smul_fst, BoundedContinuousFunction.smul_apply, smul_sub]
      rw [hsplit]
      exact Submodule.smul_mem _ _ (hp1 n)

theorem mem_expansionSpace {e : ℕ → X} {p : (ℕ →ᵇ X) × X} :
    p ∈ expansionSpace 𝕜 e ↔
      p.1 0 = 0 ∧ (∀ n, p.1 (n + 1) - p.1 n ∈ Submodule.span 𝕜 {e n}) ∧
        Tendsto p.1 atTop (𝓝 p.2) :=
  Iff.rfl

/-- A convergent expansion defines a point of the expansion space. -/
theorem exists_mem_expansionSpace {e : ℕ → X} {a : ℕ → 𝕜} {x : X}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n • e n) atTop (𝓝 x)) :
    ∃ s : ℕ →ᵇ X, (∀ N, s N = ∑ n ∈ Finset.range N, a n • e n) ∧
      (s, x) ∈ expansionSpace 𝕜 e := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ h)
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete _ C
    (fun N => hC _ (Set.mem_range_self N)), fun N => rfl, ?_, fun n => ?_, h⟩
  · simp
  · simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
      Finset.sum_range_succ, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- Every point of the expansion space comes from a convergent expansion. -/
theorem exists_coeff_of_mem_expansionSpace {e : ℕ → X} {p : (ℕ →ᵇ X) × X}
    (hp : p ∈ expansionSpace 𝕜 e) :
    ∃ a : ℕ → 𝕜, (∀ N, p.1 N = ∑ n ∈ Finset.range N, a n • e n) ∧
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n • e n) atTop (𝓝 p.2) := by
  obtain ⟨h0, h1, h2⟩ := hp
  choose a ha using fun n => Submodule.mem_span_singleton.mp (h1 n)
  have hs : ∀ N, p.1 N = ∑ n ∈ Finset.range N, a n • e n := by
    intro N
    induction N with
    | zero => simpa using h0
    | succ N ih => rw [Finset.sum_range_succ, ← ih, ha N]; abel
  refine ⟨a, hs, ?_⟩
  have hfun : (fun N => ∑ n ∈ Finset.range N, a n • e n) = p.1 := funext fun N => (hs N).symm
  rw [hfun]
  exact h2

/-- The expansion space is closed: it is cut out by closed conditions, the finite-dimensional
subspaces `span {e n}` being closed and uniform limits of convergent sequences being
convergent. -/
theorem isClosed_expansionSpace [CompleteSpace 𝕜] (e : ℕ → X) :
    IsClosed (expansionSpace 𝕜 e : Set ((ℕ →ᵇ X) × X)) := by
  have h1 : IsClosed {p : (ℕ →ᵇ X) × X | p.1 0 = 0} :=
    isClosed_eq ((continuous_eval_const 0).comp continuous_fst) continuous_const
  have h2 : IsClosed (⋂ n : ℕ, {p : (ℕ →ᵇ X) × X |
      p.1 (n + 1) - p.1 n ∈ Submodule.span 𝕜 {e n}}) :=
    isClosed_iInter fun n =>
      (Submodule.closed_of_finiteDimensional (Submodule.span 𝕜 {e n})).preimage
        (((continuous_eval_const (n + 1)).comp continuous_fst).sub
          ((continuous_eval_const n).comp continuous_fst))
  have h3 : IsClosed {p : (ℕ →ᵇ X) × X | Tendsto p.1 atTop (𝓝 p.2)} := by
    refine isClosed_of_closure_subset fun p hp => Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨q, hq, hpq⟩ := Metric.mem_closure_iff.mp hp (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hq (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [Prod.dist_eq] at hpq
    have hfg : dist (p.1 n) (q.1 n) < ε / 3 :=
      (BoundedContinuousFunction.dist_coe_le_dist n).trans_lt ((le_max_left _ _).trans_lt hpq)
    have hxy : dist q.2 p.2 < ε / 3 := by
      rw [dist_comm]
      exact (le_max_right _ _).trans_lt hpq
    calc dist (p.1 n) p.2
        ≤ dist (p.1 n) (q.1 n) + dist (q.1 n) q.2 + dist q.2 p.2 := dist_triangle4 _ _ _ _
      _ < ε := by linarith [hN n hn]
  convert h1.inter (h2.inter h3) using 1
  ext p
  simp [mem_expansionSpace]

end ExpansionSpace

/-! ### Banach's theorem -/

section Banach

/-- A sequence with unique expansions consists of nonzero vectors. -/
theorem ne_zero_of_existsUnique_expansion (e : ℕ → X)
    (h : ∀ x : X, ∃! a : ℕ → 𝕜,
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n • e n) atTop (𝓝 x)) (n : ℕ) :
    e n ≠ 0 := by
  intro hn
  have h1 : Tendsto (fun N => ∑ m ∈ Finset.range N, (Pi.single n (1 : 𝕜) : ℕ → 𝕜) m • e m)
      atTop (𝓝 0) := by
    have hz : ∀ N, ∑ m ∈ Finset.range N, (Pi.single n (1 : 𝕜) : ℕ → 𝕜) m • e m = 0 := by
      intro N
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hm : m = n
      · rw [hm, hn, smul_zero]
      · rw [Pi.single_eq_of_ne hm, zero_smul]
    simp only [hz]
    exact tendsto_const_nhds
  have h0 : Tendsto (fun N => ∑ m ∈ Finset.range N, (0 : ℕ → 𝕜) m • e m) atTop (𝓝 0) := by
    simp
  have h10 := congrFun ((h 0).unique h1 h0) n
  simp at h10

variable [CompleteSpace 𝕜] [CompleteSpace X]

/-- If every vector has a unique convergent expansion in `e`, then the partial sums of the
expansion of `x` are bounded by a constant multiple of `‖x‖`.  This is the open mapping theorem
applied to the limit map from the expansion space onto `X`. -/
theorem exists_partialSum_bound_of_existsUnique_expansion (e : ℕ → X)
    (h : ∀ x : X, ∃! a : ℕ → 𝕜,
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n • e n) atTop (𝓝 x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : X) (a : ℕ → 𝕜),
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n • e n) atTop (𝓝 x) →
        ∀ N, ‖∑ n ∈ Finset.range N, a n • e n‖ ≤ C * ‖x‖ := by
  have : CompleteSpace (expansionSpace 𝕜 e) := (isClosed_expansionSpace e).completeSpace_coe
  -- the limit map `(s, x) ↦ x`
  let L : expansionSpace 𝕜 e →L[𝕜] X :=
    (ContinuousLinearMap.snd 𝕜 (ℕ →ᵇ X) X).comp (expansionSpace 𝕜 e).subtypeL
  have hsurj : Function.Surjective L := by
    intro x
    obtain ⟨a, ha, -⟩ := h x
    obtain ⟨s, -, hs⟩ := exists_mem_expansionSpace ha
    exact ⟨⟨(s, x), hs⟩, rfl⟩
  obtain ⟨C, hC0, hC⟩ := L.exists_preimage_norm_le hsurj
  refine ⟨C, hC0, fun x a ha N => ?_⟩
  -- a preimage `p = (s, x)` of `x` of norm at most `C * ‖x‖`
  obtain ⟨p, hpx, hpC⟩ := hC x
  obtain ⟨a', hs, ha'⟩ := exists_coeff_of_mem_expansionSpace p.2
  have hpx' : (p : (ℕ →ᵇ X) × X).2 = x := hpx
  rw [hpx'] at ha'
  -- by uniqueness, `s` is the sequence of partial sums of the given expansion of `x`
  obtain rfl : a' = a := (h x).unique ha' ha
  rw [← hs N]
  calc ‖(p : (ℕ →ᵇ X) × X).1 N‖ ≤ ‖(p : (ℕ →ᵇ X) × X).1‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ N
    _ ≤ ‖(p : (ℕ →ᵇ X) × X)‖ := norm_fst_le _
    _ ≤ C * ‖x‖ := hpC

/-- **Banach's theorem.** If every vector has a unique norm-convergent ordered expansion in
the sequence `e`, then `e` is the sequence of vectors of a Schauder basis (in Mathlib's sense). -/
theorem exists_schauderBasis_of_existsUnique_expansion (e : ℕ → X)
    (h : ∀ x : X, ∃! a : ℕ → 𝕜,
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n • e n) atTop (𝓝 x)) :
    ∃ b : SchauderBasis 𝕜 X, ⇑b = e := by
  obtain ⟨C, -, hC⟩ := exists_partialSum_bound_of_existsUnique_expansion e h
  have hne : ∀ n, e n ≠ 0 := ne_zero_of_existsUnique_expansion e h
  -- `a x` is the coefficient sequence of `x`
  choose a ha huniq using h
  -- the coefficients depend linearly on the vector, by uniqueness
  have hadd : ∀ x y, a (x + y) = a x + a y := by
    intro x y
    refine (huniq (x + y) (a x + a y) ?_).symm
    simpa only [Pi.add_apply, add_smul, Finset.sum_add_distrib] using (ha x).add (ha y)
  have hsmul : ∀ (k : 𝕜) x, a (k • x) = k • a x := by
    intro k x
    refine (huniq (k • x) (k • a x) ?_).symm
    simpa only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum] using
      (ha x).const_smul k
  -- the coefficients are bounded, by the bound on the partial sums
  have hbound : ∀ n x, ‖a x n‖ ≤ 2 * C / ‖e n‖ * ‖x‖ := by
    intro n x
    have hp : 0 < ‖e n‖ := norm_pos_iff.mpr (hne n)
    have hb : ‖a x n‖ * ‖e n‖ ≤ 2 * C * ‖x‖ := by
      calc ‖a x n‖ * ‖e n‖ = ‖a x n • e n‖ := (norm_smul _ _).symm
        _ = ‖∑ m ∈ Finset.range (n + 1), a x m • e m - ∑ m ∈ Finset.range n, a x m • e m‖ := by
          rw [Finset.sum_range_succ, add_sub_cancel_left]
        _ ≤ ‖∑ m ∈ Finset.range (n + 1), a x m • e m‖ + ‖∑ m ∈ Finset.range n, a x m • e m‖ :=
          norm_sub_le _ _
        _ ≤ C * ‖x‖ + C * ‖x‖ := add_le_add (hC x _ (ha x) _) (hC x _ (ha x) _)
        _ = 2 * C * ‖x‖ := by ring
    calc ‖a x n‖ ≤ 2 * C * ‖x‖ / ‖e n‖ := (le_div_iff₀ hp).mpr hb
      _ = 2 * C / ‖e n‖ * ‖x‖ := by ring
  -- hence they are continuous linear functionals
  let c : ℕ → X →L[𝕜] 𝕜 := fun n =>
    LinearMap.mkContinuous
      { toFun := fun x => a x n
        map_add' := fun x y => by rw [hadd]; rfl
        map_smul' := fun k x => by rw [hsmul]; rfl }
      (2 * C / ‖e n‖) (hbound n)
  -- biorthogonality, by uniqueness of the expansion of `e m`
  have hbi : ∀ n m, c n (e m) = if n = m then 1 else 0 := by
    intro n m
    have hm : Tendsto (fun N => ∑ k ∈ Finset.range N, (Pi.single m (1 : 𝕜) : ℕ → 𝕜) k • e k)
        atTop (𝓝 (e m)) := by
      refine tendsto_atTop_of_eventually_const (i₀ := m + 1) fun N hN => ?_
      rw [Finset.sum_eq_single m]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hmN
        exact absurd (Finset.mem_range.mpr (by omega)) hmN
    have hsingle := congrFun (huniq (e m) _ hm) n
    change a (e m) n = _
    rw [← hsingle, Pi.single_apply]
  exact ⟨ofCoord e c hbi ha, rfl⟩

/-- Mathlib's `SchauderBasis` agrees with the textbook definition. -/
theorem schauderBasis_iff_existsUnique_expansion (e : ℕ → X) :
    (∃ b : SchauderBasis 𝕜 X, ⇑b = e) ↔
      ∀ x : X, ∃! a : ℕ → 𝕜,
        Tendsto (fun N => ∑ n ∈ Finset.range N, a n • e n) atTop (𝓝 x) := by
  constructor
  · rintro ⟨b, rfl⟩ x
    exact existsUnique_expansion b x
  · exact exists_schauderBasis_of_existsUnique_expansion e

end Banach

end StructuredBases
