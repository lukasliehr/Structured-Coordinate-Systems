import Lean_Code.PositiveTranslates.Global.Roots

/-!
# The prefix inequality for the roots

Cell by cell, a global prefix `∑_{j<m} t j • rootVec j` is a local prefix of the local
combination: its part in the cell `c` is the local prefix operator of `β c` applied to the
part of the full combination.  Since the `p`-th powers of the norms add over the disjoint
cells, the roots satisfy the prefix inequality with the same constant as the local bases.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpfin : p ≠ ∞) {A : ℕ → Set ℝ}
  (hA : ∀ c, MeasurableSet (A c)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
  {β : ℕ → ℕ → LebesgueLp p} {B : ℝ} (hβ : ∀ c, LocalBasis p (β c) (A c) B)
  (isCoord : ℕ → Bool)

theorem rootIndex_lt_rootCount_iff (j m : ℕ) :
    rootIndex isCoord (Nat.unpair j).1 (Nat.unpair j).2 <
      rootIndex isCoord (Nat.unpair j).1 (rootCount (Nat.unpair j).1 m) ↔ j < m := by
  rw [rootIndex_lt_rootIndex_iff, lt_rootCount_iff, Nat.pair_unpair]

include hdis hβ in
/-- The cell part of a root: the root itself in its own cell, zero in all others. -/
theorem lpCellProjection_rootVec (c j : ℕ) :
    lpCellProjection p volume (A c) (hA c) (rootVec β isCoord j) =
      if (Nat.unpair j).1 = c then rootVec β isCoord j else 0 := by
  by_cases h : (Nat.unpair j).1 = c
  · rw [if_pos h]
    subst h
    exact lpCellProjection_eq_of_supported p volume _ _ _ (rootVec_supported hβ isCoord j)
  · rw [if_neg h]
    exact lpCellProjection_eq_zero_of_supported (hA c) _ (rootVec_supported hβ isCoord j)
      (hdis h)

include hdis in
/-- The local prefix operator of the cell `c` on a root. -/
theorem coordPrefix_rootVec (c N j : ℕ) :
    coordPrefix (β c) ((hβ c).wholeCoord (hA c)) N (rootVec β isCoord j) =
      if (Nat.unpair j).1 = c ∧ rootIndex isCoord c (Nat.unpair j).2 < N then
        rootVec β isCoord j else 0 := by
  rw [coordPrefix_apply]
  by_cases h : (Nat.unpair j).1 = c
  · subst h
    rw [rootVec_eq_rootIndex, ((hβ _).wholeCoord_spec (hA _)).prefix_basis]
    simp
  · rw [if_neg (fun h' => h h'.1)]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [((hβ c).wholeCoord_spec (hA c)).apply_of_disjoint n (rootVec_supported hβ isCoord j) (hdis h),
      zero_smul]

include hdis in
/-- The local prefix operator cut at the number of roots of the cell among the first `m`
roots keeps exactly the roots of the cell with index below `m`. -/
theorem coordPrefix_rootCount_rootVec (c m j : ℕ) :
    coordPrefix (β c) ((hβ c).wholeCoord (hA c)) (rootIndex isCoord c (rootCount c m))
        (rootVec β isCoord j) =
      if (Nat.unpair j).1 = c ∧ j < m then rootVec β isCoord j else 0 := by
  rw [coordPrefix_rootVec hA hdis hβ isCoord]
  by_cases h : (Nat.unpair j).1 = c
  · subst h
    simp only [rootIndex_lt_rootCount_iff]
  · rw [if_neg (fun h' => h h'.1), if_neg (fun h' => h h'.1)]

include hdis in
/-- **Cell by cell the global prefix is a local prefix of the local combination.** -/
theorem lpCellProjection_rootPrefix (c m : ℕ) (t : ℕ →₀ ℂ) :
    lpCellProjection p volume (A c) (hA c) (∑ j ∈ Finset.range m, t j • rootVec β isCoord j) =
      coordPrefix (β c) ((hβ c).wholeCoord (hA c)) (rootIndex isCoord c (rootCount c m))
        (Finsupp.linearCombination ℂ (rootVec β isCoord) t) := by
  have key : (lpCellProjection p volume (A c) (hA c)).toLinearMap ∘ₗ
        finitePrefix (rootVec β isCoord) m =
      (coordPrefix (β c) ((hβ c).wholeCoord (hA c))
        (rootIndex isCoord c (rootCount c m))).toLinearMap ∘ₗ
        Finsupp.linearCombination ℂ (rootVec β isCoord) := by
    apply Finsupp.lhom_ext
    intro j a
    have hsum : ∑ n ∈ Finset.range m, (Finsupp.single j a) n • rootVec β isCoord n =
        if j < m then a • rootVec β isCoord j else 0 := by
      simp only [Finsupp.single_apply, ite_smul, zero_smul]
      rw [Finset.sum_ite_eq (Finset.range m) j (fun n => a • rootVec β isCoord n)]
      simp only [Finset.mem_range]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, finitePrefix_apply,
      Finsupp.linearCombination_single, map_smul, hsum]
    rw [coordPrefix_rootCount_rootVec hA hdis hβ isCoord]
    by_cases hm : j < m
    · rw [if_pos hm, map_smul, lpCellProjection_rootVec hA hdis hβ isCoord]
      by_cases hc : (Nat.unpair j).1 = c
      · rw [if_pos hc, if_pos ⟨hc, hm⟩]
      · rw [if_neg hc, if_neg (fun h' => hc h'.1)]
    · rw [if_neg hm, map_zero, if_neg (fun h' => hm h'.2), smul_zero]
  have h := LinearMap.congr_fun key t
  simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, finitePrefix_apply] using h

include hpfin hA hdis hβ in
/-- **The prefix inequality for the roots**, with the constant of the local bases. -/
theorem rootVec_prefix_le (hcover : volume (⋃ c, A c)ᶜ = 0) (m : ℕ) (t : ℕ →₀ ℂ) :
    ‖∑ j ∈ Finset.range m, t j • rootVec β isCoord j‖ ≤
      B * ‖Finsupp.linearCombination ℂ (rootVec β isCoord) t‖ := by
  have hB : 0 ≤ B := (hβ 0).const_nonneg
  have hpR := lpExponent_toReal_pos p hpfin
  have hcell : ∀ c, ‖lpCellProjection p volume (A c) (hA c)
        (∑ j ∈ Finset.range m, t j • rootVec β isCoord j)‖ ≤
      B * ‖lpCellProjection p volume (A c) (hA c)
        (Finsupp.linearCombination ℂ (rootVec β isCoord) t)‖ := by
    intro c
    rw [lpCellProjection_rootPrefix hA hdis hβ isCoord c m t, coordPrefix_apply]
    exact ((hβ c).wholeCoord_spec (hA c)).prefix_le _ _
  have h1 := lpCellProjection_norm_rpow_hasSum hA hdis hpfin hcover
    (∑ j ∈ Finset.range m, t j • rootVec β isCoord j)
  have h2 := (lpCellProjection_norm_rpow_hasSum hA hdis hpfin hcover
    (Finsupp.linearCombination ℂ (rootVec β isCoord) t)).mul_left (B ^ p.toReal)
  have hle : ‖∑ j ∈ Finset.range m, t j • rootVec β isCoord j‖ ^ p.toReal ≤
      B ^ p.toReal * ‖Finsupp.linearCombination ℂ (rootVec β isCoord) t‖ ^ p.toReal := by
    refine hasSum_le (fun c => ?_) h1 h2
    rw [← Real.mul_rpow hB (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hcell c) hpR.le
  rw [← Real.mul_rpow hB (norm_nonneg _)] at hle
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hB (norm_nonneg _)) hpR).mp hle

end StructuredBases.PositiveTranslates
