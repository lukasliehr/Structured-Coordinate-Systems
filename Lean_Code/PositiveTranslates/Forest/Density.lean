import Lean_Code.PositiveTranslates.Forest.Synthesis

/-!
# Completeness of the sequence of a positive forest

The identity `h_s = ½ ∑ᵢ (N s)^{-1/r} x_{s,i} - ½ u_s` and `u_s = h_{succStage s}` give

`h_s - (-1/2)^L h_{succStage^[L] s} ∈ span (range seq)` for every `L`

(`target_sub_pow_smul_mem_span`). Since all targets are unit vectors, every target lies in
the closed span of the sequence; hence so do all coordinates
`coord s i = x_{s,i} - 2 (N s)^{-(r-1)/r} h_s` and all roots `root j = h_{(j,0)}`, and the
closed span is everything because `Z = range PY ⊕ ker PY` (`dense_span_seq`).

We also show that no vector of the sequence vanishes (`seq_ne_zero`).
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates.PositiveForest

open Forest

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {r : ℝ} (F : PositiveForest Z r)

theorem e0_mem_span : F.e0 ∈ Submodule.span ℂ (Set.range F.seq) :=
  Submodule.subset_span ⟨0, F.seq_zero⟩

theorem atom_mem_span (s : ℕ) (i : Fin (F.N s)) :
    F.atom s i ∈ Submodule.span ℂ (Set.range F.seq) :=
  Submodule.subset_span ⟨_, F.seq_offset_add s i⟩

/-- The normalized sum of the atoms of a stage: `∑ᵢ (N s)^{-1/r} x_{s,i} = u_s + 2 h_s`. -/
theorem sum_primalScale_smul_atom (hr : 0 < r) (s : ℕ) :
    ∑ i, (primalScale r (F.N s) : ℂ) • F.atom s i = F.avg s + (2 : ℂ) • F.target s := by
  have h := F.sum_smul_atom s (blockUnit r (F.N s))
  rw [blockMean_blockUnit hr (F.N_pos' s), mul_one, ← avg_eq_blk] at h
  exact h

/-- `h_s + ½ h_{succStage s}` is a combination of the atoms of stage `s`. -/
theorem target_add_half_smul_mem_span (hr : 0 < r) (s : ℕ) :
    F.target s + (1 / 2 : ℂ) • F.target (succStage s) ∈ Submodule.span ℂ (Set.range F.seq) := by
  have h : F.target s + (1 / 2 : ℂ) • F.target (succStage s) =
      (1 / 2 : ℂ) • ∑ i, (primalScale r (F.N s) : ℂ) • F.atom s i := by
    rw [F.sum_primalScale_smul_atom hr, target_succStage]
    module
  rw [h]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (F.atom_mem_span s i))

/-- Iterating `h_s ≡ -½ h_{succStage s}` modulo the span of the sequence. -/
theorem target_sub_pow_smul_mem_span (hr : 0 < r) (L s : ℕ) :
    F.target s - (-1 / 2 : ℂ) ^ L • F.target (succStage^[L] s) ∈
      Submodule.span ℂ (Set.range F.seq) := by
  induction L generalizing s with
  | zero => simp
  | succ L ih =>
    have e : F.target s - (-1 / 2 : ℂ) ^ (L + 1) • F.target (succStage^[L + 1] s) =
        (F.target s + (1 / 2 : ℂ) • F.target (succStage s)) +
          (-1 / 2 : ℂ) • (F.target (succStage s) -
            (-1 / 2 : ℂ) ^ L • F.target (succStage^[L] (succStage s))) := by
      rw [Function.iterate_succ_apply, pow_succ]
      module
    rw [e]
    exact Submodule.add_mem _ (F.target_add_half_smul_mem_span hr s)
      (Submodule.smul_mem _ _ (ih (succStage s)))

/-- Every target lies in the closed span of the sequence. -/
theorem target_mem_closure_span (hr : 0 < r) (s : ℕ) :
    F.target s ∈ (Submodule.span ℂ (Set.range F.seq)).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨_, F.target_sub_pow_smul_mem_span hr L s, ?_⟩
  rw [dist_eq_norm, sub_sub_cancel, norm_smul, norm_pow, F.norm_target hr, mul_one]
  have h2 : ‖(-1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  exact hL

theorem coord_mem_closure_span (hr : 0 < r) (s : ℕ) (i : Fin (F.N s)) :
    F.coord s i ∈ (Submodule.span ℂ (Set.range F.seq)).topologicalClosure := by
  have h : F.coord s i = F.atom s i - (2 * (dualScale r (F.N s) : ℂ)) • F.target s := by
    rw [atom_eq]
    abel
  rw [h]
  exact Submodule.sub_mem _ (Submodule.le_topologicalClosure _ (F.atom_mem_span s i))
    (Submodule.smul_mem _ _ (F.target_mem_closure_span hr s))

theorem root_mem_closure_span (hr : 0 < r) (j : ℕ) :
    F.root j ∈ (Submodule.span ℂ (Set.range F.seq)).topologicalClosure := by
  rw [← F.target_stageOf_zero j]
  exact F.target_mem_closure_span hr _

/-- **Completeness.** The linear span of the sequence is dense. -/
theorem dense_span_seq (hr : 0 < r) : Dense (Submodule.span ℂ (Set.range F.seq) : Set Z) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.eq_top_iff']
  intro z
  have hclosed : IsClosed ((Submodule.span ℂ (Set.range F.seq)).topologicalClosure : Set Z) :=
    Submodule.isClosed_topologicalClosure _
  have hY : Submodule.span ℂ (insert F.e0 (⋃ s, Set.range (F.coord s))) ≤
      (Submodule.span ℂ (Set.range F.seq)).topologicalClosure := by
    rw [Submodule.span_le]
    rintro w (rfl | hw)
    · exact Submodule.le_topologicalClosure _ F.e0_mem_span
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hw
      obtain ⟨i, rfl⟩ := hs
      exact F.coord_mem_closure_span hr s i
  have hX : Submodule.span ℂ (Set.range F.root) ≤
      (Submodule.span ℂ (Set.range F.seq)).topologicalClosure := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact F.root_mem_closure_span hr j
  have h1 : F.PY z ∈ (Submodule.span ℂ (Set.range F.seq)).topologicalClosure :=
    hclosed.closure_subset_iff.mpr (SetLike.coe_subset_coe.mpr hY)
      (F.coord_dense _ (F.PY_idem z))
  have h2 : z - F.PY z ∈ (Submodule.span ℂ (Set.range F.seq)).topologicalClosure :=
    hclosed.closure_subset_iff.mpr (SetLike.coe_subset_coe.mpr hX)
      (F.root_dense _ (by rw [map_sub, F.PY_idem, sub_self]))
  have h3 := Submodule.add_mem _ h1 h2
  rwa [add_sub_cancel] at h3

/-! ### The vectors of the sequence do not vanish -/

theorem atom_ne_zero (hr : 1 ≤ r) (s : ℕ) (i : Fin (F.N s)) : F.atom s i ≠ 0 := by
  classical
  have hr0 : 0 < r := by linarith
  intro h0
  have hv0 : ∀ t, t ≠ s → (Pi.single s (Pi.single i 1) : Coef F.N) t = 0 :=
    fun t ht => Pi.single_eq_of_ne ht _
  have hvs : (Pi.single s (Pi.single i 1) : Coef F.N) s = Pi.single i 1 := Pi.single_eq_same s _
  have hsupp : ∀ t, s + 1 ≤ t → (Pi.single s (Pi.single i 1) : Coef F.N) t = 0 :=
    fun t ht => hv0 t (by omega)
  have hmem : s ∈ Finset.range (s + 1) := Finset.mem_range.mpr (Nat.lt_succ_self s)
  have hsyn : F.synth (s + 1) (Pi.single s (Pi.single i 1)) = F.atom s i := by
    rw [synth, Finset.sum_eq_single s]
    · rw [hvs, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, one_smul]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_smul]
      · exact fun h => absurd (Finset.mem_univ i) h
    · intro t _ ht
      rw [hv0 t ht]
      simp
    · exact fun h => absurd hmem h
  have hlin : F.lin (s + 1) (synthCoord r F.N (Pi.single s (Pi.single i 1))) = 0 := by
    have h := F.PY_e0_add_synth 0 hsupp
    rw [zero_smul, zero_add, zero_add, hsyn, h0, map_zero] at h
    exact h.symm
  have hblk := F.norm_blk_le_norm_lin hr0 (Nat.lt_succ_self s)
    (synthCoord r F.N (Pi.single s (Pi.single i 1)))
  rw [hlin, norm_zero, synthCoord_apply, hv0 _ (lt_succStage s).ne', map_zero, mul_zero,
    zero_smul, add_zero, hvs] at hblk
  have hc : F.blk s (Pi.single i 1) = F.coord s i := by
    rw [blk_apply, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_smul]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [hc, F.norm_coord hr0] at hblk
  linarith

/-- No vector of the sequence vanishes. -/
theorem seq_ne_zero (hr : 1 ≤ r) (n : ℕ) : F.seq n ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [seq_zero]
    intro h0
    have := F.norm_e0 (by linarith : 0 < r)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  · obtain ⟨s, i, rfl⟩ := F.exists_offset_add h
    rw [seq_offset_add]
    exact F.atom_ne_zero hr s i

end StructuredBases.PositiveTranslates.PositiveForest
