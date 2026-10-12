import Lean_Code.PositiveBiorthogonal.GlobalCorrection

/-! The global correction acts locally on auxiliary coefficients and kills every Haar coefficient. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ComplexOrder
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem UnitBlock.transfer_pairing_haarPhi_grid {m : ℕ} (F : UnitBlock m)
    (v : FiniteLp 𝕜 p m) (S : IntervalSplit) (z : ℤ)
    (hz : S.parent.carrier ⊆ (gridUnit z).carrier) :
    pairing (F.transfer v) (S.haarPhi : L 𝕜 q) = 0 := by
  rw [← representedFunctional_apply]
  change representedFunctional (S.haarPhi : L 𝕜 q) (∑ i : Fin m, v i • (F.cell i).indicator) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul, representedFunctional_apply, pairing_comm, IntervalCell.pairing_indicator]
  change v i • (∫ x in (gridUnit (F.unit i)).carrier, (S.haarPhi : L 𝕜 q) x) = 0
  rw [S.haarPhi_unit_integral z hz, smul_zero]

theorem RefinementTrace.parent_in_grid {N : ℕ} (T : RefinementTrace N) (j : Fin N) :
    ∃ z : ℤ, (T.split j).parent.carrier ⊆ (gridUnit z).carrier := by
  obtain ⟨z, hz, hsub⟩ := (T.state j.castSucc).in_grid (T.index j)
  exact ⟨z, by rw [T.parent]; exact hsub⟩

namespace ConstructionData
variable (C : ConstructionData 𝕜 p q)

theorem localR_other_auxiliary (l k : ℕ) (hlk : l ≠ k) (j : Fin (2 * C.batchSize k)) :
    C.localR l ((C.fresh k).transfer (C.aux.s (C.batchSize k) j)) = 0 := by
  apply localR_zero_of_pairing_zero
  exact pairing_zero_disjoint_support _ _ _ _ (C.fresh_pairwise_disjoint hlk)
    ((C.fresh l).transfer_supported _) ((C.fresh k).transfer_supported _)

theorem localR_haar (l k : ℕ) (j : Fin (C.batchSize k)) :
    C.localR l (((C.trace k).split j).haarPhi : L 𝕜 q) = 0 := by
  apply localR_zero_of_pairing_zero
  obtain ⟨z, hz⟩ := (C.trace k).parent_in_grid j
  exact (C.fresh l).transfer_pairing_haarPhi_grid _ _ z hz

theorem localR_root (l : ℕ) : C.localR l ((gridUnit 0).indicator : L 𝕜 q) = 0 := by
  apply localR_zero_of_pairing_zero
  have hz : 0 ∈ (C.stage l).part.units := by
    rw [(C.stage l).units_eq]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (C.stage l).activeCount_pos, gridEnumeration_zero⟩
  apply pairing_zero_disjoint_support _ _ (C.fresh l).carrier (gridUnit 0).carrier
    ((C.fresh_disjoint l).mono_right ((C.stage l).part.gridUnit_subset_active 0 hz))
    ((C.fresh l).transfer_supported _)
  filter_upwards [(gridUnit 0).coe_indicator (𝕜 := 𝕜) (p := q)] with x hx
  intro hn
  simp [hx, hn]

theorem sumR_auxiliary (k : ℕ) (j : Fin (2 * C.batchSize k)) :
    C.sumR ((C.fresh k).transfer (C.aux.s (C.batchSize k) j)) =
      (((C.scale k * splitTheta (C.steps k) : ℝ) : 𝕜) *
        pairing ((C.fresh k).transfer (C.aux.z (C.batchSize k)))
          ((C.fresh k).transfer (C.aux.s (C.batchSize k) j))) • ((C.stage k).part.indicator : L 𝕜 q) := by
  rw [C.sumR_apply, tsum_eq_single k (fun l hl => C.localR_other_auxiliary l k hl j)]
  exact localR_apply _ _ _ _

theorem sumR_haar (k : ℕ) (j : Fin (C.batchSize k)) :
    C.sumR (((C.trace k).split j).haarPhi : L 𝕜 q) = 0 := by
  rw [C.sumR_apply]
  simp only [C.localR_haar, tsum_zero]

theorem sumR_root : C.sumR ((gridUnit 0).indicator : L 𝕜 q) = 0 := by
  rw [C.sumR_apply]
  simp only [C.localR_root, tsum_zero]

theorem localR_other_batch (l k : ℕ) (hlk : l ≠ k) (i : Fin (3 * C.batchSize k)) :
    C.localR l (C.batchCoefficients k i) = 0 := by
  change C.localR l (batchCoefficient (fun j => (C.fresh k).transfer (C.aux.s (C.batchSize k) j))
    (fun j => ((C.trace k).split j).haarPhi) (C.scale k : 𝕜) ((batchOrder (C.batchSize k)).symm i)) = 0
  generalize (batchOrder (C.batchSize k)).symm i = a
  rcases a with ⟨j, b⟩ | j
  · by_cases hb : b = 0 <;> simp only [batchCoefficient, hb, ↓reduceIte, map_add, map_smul,
      C.localR_other_auxiliary l k hlk, C.localR_haar, smul_zero, add_zero]
  · exact C.localR_other_auxiliary l k hlk _

theorem sumR_batch (k : ℕ) (i : Fin (3 * C.batchSize k)) :
    C.sumR (C.batchCoefficients k i) = C.localR k (C.batchCoefficients k i) := by
  rw [C.sumR_apply]
  exact tsum_eq_single k (fun l hl => C.localR_other_batch l k hl i)

theorem trace_ratio (k : ℕ) (j : Fin (C.batchSize k)) :
    ((C.trace k).split j).ratio = splitTheta (C.steps k) := by
  have h := splittingSchedule_split (C.stage k).part (C.steps k) (C.steps_ge_two k) j
  have hr := congrArg IntervalSplit.ratio h
  rw [geometricSplit_ratio] at hr
  exact hr

theorem V_batch_nonnegative (k : ℕ) (i : Fin (3 * C.batchSize k)) :
    Nonnegative (C.V (C.batchCoefficients k i)) := by
  rw [C.V_apply, C.sumR_batch]
  exact C.aux.corrected_batch_nonnegative
    (lt_of_lt_of_le (by decide : 0 < 2) (C.batchSize_ge_two k))
    (C.trace k) (C.fresh k) (C.fresh_disjoint k) (C.scale k) (splitTheta (C.steps k))
    (C.scale_pos k) (splitTheta_pos (C.steps k) (C.steps_ge_two k)).le (C.trace_ratio k) i

theorem V_batch_step (k : ℕ) (i : Fin (3 * C.batchSize k)) :
    CompactlySupportedStep (C.V (C.batchCoefficients k i)) := by
  rw [C.V_apply, C.sumR_batch]
  exact C.aux.corrected_batch_step (C.trace k) (C.fresh k) _ _ i

theorem V_rawCoefficient_nonnegative (n : ℕ) : Nonnegative (C.V (C.rawCoefficient n)) := by
  by_cases hn : n = 0
  · subst n
    rw [C.rawCoefficient_zero, C.V_apply, C.sumR_root, add_zero]
    exact (gridUnit 0).indicator_nonnegative
  · simp only [rawCoefficient, if_neg hn]
    exact C.V_batch_nonnegative _ _

theorem V_rawCoefficient_step (n : ℕ) : CompactlySupportedStep (C.V (C.rawCoefficient n)) := by
  by_cases hn : n = 0
  · subst n
    rw [C.rawCoefficient_zero, C.V_apply, C.sumR_root, add_zero]
    exact (gridUnit 0).indicator_step
  · simp only [rawCoefficient, if_neg hn]
    exact C.V_batch_step _ _

end ConstructionData
end PositiveBiorthogonal
