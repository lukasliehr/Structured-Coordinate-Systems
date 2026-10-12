import Lean_Code.PositiveTranslates.Local.RearrangementStep
import Lean_Code.PositiveTranslates.Local.Model

/-!
# The model basis of `Lᵖ([0, 2))`

The unit intervals `[k, k + 1)`, `k ∈ ℤ`, are enumerated by `PositiveBiorthogonal.gridEnumeration`
(`0, 1, -1, 2, -2, …`). The `n`-th of them is sent affinely onto the dyadic piece
`[2 - 2^{1-n}, 2 - 2^{-n})` of `[0, 2)`; the zeroth piece is `[0, 1)` and is not moved.
This rearrangement is a positive isometry of `Lᵖ(ℝ)` onto `Lᵖ([0, 2))` which preserves
compactly supported step functions and fixes `𝟙_[0,1)` (`unitIsometry`,
`isCellIsometry_unitIsometry`, `unitIsometry_unit`). Transporting the model basis of
`Lᵖ(ℝ)` gives a local basis of `[0, 2)` with first vector `𝟙_[0,1)`
(`exists_unit_model_basis`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction PositiveBiorthogonal
open Local

/-- The breakpoints `2 - 2^{1-n}` of the dyadic partition of `[0, 2)`. -/
def dyadicPoint (n : ℕ) : ℝ := 2 - 2 * (1 / 2 : ℝ) ^ n

theorem dyadicPoint_zero : dyadicPoint 0 = 0 := by simp [dyadicPoint]

theorem dyadicPoint_one : dyadicPoint 1 = 1 := by norm_num [dyadicPoint]

theorem dyadicPoint_succ (n : ℕ) : dyadicPoint (n + 1) = 2 - (1 / 2 : ℝ) ^ n := by
  rw [dyadicPoint, pow_succ]
  ring

theorem dyadicPoint_lt_succ (n : ℕ) : dyadicPoint n < dyadicPoint (n + 1) := by
  have h : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  rw [dyadicPoint_succ, dyadicPoint]
  linarith

theorem dyadicPoint_strictMono : StrictMono dyadicPoint :=
  strictMono_nat_of_lt_succ dyadicPoint_lt_succ

theorem dyadicPoint_lt_two (n : ℕ) : dyadicPoint n < 2 := by
  have h : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  rw [dyadicPoint]
  linarith

theorem dyadicPoint_nonneg (n : ℕ) : 0 ≤ dyadicPoint n := by
  rw [← dyadicPoint_zero]
  exact dyadicPoint_strictMono.monotone (Nat.zero_le n)

theorem pairwise_disjoint_dyadic :
    Pairwise (Function.onFun Disjoint fun n => Set.Ico (dyadicPoint n) (dyadicPoint (n + 1))) := by
  have key : ∀ m n : ℕ, m < n →
      Disjoint (Set.Ico (dyadicPoint m) (dyadicPoint (m + 1)))
        (Set.Ico (dyadicPoint n) (dyadicPoint (n + 1))) := by
    intro m n h
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    have hle : dyadicPoint (m + 1) ≤ dyadicPoint n :=
      dyadicPoint_strictMono.monotone (Nat.succ_le_of_lt h)
    exact absurd (hx.2.trans_le (hle.trans hy.1)) (lt_irrefl _)
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact key m n h
  · exact (key n m h).symm

theorem iUnion_Ico_dyadicPoint :
    (⋃ n, Set.Ico (dyadicPoint n) (dyadicPoint (n + 1))) = Set.Ico (0 : ℝ) 2 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun n x hx =>
      ⟨(dyadicPoint_nonneg n).trans hx.1, hx.2.trans (dyadicPoint_lt_two _)⟩
  · intro x hx
    have hex : ∃ n, x < dyadicPoint (n + 1) := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hx.2) (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨n, by rw [dyadicPoint_succ]; linarith⟩
    obtain ⟨n, hn, hmin⟩ : ∃ n, x < dyadicPoint (n + 1) ∧ ∀ k < n, ¬ x < dyadicPoint (k + 1) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_, hn⟩
    cases n with
    | zero => rw [dyadicPoint_zero]; exact hx.1
    | succ k => exact not_lt.mp (hmin k (Nat.lt_succ_self k))

/-- The rearrangement sending the `n`-th unit interval (in the enumeration `0, 1, -1, 2, …`)
onto the `n`-th dyadic piece of `[0, 2)`. -/
def dyadicRearrangement : Rearrangement ℕ where
  src n := ((gridEnumeration n : ℝ), (gridEnumeration n : ℝ) + 1)
  tgt n := (dyadicPoint n, dyadicPoint (n + 1))
  src_lt _ := lt_add_one _
  tgt_lt n := dyadicPoint_lt_succ n
  src_disjoint :=
    (Set.pairwise_disjoint_Ico_intCast ℝ).comp_of_injective gridEnumeration_injective
  tgt_disjoint := pairwise_disjoint_dyadic

theorem dyadicRearrangement_srcSet (n : ℕ) :
    dyadicRearrangement.srcSet n =
      Set.Ico (gridEnumeration n : ℝ) ((gridEnumeration n : ℝ) + 1) := rfl

theorem dyadicRearrangement_srcUnion : dyadicRearrangement.srcUnion = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨n, hn⟩ := gridEnumeration_surjective ⌊x⌋
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  rw [dyadicRearrangement_srcSet, hn]
  exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

theorem dyadicRearrangement_tgtUnion : dyadicRearrangement.tgtUnion = Set.Ico (0 : ℝ) 2 :=
  iUnion_Ico_dyadicPoint

theorem dyadicRearrangement_locallyFinite : dyadicRearrangement.LocallyFinite := by
  intro c d
  refine ⟨(Finset.Icc ⌊c⌋ ⌈d⌉).image gridEnumerationEquiv.symm, fun n hn => ?_⟩
  have hout : gridEnumeration n ∉ Finset.Icc ⌊c⌋ ⌈d⌉ := by
    intro h
    apply hn
    refine Finset.mem_image.mpr ⟨gridEnumeration n, h, ?_⟩
    exact gridEnumerationEquiv.symm_apply_apply n
  rw [dyadicRearrangement_srcSet]
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hout
  refine Set.disjoint_left.mpr fun x hx hy => ?_
  rcases hout with h | h
  · have h1 : (gridEnumeration n : ℝ) + 1 ≤ (⌊c⌋ : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    have h2 := Int.floor_le c
    linarith [hx.2, hy.1]
  · have h1 : ((⌈d⌉ : ℤ) : ℝ) < (gridEnumeration n : ℝ) := by exact_mod_cast h
    have h2 := Int.le_ceil d
    linarith [hx.1, hy.2]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The dyadic rearrangement does not move the unit interval `[0, 1)`. -/
theorem dyadicRearrangement_op_unit (hpfin : p ≠ ∞) :
    dyadicRearrangement.op hpfin (intervalAtom p (0, 1)) = intervalAtom p (0, 1) := by
  have h := dyadicRearrangement.op_intervalAtom_src hpfin (p := p) 0
  have hsrc : dyadicRearrangement.src 0 = (0, 1) := by
    simp [dyadicRearrangement]
  have htgt : dyadicRearrangement.tgt 0 = (0, 1) := by
    simp [dyadicRearrangement, dyadicPoint_zero, dyadicPoint_one]
  have hw : dyadicRearrangement.weight p 0 = 1 := by
    simp [Rearrangement.weight, Rearrangement.slope, hsrc, htgt]
  rw [hsrc, htgt, hw, one_smul] at h
  exact h

/-- The positive isometry of `Lᵖ(ℝ)` onto `Lᵖ([0, 2))` given by the dyadic rearrangement. -/
def unitIsometry (hpfin : p ≠ ∞) : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p :=
  dyadicRearrangement.compIsometry hpfin LinearIsometry.id
    (IsCellIsometry.id.congr_set dyadicRearrangement_srcUnion.symm).supported

theorem unitIsometry_apply (hpfin : p ≠ ∞) (F : LebesgueLp p) :
    unitIsometry hpfin F = dyadicRearrangement.op hpfin F := rfl

/-- The dyadic rearrangement is a cell isometry of `Lᵖ(ℝ)` onto `Lᵖ([0, 2))`. -/
theorem isCellIsometry_unitIsometry (hpfin : p ≠ ∞) :
    IsCellIsometry (unitIsometry hpfin) (Set.Ico (0 : ℝ) 2) :=
  (dyadicRearrangement.isCellIsometry_compIsometry hpfin dyadicRearrangement_locallyFinite
    (IsCellIsometry.id.congr_set dyadicRearrangement_srcUnion.symm)).congr_set
      dyadicRearrangement_tgtUnion

/-- The isometry onto `Lᵖ([0, 2))` fixes the indicator of `[0, 1)`. -/
theorem unitIsometry_unit (hpfin : p ≠ ∞) :
    unitIsometry hpfin (intervalAtom p (0, 1)) = intervalAtom p (0, 1) :=
  dyadicRearrangement_op_unit hpfin

/-- **Model basis of `Lᵖ([0, 2))`.** For `1 < p < ∞` and `B > 1` there is a normalized
non-negative compact-step Schauder basis of `Lᵖ([0, 2))` with prefix constant `B` whose first
vector is the indicator of `[0, 1)`. -/
theorem exists_unit_model_basis (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {B : ℝ} (hB : 1 < B) :
    ∃ r : ℕ → LebesgueLp p, r 0 = intervalAtom p (0, 1) ∧
      LocalBasis p r (Set.Ico (0 : ℝ) 2) B := by
  obtain ⟨r, hr0, hr⟩ := exists_model_basis p hp1 hpfin hB
  refine ⟨fun n => unitIsometry hpfin (r n), ?_, ?_⟩
  · change unitIsometry hpfin (r 0) = _
    rw [hr0, unitIsometry_unit]
  · exact LocalBasis.of_cellIsometry (isCellIsometry_unitIsometry hpfin) hr

end StructuredBases.PositiveTranslates
