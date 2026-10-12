import Lean_Code.PositiveTranslates.Local.Dyadic
import Lean_Code.SchauderTranslates.Lp.PositiveMassPartition

/-!
# Cell isometries and local bases on intervals and on cells with a prescribed first vector

* `exists_cellIsometry_Ico`: for every bounded interval `[a, b)` there is a positive isometry
  of `Lᵖ(ℝ)` onto `Lᵖ([a, b))` preserving compactly supported step functions.
* `exists_cellIsometry_first_vector`: let `e = ∑ₖ cₖ 𝟙_{Iₖ}` be a non-negative unit step
  function given by finitely many pairwise disjoint intervals with positive values, and let
  `[a, b)` be an interval disjoint from them. Then there is such an isometry onto
  `Lᵖ((⋃ₖ Iₖ) ∪ [a, b))` which sends `𝟙_[0,1)` to `e`.
* `exists_localBasis_Ico`, `exists_localBasis_first_vector`: the images of the model basis
  of `Lᵖ(ℝ)` under these isometries.

For the second statement `[0, 1)` is cut into consecutive intervals of lengths
`cₖ^p |Iₖ|` (they add up to `‖e‖^p = 1`), the `k`-th of which is sent affinely onto `Iₖ`,
and `[1, 2)` is sent affinely onto `[a, b)`. The resulting operator sends `𝟙_[0,1)` to `e`.
When the intervals `Iₖ` are listed from left to right, its restriction to `Lᵖ([0, 1))` is the
isometry `ψ ↦ e · (ψ ∘ C_e)` of the paper, `C_e(x) = ∫_{(-∞, x]} e^p`. Both isometries are
composed with the isometry `unitIsometry` of `Lᵖ(ℝ)` onto `Lᵖ([0, 2))`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Intervals -/

/-- The affine rearrangement of `[0, 2)` onto `[a, b)`. -/
def intervalRearrangement (a b : ℝ) (hab : a < b) : Rearrangement Unit where
  src _ := (0, 2)
  tgt _ := (a, b)
  src_lt _ := by norm_num
  tgt_lt _ := hab
  src_disjoint := fun i j h => absurd (Subsingleton.elim i j) h
  tgt_disjoint := fun i j h => absurd (Subsingleton.elim i j) h

theorem intervalRearrangement_srcUnion (a b : ℝ) (hab : a < b) :
    (intervalRearrangement a b hab).srcUnion = Set.Ico (0 : ℝ) 2 := by
  change (⋃ _ : Unit, Set.Ico (0 : ℝ) 2) = Set.Ico (0 : ℝ) 2
  exact Set.iUnion_const _

theorem intervalRearrangement_tgtUnion (a b : ℝ) (hab : a < b) :
    (intervalRearrangement a b hab).tgtUnion = Set.Ico a b := by
  change (⋃ _ : Unit, Set.Ico a b) = Set.Ico a b
  exact Set.iUnion_const _

/-- **Cell isometries of intervals.** For every finite exponent and every bounded interval
`[a, b)` there is a positive linear isometry of `Lᵖ(ℝ)` onto `Lᵖ([a, b))` which preserves
compactly supported step functions. -/
theorem exists_cellIsometry_Ico (hpfin : p ≠ ∞) (a b : ℝ) (hab : a < b) :
    ∃ T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p, IsCellIsometry T (Set.Ico a b) := by
  have h0 : IsCellIsometry (unitIsometry hpfin) (intervalRearrangement a b hab).srcUnion :=
    (isCellIsometry_unitIsometry hpfin).congr_set (intervalRearrangement_srcUnion a b hab).symm
  exact ⟨_, ((intervalRearrangement a b hab).isCellIsometry_compIsometry hpfin
    (Rearrangement.locallyFinite_of_finite _) h0).congr_set
      (intervalRearrangement_tgtUnion a b hab)⟩

/-- **Local bases of intervals.** For `1 < p < ∞` and `B > 1` every bounded interval `[a, b)`
has a normalized non-negative compact-step Schauder basis with prefix constant `B`. -/
theorem exists_localBasis_Ico (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {B : ℝ} (hB : 1 < B) (a b : ℝ) (hab : a < b) :
    ∃ β : ℕ → LebesgueLp p, LocalBasis p β (Set.Ico a b) B := by
  obtain ⟨r, -, hr⟩ := exists_model_basis p hp1 hpfin hB
  obtain ⟨T, hT⟩ := exists_cellIsometry_Ico hpfin a b hab
  exact ⟨_, LocalBasis.of_cellIsometry hT hr⟩

/-! ### Cells with a prescribed first vector -/

/-- The `p`-th power of the norm of a step function with disjoint pieces. -/
theorem Local.norm_rpow_sum_smul_intervalAtom {m : ℕ} (hpfin : p ≠ ∞) (I : Fin m → ℝ × ℝ)
    (c : Fin m → ℝ) (hI : ∀ k, (I k).1 < (I k).2) (hc : ∀ k, 0 ≤ c k)
    (hdis : Pairwise (fun k l =>
      Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2))) :
    ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ ^ p.toReal =
      ∑ k, c k ^ p.toReal * ((I k).2 - (I k).1) := by
  have hp0 : p ≠ 0 := exponent_ne_zero
  rw [norm_finset_sum_rpow Finset.univ _ hp0 hpfin]
  · apply Finset.sum_congr rfl
    intro k _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc k),
      Real.mul_rpow (hc k) (norm_nonneg _), intervalAtom_norm_power hp0 hpfin (I k) (hI k)]
  · intro k _ l _ hkl
    exact (supportedOn_smul (intervalAtom_supported_cell p (I k)) _).ae_disjoint
      (supportedOn_smul (intervalAtom_supported_cell p (I l)) _) (hdis hkl)

/-- The rearrangement which sends the `k`-th cell of a partition of `[0, 1)` onto the interval
`I k` and `[1, 2)` onto the room interval `[a, b)`. -/
def cellRearrangement {m : ℕ} (P : PositiveMassPartition m) (I : Fin m → ℝ × ℝ) (a b : ℝ)
    (hI : ∀ k, (I k).1 < (I k).2)
    (hdis : Pairwise (fun k l =>
      Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)))
    (hroom : ∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) (hab : a < b) :
    Rearrangement (Option (Fin m)) where
  src := fun o => match o with
    | none => (1, 2)
    | some k => (P.endpoint k, P.endpoint (k + 1))
  tgt := fun o => match o with
    | none => (a, b)
    | some k => I k
  src_lt := by
    rintro (_ | k)
    · norm_num
    · exact P.endpoint_lt_succ k.isLt
  tgt_lt := by
    rintro (_ | k)
    · exact hab
    · exact hI k
  src_disjoint := by
    rintro (_ | k) (_ | l) hne
    · exact absurd rfl hne
    · change Disjoint (Set.Ico (1 : ℝ) 2) (P.cell l)
      exact Set.disjoint_left.mpr fun x hx hy =>
        absurd (P.cell_subset_unit l hy).2 (not_lt.mpr hx.1)
    · change Disjoint (P.cell k) (Set.Ico (1 : ℝ) 2)
      exact Set.disjoint_left.mpr fun x hx hy =>
        absurd (P.cell_subset_unit k hx).2 (not_lt.mpr hy.1)
    · exact P.cells_disjoint (fun h => hne (congrArg some h))
  tgt_disjoint := by
    rintro (_ | k) (_ | l) hne
    · exact absurd rfl hne
    · exact (hroom l).symm
    · exact hroom k
    · exact hdis (fun h => hne (congrArg some h))

section CellRearrangement

variable {m : ℕ} (P : PositiveMassPartition m) (I : Fin m → ℝ × ℝ) (a b : ℝ)
    (hI : ∀ k, (I k).1 < (I k).2)
    (hdis : Pairwise (fun k l =>
      Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)))
    (hroom : ∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) (hab : a < b)

theorem cellRearrangement_srcSet_none :
    (cellRearrangement P I a b hI hdis hroom hab).srcSet none = Set.Ico (1 : ℝ) 2 := rfl

theorem cellRearrangement_srcSet_some (k : Fin m) :
    (cellRearrangement P I a b hI hdis hroom hab).srcSet (some k) = P.cell k := rfl

theorem cellRearrangement_tgt_some (k : Fin m) :
    (cellRearrangement P I a b hI hdis hroom hab).tgt (some k) = I k := rfl

theorem cellRearrangement_srcUnion :
    (cellRearrangement P I a b hI hdis hroom hab).srcUnion = Set.Ico (0 : ℝ) 2 := by
  rw [Rearrangement.srcUnion, Set.iUnion_option]
  simp only [cellRearrangement_srcSet_none, cellRearrangement_srcSet_some]
  rw [P.cells_union, Set.union_comm, Set.Ico_union_Ico_eq_Ico zero_le_one one_le_two]

theorem cellRearrangement_tgtUnion :
    (cellRearrangement P I a b hI hdis hroom hab).tgtUnion =
      (⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b := by
  rw [Rearrangement.tgtUnion, Set.iUnion_option, Set.union_comm]
  rfl

theorem cellRearrangement_slope_some (k : Fin m) :
    (cellRearrangement P I a b hI hdis hroom hab).slope (some k) =
      P.mass k / ((I k).2 - (I k).1) := by
  have h : P.endpoint (k + 1) - P.endpoint k = P.mass k := by
    rw [P.endpoint_succ k.isLt]
    simp
  rw [Rearrangement.slope]
  change (P.endpoint (k + 1) - P.endpoint k) / ((I k).2 - (I k).1) = _
  rw [h]

/-- The image of the indicator of `[0, 1)`. -/
theorem cellRearrangement_op_unit (hpfin : p ≠ ∞) :
    (cellRearrangement P I a b hI hdis hroom hab).op hpfin (intervalAtom p (0, 1)) =
      ∑ k, (cellRearrangement P I a b hI hdis hroom hab).weight p (some k) •
        intervalAtom p (I k) := by
  rw [Rearrangement.op_intervalAtom_of_union _ hpfin 0 1 (Finset.univ.image some)]
  · rw [Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)]
    rfl
  · intro o ho
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ho
    rw [cellRearrangement_srcSet_some]
    exact P.cell_subset_unit k
  · rintro (_ | k) ho
    · rw [cellRearrangement_srcSet_none]
      exact Set.disjoint_left.mpr fun x hx hy => absurd hy.2 (not_lt.mpr hx.1)
    · exact absurd (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩) ho

end CellRearrangement

/-- **Cell isometries with a prescribed image of `𝟙_[0,1)`.** Let `p` be a finite exponent,
let `e = ∑ₖ cₖ 𝟙_{Iₖ}` be a unit vector of `Lᵖ` given by finitely many nondegenerate pairwise
disjoint intervals `Iₖ = [(I k).1, (I k).2)` and positive values `cₖ`, and let `[a, b)` be a
nondegenerate interval disjoint from all `Iₖ`. Then there is a positive linear isometry of
`Lᵖ(ℝ)` onto `Lᵖ((⋃ₖ Iₖ) ∪ [a, b))` which preserves compactly supported step functions and
sends the indicator of `[0, 1)` to `e`. -/
theorem exists_cellIsometry_first_vector (hpfin : p ≠ ∞) (m : ℕ) (I : Fin m → ℝ × ℝ)
    (c : Fin m → ℝ) (a b : ℝ)
    (hI : ∀ k, (I k).1 < (I k).2) (hc : ∀ k, 0 < c k)
    (hdis : Pairwise (fun k l =>
      Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)))
    (hroom : ∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) (hab : a < b)
    (hnorm : ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1) :
    ∃ T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p,
      IsCellIsometry T ((⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b) ∧
      T (intervalAtom p (0, 1)) = ∑ k, (c k : ℂ) • intervalAtom p (I k) := by
  have hp0 : p ≠ 0 := exponent_ne_zero
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  have hlen : ∀ k, 0 < (I k).2 - (I k).1 := fun k => sub_pos.mpr (hI k)
  -- the cell masses
  have htotal : ∑ k, c k ^ p.toReal * ((I k).2 - (I k).1) = 1 := by
    rw [← norm_rpow_sum_smul_intervalAtom hpfin I c hI (fun k => (hc k).le) hdis, hnorm,
      Real.one_rpow]
  let P : PositiveMassPartition m :=
    { mass := fun k => c k ^ p.toReal * ((I k).2 - (I k).1)
      mass_pos := fun k => mul_pos (Real.rpow_pos_of_pos (hc k) _) (hlen k)
      total := htotal }
  let R := cellRearrangement P I a b hI hdis hroom hab
  have hweight : ∀ k, R.weight p (some k) = c k := by
    intro k
    have hs : R.slope (some k) = c k ^ p.toReal := by
      rw [cellRearrangement_slope_some]
      change c k ^ p.toReal * ((I k).2 - (I k).1) / ((I k).2 - (I k).1) = _
      rw [mul_div_assoc, div_self (hlen k).ne', mul_one]
    rw [Rearrangement.weight, hs, Real.rpow_rpow_inv (hc k).le hpR.ne']
  have h0 : IsCellIsometry (unitIsometry hpfin) R.srcUnion :=
    (isCellIsometry_unitIsometry hpfin).congr_set
      (cellRearrangement_srcUnion P I a b hI hdis hroom hab).symm
  refine ⟨R.compIsometry hpfin (unitIsometry hpfin) h0.supported,
    (R.isCellIsometry_compIsometry hpfin (Rearrangement.locallyFinite_of_finite _)
      h0).congr_set (cellRearrangement_tgtUnion P I a b hI hdis hroom hab), ?_⟩
  rw [Rearrangement.compIsometry_apply, unitIsometry_unit,
    cellRearrangement_op_unit P I a b hI hdis hroom hab hpfin]
  refine Finset.sum_congr rfl fun k _ => ?_
  change R.weight p (some k) • intervalAtom p (I k) = _
  rw [hweight k, ofReal_smul_eq]

/-- **Local bases with a prescribed first vector.** Let `1 < p < ∞` and `B > 1`. Let
`e = ∑ₖ cₖ 𝟙_{Iₖ}` be a unit vector of `Lᵖ` given by finitely many nondegenerate pairwise
disjoint intervals `Iₖ = [(I k).1, (I k).2)` and positive values `cₖ`, and let `[a, b)` be a
nondegenerate interval disjoint from all `Iₖ`. Then `(⋃ₖ Iₖ) ∪ [a, b)` has a normalized
non-negative compact-step Schauder basis with prefix constant `B` whose first vector is `e`. -/
theorem exists_localBasis_first_vector (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {B : ℝ} (hB : 1 < B) (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ) (a b : ℝ)
    (hI : ∀ k, (I k).1 < (I k).2) (hc : ∀ k, 0 < c k)
    (hdis : Pairwise (fun k l =>
      Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)))
    (hroom : ∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) (hab : a < b)
    (hnorm : ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1) :
    ∃ β : ℕ → LebesgueLp p, β 0 = ∑ k, (c k : ℂ) • intervalAtom p (I k) ∧
      LocalBasis p β ((⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b) B := by
  obtain ⟨r, hr0, hr⟩ := exists_model_basis p hp1 hpfin hB
  obtain ⟨T, hT, hT0⟩ :=
    exists_cellIsometry_first_vector hpfin m I c a b hI hc hdis hroom hab hnorm
  refine ⟨fun n => T (r n), ?_, LocalBasis.of_cellIsometry hT hr⟩
  change T (r 0) = _
  rw [hr0, hT0]

end StructuredBases.PositiveTranslates
