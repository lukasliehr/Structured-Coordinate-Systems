import Lean_Code.PositiveTranslates.Global.Roots
import Lean_Code.SchauderTranslates.Lp.DisjointLpSynthesis

/-!
# The coordinate projection

`coordProjection` is the operator
`PY F = ∑_{c coordinate cell} φ_c(F·𝟙_{A c}) • β c 0`,
where `φ_c` is the first coordinate functional of the local basis of the cell `c`.  The
series converges because the blocks are disjointly supported:
`‖PY F‖ᵖ = ∑_c |φ_c(F·𝟙_{A c})|ᵖ ≤ Bᵖ ∑_c ‖F·𝟙_{A c}‖ᵖ ≤ Bᵖ ‖F‖ᵖ`.

It is a projection of norm at most `B` which fixes the coordinates and kills the roots; its
range is the closed span of the coordinates and its kernel is the closed span of the roots.
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

/-! ### The coordinate functionals -/

/-- The coordinate functional of the cell `c`: the first coordinate functional of its local
basis applied to the cell part if `c` is a coordinate cell, and zero otherwise. -/
def coordFunctional (c : ℕ) : LebesgueLp p →L[ℂ] ℂ :=
  if isCoord c then (hβ c).wholeCoord (hA c) 0 else 0

theorem coordFunctional_of_coord {c : ℕ} (hc : isCoord c = true) :
    coordFunctional hA hβ isCoord c = (hβ c).wholeCoord (hA c) 0 := if_pos hc

theorem coordFunctional_of_not_coord {c : ℕ} (hc : ¬ isCoord c = true) :
    coordFunctional hA hβ isCoord c = 0 := if_neg hc

theorem norm_coordFunctional_le (c : ℕ) (F : LebesgueLp p) :
    ‖coordFunctional hA hβ isCoord c F‖ ≤ B * ‖lpCellProjection p volume (A c) (hA c) F‖ := by
  by_cases hc : isCoord c = true
  · rw [coordFunctional_of_coord hA hβ isCoord hc]
    exact ((hβ c).wholeCoord_spec (hA c)).norm_coord_zero_le ((hβ c).norm 0) F
  · rw [coordFunctional_of_not_coord hA hβ isCoord hc, zero_apply, norm_zero]
    exact mul_nonneg (hβ c).const_nonneg (norm_nonneg _)

/-- The coordinate functional of a cell vanishes on classes supported off the cell. -/
theorem coordFunctional_of_disjoint (c : ℕ) {F : LebesgueLp p} {s : Set ℝ}
    (hF : SupportedOn F s) (hd : Disjoint s (A c)) : coordFunctional hA hβ isCoord c F = 0 := by
  by_cases hc : isCoord c = true
  · rw [coordFunctional_of_coord hA hβ isCoord hc]
    exact ((hβ c).wholeCoord_spec (hA c)).apply_of_disjoint 0 hF hd
  · rw [coordFunctional_of_not_coord hA hβ isCoord hc, zero_apply]

/-- The coordinate functional of a cell on the local basis of the same cell. -/
theorem coordFunctional_basis (c n : ℕ) :
    coordFunctional hA hβ isCoord c (β c n) = if isCoord c = true ∧ n = 0 then 1 else 0 := by
  by_cases hc : isCoord c = true
  · rw [coordFunctional_of_coord hA hβ isCoord hc, ((hβ c).wholeCoord_spec (hA c)).biorth]
    simp [hc, eq_comm]
  · rw [coordFunctional_of_not_coord hA hβ isCoord hc, zero_apply]
    simp [hc]

include hpfin hdis in
theorem sum_norm_coordFunctional_rpow_le (s : Finset ℕ) (F : LebesgueLp p) :
    ∑ c ∈ s, ‖coordFunctional hA hβ isCoord c F‖ ^ p.toReal ≤ (B * ‖F‖) ^ p.toReal := by
  have hB : 0 ≤ B := (hβ 0).const_nonneg
  calc
    ∑ c ∈ s, ‖coordFunctional hA hβ isCoord c F‖ ^ p.toReal
        ≤ ∑ c ∈ s, (B * ‖lpCellProjection p volume (A c) (hA c) F‖) ^ p.toReal :=
      Finset.sum_le_sum fun c _ => Real.rpow_le_rpow (norm_nonneg _)
        (norm_coordFunctional_le hA hβ isCoord c F) ENNReal.toReal_nonneg
    _ = B ^ p.toReal * ∑ c ∈ s, ‖lpCellProjection p volume (A c) (hA c) F‖ ^ p.toReal := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => Real.mul_rpow hB (norm_nonneg _)
    _ ≤ B ^ p.toReal * ‖F‖ ^ p.toReal :=
      mul_le_mul_of_nonneg_left (sum_norm_lpCellProjection_rpow_le hA hdis hpfin s F)
        (Real.rpow_nonneg hB _)
    _ = (B * ‖F‖) ^ p.toReal := (Real.mul_rpow hB (norm_nonneg _)).symm

/-! ### The coefficient map into `ℓᵖ` -/

/-- The coordinate coefficients of a class, as an element of `ℓᵖ`. -/
def coordCoeffLinear : LebesgueLp p →ₗ[ℂ] lp (fun _ : ℕ => ℂ) p where
  toFun F := ⟨fun c => coordFunctional hA hβ isCoord c F,
    memℓp_gen' (fun s => sum_norm_coordFunctional_rpow_le hpfin hA hdis hβ isCoord s F)⟩
  map_add' F G := by
    apply lp.ext
    funext c
    exact map_add (coordFunctional hA hβ isCoord c) F G
  map_smul' a F := by
    apply lp.ext
    funext c
    exact map_smul (coordFunctional hA hβ isCoord c) a F

theorem coordCoeffLinear_bound (F : LebesgueLp p) :
    ‖coordCoeffLinear hpfin hA hdis hβ isCoord F‖ ≤ B * ‖F‖ :=
  lp.norm_le_of_forall_sum_le (lpExponent_toReal_pos p hpfin)
    (mul_nonneg (hβ 0).const_nonneg (norm_nonneg F))
    (fun s => sum_norm_coordFunctional_rpow_le hpfin hA hdis hβ isCoord s F)

/-- The coordinate coefficient map `Lᵖ → ℓᵖ`, of norm at most `B`. -/
def coordCoeff : LebesgueLp p →L[ℂ] lp (fun _ : ℕ => ℂ) p :=
  (coordCoeffLinear hpfin hA hdis hβ isCoord).mkContinuous B
    (coordCoeffLinear_bound hpfin hA hdis hβ isCoord)

theorem coordCoeff_apply (F : LebesgueLp p) (c : ℕ) :
    coordCoeff hpfin hA hdis hβ isCoord F c = coordFunctional hA hβ isCoord c F := rfl

theorem norm_coordCoeff_apply_le (F : LebesgueLp p) :
    ‖coordCoeff hpfin hA hdis hβ isCoord F‖ ≤ B * ‖F‖ :=
  coordCoeffLinear_bound hpfin hA hdis hβ isCoord F

/-! ### The projection -/

/-- **The coordinate projection** `PY F = ∑_{c coordinate cell} φ_c(F·𝟙_{A c}) • β c 0`. -/
def coordProjection : LebesgueLp p →L[ℂ] LebesgueLp p :=
  (disjointLpSynthesis (cellCoord β)).comp (coordCoeff hpfin hA hdis hβ isCoord)

/-- The defining series of the coordinate projection converges unconditionally. -/
theorem coordProjection_hasSum (F : LebesgueLp p) :
    HasSum (fun c => coordFunctional hA hβ isCoord c F • cellCoord β c)
      (coordProjection hpfin hA hdis hβ isCoord F) :=
  disjointLpSynthesis_hasSum (lpExponent_ne_zero p) hpfin (cellCoord β) (cellCoord_norm hβ)
    (cellCoord_ae_disjoint hβ hdis) (coordCoeff hpfin hA hdis hβ isCoord F)

theorem norm_coordProjection_apply (F : LebesgueLp p) :
    ‖coordProjection hpfin hA hdis hβ isCoord F‖ = ‖coordCoeff hpfin hA hdis hβ isCoord F‖ :=
  disjointLpSynthesis_norm (lpExponent_ne_zero p) hpfin (cellCoord β) (cellCoord_norm hβ)
    (cellCoord_ae_disjoint hβ hdis) (coordCoeff hpfin hA hdis hβ isCoord F)

/-- The `p`-th power of the norm of `PY F` is the `ℓᵖ` sum of the coordinate coefficients. -/
theorem norm_coordProjection_rpow_hasSum (F : LebesgueLp p) :
    HasSum (fun c => ‖coordFunctional hA hβ isCoord c F‖ ^ p.toReal)
      (‖coordProjection hpfin hA hdis hβ isCoord F‖ ^ p.toReal) := by
  rw [norm_coordProjection_apply]
  exact lp.hasSum_norm (lpExponent_toReal_pos p hpfin) (coordCoeff hpfin hA hdis hβ isCoord F)

theorem norm_coordProjection_apply_le (F : LebesgueLp p) :
    ‖coordProjection hpfin hA hdis hβ isCoord F‖ ≤ B * ‖F‖ := by
  rw [norm_coordProjection_apply]
  exact norm_coordCoeff_apply_le hpfin hA hdis hβ isCoord F

/-- The coordinate projection has norm at most the prefix constant. -/
theorem norm_coordProjection_le : ‖coordProjection hpfin hA hdis hβ isCoord‖ ≤ B :=
  ContinuousLinearMap.opNorm_le_bound _ (hβ 0).const_nonneg
    (norm_coordProjection_apply_le hpfin hA hdis hβ isCoord)

/-- On a class living in one cell only one term of the series survives. -/
theorem coordProjection_apply_of_supported {c : ℕ} {F : LebesgueLp p}
    (hF : SupportedOn F (A c)) :
    coordProjection hpfin hA hdis hβ isCoord F =
      coordFunctional hA hβ isCoord c F • cellCoord β c := by
  refine (coordProjection_hasSum hpfin hA hdis hβ isCoord F).unique ?_
  exact hasSum_single (f := fun c' => coordFunctional hA hβ isCoord c' F • cellCoord β c') c
    (fun c' hc' => by
      rw [coordFunctional_of_disjoint hA hβ isCoord c' hF (hdis hc'.symm), zero_smul])

/-- The coordinate projection on the local basis vectors. -/
theorem coordProjection_basis (c n : ℕ) :
    coordProjection hpfin hA hdis hβ isCoord (β c n) =
      if isCoord c = true ∧ n = 0 then β c n else 0 := by
  rw [coordProjection_apply_of_supported hpfin hA hdis hβ isCoord ((hβ c).supported n),
    coordFunctional_basis]
  by_cases h : isCoord c = true ∧ n = 0
  · rw [if_pos h, if_pos h, one_smul, h.2]
    rfl
  · rw [if_neg h, if_neg h, zero_smul]

/-- The coordinate projection fixes the coordinates of the coordinate cells. -/
theorem coordProjection_cellCoord {c : ℕ} (hc : isCoord c = true) :
    coordProjection hpfin hA hdis hβ isCoord (cellCoord β c) = cellCoord β c := by
  change coordProjection hpfin hA hdis hβ isCoord (β c 0) = β c 0
  rw [coordProjection_basis, if_pos ⟨hc, rfl⟩]

/-- The coordinate projection kills every root. -/
theorem coordProjection_rootVec (j : ℕ) :
    coordProjection hpfin hA hdis hβ isCoord (rootVec β isCoord j) = 0 := by
  rw [rootVec_eq_rootIndex, coordProjection_basis]
  refine if_neg fun h => ?_
  exact rootIndex_ne_zero_of_coord h.1 _ h.2

/-- The coordinate functionals do not see the difference between `F` and `PY F`. -/
theorem coordFunctional_coordProjection (c : ℕ) (F : LebesgueLp p) :
    coordFunctional hA hβ isCoord c (coordProjection hpfin hA hdis hβ isCoord F) =
      coordFunctional hA hβ isCoord c F := by
  have h := (coordFunctional hA hβ isCoord c).hasSum
    (coordProjection_hasSum hpfin hA hdis hβ isCoord F)
  have h2 : HasSum (fun c' => coordFunctional hA hβ isCoord c
      (coordFunctional hA hβ isCoord c' F • cellCoord β c'))
      (coordFunctional hA hβ isCoord c (coordFunctional hA hβ isCoord c F • cellCoord β c)) :=
    hasSum_single c (fun c' hc' => by
      rw [map_smul, coordFunctional_of_disjoint hA hβ isCoord c (cellCoord_supported hβ c')
        (hdis hc'), smul_zero])
  rw [h.unique h2, map_smul, smul_eq_mul]
  change _ * coordFunctional hA hβ isCoord c (β c 0) = _
  rw [coordFunctional_basis]
  by_cases hc : isCoord c = true
  · rw [if_pos ⟨hc, rfl⟩, mul_one]
  · rw [coordFunctional_of_not_coord hA hβ isCoord hc]
    simp

/-- The coordinate projection of a cell part: one term of the series. -/
theorem coordProjection_cellPart (c : ℕ) (F : LebesgueLp p) :
    coordProjection hpfin hA hdis hβ isCoord (lpCellProjection p volume (A c) (hA c) F) =
      coordFunctional hA hβ isCoord c F • cellCoord β c := by
  rw [coordProjection_apply_of_supported hpfin hA hdis hβ isCoord
    (lpCellProjection_supported p volume (A c) (hA c) F)]
  congr 1
  by_cases hc : isCoord c = true
  · rw [coordFunctional_of_coord hA hβ isCoord hc]
    exact ((hβ c).wholeCoord_spec (hA c)).apply_cell 0 F
  · rw [coordFunctional_of_not_coord hA hβ isCoord hc, zero_apply, zero_apply]

/-- The cell part of the coordinate projection: one term of the series. -/
theorem cellPart_coordProjection (c : ℕ) (F : LebesgueLp p) :
    lpCellProjection p volume (A c) (hA c) (coordProjection hpfin hA hdis hβ isCoord F) =
      coordFunctional hA hβ isCoord c F • cellCoord β c := by
  have h := (lpCellProjection p volume (A c) (hA c)).hasSum
    (coordProjection_hasSum hpfin hA hdis hβ isCoord F)
  have h2 : HasSum (fun c' => lpCellProjection p volume (A c) (hA c)
      (coordFunctional hA hβ isCoord c' F • cellCoord β c'))
      (lpCellProjection p volume (A c) (hA c)
        (coordFunctional hA hβ isCoord c F • cellCoord β c)) :=
    hasSum_single c (fun c' hc' => by
      rw [map_smul, lpCellProjection_eq_zero_of_supported (hA c) _ (cellCoord_supported hβ c')
        (hdis hc'), smul_zero])
  rw [h.unique h2, map_smul,
    lpCellProjection_eq_of_supported p volume (A c) (hA c) _ (cellCoord_supported hβ c)]

/-- The coordinate projection commutes with the cell parts. -/
theorem cellPart_coordProjection_comm (c : ℕ) (F : LebesgueLp p) :
    lpCellProjection p volume (A c) (hA c) (coordProjection hpfin hA hdis hβ isCoord F) =
      coordProjection hpfin hA hdis hβ isCoord (lpCellProjection p volume (A c) (hA c) F) := by
  rw [cellPart_coordProjection, coordProjection_cellPart]

/-- The coordinate projection is idempotent. -/
theorem coordProjection_idem (F : LebesgueLp p) :
    coordProjection hpfin hA hdis hβ isCoord (coordProjection hpfin hA hdis hβ isCoord F) =
      coordProjection hpfin hA hdis hβ isCoord F := by
  have hc : coordCoeff hpfin hA hdis hβ isCoord (coordProjection hpfin hA hdis hβ isCoord F) =
      coordCoeff hpfin hA hdis hβ isCoord F := by
    apply lp.ext
    funext c
    exact coordFunctional_coordProjection hpfin hA hdis hβ isCoord c F
  change disjointLpSynthesis (cellCoord β) (coordCoeff hpfin hA hdis hβ isCoord
    (coordProjection hpfin hA hdis hβ isCoord F)) = _
  rw [hc]
  rfl

theorem coordProjection_comp_self :
    (coordProjection hpfin hA hdis hβ isCoord).comp (coordProjection hpfin hA hdis hβ isCoord) =
      coordProjection hpfin hA hdis hβ isCoord :=
  ContinuousLinearMap.ext (coordProjection_idem hpfin hA hdis hβ isCoord)

/-- If `PY F = 0`, every coordinate functional vanishes at `F`. -/
theorem coordFunctional_eq_zero_of_coordProjection_eq_zero {F : LebesgueLp p}
    (hF : coordProjection hpfin hA hdis hβ isCoord F = 0) (c : ℕ) :
    coordFunctional hA hβ isCoord c F = 0 := by
  rw [← coordFunctional_coordProjection hpfin hA hdis hβ isCoord c F, hF, map_zero]

/-! ### Range and kernel -/

/-- The values of the coordinate projection lie in the closed span of the coordinates of
the coordinate cells. -/
theorem coordProjection_mem_closure (F : LebesgueLp p) :
    coordProjection hpfin hA hdis hβ isCoord F ∈
      closure (Submodule.span ℂ (cellCoord β '' {c | isCoord c = true}) : Set (LebesgueLp p)) := by
  refine mem_closure_of_tendsto (coordProjection_hasSum hpfin hA hdis hβ isCoord F)
    (Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : isCoord c = true
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, hc, rfl⟩)
  · rw [coordFunctional_of_not_coord hA hβ isCoord hc, zero_apply, zero_smul]
    exact Submodule.zero_mem _

/-- Fixed points of the coordinate projection lie in the closed span of the coordinates. -/
theorem mem_closure_cellCoord_of_coordProjection_eq_self {y : LebesgueLp p}
    (hy : coordProjection hpfin hA hdis hβ isCoord y = y) :
    y ∈ closure (Submodule.span ℂ (cellCoord β '' {c | isCoord c = true}) :
      Set (LebesgueLp p)) := by
  rw [← hy]
  exact coordProjection_mem_closure hpfin hA hdis hβ isCoord y

/-- The local basis of a cell without coordinate consists of roots; in a coordinate cell
all but the first local basis vector are roots. -/
theorem cellPart_mem_closure_rootVec {F : LebesgueLp p} (c : ℕ)
    (hF : coordFunctional hA hβ isCoord c F = 0) :
    lpCellProjection p volume (A c) (hA c) F ∈
      closure (Submodule.span ℂ (Set.range (rootVec β isCoord)) : Set (LebesgueLp p)) := by
  by_cases hc : isCoord c = true
  · rw [coordFunctional_of_coord hA hβ isCoord hc] at hF
    refine closure_mono (Submodule.span_mono ?_)
      (((hβ c).wholeCoord_spec (hA c)).cellPart_mem_closure_tail hF)
    rintro _ ⟨k, rfl⟩
    exact ⟨Nat.pair c k, rootVec_pair_of_coord β hc k⟩
  · refine closure_mono (Submodule.span_mono ?_)
      (((hβ c).wholeCoord_spec (hA c)).cellPart_mem_closure F)
    rintro _ ⟨k, rfl⟩
    exact ⟨Nat.pair c k, rootVec_pair_of_not_coord β hc k⟩

include hdis in
/-- The kernel of the coordinate projection lies in the closed span of the roots. -/
theorem mem_closure_rootVec_of_coordProjection_eq_zero (hcover : volume (⋃ c, A c)ᶜ = 0)
    {x : LebesgueLp p} (hx : coordProjection hpfin hA hdis hβ isCoord x = 0) :
    x ∈ closure (Submodule.span ℂ (Set.range (rootVec β isCoord)) : Set (LebesgueLp p)) := by
  rw [← Submodule.topologicalClosure_coe]
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (lpCellProjection_hasSum hA hdis hpfin hcover x) (Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact cellPart_mem_closure_rootVec hA hβ isCoord c
    (coordFunctional_eq_zero_of_coordProjection_eq_zero hpfin hA hdis hβ isCoord hx c)

end StructuredBases.PositiveTranslates
