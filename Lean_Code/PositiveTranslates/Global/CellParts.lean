import Lean_Code.SchauderTranslates.Lp.WholeCellFunctional

/-!
# Cell parts of an `Lᵖ` class

For a sequence of pairwise disjoint measurable cells `A c` the cell parts
`F ↦ F·𝟙_{A c}` (`lpCellProjection`) are mutually orthogonal norm-one projections.  The
`p`-th powers of the norms of the parts add up, and if the cells cover the space up to a
null set, every `F` is the unconditional sum of its parts.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {α : Type*} [MeasurableSpace α] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- The exponent of a normed `Lᵖ` space is not zero. -/
theorem lpExponent_ne_zero (p : ℝ≥0∞) [h : Fact (1 ≤ p)] : p ≠ 0 :=
  (zero_lt_one.trans_le h.out).ne'

theorem lpExponent_toReal_pos (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpfin : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (lpExponent_ne_zero p) hpfin

/-- A class supported off a cell has zero part in that cell. -/
theorem lpCellProjection_eq_zero_of_supported {A s : Set α} (hs : MeasurableSet s)
    (F : Lp ℂ p μ) (hF : SupportedOn F A) (hdis : Disjoint A s) :
    lpCellProjection p μ s hs F = 0 := by
  change lpExtendByZeroIsometry p μ s hs (lpRestriction p μ s F) = 0
  rw [lpRestriction_eq_zero_of_supported p μ hs F hF hdis, map_zero]

/-- Cell parts are idempotent. -/
theorem lpCellProjection_idem {s : Set α} (hs : MeasurableSet s) (F : Lp ℂ p μ) :
    lpCellProjection p μ s hs (lpCellProjection p μ s hs F) = lpCellProjection p μ s hs F :=
  lpCellProjection_eq_of_supported p μ s hs _ (lpCellProjection_supported p μ s hs F)

/-- A class whose part in `s` vanishes is supported off `s`. -/
theorem supportedOn_compl_of_lpCellProjection_eq_zero {s : Set α} (hs : MeasurableSet s)
    (F : Lp ℂ p μ) (h : lpCellProjection p μ s hs F = 0) : SupportedOn F sᶜ := by
  have h0 : (lpCellProjection p μ s hs F : α → ℂ) =ᵐ[μ] 0 := by
    rw [h]
    exact Lp.coeFn_zero ℂ p μ
  filter_upwards [lpCellProjection_ae p μ s hs F, h0] with x hx hz hxs
  have hxs' : x ∈ s := by simpa using hxs
  rw [hz, Set.indicator_of_mem hxs'] at hx
  exact hx.symm

omit [Fact (1 ≤ p)] in
/-- Complex scalar multiples of a.e. disjoint classes are a.e. disjoint. -/
theorem ae_disjoint_complex_smul {F G : Lp ℂ p μ} (a b : ℂ)
    (h : ∀ᵐ x ∂μ, F x = 0 ∨ G x = 0) : ∀ᵐ x ∂μ, (a • F) x = 0 ∨ (b • G) x = 0 := by
  filter_upwards [h, Lp.coeFn_smul a F, Lp.coeFn_smul b G] with x hx ha hb
  rcases hx with hx | hx
  · left
    rw [ha, Pi.smul_apply, hx, smul_zero]
  · right
    rw [hb, Pi.smul_apply, hx, smul_zero]

section Cells

variable {A : ℕ → Set α} (hA : ∀ c, MeasurableSet (A c))
  (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))

include hdis in
/-- Parts in different cells annihilate each other. -/
theorem lpCellProjection_comp_of_ne {i j : ℕ} (hij : i ≠ j) (F : Lp ℂ p μ) :
    lpCellProjection p μ (A i) (hA i) (lpCellProjection p μ (A j) (hA j) F) = 0 :=
  lpCellProjection_eq_zero_of_supported (hA i) _
    (lpCellProjection_supported p μ (A j) (hA j) F) (hdis hij.symm)

include hdis in
/-- The parts of one class in different cells are a.e. disjoint. -/
theorem lpCellProjection_ae_disjoint {i j : ℕ} (hij : i ≠ j) (F G : Lp ℂ p μ) :
    ∀ᵐ x ∂μ, lpCellProjection p μ (A i) (hA i) F x = 0 ∨
      lpCellProjection p μ (A j) (hA j) G x = 0 :=
  (lpCellProjection_supported p μ (A i) (hA i) F).ae_disjoint
    (lpCellProjection_supported p μ (A j) (hA j) G) (hdis hij)

include hdis in
/-- The remainder after removing finitely many cell parts is a.e. disjoint from each of
the removed parts. -/
theorem cellRemainder_ae_disjoint (s : Finset ℕ) (F : Lp ℂ p μ) {c : ℕ} (hc : c ∈ s) :
    ∀ᵐ x ∂μ, (F - ∑ i ∈ s, lpCellProjection p μ (A i) (hA i) F) x = 0 ∨
      lpCellProjection p μ (A c) (hA c) F x = 0 := by
  have hpart : lpCellProjection p μ (A c) (hA c)
      (F - ∑ i ∈ s, lpCellProjection p μ (A i) (hA i) F) = 0 := by
    rw [map_sub, map_sum, Finset.sum_eq_single c, lpCellProjection_idem, sub_self]
    · intro i _ hic
      exact lpCellProjection_comp_of_ne hA hdis (Ne.symm hic) F
    · intro hcs
      exact absurd hc hcs
  have hsupp := supportedOn_compl_of_lpCellProjection_eq_zero (hA c) _ hpart
  exact hsupp.ae_disjoint (lpCellProjection_supported p μ (A c) (hA c) F) disjoint_compl_left

include hdis in
/-- Pythagoras in `Lᵖ` for finitely many cells and the remainder. -/
theorem norm_rpow_eq_cellRemainder_add_sum (hpfin : p ≠ ∞) (s : Finset ℕ) (F : Lp ℂ p μ) :
    ‖F‖ ^ p.toReal = ‖F - ∑ i ∈ s, lpCellProjection p μ (A i) (hA i) F‖ ^ p.toReal +
      ∑ i ∈ s, ‖lpCellProjection p μ (A i) (hA i) F‖ ^ p.toReal := by
  have hp0 := lpExponent_ne_zero p
  rw [← norm_finset_sum_rpow s (fun i => lpCellProjection p μ (A i) (hA i) F) hp0 hpfin
      (fun i _ j _ hij => lpCellProjection_ae_disjoint hA hdis hij F F),
    ← norm_add_rpow_of_ae_disjoint _ _ hp0 hpfin
      (ae_disjoint_finset_sum s _ _ (fun c hc => cellRemainder_ae_disjoint hA hdis s F hc)),
    sub_add_cancel]

include hdis in
/-- The cell parts of finitely many cells use at most the whole `p`-th power norm. -/
theorem sum_norm_lpCellProjection_rpow_le (hpfin : p ≠ ∞) (s : Finset ℕ) (F : Lp ℂ p μ) :
    ∑ i ∈ s, ‖lpCellProjection p μ (A i) (hA i) F‖ ^ p.toReal ≤ ‖F‖ ^ p.toReal := by
  rw [norm_rpow_eq_cellRemainder_add_sum hA hdis hpfin s F]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

include hdis in
/-- If the cells cover the space up to a null set, the `p`-th powers of the norms of the
cell parts sum to the `p`-th power of the norm. -/
theorem lpCellProjection_norm_rpow_hasSum (hpfin : p ≠ ∞) (hcover : μ (⋃ c, A c)ᶜ = 0)
    (F : Lp ℂ p μ) :
    HasSum (fun c => ‖lpCellProjection p μ (A c) (hA c) F‖ ^ p.toReal) (‖F‖ ^ p.toReal) := by
  have hp0 := lpExponent_ne_zero p
  have h := hasSum_integral_iUnion hA hdis (integrable_norm_rpow F hp0 hpfin).integrableOn
  have hres : μ.restrict (⋃ c, A c) = μ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hcover)
  rw [hres, integral_norm_rpow F hp0 hpfin] at h
  have he : (fun c => ‖lpCellProjection p μ (A c) (hA c) F‖ ^ p.toReal) =
      (fun c => ∫ x in A c, ‖F x‖ ^ p.toReal ∂μ) := by
    funext c
    rw [lpCellProjection_norm_eq, lpRestriction_norm_rpow p μ (A c) hp0 hpfin F]
  rw [he]
  exact h

include hdis in
/-- If the cells cover the space up to a null set, every class is the unconditional sum of
its cell parts. -/
theorem lpCellProjection_hasSum (hpfin : p ≠ ∞) (hcover : μ (⋃ c, A c)ᶜ = 0)
    (F : Lp ℂ p μ) : HasSum (fun c => lpCellProjection p μ (A c) (hA c) F) F := by
  have hpR := lpExponent_toReal_pos p hpfin
  have hsum : Tendsto
      (fun s : Finset ℕ => ∑ c ∈ s, ‖lpCellProjection p μ (A c) (hA c) F‖ ^ p.toReal)
      atTop (𝓝 (‖F‖ ^ p.toReal)) := lpCellProjection_norm_rpow_hasSum hA hdis hpfin hcover F
  have hrem : Tendsto
      (fun s : Finset ℕ => ‖F - ∑ c ∈ s, lpCellProjection p μ (A c) (hA c) F‖ ^ p.toReal)
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ‖F‖ ^ p.toReal)).sub hsum
    rw [sub_self] at h
    refine h.congr fun s => ?_
    rw [norm_rpow_eq_cellRemainder_add_sum hA hdis hpfin s F, add_sub_cancel_right]
  have hroot := hrem.rpow_const (p := p.toReal⁻¹) (Or.inr (inv_nonneg.mpr hpR.le))
  rw [Real.zero_rpow (inv_ne_zero hpR.ne')] at hroot
  change Tendsto (fun s : Finset ℕ => ∑ c ∈ s, lpCellProjection p μ (A c) (hA c) F)
    atTop (𝓝 F)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hroot.congr fun s => ?_
  rw [Real.rpow_rpow_inv (norm_nonneg _) hpR.ne', norm_sub_rev]

include hdis in
/-- Ordered form of `lpCellProjection_hasSum`. -/
theorem lpCellProjection_tendsto (hpfin : p ≠ ∞) (hcover : μ (⋃ c, A c)ᶜ = 0)
    (F : Lp ℂ p μ) :
    Tendsto (fun n => ∑ c ∈ Finset.range n, lpCellProjection p μ (A c) (hA c) F) atTop (𝓝 F) :=
  (lpCellProjection_hasSum hA hdis hpfin hcover F).tendsto_sum_nat

end Cells

end StructuredBases.PositiveTranslates
