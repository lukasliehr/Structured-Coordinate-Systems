import Lean_Code.PositiveTranslates.Global.CoordinateProjection
import Lean_Code.PositiveTranslates.Global.RootPrefix

/-!
# The global splitting into coordinates and roots

**Data.** An exponent `1 ≤ p < ∞`; measurable pairwise disjoint cells `A c ⊆ ℝ` (`c : ℕ`)
covering `ℝ` up to a null set; on every cell a `LocalBasis p (β c) (A c) B` (the same `B`
for all cells); a flag `isCoord : ℕ → Bool`.

**Definitions.** `cellCoord β c = β c 0` and
`rootVec β isCoord j = β c (if isCoord c then k + 1 else k)`, `(c, k) = Nat.unpair j`
(file `Roots.lean`).

**Result.** `GlobalSplitting p A hA β isCoord B PY` collects the conclusions: `PY` is a
projection of norm at most `B` which fixes the coordinates of the coordinate cells and kills
the roots; its fixed points lie in the closed span of the coordinates and its kernel in the
closed span of the roots; the roots satisfy the prefix inequality with constant `B`; the
coordinates are isometrically the unit vectors of `ℓᵖ`; and every class is the sum of its
cell parts.

* `exists_globalSplitting` (cells covering `ℝ` up to a null set) and
  `exists_globalSplitting_of_iUnion_eq_univ` (cells covering `ℝ`) produce such a `PY`;
* `coordProjection_globalSplitting` says that the explicit operator `coordProjection`
  (`PY F = ∑_{c coordinate cell} φ_c(F·𝟙_{A c}) • β c 0`) is one;
* `GlobalSplitting.unique`: there is only one;
* `GlobalSplitting.apply_eq_self_iff`, `GlobalSplitting.apply_eq_zero_iff`,
  `GlobalSplitting.isCompl`, `GlobalSplitting.exists_root_basis`: range and kernel of `PY` are
  exactly the closed spans of the coordinates and of the roots, they are complementary, and
  the roots are a Schauder basis of their closed span with constant at most `B`.

The hypothesis `1 ≤ B` is not needed: it follows from `LocalBasis` (`GlobalSplitting.one_le`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

/-- The conclusions of the global splitting for the operator `PY`.

Here `lpCellProjection p volume (A c) (hA c) F` is the cell part `F·𝟙_{A c}` of `F`; by
`lpCellProjection_ae` it is a.e. equal to `(A c).indicator F`.  The numbers in the field
descriptions refer to the items of the splitting statement; the fields marked "extra" are
additional facts about the same operator. -/
structure GlobalSplitting (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℕ → Set ℝ)
    (hA : ∀ c, MeasurableSet (A c)) (β : ℕ → ℕ → LebesgueLp p) (isCoord : ℕ → Bool) (B : ℝ)
    (PY : LebesgueLp p →L[ℂ] LebesgueLp p) : Prop where
  /-- (1) `PY` is a projection. -/
  comp_self : PY.comp PY = PY
  /-- (1) `PY` has norm at most the prefix constant. -/
  norm_le : ‖PY‖ ≤ B
  /-- (1) `PY` fixes the coordinate of every coordinate cell. -/
  apply_coord : ∀ c, isCoord c = true → PY (cellCoord β c) = cellCoord β c
  /-- (1) `PY` kills every root. -/
  apply_root : ∀ j, PY (rootVec β isCoord j) = 0
  /-- (2) The fixed points of `PY` lie in the closed span of the coordinates. -/
  mem_coord_closure : ∀ y : LebesgueLp p, PY y = y →
    y ∈ closure (Submodule.span ℂ (cellCoord β '' {c | isCoord c = true}) : Set (LebesgueLp p))
  /-- (3) The kernel of `PY` lies in the closed span of the roots. -/
  mem_root_closure : ∀ x : LebesgueLp p, PY x = 0 →
    x ∈ closure (Submodule.span ℂ (Set.range (rootVec β isCoord)) : Set (LebesgueLp p))
  /-- (4) The roots satisfy the prefix inequality with the same constant. -/
  root_prefix_le : ∀ (m : ℕ) (t : ℕ →₀ ℂ),
    ‖∑ j ∈ Finset.range m, t j • rootVec β isCoord j‖ ≤
      B * ‖Finsupp.linearCombination ℂ (rootVec β isCoord) t‖
  /-- (5) The roots are unit vectors. -/
  root_norm : ∀ j, ‖rootVec β isCoord j‖ = 1
  /-- (5) The roots are non-negative. -/
  root_nonneg : ∀ j, IsNonneg (rootVec β isCoord j)
  /-- (5) The roots are compactly supported step functions. -/
  root_step : ∀ j, IsCompactStep p (rootVec β isCoord j)
  /-- (5) Every root lives in its cell. -/
  root_supported : ∀ j, SupportedOn (rootVec β isCoord j) (A (Nat.unpair j).1)
  /-- (5) The coordinates are unit vectors. -/
  coord_norm : ∀ c, ‖cellCoord β c‖ = 1
  /-- (5) The coordinates are non-negative. -/
  coord_nonneg : ∀ c, IsNonneg (cellCoord β c)
  /-- (5) The coordinates are compactly supported step functions. -/
  coord_step : ∀ c, IsCompactStep p (cellCoord β c)
  /-- (5) Every coordinate lives in its cell. -/
  coord_supported : ∀ c, SupportedOn (cellCoord β c) (A c)
  /-- (6) The `ℓᵖ` identity for the coordinates. -/
  coord_norm_rpow : ∀ (s : Finset ℕ) (a : ℕ → ℂ),
    ‖∑ c ∈ s, a c • cellCoord β c‖ ^ p.toReal = ∑ c ∈ s, ‖a c‖ ^ p.toReal
  /-- (7) Every class is the `Lᵖ` limit of the partial sums of its cell parts. -/
  cell_tendsto : ∀ F : LebesgueLp p,
    Tendsto (fun n => ∑ c ∈ Finset.range n, lpCellProjection p volume (A c) (hA c) F) atTop (𝓝 F)
  /-- (7) The `p`-th powers of the norms of the cell parts sum to `‖F‖ᵖ`. -/
  cell_norm_rpow : ∀ F : LebesgueLp p,
    HasSum (fun c => ‖lpCellProjection p volume (A c) (hA c) F‖ ^ p.toReal) (‖F‖ ^ p.toReal)
  /-- (extra) The prefix constant is at least one. -/
  one_le : 1 ≤ B
  /-- (extra) `PY` on all local basis vectors. -/
  apply_basis : ∀ c n, PY (β c n) = if isCoord c = true ∧ n = 0 then β c n else 0
  /-- (extra) `PY` commutes with the cell parts. -/
  cell_comm : ∀ (c : ℕ) (F : LebesgueLp p),
    lpCellProjection p volume (A c) (hA c) (PY F) = PY (lpCellProjection p volume (A c) (hA c) F)
  /-- (extra) Every class is the unconditional sum of its cell parts. -/
  cell_hasSum : ∀ F : LebesgueLp p,
    HasSum (fun c => lpCellProjection p volume (A c) (hA c) F) F
  /-- (extra) The expansion of `PY F` in the coordinates, with `ℓᵖ` coefficients carried by
  the coordinate cells and bounded cell by cell. -/
  coord_expansion : ∀ F : LebesgueLp p, ∃ a : ℕ → ℂ,
    (∀ c, ¬ isCoord c = true → a c = 0) ∧
    (∀ c, ‖a c‖ ≤ B * ‖lpCellProjection p volume (A c) (hA c) F‖) ∧
    (∀ c, lpCellProjection p volume (A c) (hA c) (PY F) = a c • cellCoord β c) ∧
    HasSum (fun c => a c • cellCoord β c) (PY F) ∧
    HasSum (fun c => ‖a c‖ ^ p.toReal) (‖PY F‖ ^ p.toReal)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpfin : p ≠ ∞) {A : ℕ → Set ℝ}
  (hA : ∀ c, MeasurableSet (A c)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
  {β : ℕ → ℕ → LebesgueLp p} {B : ℝ} (hβ : ∀ c, LocalBasis p (β c) (A c) B)
  (isCoord : ℕ → Bool)

/-- **Global splitting.**  The coordinate projection `coordProjection` has all the
properties collected in `GlobalSplitting`.  The cells need to cover `ℝ` only up to a null
set. -/
theorem coordProjection_globalSplitting (hcover : volume (⋃ c, A c)ᶜ = 0) :
    GlobalSplitting p A hA β isCoord B (coordProjection hpfin hA hdis hβ isCoord) where
  comp_self := coordProjection_comp_self hpfin hA hdis hβ isCoord
  norm_le := norm_coordProjection_le hpfin hA hdis hβ isCoord
  apply_coord := fun _ hc => coordProjection_cellCoord hpfin hA hdis hβ isCoord hc
  apply_root := coordProjection_rootVec hpfin hA hdis hβ isCoord
  mem_coord_closure := fun _ hy =>
    mem_closure_cellCoord_of_coordProjection_eq_self hpfin hA hdis hβ isCoord hy
  mem_root_closure := fun _ hx =>
    mem_closure_rootVec_of_coordProjection_eq_zero hpfin hA hdis hβ isCoord hcover hx
  root_prefix_le := rootVec_prefix_le hpfin hA hdis hβ isCoord hcover
  root_norm := rootVec_norm hβ isCoord
  root_nonneg := rootVec_nonneg hβ isCoord
  root_step := rootVec_step hβ isCoord
  root_supported := rootVec_supported hβ isCoord
  coord_norm := cellCoord_norm hβ
  coord_nonneg := cellCoord_nonneg hβ
  coord_step := cellCoord_step hβ
  coord_supported := cellCoord_supported hβ
  coord_norm_rpow := cellCoord_sum_norm_rpow hβ hdis hpfin
  cell_tendsto := lpCellProjection_tendsto hA hdis hpfin hcover
  cell_norm_rpow := lpCellProjection_norm_rpow_hasSum hA hdis hpfin hcover
  one_le := (hβ 0).one_le_const
  apply_basis := coordProjection_basis hpfin hA hdis hβ isCoord
  cell_comm := cellPart_coordProjection_comm hpfin hA hdis hβ isCoord
  cell_hasSum := lpCellProjection_hasSum hA hdis hpfin hcover
  coord_expansion := fun F =>
    ⟨fun c => coordFunctional hA hβ isCoord c F,
      fun c hc => by
        change coordFunctional hA hβ isCoord c F = 0
        rw [coordFunctional_of_not_coord hA hβ isCoord hc, zero_apply],
      fun c => norm_coordFunctional_le hA hβ isCoord c F,
      fun c => cellPart_coordProjection hpfin hA hdis hβ isCoord c F,
      coordProjection_hasSum hpfin hA hdis hβ isCoord F,
      norm_coordProjection_rpow_hasSum hpfin hA hdis hβ isCoord F⟩

/-- **Global splitting, existence form.**  Hypotheses: `p ≠ ∞`; measurable, pairwise
disjoint cells covering `ℝ` up to a null set; a local basis with prefix constant `B` on
every cell. -/
theorem exists_globalSplitting (hpfin : p ≠ ∞) {A : ℕ → Set ℝ}
    (hA : ∀ c, MeasurableSet (A c)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : volume (⋃ c, A c)ᶜ = 0)
    {β : ℕ → ℕ → LebesgueLp p} {B : ℝ} (hβ : ∀ c, LocalBasis p (β c) (A c) B)
    (isCoord : ℕ → Bool) :
    ∃ PY : LebesgueLp p →L[ℂ] LebesgueLp p, GlobalSplitting p A hA β isCoord B PY :=
  ⟨coordProjection hpfin hA hdis hβ isCoord,
    coordProjection_globalSplitting hpfin hA hdis hβ isCoord hcover⟩

/-- **Global splitting** for cells covering all of `ℝ`. -/
theorem exists_globalSplitting_of_iUnion_eq_univ (hpfin : p ≠ ∞) {A : ℕ → Set ℝ}
    (hA : ∀ c, MeasurableSet (A c)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : ⋃ c, A c = Set.univ)
    {β : ℕ → ℕ → LebesgueLp p} {B : ℝ} (hβ : ∀ c, LocalBasis p (β c) (A c) B)
    (isCoord : ℕ → Bool) :
    ∃ PY : LebesgueLp p →L[ℂ] LebesgueLp p, GlobalSplitting p A hA β isCoord B PY :=
  exists_globalSplitting hpfin hA hdis (by rw [hcover, Set.compl_univ, measure_empty]) hβ isCoord

/-- **Global splitting, as one statement.**  The items (1)–(7) written out, with `β c 0` in
place of `cellCoord β c`.  It is a restatement of `exists_globalSplitting`; the structure
`GlobalSplitting` is more convenient to use and contains more. -/
theorem exists_globalSplitting_unbundled (hpfin : p ≠ ∞) {A : ℕ → Set ℝ}
    (hA : ∀ c, MeasurableSet (A c)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : volume (⋃ c, A c)ᶜ = 0)
    {β : ℕ → ℕ → LebesgueLp p} {B : ℝ} (hβ : ∀ c, LocalBasis p (β c) (A c) B)
    (isCoord : ℕ → Bool) :
    ∃ PY : LebesgueLp p →L[ℂ] LebesgueLp p,
      -- (1) a projection of norm at most `B` fixing the coordinates and killing the roots
      PY.comp PY = PY ∧ ‖PY‖ ≤ B ∧
      (∀ c, isCoord c = true → PY (β c 0) = β c 0) ∧
      (∀ j, PY (rootVec β isCoord j) = 0) ∧
      -- (2) its fixed points lie in the closed span of the coordinates
      (∀ y, PY y = y → y ∈ closure (Submodule.span ℂ {x | ∃ c, isCoord c = true ∧ β c 0 = x} :
        Set (LebesgueLp p))) ∧
      -- (3) its kernel lies in the closed span of the roots
      (∀ x, PY x = 0 → x ∈ closure (Submodule.span ℂ (Set.range (rootVec β isCoord)) :
        Set (LebesgueLp p))) ∧
      -- (4) the prefix inequality for the roots
      (∀ (m : ℕ) (t : ℕ →₀ ℂ), ‖∑ j ∈ Finset.range m, t j • rootVec β isCoord j‖ ≤
        B * ‖Finsupp.linearCombination ℂ (rootVec β isCoord) t‖) ∧
      -- (5) roots and coordinates are normalized, non-negative, compact-step, and live in
      -- their cells
      (∀ j, ‖rootVec β isCoord j‖ = 1 ∧ IsNonneg (rootVec β isCoord j) ∧
        IsCompactStep p (rootVec β isCoord j) ∧
        SupportedOn (rootVec β isCoord j) (A (Nat.unpair j).1)) ∧
      (∀ c, ‖β c 0‖ = 1 ∧ IsNonneg (β c 0) ∧ IsCompactStep p (β c 0) ∧
        SupportedOn (β c 0) (A c)) ∧
      -- (6) the `ℓᵖ` identity for the coordinates
      (∀ a : ℕ →₀ ℂ,
        ‖∑ c ∈ a.support, a c • β c 0‖ ^ p.toReal = ∑ c ∈ a.support, ‖a c‖ ^ p.toReal) ∧
      -- (7) every class is the limit of the partial sums of its cell parts
      (∀ F : LebesgueLp p, Tendsto (fun n => ∑ c ∈ Finset.range n,
        lpCellProjection p volume (A c) (hA c) F) atTop (𝓝 F)) ∧
      (∀ F : LebesgueLp p, HasSum
        (fun c => ‖lpCellProjection p volume (A c) (hA c) F‖ ^ p.toReal) (‖F‖ ^ p.toReal)) := by
  obtain ⟨PY, h⟩ := exists_globalSplitting hpfin hA hdis hcover hβ isCoord
  exact ⟨PY, h.comp_self, h.norm_le, h.apply_coord, h.apply_root, h.mem_coord_closure,
    h.mem_root_closure, h.root_prefix_le,
    fun j => ⟨h.root_norm j, h.root_nonneg j, h.root_step j, h.root_supported j⟩,
    fun c => ⟨h.coord_norm c, h.coord_nonneg c, h.coord_step c, h.coord_supported c⟩,
    fun a => h.coord_norm_rpow a.support a, h.cell_tendsto, h.cell_norm_rpow⟩

/-! ### Consequences -/

namespace GlobalSplitting

variable {hA} {isCoord} {PY : LebesgueLp p →L[ℂ] LebesgueLp p}
  (h : GlobalSplitting p A hA β isCoord B PY)

include h

theorem apply_apply (F : LebesgueLp p) : PY (PY F) = PY F :=
  DFunLike.congr_fun h.comp_self F

theorem norm_apply_le (F : LebesgueLp p) : ‖PY F‖ ≤ B * ‖F‖ :=
  (PY.le_opNorm F).trans (mul_le_mul_of_nonneg_right h.norm_le (norm_nonneg F))

/-- The complementary projection `1 - PY` has norm at most `1 + B`. -/
theorem norm_id_sub_le : ‖ContinuousLinearMap.id ℂ (LebesgueLp p) - PY‖ ≤ 1 + B :=
  (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le h.norm_le)

theorem apply_mem_coord_closure (F : LebesgueLp p) :
    PY F ∈ closure (Submodule.span ℂ (cellCoord β '' {c | isCoord c = true}) :
      Set (LebesgueLp p)) :=
  h.mem_coord_closure _ (h.apply_apply F)

theorem sub_apply_mem_root_closure (F : LebesgueLp p) :
    F - PY F ∈ closure (Submodule.span ℂ (Set.range (rootVec β isCoord)) : Set (LebesgueLp p)) :=
  h.mem_root_closure _ (by rw [map_sub, h.apply_apply, sub_self])

/-- The fixed points of `PY` are exactly the closed span of the coordinates. -/
theorem apply_eq_self_iff (y : LebesgueLp p) :
    PY y = y ↔ y ∈ closure (Submodule.span ℂ (cellCoord β '' {c | isCoord c = true}) :
      Set (LebesgueLp p)) := by
  refine ⟨h.mem_coord_closure y, fun hy => ?_⟩
  have hle : Submodule.span ℂ (cellCoord β '' {c | isCoord c = true}) ≤
      LinearMap.eqLocus (PY : LebesgueLp p →ₗ[ℂ] LebesgueLp p) LinearMap.id := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, hc, rfl⟩
    exact h.apply_coord c hc
  have hclosed : IsClosed {z : LebesgueLp p | PY z = z} := isClosed_eq PY.continuous continuous_id
  exact closure_minimal (fun z hz => hle hz) hclosed hy

/-- The kernel of `PY` is exactly the closed span of the roots. -/
theorem apply_eq_zero_iff (x : LebesgueLp p) :
    PY x = 0 ↔ x ∈ closure (Submodule.span ℂ (Set.range (rootVec β isCoord)) :
      Set (LebesgueLp p)) := by
  refine ⟨h.mem_root_closure x, fun hx => ?_⟩
  have hle : Submodule.span ℂ (Set.range (rootVec β isCoord)) ≤
      LinearMap.ker (PY : LebesgueLp p →ₗ[ℂ] LebesgueLp p) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact h.apply_root j
  have hclosed : IsClosed {z : LebesgueLp p | PY z = 0} :=
    isClosed_eq PY.continuous continuous_const
  exact closure_minimal (fun z hz => hle hz) hclosed hx

/-- The `p`-th power of the norm is the sum of the `p`-th powers of the norms of the cell
parts. -/
theorem norm_rpow_eq_tsum (F : LebesgueLp p) :
    ‖F‖ ^ p.toReal = ∑' c, ‖lpCellProjection p volume (A c) (hA c) F‖ ^ p.toReal :=
  (h.cell_norm_rpow F).tsum_eq.symm

/-- The `ℓᵖ` identity for the coordinates, for finitely supported coefficient families. -/
theorem coord_linearCombination_norm_rpow (a : ℕ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (cellCoord β) a‖ ^ p.toReal =
      ∑ c ∈ a.support, ‖a c‖ ^ p.toReal := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact h.coord_norm_rpow a.support a

/-- The whole space is the direct sum of the closed span of the coordinates and the closed
span of the roots. -/
theorem isCompl :
    IsCompl (Submodule.span ℂ (cellCoord β '' {c | isCoord c = true})).topologicalClosure
      (Submodule.span ℂ (Set.range (rootVec β isCoord))).topologicalClosure := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx hx'
    rw [← (h.apply_eq_self_iff x).mpr hx, (h.apply_eq_zero_iff x).mpr hx']
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro F
    refine ⟨PY F, F - PY F, ?_, ?_, add_sub_cancel _ _⟩
    · rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact h.apply_mem_coord_closure F
    · rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact h.sub_apply_mem_root_closure F

omit h in
/-- The operator of a global splitting is unique: it is the projection onto the closed span
of the coordinates along the closed span of the roots. -/
theorem unique {PY PY' : LebesgueLp p →L[ℂ] LebesgueLp p}
    (h : GlobalSplitting p A hA β isCoord B PY) (h' : GlobalSplitting p A hA β isCoord B PY') :
    PY = PY' := by
  ext1 F
  have h1 : PY' (PY F) = PY F := (h'.apply_eq_self_iff _).mpr (h.apply_mem_coord_closure F)
  have h2 : PY' (F - PY F) = 0 := (h'.apply_eq_zero_iff _).mpr (h.sub_apply_mem_root_closure F)
  rw [map_sub, h1, sub_eq_zero] at h2
  exact h2.symm

/-- The roots form a Schauder basis of their closed span, with basis constant at most `B`. -/
theorem exists_root_basis :
    ∃ b : SchauderBasis ℂ (Submodule.span ℂ (Set.range (rootVec β isCoord))).topologicalClosure,
      (∀ j, (b j : LebesgueLp p) = rootVec β isCoord j) ∧ ∀ N, ‖b.proj N‖ ≤ B :=
  exists_schauderBasis_closedSpan_of_prefix_bound (rootVec β isCoord)
    (fun j hj => by
      have h1 := h.root_norm j
      rw [hj, norm_zero] at h1
      exact zero_ne_one h1)
    h.root_prefix_le

end GlobalSplitting

end StructuredBases.PositiveTranslates
