import Lean_Code.PositiveTranslates.Global.LocalBasis
import Lean_Code.PositiveTranslates.Global.BasicSequence
import Lean_Code.PositiveTranslates.Global.CellParts

/-!
# Coordinate functionals of a local basis

A `LocalBasis` of `Lᵖ(A)` has continuous coordinate functionals on `Lᵖ(A)`.  Composing them
with the cell part `F ↦ F·𝟙_A` gives functionals on the whole space.  `LocalCoords`
collects the properties used by the global splitting: biorthogonality, dependence on the
cell part only, the prefix bound and convergence of the expansion to the cell part.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ℕ → LebesgueLp p} {A : Set ℝ} {B : ℝ}

theorem LocalBasis.basis_ne_zero (h : LocalBasis p β A B) (n : ℕ) : β n ≠ 0 := by
  intro h0
  have h1 := h.norm n
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

/-- The prefix constant of a local basis is at least one. -/
theorem LocalBasis.one_le_const (h : LocalBasis p β A B) : 1 ≤ B := by
  have h1 := h.prefix_le 1 (Finsupp.single 0 1)
  simpa [h.norm 0] using h1

theorem LocalBasis.const_nonneg (h : LocalBasis p β A B) : 0 ≤ B :=
  zero_le_one.trans h.one_le_const

/-- The prefix constant of a local basis may be enlarged (so that different cells can be
given one common constant). -/
theorem LocalBasis.mono_const {B' : ℝ} (h : LocalBasis p β A B) (hB : B ≤ B') :
    LocalBasis p β A B' :=
  { h with
    prefix_le := fun N c =>
      (h.prefix_le N c).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) }

/-- `φ n` are the coordinate functionals of the local basis `β` of `Lᵖ(A)`, extended to the
whole space through the cell part `F ↦ F·𝟙_A`. -/
structure LocalCoords (β : ℕ → LebesgueLp p) (A : Set ℝ) (hA : MeasurableSet A) (B : ℝ)
    (φ : ℕ → LebesgueLp p →L[ℂ] ℂ) : Prop where
  biorth : ∀ n m, φ n (β m) = if n = m then 1 else 0
  apply_cell : ∀ n F, φ n (lpCellProjection p volume A hA F) = φ n F
  prefix_le : ∀ N F,
    ‖∑ n ∈ Finset.range N, φ n F • β n‖ ≤ B * ‖lpCellProjection p volume A hA F‖
  tendsto : ∀ F, Tendsto (fun N => ∑ n ∈ Finset.range N, φ n F • β n) atTop
    (𝓝 (lpCellProjection p volume A hA F))

/-- A local basis has whole-space coordinate functionals. -/
theorem LocalBasis.exists_localCoords (h : LocalBasis p β A B) (hA : MeasurableSet A) :
    ∃ φ : ℕ → LebesgueLp p →L[ℂ] ℂ, LocalCoords β A hA B φ := by
  obtain ⟨ψ, hbi, hpre, htend⟩ :=
    exists_coord_closedSpan_of_prefix_bound (𝕜 := ℂ) β h.basis_ne_zero h.prefix_le
  have hmem : ∀ F : LebesgueLp p, SupportedOn F A →
      F ∈ (Submodule.span ℂ (Set.range β)).topologicalClosure := by
    intro F hF
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact h.dense F hF
  have hQ : ∀ F : LebesgueLp p, lpCellProjection p volume A hA F ∈
      (Submodule.span ℂ (Set.range β)).topologicalClosure :=
    fun F => hmem _ (lpCellProjection_supported p volume A hA F)
  refine ⟨fun n => (ψ n).comp ((lpCellProjection p volume A hA).codRestrict _ hQ), ?_, ?_, ?_, ?_⟩
  · intro n m
    exact hbi n m _ (lpCellProjection_eq_of_supported p volume A hA _ (h.supported m))
  · intro n F
    change ψ n _ = ψ n _
    congr 1
    exact Subtype.ext (lpCellProjection_idem hA F)
  · intro N F
    exact hpre N ((lpCellProjection p volume A hA).codRestrict _ hQ F)
  · intro F
    exact htend ((lpCellProjection p volume A hA).codRestrict _ hQ F)

/-- A choice of whole-space coordinate functionals of a local basis. -/
def LocalBasis.wholeCoord (h : LocalBasis p β A B) (hA : MeasurableSet A) :
    ℕ → LebesgueLp p →L[ℂ] ℂ :=
  Classical.choose (h.exists_localCoords hA)

theorem LocalBasis.wholeCoord_spec (h : LocalBasis p β A B) (hA : MeasurableSet A) :
    LocalCoords β A hA B (h.wholeCoord hA) :=
  Classical.choose_spec (h.exists_localCoords hA)

/-- The prefix operator `F ↦ ∑_{n<N} φ n F • β n` of a system of coordinate functionals. -/
def coordPrefix (β : ℕ → LebesgueLp p) (φ : ℕ → LebesgueLp p →L[ℂ] ℂ) (N : ℕ) :
    LebesgueLp p →L[ℂ] LebesgueLp p :=
  ∑ n ∈ Finset.range N, (φ n).smulRight (β n)

theorem coordPrefix_apply (β : ℕ → LebesgueLp p) (φ : ℕ → LebesgueLp p →L[ℂ] ℂ) (N : ℕ)
    (F : LebesgueLp p) : coordPrefix β φ N F = ∑ n ∈ Finset.range N, φ n F • β n := by
  simp [coordPrefix]

namespace LocalCoords

variable {hA : MeasurableSet A} {φ : ℕ → LebesgueLp p →L[ℂ] ℂ}

theorem apply_eq_zero (hφ : LocalCoords β A hA B φ) (n : ℕ) {F : LebesgueLp p}
    (hF : lpCellProjection p volume A hA F = 0) : φ n F = 0 := by
  rw [← hφ.apply_cell n F, hF, map_zero]

/-- The coordinates of a class supported off the cell vanish. -/
theorem apply_of_disjoint (hφ : LocalCoords β A hA B φ) (n : ℕ) {F : LebesgueLp p} {s : Set ℝ}
    (hF : SupportedOn F s) (hdis : Disjoint s A) : φ n F = 0 :=
  hφ.apply_eq_zero n (lpCellProjection_eq_zero_of_supported hA F hF hdis)

/-- The local prefix of a basis vector. -/
theorem prefix_basis (hφ : LocalCoords β A hA B φ) (N m : ℕ) :
    ∑ n ∈ Finset.range N, φ n (β m) • β n = if m < N then β m else 0 := by
  simp only [hφ.biorth, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' (Finset.range N) m (fun n => β n)]
  simp only [Finset.mem_range]

/-- The first coordinate functional is bounded by the prefix constant. -/
theorem norm_coord_zero_le (hφ : LocalCoords β A hA B φ) (h0 : ‖β 0‖ = 1) (F : LebesgueLp p) :
    ‖φ 0 F‖ ≤ B * ‖lpCellProjection p volume A hA F‖ := by
  have h := hφ.prefix_le 1 F
  simpa [norm_smul, h0] using h

/-- If the first coordinate of `F` vanishes, the cell part of `F` lies in the closed span of
the remaining basis vectors. -/
theorem cellPart_mem_closure_tail (hφ : LocalCoords β A hA B φ) {F : LebesgueLp p}
    (h0 : φ 0 F = 0) :
    lpCellProjection p volume A hA F ∈
      closure (Submodule.span ℂ (Set.range fun k => β (k + 1)) : Set (LebesgueLp p)) := by
  refine mem_closure_of_tendsto (hφ.tendsto F) (Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun n _ => ?_
  rcases n with _ | k
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The cell part of any class lies in the closed span of the local basis. -/
theorem cellPart_mem_closure (hφ : LocalCoords β A hA B φ) (F : LebesgueLp p) :
    lpCellProjection p volume A hA F ∈
      closure (Submodule.span ℂ (Set.range β) : Set (LebesgueLp p)) := by
  refine mem_closure_of_tendsto (hφ.tendsto F) (Eventually.of_forall fun N => ?_)
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

end LocalCoords

end StructuredBases.PositiveTranslates
