import Lean_Code.PositiveTranslates.Forest.Defs

/-!
# Tools for users of the positive forest

This file contains statements which are not needed for the proof of the main theorem but
help to construct a `PositiveForest` and to use its sequence.

Verifying the hypotheses:

* `lr_norm_of_family`: the field `lr_norm` for `e0 = g (φ none)`, `coord s i = g (φ (some ⟨s, i⟩))`,
  where `g : ι → Z` is any family satisfying the `ℓ^r` identity
  `‖∑_{x ∈ S} c x • g x‖^r = ∑_{x ∈ S} ‖c x‖^r` on finite sets (for example a family of
  pairwise disjointly supported unit functions in `L^r`) and `φ` is injective;
* `lr_norm_of_sigma`: the same for a hypothesis stated on finite subsets of
  `Σ s, Fin (N s)`;
* `root_prefix_of_schauderBasis`, `mem_closure_span_of_schauderBasis`: the fields
  `root_prefix` and `root_dense` for `root j = (b j : Z)`, where `b` is a Schauder basis of a
  subspace `X` (for example `X = ker PY`) whose partial sum projections have norm `≤ D`.

A constructor:

* `PositiveForest.ofFamily`: the positive forest of a family satisfying the `ℓ^r` identity,
  a bounded projection onto its closed span and a normalized Schauder basis of the kernel
  of the projection.

Using the sequence:

* `PositiveForest.prefixList s`: the list of the first `offset s` vectors of the sequence;
  `prefixList_zero`, `prefixList_succ` describe it as `[e0]`, extended stage by stage by
  the atoms `List.ofFn (atom s)`.
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-! ### The `ℓ^r` identity -/

/-- The hypothesis `PositiveForest.lr_norm` for vectors taken injectively from a family
`g` which satisfies the `ℓ^r` identity on all finite sets of indices. -/
theorem lr_norm_of_family {ι : Type*} {r : ℝ} (g : ι → Z)
    (hg : ∀ (S : Finset ι) (c : ι → ℂ), ‖∑ x ∈ S, c x • g x‖ ^ r = ∑ x ∈ S, ‖c x‖ ^ r)
    {N : ℕ → ℕ} (φ : Option (Σ s, Fin (N s)) → ι) (hφ : Function.Injective φ)
    (c0 : ℂ) (T : ℕ) (c : (s : ℕ) → Fin (N s) → ℂ) :
    ‖c0 • g (φ none) + ∑ s ∈ Finset.range T, ∑ i, c s i • g (φ (some ⟨s, i⟩))‖ ^ r =
      ‖c0‖ ^ r + ∑ s ∈ Finset.range T, ∑ i, ‖c s i‖ ^ r := by
  classical
  have h := hg ((Finset.insertNone ((Finset.range T).sigma fun _ => Finset.univ)).image φ)
    (Function.extend φ (fun x => x.elim c0 fun p => c p.1 p.2) 0)
  rw [Finset.sum_image fun _ _ _ _ h => hφ h, Finset.sum_image fun _ _ _ _ h => hφ h] at h
  simp only [hφ.extend_apply] at h
  rw [Finset.sum_insertNone, Finset.sum_insertNone, Finset.sum_sigma, Finset.sum_sigma] at h
  exact h

/-- The hypothesis `PositiveForest.lr_norm` from the `ℓ^r` identity on the finite subsets
of the index set `Σ s, Fin (N s)` of the coordinates. -/
theorem lr_norm_of_sigma {r : ℝ} {N : ℕ → ℕ} (e0 : Z) (coord : (s : ℕ) → Fin (N s) → Z)
    (h : ∀ (c0 : ℂ) (S : Finset (Σ s, Fin (N s))) (c : (Σ s, Fin (N s)) → ℂ),
      ‖c0 • e0 + ∑ x ∈ S, c x • coord x.1 x.2‖ ^ r = ‖c0‖ ^ r + ∑ x ∈ S, ‖c x‖ ^ r)
    (c0 : ℂ) (T : ℕ) (c : (s : ℕ) → Fin (N s) → ℂ) :
    ‖c0 • e0 + ∑ s ∈ Finset.range T, ∑ i, c s i • coord s i‖ ^ r =
      ‖c0‖ ^ r + ∑ s ∈ Finset.range T, ∑ i, ‖c s i‖ ^ r := by
  have h' := h c0 ((Finset.range T).sigma fun _ => Finset.univ) (fun x => c x.1 x.2)
  rw [Finset.sum_sigma, Finset.sum_sigma] at h'
  exact h'

/-! ### Roots from a Schauder basis of a subspace -/

/-- The prefix inequality (`PositiveForest.root_prefix`) for the vectors of a Schauder basis
of a subspace whose partial sum projections are bounded by `D`. -/
theorem root_prefix_of_schauderBasis {X : Submodule ℂ Z} (b : SchauderBasis ℂ X) {D : ℝ}
    (hD : ∀ m, ‖b.proj m‖ ≤ D) (t : ℕ → ℂ) (m M : ℕ) (hmM : m ≤ M) :
    ‖∑ j ∈ Finset.range m, t j • (b j : Z)‖ ≤ D * ‖∑ j ∈ Finset.range M, t j • (b j : Z)‖ := by
  classical
  have hproj : b.proj m (∑ j ∈ Finset.range M, t j • b j) =
      ∑ j ∈ Finset.range m, t j • b j := by
    rw [map_sum]
    have hfil : (Finset.range M).filter (fun j => j < m) = Finset.range m := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← hfil, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, b.proj_apply_basis_mem]
      split_ifs
      · rfl
      · rw [smul_zero]
  have hcoe : ∀ n, ((∑ j ∈ Finset.range n, t j • b j : X) : Z) =
      ∑ j ∈ Finset.range n, t j • (b j : Z) := by
    intro n
    simp
  calc ‖∑ j ∈ Finset.range m, t j • (b j : Z)‖
      = ‖b.proj m (∑ j ∈ Finset.range M, t j • b j)‖ := by
        rw [hproj, Submodule.coe_norm, hcoe]
    _ ≤ ‖b.proj m‖ * ‖∑ j ∈ Finset.range M, t j • b j‖ := (b.proj m).le_opNorm _
    _ ≤ D * ‖∑ j ∈ Finset.range M, t j • (b j : Z)‖ := by
        rw [Submodule.coe_norm, hcoe]
        exact mul_le_mul_of_nonneg_right (hD m) (norm_nonneg _)

/-- Density (`PositiveForest.root_dense`) for the vectors of a Schauder basis of a
subspace. -/
theorem mem_closure_span_of_schauderBasis {X : Submodule ℂ Z} (b : SchauderBasis ℂ X) {x : Z}
    (hx : x ∈ X) : x ∈ closure (Submodule.span ℂ (Set.range fun j => (b j : Z)) : Set Z) := by
  have h := b.tendsto_proj ⟨x, hx⟩
  have h' : Filter.Tendsto (fun n => ((b.proj n ⟨x, hx⟩ : X) : Z)) Filter.atTop (nhds x) :=
    (continuous_subtype_val.tendsto _).comp h
  refine mem_closure_of_tendsto h' (Filter.Eventually.of_forall fun n => ?_)
  rw [SchauderBasis.proj_apply, Submodule.coe_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-! ### A constructor -/

namespace PositiveForest

/-- **Constructor for the application.** A positive forest from

* a family `g : ι → Z` satisfying the `ℓ^r` identity on finite sets (e.g. pairwise
  disjointly supported unit functions in `L^r`), from which `e0 = g (φ none)` and the
  coordinates `coord s i = g (φ (some ⟨s, i⟩))` are taken by an injection `φ`;
* a bounded projection `PY` which fixes these vectors and whose range is contained in
  their closed span;
* a normalized Schauder basis `b` of the kernel of `PY` whose partial sum projections have
  norm at most `D`; the roots are `root j = (b j : Z)`. -/
@[simps]
def ofFamily {ι : Type*} {r : ℝ} (g : ι → Z)
    (hg : ∀ (S : Finset ι) (c : ι → ℂ), ‖∑ x ∈ S, c x • g x‖ ^ r = ∑ x ∈ S, ‖c x‖ ^ r)
    (N : ℕ → ℕ) (hN : ∀ s, 1 ≤ N s)
    (φ : Option (Σ s, Fin (N s)) → ι) (hφ : Function.Injective φ)
    (PY : Z →L[ℂ] Z) (hPY : ∀ z, PY (PY z) = PY z) (B : ℝ) (hB : ‖PY‖ ≤ B)
    (hfix : ∀ x, PY (g (φ x)) = g (φ x))
    (hdense : ∀ y, PY y = y →
      y ∈ closure (Submodule.span ℂ (Set.range fun x => g (φ x)) : Set Z))
    (b : SchauderBasis ℂ PY.ker) (hb : ∀ j, ‖b j‖ = 1)
    (D : ℝ) (hD : ∀ m, ‖b.proj m‖ ≤ D) : PositiveForest Z r where
  PY := PY
  B := B
  D := D
  e0 := g (φ none)
  root := fun j => (b j : Z)
  N := N
  coord := fun s i => g (φ (some ⟨s, i⟩))
  PY_idem := hPY
  norm_PY_le := hB
  N_pos := hN
  PY_e0 := hfix none
  PY_coord := fun s i => hfix (some ⟨s, i⟩)
  lr_norm := lr_norm_of_family g hg φ hφ
  coord_dense := by
    intro y hy
    refine closure_mono (SetLike.coe_subset_coe.mpr (Submodule.span_mono ?_)) (hdense y hy)
    rintro _ ⟨x, rfl⟩
    rcases x with _ | ⟨s, i⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨s, ⟨i, rfl⟩⟩)
  PY_root := fun j => LinearMap.mem_ker.mp (b j).2
  norm_root := fun j => by rw [← Submodule.coe_norm]; exact hb j
  root_dense := fun _ hx => mem_closure_span_of_schauderBasis b (LinearMap.mem_ker.mpr hx)
  root_prefix := root_prefix_of_schauderBasis b hD

end PositiveForest

/-! ### The sequence as a list -/

namespace PositiveForest

variable {r : ℝ} (F : PositiveForest Z r)

/-- The first `offset s` vectors of the sequence — `e0` and the atoms of the stages `< s` —
as a list. -/
def prefixList (s : ℕ) : List Z := (List.range (F.offset s)).map F.seq

@[simp] theorem length_prefixList (s : ℕ) : (F.prefixList s).length = F.offset s := by
  simp [prefixList]

theorem getElem_prefixList (s n : ℕ) (h : n < (F.prefixList s).length) :
    (F.prefixList s)[n] = F.seq n := by
  simp [prefixList]

@[simp] theorem prefixList_zero : F.prefixList 0 = [F.e0] := by
  simp [prefixList, List.range_succ]

/-- Each stage appends its atoms, in the order of their indices. -/
theorem prefixList_succ (s : ℕ) :
    F.prefixList (s + 1) = F.prefixList s ++ List.ofFn (F.atom s) := by
  rw [prefixList, offset_succ, List.range_add, List.map_append, List.map_map, ← prefixList]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < F.N s := by simpa using h2
    simp [F.seq_offset_add' s hi]

end PositiveForest

end StructuredBases.PositiveTranslates
