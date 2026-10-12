import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.PiSystem

/-!
# Indicator functions in `L¹` and a density criterion

`indL 𝕜 μ s` is the indicator function of the set `s` as an element of `L¹(μ)`.  In contrast
to `MeasureTheory.indicatorConstLp` it does not take proofs as arguments (it is zero by
convention if `s` is not measurable or has infinite measure), so that sets can be rewritten
freely.

The main results are closure properties of closed subspaces of `L¹`:

* `indL_iUnion_mem`: countable disjoint unions;
* `eq_top_of_indL_mem`: a closed subspace containing all indicators is everything;
* `eq_top_of_indL_Ioc_inter_mem`: a closed subspace of `L¹(ℝ)` containing the indicators of
  the traces of all intervals on the members of a countable partition of `ℝ` is everything.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Function
open scoped ENNReal Topology symmDiff

namespace StructuredBases
namespace PositiveL1

variable {α : Type*} [MeasurableSpace α] {𝕜 : Type*} [RCLike 𝕜] {μ : Measure α}

variable (𝕜 μ) in
open scoped Classical in
/-- The indicator function of a set as an element of `L¹(μ)`.  By convention it is zero if
the set is not measurable or has infinite measure. -/
def indL (s : Set α) : Lp 𝕜 1 μ :=
  if h : MeasurableSet s ∧ μ s ≠ ∞ then indicatorConstLp 1 h.1 h.2 (1 : 𝕜) else 0

theorem indL_eq {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) :
    indL 𝕜 μ s = indicatorConstLp 1 hs hμ (1 : 𝕜) := by
  rw [indL, dif_pos ⟨hs, hμ⟩]

@[simp] theorem indL_empty : indL 𝕜 μ (∅ : Set α) = 0 := by
  rw [indL_eq MeasurableSet.empty (by simp)]
  exact indicatorConstLp_empty

theorem indL_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hd : Disjoint s t) : indL 𝕜 μ (s ∪ t) = indL 𝕜 μ s + indL 𝕜 μ t := by
  rw [indL_eq hs hμs, indL_eq ht hμt, indL_eq (hs.union ht) (measure_union_ne_top hμs hμt)]
  exact indicatorConstLp_disjoint_union hs ht hμs hμt hd 1

theorem norm_indL {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) :
    ‖indL 𝕜 μ s‖ = μ.real s := by
  rw [indL_eq hs hμ, norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
  simp

theorem coeFn_indL {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) :
    (indL 𝕜 μ s : α → 𝕜) =ᵐ[μ] s.indicator fun _ => (1 : 𝕜) := by
  rw [indL_eq hs hμ]
  exact indicatorConstLp_coeFn

theorem indicatorConstLp_eq_smul_indL {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞)
    (c : 𝕜) : indicatorConstLp 1 hs hμ c = c • indL 𝕜 μ s := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμ) (c := c),
    coeFn_indL (𝕜 := 𝕜) hs hμ, Lp.coeFn_smul c (indL 𝕜 μ s)] with x hc h1 hsm
  rw [hc, hsm, Pi.smul_apply, h1]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx, smul_eq_mul, mul_one]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]

theorem tendsto_indL {ι : Type*} {l : Filter ι} {t : ι → Set α} {s : Set α}
    (ht : ∀ i, MeasurableSet (t i)) (hμt : ∀ i, μ (t i) ≠ ∞) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (h : Tendsto (fun i => μ (t i ∆ s)) l (𝓝 0)) :
    Tendsto (fun i => indL 𝕜 μ (t i)) l (𝓝 (indL 𝕜 μ s)) := by
  simp only [indL_eq (ht _) (hμt _), indL_eq hs hμs]
  exact tendsto_indicatorConstLp_set ENNReal.one_ne_top h

/-! ### Closed subspaces -/

/-- A closed subspace of `L¹` containing the indicators of countably many pairwise disjoint
sets contains the indicator of their union. -/
theorem indL_iUnion_mem (W : Submodule 𝕜 (Lp 𝕜 1 μ)) (hW : IsClosed (W : Set (Lp 𝕜 1 μ)))
    {t : ℕ → Set α} (ht : ∀ n, MeasurableSet (t n)) (hdis : Pairwise (Disjoint on t))
    (hfin : μ (⋃ n, t n) ≠ ∞) (hmem : ∀ n, indL 𝕜 μ (t n) ∈ W) :
    indL 𝕜 μ (⋃ n, t n) ∈ W := by
  have hfin' : ∀ n, μ (t n) ≠ ∞ := fun n => measure_ne_top_of_subset (subset_iUnion t n) hfin
  set u : ℕ → Set α := fun N => ⋃ i ∈ Finset.range N, t i with hu
  have hum : ∀ N, MeasurableSet (u N) := fun N =>
    Finset.measurableSet_biUnion _ fun i _ => ht i
  have husub : ∀ N, u N ⊆ ⋃ n, t n := fun N => iUnion₂_subset fun i _ => subset_iUnion t i
  have hufin : ∀ N, μ (u N) ≠ ∞ := fun N => measure_ne_top_of_subset (husub N) hfin
  have humem : ∀ N, indL 𝕜 μ (u N) ∈ W := by
    intro N
    induction N with
    | zero => simp [hu]
    | succ N ih =>
      have hstep : u (N + 1) = t N ∪ u N := by
        simp only [hu, Finset.range_add_one, Finset.set_biUnion_insert]
      have hd : Disjoint (t N) (u N) := by
        simp only [hu, disjoint_iUnion_right]
        intro i hi
        exact hdis (Finset.mem_range.mp hi).ne'
      rw [hstep, indL_union (ht N) (hum N) (hfin' N) (hufin N) hd]
      exact W.add_mem (hmem N) ih
  have hmono : Monotone u := fun a b hab =>
    biUnion_subset_biUnion_left (Finset.range_mono hab)
  have hUeq : (⋃ N, u N) = ⋃ n, t n := by
    apply Subset.antisymm (iUnion_subset husub)
    refine iUnion_subset fun n => ?_
    exact (subset_biUnion_of_mem (u := t) (Finset.mem_coe.mpr (Finset.self_mem_range_succ n))).trans
      (subset_iUnion u (n + 1))
  have hlim : Tendsto (fun N => μ (u N ∆ ⋃ n, t n)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hUeq] at h1
    have h2 := ((ENNReal.continuous_sub_left hfin).tendsto (μ (⋃ n, t n))).comp h1
    simpa only [tsub_self, Function.comp_def, symmDiff_of_le (husub _),
      measure_sdiff (husub _) (hum _).nullMeasurableSet (hufin _)] using h2
  exact hW.mem_of_tendsto (tendsto_indL hum hufin (MeasurableSet.iUnion ht) hfin hlim)
    (Eventually.of_forall humem)

/-- A closed subspace of `L¹` containing the indicators of all measurable sets of finite
measure is everything. -/
theorem eq_top_of_indL_mem (W : Submodule 𝕜 (Lp 𝕜 1 μ)) (hW : IsClosed (W : Set (Lp 𝕜 1 μ)))
    (h : ∀ s, MeasurableSet s → μ s ≠ ∞ → indL 𝕜 μ s ∈ W) : W = ⊤ := by
  refine top_unique fun f _ => ?_
  apply Lp.induction ENNReal.one_ne_top (fun f : Lp 𝕜 1 μ => f ∈ W) ?_ ?_ hW f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_indL]
    exact W.smul_mem c (h s hs hμs.ne)
  · intro f g hf hg _ hfm hgm
    exact W.add_mem hfm hgm

/-! ### Subspaces of `L¹(ℝ)` -/

/-- If a closed subspace of `L¹(ℝ)` contains the indicators of the traces of all intervals
on a set `U` of finite measure, then it contains the indicators of the traces of all
measurable sets on `U`. -/
theorem indL_inter_mem_of_Ioc (W : Submodule 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)))
    (hW : IsClosed (W : Set (Lp 𝕜 1 (volume : Measure ℝ)))) {U : Set ℝ} (hU : MeasurableSet U)
    (hUfin : volume U ≠ ∞) (hUmem : indL 𝕜 volume U ∈ W)
    (hI : ∀ a b : ℝ, indL 𝕜 volume (Ioc a b ∩ U) ∈ W) {s : Set ℝ} (hs : MeasurableSet s) :
    indL 𝕜 volume (s ∩ U) ∈ W := by
  have hfin : ∀ r : Set ℝ, volume (r ∩ U) ≠ ∞ := fun r =>
    measure_ne_top_of_subset inter_subset_right hUfin
  induction s, hs using MeasurableSpace.induction_on_inter
    (borel_eq_generateFrom_Ioc ℝ) (isPiSystem_Ioc id id) with
  | empty => simp
  | basic t ht =>
    obtain ⟨a, b, -, rfl⟩ := ht
    exact hI a b
  | compl t ht ih =>
    have hd : Disjoint (t ∩ U) (tᶜ ∩ U) :=
      (disjoint_compl_right (a := t)).mono inter_subset_left inter_subset_left
    have hu : t ∩ U ∪ tᶜ ∩ U = U := by
      rw [← union_inter_distrib_right, union_compl_self, univ_inter]
    have hadd := indL_union (𝕜 := 𝕜) (ht.inter hU) (ht.compl.inter hU) (hfin t) (hfin tᶜ) hd
    rw [hu] at hadd
    have hsub : indL 𝕜 volume (tᶜ ∩ U) = indL 𝕜 volume U - indL 𝕜 volume (t ∩ U) := by
      rw [hadd]
      abel
    rw [hsub]
    exact W.sub_mem hUmem ih
  | iUnion f hdis hf ih =>
    rw [iUnion_inter]
    exact indL_iUnion_mem W hW (fun n => (hf n).inter hU)
      (fun i j hij => (hdis hij).mono inter_subset_left inter_subset_left)
      (measure_ne_top_of_subset (iUnion_subset fun n => inter_subset_right) hUfin) ih

/-- A closed subspace of `L¹(ℝ)` which contains the indicators of the traces of all
intervals on the members of a countable measurable partition of `ℝ` into sets of finite
measure is everything. -/
theorem eq_top_of_indL_Ioc_inter_mem (W : Submodule 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)))
    (hW : IsClosed (W : Set (Lp 𝕜 1 (volume : Measure ℝ)))) {U : ℕ → Set ℝ}
    (hU : ∀ n, MeasurableSet (U n)) (hUfin : ∀ n, volume (U n) ≠ ∞)
    (hUdis : Pairwise (Disjoint on U)) (hUcov : (⋃ n, U n) = univ)
    (hUmem : ∀ n, indL 𝕜 volume (U n) ∈ W)
    (hI : ∀ n (a b : ℝ), indL 𝕜 volume (Ioc a b ∩ U n) ∈ W) : W = ⊤ := by
  refine eq_top_of_indL_mem W hW fun s hs hμs => ?_
  have hs' : (⋃ n, s ∩ U n) = s := by rw [← inter_iUnion, hUcov, inter_univ]
  rw [← hs']
  refine indL_iUnion_mem W hW (fun n => hs.inter (hU n))
    (fun i j hij => (hUdis hij).mono inter_subset_right inter_subset_right) ?_
    fun n => indL_inter_mem_of_Ioc W hW (hU n) (hUfin n) (hUmem n) (hI n) hs
  rw [hs']
  exact hμs

end PositiveL1
end StructuredBases
