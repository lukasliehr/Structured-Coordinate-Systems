import Lean_Code.PositiveBiorthogonal.BasicLp
import Mathlib.MeasureTheory.PiSystem

/-! Closed linear spaces are stable under increasing finite-measure indicator limits. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem indicatorConstLp_monotone_tendsto (hp : p ≠ ∞) (t : ℕ → Set ℝ)
    (ht : ∀ n, MeasurableSet (t n)) (hm : Monotone t) (s : Set ℝ)
    (hs : MeasurableSet s) (hsfin : volume s ≠ ∞) (heq : (⋃ n, t n) = s) (c : 𝕜) :
    Tendsto (fun n => indicatorConstLp p (ht n)
      (measure_ne_top_of_subset (heq ▸ subset_iUnion t n) hsfin) c)
      atTop (𝓝 (indicatorConstLp p hs hsfin c)) := by
  apply tendsto_indicatorConstLp_set hp
  have hsub (n) : t n ⊆ s := heq ▸ subset_iUnion t n
  have hlim := tendsto_measure_iUnion_atTop (μ := volume) hm
  rw [heq] at hlim
  have h := (ENNReal.continuous_sub_left hsfin).tendsto (volume s) |>.comp hlim
  simpa only [tsub_self, Function.comp_def, symmDiff_of_le (hsub _),
    measure_sdiff (hsub _) (ht _).nullMeasurableSet (measure_ne_top_of_subset (hsub _) hsfin)] using h

theorem indicatorConstLp_finsetUnion_mem (W : Submodule 𝕜 (L 𝕜 p)) {ι : Type*}
    (u : Finset ι) (t : ι → Set ℝ) (ht : ∀ i, MeasurableSet (t i))
    (hdis : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hfin : ∀ i, volume (t i) ≠ ∞) (c : 𝕜)
    (hmem : ∀ i ∈ u, indicatorConstLp p (ht i) (hfin i) c ∈ W) :
    indicatorConstLp p (MeasurableSet.biUnion u.countable_toSet (fun i _ => ht i))
      (by exact (measure_biUnion_lt_top u.finite_toSet (fun i _ => (hfin i).lt_top)).ne) c ∈ W := by
  classical
  induction u using Finset.induction with
  | empty => simp
  | @insert a u ha ih =>
    have hd : Disjoint (t a) (⋃ i ∈ u, t i) := by
      simp only [Set.disjoint_iUnion_right]
      intro i hi
      exact hdis (by intro h; subst i; exact ha hi)
    have hm := W.add_mem (hmem a (Finset.mem_insert_self a u))
      (ih (fun i hi => hmem i (Finset.mem_insert_of_mem hi)))
    rw [← indicatorConstLp_disjoint_union (ht a)
      (MeasurableSet.biUnion u.countable_toSet (fun i _ => ht i)) (hfin a)
      (by exact (measure_biUnion_lt_top u.finite_toSet (fun i _ => (hfin i).lt_top)).ne) hd] at hm
    convert hm using 1 <;> simp

theorem indicatorConstLp_iUnion_mem (hp : p ≠ ∞) (W : Submodule 𝕜 (L 𝕜 p))
    (hW : IsClosed (W : Set (L 𝕜 p))) (t : ℕ → Set ℝ)
    (ht : ∀ n, MeasurableSet (t n)) (hdis : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hfin : volume (⋃ n, t n) ≠ ∞) (c : 𝕜)
    (hmem : ∀ n, indicatorConstLp p (ht n)
      (measure_ne_top_of_subset (subset_iUnion t n) hfin) c ∈ W) :
    indicatorConstLp p (MeasurableSet.iUnion ht) hfin c ∈ W := by
  let u (n : ℕ) := ⋃ i ∈ Finset.range n, t i
  have hu (n) : MeasurableSet (u n) :=
    MeasurableSet.biUnion (Finset.range n).countable_toSet (fun i _ => ht i)
  have hmono : Monotone u := fun a b hab =>
    Set.biUnion_subset_biUnion_left (Finset.range_mono hab)
  have heq : (⋃ n, u n) = ⋃ n, t n := by
    ext x
    simp only [u, mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨n, i, hi, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i + 1, i, Nat.lt_succ_self i, hx⟩
  apply hW.mem_of_tendsto (indicatorConstLp_monotone_tendsto hp u hu hmono _
    (MeasurableSet.iUnion ht) hfin heq c)
  exact Eventually.of_forall fun n => indicatorConstLp_finsetUnion_mem W (Finset.range n)
    t ht hdis (fun i => measure_ne_top_of_subset (subset_iUnion t i) hfin) c (fun i _ => hmem i)

end PositiveBiorthogonal
