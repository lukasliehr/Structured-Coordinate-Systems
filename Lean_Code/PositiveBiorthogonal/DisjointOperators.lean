import Lean_Code.PositiveBiorthogonal.BasicLp
import Lean_Code.PositiveBiorthogonal.PairingNorms

/-! Sharp norm bounds for operators localized to disjoint measurable regions. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_rpow_add_of_ae_disjoint (hpfin : p ≠ ∞) (f g : L 𝕜 p)
    (hfg : ∀ᵐ x : ℝ, f x = 0 ∨ g x = 0) :
    ‖f + g‖ ^ p.toReal = ‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hpfin).ne'
  rw [norm_rpow_eq_integral _ hp0 hpfin, norm_rpow_eq_integral _ hp0 hpfin,
    norm_rpow_eq_integral _ hp0 hpfin,
    ← integral_add ((Lp.memLp f).integrable_norm_rpow hp0 hpfin)
      ((Lp.memLp g).integrable_norm_rpow hp0 hpfin)]
  apply integral_congr_ae
  filter_upwards [hfg, Lp.coeFn_add f g] with x hx ha
  rw [ha]
  rcases hx with hz | hz <;> simp [Pi.add_apply, hz, Real.zero_rpow hr]

theorem norm_top_ae_le (f : L 𝕜 ∞) : ∀ᵐ x : ℝ, ‖f x‖ ≤ ‖f‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := (f : ℝ → 𝕜)) (μ := volume)] with x hx
  have he := ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hx
  simpa only [Lp.norm_def, eLpNorm_exponent_top, toReal_enorm] using he

theorem norm_top_add_le_max_of_ae_disjoint (f g : L 𝕜 ∞)
    (hfg : ∀ᵐ x : ℝ, f x = 0 ∨ g x = 0) : ‖f + g‖ ≤ max ‖f‖ ‖g‖ := by
  apply norm_top_le_of_ae_bound _ _ ((norm_nonneg f).trans (le_max_left _ _))
  filter_upwards [hfg, Lp.coeFn_add f g, norm_top_ae_le f, norm_top_ae_le g]
    with x hx ha hf hg
  rw [ha]
  rcases hx with hz | hz
  · simpa only [Pi.add_apply, hz, zero_add] using hg.trans (le_max_right _ _)
  · simpa only [Pi.add_apply, hz, add_zero] using hf.trans (le_max_left _ _)

omit [Fact (1 ≤ p)] in
theorem cut_ae_disjoint (A F : Set ℝ) (hA : MeasurableSet A) (hF : MeasurableSet F)
    (hAF : Disjoint A F) (f g : L 𝕜 p) :
    ∀ᵐ x : ℝ, cut A hA f x = 0 ∨ cut F hF g x = 0 := by
  filter_upwards [coeFn_cut A hA f, coeFn_cut F hF g] with x ha hf
  by_cases hx : x ∈ A
  · have hxF : x ∉ F := fun hf => Set.disjoint_left.mp hAF hx hf
    right
    simp [hf, hxF]
  · left
    simp [ha, hx]

omit [Fact (1 ≤ p)] in
theorem cut_add_union (A F : Set ℝ) (hA : MeasurableSet A) (hF : MeasurableSet F)
    (hAF : Disjoint A F) (f : L 𝕜 p) :
    cut A hA f + cut F hF f = cut (A ∪ F) (hA.union hF) f := by
  apply Lp.ext
  filter_upwards [coeFn_cut A hA f, coeFn_cut F hF f, coeFn_cut (A ∪ F) (hA.union hF) f,
    Lp.coeFn_add (cut A hA f) (cut F hF f)] with x ha hf hu hadd
  rw [hadd, Pi.add_apply, ha, hf, hu]
  by_cases hxA : x ∈ A
  · have hxF : x ∉ F := fun hf => Set.disjoint_left.mp hAF hxA hf
    simp [hxA, hxF]
  · by_cases hxF : x ∈ F <;> simp [hxA, hxF]

theorem cut_norm_rpow_sum_le (hpfin : p ≠ ∞) (A F : Set ℝ)
    (hA : MeasurableSet A) (hF : MeasurableSet F) (hAF : Disjoint A F) (f : L 𝕜 p) :
    ‖cut A hA f‖ ^ p.toReal + ‖cut F hF f‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
  rw [← norm_rpow_add_of_ae_disjoint hpfin _ _ (cut_ae_disjoint A F hA hF hAF f f),
    cut_add_union A F hA hF hAF f]
  exact Real.rpow_le_rpow (norm_nonneg _) (cut_norm_le _ _ _) ENNReal.toReal_nonneg

/-- An operator reads only its region and has output supported in that region. -/
structure LocalizedOperator (A : Set ℝ) (hA : MeasurableSet A) (T : L 𝕜 p →L[𝕜] L 𝕜 p) : Prop where
  input : ∀ f, T f = T (cut A hA f)
  output : ∀ f, ∀ᵐ x : ℝ, x ∉ A → T f x = 0

theorem localized_outputs_disjoint (A F : Set ℝ) (hA : MeasurableSet A) (hF : MeasurableSet F)
    (hAF : Disjoint A F) (TA TF : L 𝕜 p →L[𝕜] L 𝕜 p)
    (hTA : LocalizedOperator A hA TA) (hTF : LocalizedOperator F hF TF) (f : L 𝕜 p) :
    ∀ᵐ x : ℝ, TA f x = 0 ∨ TF f x = 0 := by
  filter_upwards [hTA.output f, hTF.output f] with x hxA hxF
  by_cases hx : x ∈ A
  · right
    exact hxF (fun hf => Set.disjoint_left.mp hAF hx hf)
  · exact Or.inl (hxA hx)

theorem localized_norm_le (A : Set ℝ) (hA : MeasurableSet A) (T : L 𝕜 p →L[𝕜] L 𝕜 p)
    (hT : LocalizedOperator A hA T) (C : ℝ) (hC : ‖T‖ ≤ C) (f : L 𝕜 p) :
    ‖T f‖ ≤ C * ‖cut A hA f‖ := by
  rw [hT.input]
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

theorem disjoint_operators (A F : Set ℝ) (hA : MeasurableSet A) (hF : MeasurableSet F)
    (hAF : Disjoint A F) (TA TF : L 𝕜 p →L[𝕜] L 𝕜 p)
    (hTA : LocalizedOperator A hA TA) (hTF : LocalizedOperator F hF TF)
    (C : ℝ) (hCA : ‖TA‖ ≤ C) (hCF : ‖TF‖ ≤ C) : ‖TA + TF‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg TA).trans hCA
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖TA f + TF f‖ ≤ C * ‖f‖
  have hdisj := localized_outputs_disjoint A F hA hF hAF TA TF hTA hTF f
  by_cases hpfin : p = ∞
  · subst p
    apply (norm_top_add_le_max_of_ae_disjoint _ _ hdisj).trans
    apply max_le
    · exact (TA.le_opNorm f).trans (mul_le_mul_of_nonneg_right hCA (norm_nonneg f))
    · exact (TF.le_opNorm f).trans (mul_le_mul_of_nonneg_right hCF (norm_nonneg f))
  · have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hpfin
    apply (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)) hr).mp
    rw [norm_rpow_add_of_ae_disjoint hpfin _ _ hdisj, Real.mul_rpow hC (norm_nonneg _)]
    calc
      _ ≤ (C * ‖cut A hA f‖) ^ p.toReal + (C * ‖cut F hF f‖) ^ p.toReal :=
        add_le_add (Real.rpow_le_rpow (norm_nonneg _) (localized_norm_le A hA TA hTA C hCA f) hr.le)
          (Real.rpow_le_rpow (norm_nonneg _) (localized_norm_le F hF TF hTF C hCF f) hr.le)
      _ = C ^ p.toReal * (‖cut A hA f‖ ^ p.toReal + ‖cut F hF f‖ ^ p.toReal) := by
        rw [Real.mul_rpow hC (norm_nonneg _), Real.mul_rpow hC (norm_nonneg _), mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left (cut_norm_rpow_sum_le hpfin A F hA hF hAF f)
        (Real.rpow_nonneg hC _)

omit [Fact (1 ≤ p)] in
theorem cut_cut_of_subset (A U : Set ℝ) (hA : MeasurableSet A) (hU : MeasurableSet U)
    (hAU : A ⊆ U) (f : L 𝕜 p) : cut A hA (cut U hU f) = cut A hA f := by
  apply Lp.ext
  filter_upwards [coeFn_cut A hA (cut U hU f), coeFn_cut U hU f, coeFn_cut A hA f]
    with x ha hu haf
  rw [ha, haf]
  by_cases hx : x ∈ A
  · simp [hx, hu, hAU hx]
  · simp [hx]

theorem localized_add_union (A F : Set ℝ) (hA : MeasurableSet A) (hF : MeasurableSet F)
    (TA TF : L 𝕜 p →L[𝕜] L 𝕜 p) (hTA : LocalizedOperator A hA TA)
    (hTF : LocalizedOperator F hF TF) :
    LocalizedOperator (A ∪ F) (hA.union hF) (TA + TF) where
  input f := by
    simp only [add_apply]
    congr 1
    · rw [hTA.input f, hTA.input (cut (A ∪ F) (hA.union hF) f),
        cut_cut_of_subset A (A ∪ F) hA (hA.union hF) subset_union_left]
    · rw [hTF.input f, hTF.input (cut (A ∪ F) (hA.union hF) f),
        cut_cut_of_subset F (A ∪ F) hF (hA.union hF) subset_union_right]
  output f := by
    filter_upwards [hTA.output f, hTF.output f, Lp.coeFn_add (TA f) (TF f)] with x ha hf hadd
    intro hx
    have hxA : x ∉ A := fun h => hx (Or.inl h)
    have hxF : x ∉ F := fun h => hx (Or.inr h)
    change (TA f + TF f) x = 0
    rw [hadd, Pi.add_apply, ha hxA, hf hxF, add_zero]

theorem disjoint_operator_sum {ι : Type*} (s : Finset ι) (A : ι → Set ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hpair : Pairwise (fun i j => Disjoint (A i) (A j)))
    (T : ι → L 𝕜 p →L[𝕜] L 𝕜 p) (hT : ∀ i, LocalizedOperator (A i) (hA i) (T i))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, ‖T i‖ ≤ C) :
    LocalizedOperator (⋃ i ∈ s, A i) (MeasurableSet.biUnion s.countable_toSet (fun i _ => hA i))
      (∑ i ∈ s, T i) ∧ ‖∑ i ∈ s, T i‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, Finset.sum_empty, norm_zero]
    refine ⟨⟨?_, ?_⟩, hC⟩
    · intro f
      simp
    · intro f
      filter_upwards [Lp.coeFn_zero 𝕜 p (volume : Measure ℝ)] with x hx
      intro _
      simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hdisj : Disjoint (A a) (⋃ i ∈ s, A i) := by
      simp only [Set.disjoint_iUnion_right]
      intro i hi
      exact hpair (fun he => ha (he.symm ▸ hi))
    have hloc := localized_add_union (A a) (⋃ i ∈ s, A i) (hA a)
      (MeasurableSet.biUnion s.countable_toSet (fun i _ => hA i)) (T a) (∑ i ∈ s, T i) (hT a) ih.1
    have hnorm := disjoint_operators (A a) (⋃ i ∈ s, A i) (hA a)
      (MeasurableSet.biUnion s.countable_toSet (fun i _ => hA i)) hdisj
      (T a) (∑ i ∈ s, T i) (hT a) ih.1 C (hbound a) ih.2
    simpa only [Finset.set_biUnion_insert] using And.intro hloc hnorm

end PositiveBiorthogonal
