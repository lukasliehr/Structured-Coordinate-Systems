import Lean_Code.SchauderTranslates.CutoffProductStep
import Lean_Code.SchauderTranslates.ScalarRowBounds
import Lean_Code.SchauderTranslates.ScalarCopyPrefixBounds
import Lean_Code.SchauderTranslates.Sharp.ScalarSharpNumerics

/-!
# One activation/cutoff/product step with parametrized constants

These are the counterparts of `scalar_floor_step`, `ScalarData.cutoff_product_step`,
`ScalarData.scalar_rows_bound`, `ScalarData.orderedCutoffData_prefix_step` and
`ScalarData.product_augmented_prefix` in which the absolute constants of the first
formalization (`1/646 ≤ Z ≤ 1/323`, `2 ≤ q < 3`, cost `10`) are replaced by the relative
hypotheses of the sharp induction (paper: `h2:ss:scalar-induction`). The analytic input
(rare activation, the row-splitting lemma, the copies lemma) is used in its existing
general form.
-/

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp.Scalar
open SchauderTranslates ScalarData

variable {d n : ℕ}

/-- Spectral-floor propagation for one activation/cutoff/product step, for any retained
gain bound `Z ≤ 1`. -/
theorem scalar_floor_step_sharp (cut : ScalarData d n) (L : ℕ)
    {ε ε' h Z : ℝ} (he : 0 < ε) (hemax : ε ≤ 1 / 10)
    (he' : 0 < ε') (hdecrease : ε' ≤ ε - 3 * ε ^ 2 / 4)
    (hmass : (cut.product L).mass = 1 - ε')
    (hgain : (cut.product L).gain ≤ Z) (hZ : Z ≤ 1)
    (hcut : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) cut.rawGram⁻¹‖ ≤ h)
    (hold : h ≤ ε⁻¹ ^ 2) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (cut.product L).rawGram⁻¹‖ ≤ ε'⁻¹ ^ 2 := by
  apply scalar_floor_norm_step_sharp he hemax he' hdecrease hZ hold
  have hh : 0 ≤ h := (norm_nonneg _).trans hcut
  have hm : 0 < 1 - ε' := hmass ▸ (cut.product L).toTorusWeight.mass_pos
  have hM : cut.mass * h ≤ h := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right cut.toTorusWeight.mass_le_one hh
  have hbound := cut.product_rawInverse_norm_le L hcut
  rw [← cut.product_mass, hmass, ← cut.product_gain] at hbound
  refine hbound.trans (div_le_div_of_nonneg_right ?_ hm.le)
  linarith

/-- The concrete product of a finite cutoff inherits the complete rare-step numerical bounds,
assuming only `ε² ≤ (16 / 3) Z` and `Z ≤ 1` for the old block. -/
theorem cutoff_product_step_sharp (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {ε p : ℝ} (hm : s.mass = 1 - ε)
    (he : 0 < ε) (hemax : ε ≤ 1 / 10) (hZ0 : 0 < s.gain)
    (hZε : ε ^ 2 ≤ (16 / 3) * s.gain) (hZmax : s.gain ≤ 1)
    (hp : 0 < p) (hpmax : p ≤ 1 / 100)
    (hpe : p ≤ ε / (s.gain + ε))
    (hold : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ ≤ ε⁻¹ ^ 2)
    (N : ℕ) {m : ℕ} (e : Fin m ≃ CutoffNonconstant n N)
    (hzlo : (1 - ε / 4) * rareGain ε s.gain p ≤ (s.cutoffData p N e).gain)
    (hzhi : (s.cutoffData p N e).gain ≤ rareGain ε s.gain p) :
    let cut := s.cutoffData p N e
    let L := ⌊s.gain / cut.gain⌋₊
    let next := cut.product L
    let ε' := 1 - next.mass
    0 < ε' ∧ ε / 12 ≤ ε' ∧ ε' ≤ ε - 3 * ε ^ 2 / 4 ∧
    s.gain - cut.gain < next.gain ∧ next.gain ≤ s.gain ∧
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) next.rawGram⁻¹‖ ≤ ε'⁻¹ ^ 2 ∧
    (∀ C : ℝ, (∀ j, (s.rawGram⁻¹ j j).re - 1 ≤ C) → p * C ≤ ε / 100 →
      ∀ q : Fin (L * m), (next.rawGram⁻¹ (Sum.inr q) (Sum.inr q)).re - 1 < 2 * ε') := by
  dsimp only
  let cut := s.cutoffData p N e
  let L := ⌊s.gain / cut.gain⌋₊
  let next := cut.product L
  let ε' := 1 - next.mass
  have hp1 : p ≤ 1 := by linarith
  have hmcut : cut.mass = 1 - p * ε := s.cutoffData_mass_deficit hm hp.le hp1 N e
  have hmass : next.mass = (1 - p * ε) ^ L := by
    dsimp only [next]
    rw [cut.product_mass, hmcut]
  obtain ⟨hgl, hgu, _, _, hel, heu, hinv⟩ :=
    scalar_step_numerics_sharp he hemax hZ0 hZε hp hpmax hpe hzlo hzhi
  have heq : ε' = 1 - (1 - p * ε) ^ L := by dsimp [ε']; rw [hmass]
  have hel' : ε / 12 ≤ ε' := by simpa only [heq] using hel
  have heu' : ε' ≤ ε - 3 * ε ^ 2 / 4 := by simpa only [heq] using heu
  have he' : 0 < ε' := lt_of_lt_of_le (by positivity) hel'
  have hgain : next.gain = (L : ℝ) * cut.gain := cut.product_gain L
  have hgl' : s.gain - cut.gain < next.gain := by rw [hgain]; exact hgl
  have hgu' : next.gain ≤ s.gain := by rw [hgain]; exact hgu
  have hnorm : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) next.rawGram⁻¹‖ ≤ ε'⁻¹ ^ 2 := by
    apply scalar_floor_step_sharp cut L he hemax he' heu' (by dsimp [ε', next]; ring)
      hgu' hZmax (s.cutoffData_rawInverse_norm_le hb hfloor p N e) hold
  refine ⟨he', hel', heu', hgl', hgu', hnorm, ?_⟩
  intro C hC hpC q
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective q
  have hcenter : (cut.rawCenteredGram⁻¹ a a).re ≤ 1 + p * C := by
    exact (s.cutoffData_rawCenteredInverse_diagonal_le hb hfloor hp.le hp1 N e a).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hC _) hp.le))
  have hdiag := cut.product_inverse_nonconstant_le L i a hcenter
  have hden : cut.mass ^ L = 1 - ε' := by
    dsimp [ε', next]
    rw [cut.product_mass]
    ring
  rw [hden, hmcut] at hdiag
  have hbound := hinv C ((next.rawGram⁻¹ (Sum.inr (finProdFinEquiv (i,a)))
    (Sum.inr (finProdFinEquiv (i,a)))).re) hpC
  rw [← heq] at hbound
  exact hbound hdiag

/-- Both kinds of rows fit in the next centered-prefix budget once the explicit cost of the
constant row is below the old augmented bound. -/
theorem scalar_rows_bound_sharp (s : ScalarData d n) (hs : s.IsEven)
    {ε q : ℝ} (hε : 0 ≤ ε) (hm : s.mass = 1 - ε) (hq : 0 ≤ q)
    (hconst : 1 + s.gain + ε * (s.gain + ε) / (4 * (1 - ε)) ≤ q)
    (hp : s.AugmentedPrefixSqBound q)
    (hdiag : ∀ j : Fin n, (s.rawGram⁻¹ (Sum.inr j) (Sum.inr j)).re - 1 ≤ 2 * ε)
    (j : Unit ⊕ Fin n) :
    metricRowBound s.realRawGram
      (fun i : precedingScalarRows n j => (i : Unit ⊕ Fin n)) j ≤ q + ε ^ 2 / 2 := by
  rcases j with (u | j)
  · cases u
    rw [s.constant_row_bound_eq hs, hm]
    have he : 1 + s.gain - (1 - ε) = s.gain + ε := by ring
    rw [sub_sub_cancel, he]
    nlinarith [sq_nonneg ε]
  · exact s.nonconstant_row_bound hs hε hm hq hp j (hdiag j)

/-- The ordered cutoff has the precise prefix increment needed by the sharp induction. -/
theorem orderedCutoffData_prefix_step_sharp (s : ScalarData d n) (hs : s.IsEven)
    {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ s.density x)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ)
    {ε q : ℝ} (hε : 0 ≤ ε) (hm : s.mass = 1 - ε) (hq : 1 ≤ q)
    (hconst : 1 + s.gain + ε * (s.gain + ε) / (4 * (1 - ε)) ≤ q)
    (hp : s.AugmentedPrefixSqBound q)
    (hdiag : ∀ j : Fin n, (s.rawGram⁻¹ (Sum.inr j) (Sum.inr j)).re - 1 ≤ 2 * ε) :
    (s.orderedCutoffData p N).CenteredPrefixSqBound (q + ε ^ 2 / 2) :=
  s.orderedCutoffData_centered_prefix hs hb hfloor hp0 hp1 N (by nlinarith [sq_nonneg ε])
    (scalar_rows_bound_sharp s hs hε hm (by linarith) hconst hp hdiag)

/-- All augmented prefixes of independent scalar copies have the small *individual* gain
cost `(5 / t) η` (paper: the copies lemma with `Q² / (Q - 1 - Z) < 5 / t`). -/
theorem product_augmented_prefix_sharp (s : ScalarData d n) (L : ℕ) {t q : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (hq : 1 + t ≤ q) (hq2 : q < 1 + 2 * t)
    (hZ : (L : ℝ) * s.gain ≤ t / 2) (hp : s.CenteredPrefixSqBound q) :
    (s.product L).AugmentedPrefixSqBound (q + (5 / t) * s.gain) := by
  have hκ : (0 : ℝ) ≤ 5 / t := by positivity
  have hC : 1 ≤ q + (5 / t) * s.gain := by
    have := mul_nonneg hκ s.gain_nonneg
    linarith
  apply ((s.product L).augmentedPrefixSqBound_iff_gram (zero_le_one.trans hC)).mpr
  intro K
  by_cases hK0 : K = 0
  · subst K
    have hzero : scalarRowPrefixMatrix (L * n) 0 = 0 := by simp [scalarRowPrefixMatrix]
    rw [hzero]
    simpa [gramConjugate] using zero_le_one.trans hC
  by_cases hKfull : L * n + 1 ≤ K
  · have hall : scalarRowPrefixMatrix (L * n) K = 1 := by
      have hi (i : Unit ⊕ Fin (L * n)) : (scalarRowEquiv (L * n) i).val < K :=
        lt_of_lt_of_le (scalarRowEquiv (L * n) i).isLt hKfull
      simp [scalarRowPrefixMatrix, hi]
    rw [hall]
    exact gramConjugate_one_sq_le (s.product L).rawGram_posDef hC
  have hjlt : K - 1 < L * n := by omega
  let j : Fin (L * n) := ⟨K - 1, hjlt⟩
  obtain ⟨⟨k, b⟩, hkb⟩ := finProdFinEquiv.surjective j
  have hmask : scalarRowPrefixMatrix (L * n) K = Matrix.diagonal (copyPrefixMask L n k b.val) := by
    apply congrArg Matrix.diagonal
    funext i
    rcases i with (u | i)
    · cases u
      simp [copyPrefixMask, show 0 < K by omega]
    · obtain ⟨⟨t, a⟩, rfl⟩ := finProdFinEquiv.surjective i
      have he : (finProdFinEquiv (t, a)).val + 1 < K ↔
          finProdFinEquiv (t, a) < finProdFinEquiv (k, b) := by
        rw [hkb]
        change _ ↔ (finProdFinEquiv (t, a)).val < K - 1
        omega
      change (if (finProdFinEquiv (t, a)).val + 1 < K then (1 : ℂ) else 0) = _
      simp only [he]
      simp only [finProdFinEquiv_lt_iff]
      simp only [copyPrefixMask, Sum.elim_inr, Equiv.symm_apply_apply, Fin.lt_def]
  rw [hmask]
  exact (s.product_augmented_copy_cut L k b.val (by linarith) hp).trans
    (sharp_copy_prefix_cost ht0 ht1 hq hq2 hZ s.gain_nonneg)

end SchauderTranslates.Sharp.Scalar
