import Lean_Code.SchauderTranslates.ScalarBlocks
import Lean_Code.SchauderTranslates.ScalarSmoothing

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Arbitrarily small loss with a fixed positive retained gain, now for genuine even
trigonometric-polynomial densities. Both prefix predicates concern the actual ordered
characters, and the floor and inverse estimates use the raw augmented Gram. -/
theorem scalar_blocks {δ : ℝ} (hδ : 0 < δ) :
    ∃ (d n : ℕ) (s : ScalarData d n) (ε q K : ℝ),
      s.IsPolynomial ∧ s.IsEven ∧ s.HasPositiveFloor ∧
      (∀ i j, (s.rawGram i j).im = 0) ∧
      0 < ε ∧ ε < δ ∧ ε ≤ 1 / 10 ∧ s.mass = 1 - ε ∧
      1 / 646 ≤ s.gain ∧ 0 ≤ q ∧ q < 3 ∧ s.CenteredPrefixSqBound q ∧
      0 ≤ K ∧ K < 2 ∧ s.AugmentedPrefixSqBound (K ^ 2) ∧
      (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef ∧
      (∀ i : Fin n, (s.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re ≤ 1 + 2 * ε) ∧
      (s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2 := by
  obtain ⟨d, n, s, ε, q, K, _, hlim, hK0, hK2, hs⟩ := measurable_scalar_blocks
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨heven, hfloor, hε0, hε1, hmass, hgain, _, hdiag, hmat,
    hq2, _, hq3, hcenter, haug, hconst⟩ := hs j
  obtain ⟨b, hb, hf⟩ := hfloor
  let r : ℝ := (q j + 3) / 2
  have hqr : q j < r := by dsimp [r]; linarith
  have hr3 : r < 3 := by dsimp [r]; linarith
  have hq0 : 0 ≤ q j := by linarith
  have hgain' : 1 / 646 < (s j).gain := by linarith
  have hcp := (s j).fejer_centered_prefix_eventually hb hf hq0 hqr hcenter
  have hgp := ((s j).fejer_gain_tendsto hb hf).eventually (lt_mem_nhds hgain')
  obtain ⟨N, hNcenter, hNgain⟩ := (hcp.and hgp).exists
  let t := (s j).fejer hb hf N
  have htEven : t.IsEven := (s j).fejer_even hb hf heven N
  refine ⟨d j, n j, t, ε j, r, K, (s j).fejer_polynomial hb hf N, htEven,
    ⟨b, hb, (s j).fejer_floor hb hf N⟩, ?_, hε0, hj, hε1, ?_, hNgain.le,
    hq0.trans hqr.le, hr3, hNcenter, hK0, hK2,
    (s j).fejer_augmented_prefix hb hf N (sq_nonneg K) haug,
    (s j).fejer_matrix_floor hb hf N hmat, ?_, ?_⟩
  · exact t.rawGram_real htEven
  · exact ((s j).fejer_mass hb hf N).trans hmass
  · intro i
    have hi := (s j).fejer_inverse_diagonal hb hf N (Sum.inr i)
    linarith [hdiag i]
  · exact ((s j).fejer_inverse_diagonal hb hf N (Sum.inl ())).trans_lt hconst

end SchauderTranslates
