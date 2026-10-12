import Lean_Code.SchauderTranslates.Sharp.Contracts
import Lean_Code.SchauderTranslates.Sharp.ScalarSharpStage
import Lean_Code.SchauderTranslates.ScalarSmoothing
import Lean_Code.SchauderTranslates.ScalarAffinePrefixes
import Lean_Code.SchauderTranslates.ScalarAffineGain

/-!
# Sharp scalar supply and sharp prescribed gain

Paper: Proposition `h2:lem:scalar` and Corollary `h2:cor:tune` of `combined_v3.tex`.
For every `0 < dd ≤ 1` the scalar blocks have centered and augmented prefix constants
`< 1 + dd` and retained gain at least `c_d = Z₀ / 2`, where `t = dd / 4`, `a₀ = t / 100`
and `Z₀ = a₀² / (4 - 8 a₀ + 3 a₀²)`.

The centered squared constant is `Q_n < 1 + 2 t`, and the augmented squared constant is
`Q_n + (5 / t) η_n < 1 + 2 t` (the bound supplied by the copies lemma, which is also the
next centered budget), so `K = √(1 + 2 t) < 1 + dd` serves for both families.
-/

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates

namespace Scalar

/-- Even polynomial scalar blocks with arbitrarily small loss for the parameter `t`:
gain in `[Z₀ / 2, Z₀]`, centered squared prefix bound `q < 1 + 2 t`, augmented squared prefix
bound `1 + 2 t`, and the raw floor and inverse estimates. -/
theorem polynomial_scalar_blocks_sharp {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (d n : ℕ) (s : ScalarData d n) (ε q : ℝ),
      s.IsPolynomial ∧ s.IsEven ∧ s.HasPositiveFloor ∧
      (∀ i j, (s.rawGram i j).im = 0) ∧
      0 < ε ∧ ε < δ ∧ ε ≤ sharpA t ∧ s.mass = 1 - ε ∧
      sharpZ t / 2 ≤ s.gain ∧ s.gain ≤ sharpZ t ∧
      1 + t ≤ q ∧ q < 1 + 2 * t ∧ s.CenteredPrefixSqBound q ∧
      s.AugmentedPrefixSqBound (1 + 2 * t) ∧
      (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef ∧
      (∀ i : Fin n, (s.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re ≤ 1 + 2 * ε) ∧
      (s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2 := by
  obtain ⟨d, n, s, ε, q, _, hlim, hs⟩ := measurable_scalar_blocks_sharp ht0 ht1
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨heven, hfloor, hε0, hε1, hmass, hgain, hgainU, hdiag, hmat,
    hq1, hq2, hcenter, haug, hconst⟩ := hs j
  obtain ⟨b, hb, hf⟩ := hfloor
  let r : ℝ := (q j + (1 + 2 * t)) / 2
  have hqr : q j < r := by dsimp [r]; linarith
  have hr : r < 1 + 2 * t := by dsimp [r]; linarith
  have hq0 : 0 ≤ q j := by linarith
  have hZ := sharpZ_pos ht0 ht1
  have hgain' : sharpZ t / 2 < (s j).gain := by linarith
  have hcp := (s j).fejer_centered_prefix_eventually hb hf hq0 hqr hcenter
  have hgp := ((s j).fejer_gain_tendsto hb hf).eventually (lt_mem_nhds hgain')
  obtain ⟨N, hNcenter, hNgain⟩ := (hcp.and hgp).exists
  let u := (s j).fejer hb hf N
  have huEven : u.IsEven := (s j).fejer_even hb hf heven N
  have huMass : u.mass = (s j).mass := (s j).fejer_mass hb hf N
  refine ⟨d j, n j, u, ε j, r, (s j).fejer_polynomial hb hf N, huEven,
    ⟨b, hb, (s j).fejer_floor hb hf N⟩, u.rawGram_real huEven, hε0, hj, hε1,
    huMass.trans hmass, hNgain.le, ?_, by linarith, hr, hNcenter,
    (s j).fejer_augmented_prefix hb hf N (by linarith) haug,
    (s j).fejer_matrix_floor hb hf N hmat, ?_, ?_⟩
  · have hi := (s j).fejer_inverse_diagonal hb hf N (Sum.inl ())
    have hm := (s j).toTorusWeight.mass_pos
    have hmul := mul_le_mul_of_nonneg_left hi hm.le
    have hu : u.gain ≤ (s j).gain := by
      rw [u.gain_eq_mass_inverse_constant, (s j).gain_eq_mass_inverse_constant, huMass]
      linarith
    exact hu.trans hgainU
  · intro i
    have hi := (s j).fejer_inverse_diagonal hb hf N (Sum.inr i)
    linarith [hdiag i]
  · exact ((s j).fejer_inverse_diagonal hb hf N (Sum.inl ())).trans_lt hconst

end Scalar

open Scalar

/-- The retained scalar gain `c_d = Z₀ / 2` of the sharp construction, where `t = dd / 4`,
`a₀ = t / 100` and `Z₀ = a₀² / (4 - 8 a₀ + 3 a₀²)`. -/
def scalarSharpGain (dd : ℝ) : ℝ := sharpZ (dd / 4) / 2

theorem scalarSharpGain_pos {dd : ℝ} (hd0 : 0 < dd) (hd1 : dd ≤ 1) : 0 < scalarSharpGain dd :=
  half_pos (sharpZ_pos (by positivity) (by linarith))

theorem scalarSharpGain_le_one {dd : ℝ} (hd0 : 0 < dd) (hd1 : dd ≤ 1) :
    scalarSharpGain dd ≤ 1 := by
  have h := sharpZ_le_one (t := dd / 4) (by positivity) (by linarith)
  unfold scalarSharpGain
  linarith

/-- The body of `ScalarSupplySharp` for an explicit gain `cd`. -/
def ScalarSupplySharpWith (dd cd : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ (d n : ℕ) (s : ScalarData d n) (ε q K : ℝ),
      s.IsPolynomial ∧ s.IsEven ∧ s.HasPositiveFloor ∧
      (∀ i j, (s.rawGram i j).im = 0) ∧
      0 < ε ∧ ε < δ ∧ ε ≤ 1 / 10 ∧ s.mass = 1 - ε ∧
      cd ≤ s.gain ∧ 0 ≤ q ∧ q < (1 + dd) ^ 2 ∧ s.CenteredPrefixSqBound q ∧
      0 ≤ K ∧ K < 1 + dd ∧ s.AugmentedPrefixSqBound (K ^ 2) ∧
      (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef ∧
      (∀ i : Fin n, (s.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re ≤ 1 + 2 * ε) ∧
      (s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2

/-- The body of `ScalarTuneSharp` for an explicit gain `cd`. -/
def ScalarTuneSharpWith (dd cd : ℝ) : Prop :=
  ∀ z δ : ℝ, 0 < z → z < cd → 0 < δ →
    ∃ (d n : ℕ) (s : ScalarData d n) (ε K : ℝ),
      s.IsPolynomial ∧ s.IsEven ∧ s.HasPositiveFloor ∧
      (∀ i j, (s.rawGram i j).im = 0) ∧
      0 < ε ∧ ε < δ ∧ ε ≤ 1 / 10 ∧ s.mass = 1 - ε ∧ s.gain = z ∧
      0 ≤ K ∧ K < 1 + dd ∧ s.CenteredPrefixSqBound (K ^ 2) ∧ s.AugmentedPrefixSqBound (K ^ 2)

/-- Sharp scalar supply with the explicit gain `scalarSharpGain dd = Z₀ / 2`
(paper: Proposition `h2:lem:scalar`). -/
theorem scalarSupplySharpWith {dd : ℝ} (hd0 : 0 < dd) (hd1 : dd ≤ 1) :
    ScalarSupplySharpWith dd (scalarSharpGain dd) := by
  intro δ hδ
  have ht0 : (0 : ℝ) < dd / 4 := by positivity
  have ht1 : dd / 4 ≤ 1 / 4 := by linarith
  obtain ⟨d, n, s, ε, q, hpoly, heven, hfloor, hreal, hε0, hεδ, hε1, hmass, hgain, _,
    hq1, hq2, hcenter, haug, hmat, hdiag, hconst⟩ :=
    polynomial_scalar_blocks_sharp ht0 ht1 hδ
  have hK : (0 : ℝ) ≤ 1 + 2 * (dd / 4) := by linarith
  refine ⟨d, n, s, ε, q, Real.sqrt (1 + 2 * (dd / 4)), hpoly, heven, hfloor, hreal, hε0, hεδ,
    hε1.trans (sharpA_le_tenth ht1), hmass, hgain, by linarith, by nlinarith, hcenter,
    Real.sqrt_nonneg _, ?_, ?_, hmat, hdiag, hconst⟩
  · exact (Real.sqrt_lt' (by linarith)).mpr (by nlinarith)
  · rw [Real.sq_sqrt hK]
    exact haug

/-- Sharp prescribed gain below the same explicit constant `scalarSharpGain dd`
(paper: Corollary `h2:cor:tune`). The affine path preserves the ordered augmented bound;
orthogonal removal of the initial constant gives the same centered bound. -/
theorem scalarTuneSharpWith {dd : ℝ} (hd0 : 0 < dd) (hd1 : dd ≤ 1) :
    ScalarTuneSharpWith dd (scalarSharpGain dd) := by
  intro z δ hz hz1 hδ
  obtain ⟨d, n, s, ε, q, K, hpoly, heven, hfloor, _, hε0, hεδ, hε1, hmass,
    hgain, _, _, _, hK0, hK2, haug, _, _, _⟩ := scalarSupplySharpWith hd0 hd1 δ hδ
  obtain ⟨θ, hθ0, hθ1, hθpos, hθgain⟩ := s.exists_affine_gain hz (hz1.le.trans hgain)
  let u := s.affine θ hθ0 hθ1
  let J := max 1 K
  have hJ1 : 1 ≤ J := le_max_left _ _
  have hJK : K ≤ J := le_max_right _ _
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ1
  have hJ2 : J < 1 + dd := max_lt (by linarith) hK2
  have hqJ : K ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ hK0 hJK 2
  have hJq : 1 ≤ J ^ 2 := by nlinarith
  have hpJ : s.AugmentedPrefixSqBound (J ^ 2) := FinitePrefixSqBound.mono haug hqJ
  have huEven : u.IsEven := s.affine_even heven θ hθ0 hθ1
  obtain ⟨b, hb, hf⟩ := hfloor
  refine ⟨d, n, u, θ * ε, J, s.affine_polynomial hpoly θ hθ0 hθ1, huEven,
    ⟨b, hb, s.affine_floor hb hf θ hθ0 hθ1⟩, u.rawGram_real huEven,
    mul_pos hθpos hε0, ?_, ?_, ?_, hθgain, hJ0, hJ2,
    s.affine_centered_prefix θ hθ0 hθ1 hJq hpJ,
    s.affine_augmented_prefix θ hθ0 hθ1 hJq hpJ⟩
  · exact (mul_le_of_le_one_left hε0.le hθ1).trans_lt hεδ
  · exact (mul_le_of_le_one_left hε0.le hθ1).trans hε1
  · change (s.affine θ hθ0 hθ1).mass = _
    rw [s.affine_mass, hmass]
    ring

/-- Sharp scalar supply (paper: Proposition `h2:lem:scalar`). -/
theorem scalarSupplySharp {dd : ℝ} (hd0 : 0 < dd) (hd1 : dd ≤ 1) : ScalarSupplySharp dd :=
  ⟨scalarSharpGain dd, scalarSharpGain_pos hd0 hd1, scalarSupplySharpWith hd0 hd1⟩

/-- Sharp prescribed gain (paper: Corollary `h2:cor:tune`). -/
theorem scalarTuneSharp {dd : ℝ} (hd0 : 0 < dd) (hd1 : dd ≤ 1) : ScalarTuneSharp dd :=
  ⟨scalarSharpGain dd, scalarSharpGain_pos hd0 hd1, scalarTuneSharpWith hd0 hd1⟩

/-- Supply and tuning with one common gain constant. -/
theorem scalarSupplyTuneSharp {dd : ℝ} (hd0 : 0 < dd) (hd1 : dd ≤ 1) :
    ∃ cd : ℝ, 0 < cd ∧ ScalarSupplySharpWith dd cd ∧ ScalarTuneSharpWith dd cd :=
  ⟨scalarSharpGain dd, scalarSharpGain_pos hd0 hd1, scalarSupplySharpWith hd0 hd1,
    scalarTuneSharpWith hd0 hd1⟩

end SchauderTranslates.Sharp
