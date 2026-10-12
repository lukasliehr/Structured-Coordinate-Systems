import Lean_Code.SchauderTranslates.ActivatedScalarEstimates
import Lean_Code.SchauderTranslates.ScalarFloor

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- The operator activation gain agrees with the scalar rare-step polynomial. -/
theorem activationLimitGain_eq_rareGain (s : ScalarData d n) {ε : ℝ} (hm : s.mass = 1 - ε)
    (p : ℝ) : s.activationLimitGain p = rareGain ε s.gain p := by
  rw [s.activationLimitGain_formula, hm]
  simp only [sub_sub_cancel, rareGain]

/-- The mass of a finite scalar cutoff, written in deficit coordinates. -/
theorem cutoffData_mass_deficit (s : ScalarData d n) {ε p : ℝ} (hm : s.mass = 1 - ε)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) {m : ℕ}
    (e : Fin m ≃ CutoffNonconstant n N) :
    (s.cutoffData p N e).mass = 1 - p * ε := by
  rw [cutoffData, s.activationData_mass hp0 hp1, hm, sub_sub_cancel]

/-- The concrete product of a finite cutoff inherits the complete rare-step numerical bounds.
The two cutoff gain hypotheses are precisely the finite-approximation target and upper bound;
the remaining conclusions concern the actual next torus block. -/
theorem cutoff_product_step (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {ε p : ℝ} (hm : s.mass = 1 - ε)
    (he : 0 < ε) (hemax : ε ≤ 1 / 10) (hZ : 1 / 646 ≤ s.gain)
    (hZmax : s.gain ≤ 1 / 323) (hp : 0 < p) (hpmax : p ≤ 1 / 100)
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
    scalar_step_numerics he hemax hZ hp hpmax hpe hzlo hzhi
  have heq : ε' = 1 - (1 - p * ε) ^ L := by dsimp [ε']; rw [hmass]
  have hel' : ε / 12 ≤ ε' := by simpa only [heq] using hel
  have heu' : ε' ≤ ε - 3 * ε ^ 2 / 4 := by simpa only [heq] using heu
  have he' : 0 < ε' := lt_of_lt_of_le (by positivity) hel'
  have hgain : next.gain = (L : ℝ) * cut.gain := cut.product_gain L
  have hgl' : s.gain - cut.gain < next.gain := by rw [hgain]; exact hgl
  have hgu' : next.gain ≤ s.gain := by rw [hgain]; exact hgu
  have hnorm : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) next.rawGram⁻¹‖ ≤ ε'⁻¹ ^ 2 := by
    apply scalar_floor_step cut L he hemax he' heu' (by dsimp [ε', next]; ring)
      (hgu'.trans hZmax) (s.cutoffData_rawInverse_norm_le hb hfloor p N e) hold
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

end ScalarData
end SchauderTranslates
