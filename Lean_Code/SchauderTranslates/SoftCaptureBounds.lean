import Lean_Code.SchauderTranslates.SoftCapture
import Lean_Code.SchauderTranslates.ScalarRawCapture
import Lean_Code.SchauderTranslates.ScalarSupply

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Continuity includes both endpoints because the whole interpolated Gram is positive definite. -/
theorem softCapture_continuousOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ) :
    ContinuousOn (softCapture G b) (Set.Icc 0 1) := by
  intro t ht
  have hc : Continuous (fun t : ℝ => (softGram G t, b)) := by unfold softGram; fun_prop
  have hcap : ContinuousAt (fun t => gramCapture (softGram G t) b) t :=
    (gramCapture_continuousAt (softGram_posDef hG ht.1 ht.2) b).comp
      (f := fun u : ℝ => (softGram G u, b)) (x := t) hc.continuousAt
  exact ((show ContinuousAt (fun t : ℝ => (1 - t) ^ 2) t by fun_prop).mul hcap).continuousWithinAt

namespace ScalarData
variable {d n : ℕ}

def softCapture (s : ScalarData d n) : ℝ → ℝ :=
  SchauderTranslates.softCapture s.nonconstantGram s.moment

theorem softCapture_zero_lower (s : ScalarData d n) {ε : ℝ} (hε : ε ≤ 1 / 10)
    (hm : s.mass = 1 - ε) (hz : 1 / 646 ≤ s.gain) : (1 / 1000 : ℝ) ≤ s.softCapture 0 := by
  rw [softCapture, SchauderTranslates.softCapture_zero, s.raw_capture_gain]
  have hden : 0 < 1 + s.gain := by linarith [s.gain_nonneg]
  apply (le_div_iff₀ hden).mpr
  have hmass : 9 / 10 ≤ s.mass := by rw [hm]; linarith
  have hprod := mul_le_mul_of_nonneg_right hmass s.gain_nonneg
  nlinarith

theorem softCapture_sqrt_upper (s : ScalarData d n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (hm : s.mass = 1 - ε) : s.softCapture (Real.sqrt ε) ≤ Real.sqrt ε := by
  have hr0 := Real.sqrt_pos.mpr hε0
  have hr1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have h := softCapture_le_norm_div s.nonconstantGram_posDef s.moment hr0 hr1
  have hn := s.moment_norm_sq_le_deficit
  rw [hm] at hn
  have hs := Real.sq_sqrt hε0.le
  apply h.trans
  apply (div_le_iff₀ hr0).mpr
  nlinarith

end ScalarData

/-- All soft-capture estimates for an actual scalar-supply block, with explicit numerical
thresholds. In particular `c₀ = 1/1000` works for every deficit at most `1/10`. -/
theorem soft_capture_bounds {d n : ℕ} (s : ScalarData d n) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) (hm : s.mass = 1 - ε)
    (hz : 1 / 646 ≤ s.gain) (hfloor : (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef) :
    AntitoneOn s.softCapture (Set.Icc 0 1) ∧ ContinuousOn s.softCapture (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ s.softCapture t) ∧
      (1 / 1000 : ℝ) ≤ s.softCapture 0 ∧
      (1 / 1000 : ℝ) / 4 ≤ s.softCapture (ε ^ 2) ∧
      s.softCapture (Real.sqrt ε) ≤ Real.sqrt ε ∧
      (∀ R t : ℝ, 1 ≤ R → 0 ≤ t → R * t ≤ 1 / 2 →
        s.softCapture t / (4 * R) ≤ s.softCapture (R * t)) := by
  have hzero := s.softCapture_zero_lower hε1 hm hz
  have hlow := softCapture_floor_lower s.nonconstantGram_posDef s.moment hε0.le hε1
    (s.nonconstantGram_floor hfloor)
  refine ⟨softCapture_antitone s.nonconstantGram_posDef s.nonconstantGram_le_one s.moment,
    softCapture_continuousOn s.nonconstantGram_posDef s.moment,
    fun t ht => softCapture_nonneg s.nonconstantGram_posDef s.moment ht.1 ht.2,
    hzero, ?_, s.softCapture_sqrt_upper hε0 hε1 hm,
    fun R t hR ht hRt => softCapture_scale_lower s.nonconstantGram_posDef s.moment hR ht hRt⟩
  have hz' : (1 / 1000 : ℝ) ≤ gramCapture s.nonconstantGram s.moment := by
    simpa only [ScalarData.softCapture, softCapture_zero] using hzero
  exact (div_le_div_of_nonneg_right hz' (by norm_num)).trans hlow

end SchauderTranslates
