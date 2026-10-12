import Lean_Code.PositiveBiorthogonal.Interpretation
import Lean_Code.PositiveBiorthogonal.BasicLp
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! Bilinear norm detection, paired operator norms, and rank-one norms. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators ComplexOrder
open scoped ComplexConjugate

namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

/-- The bilinear norming phase, with value zero at zero by totalized division. -/
def normingPhase (z : 𝕜) : 𝕜 := conj z / (‖z‖ : 𝕜)

theorem mul_normingPhase (z : 𝕜) : z * normingPhase z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [normingPhase, hz]
  have hn : (‖z‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [normingPhase, ← mul_div_assoc, RCLike.mul_conj]
  simp [pow_two, hn]

theorem norm_normingPhase_le (z : 𝕜) : ‖normingPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [normingPhase, hz]
  simp [normingPhase, norm_div, norm_ne_zero_iff.mpr hz]

theorem stronglyMeasurable_normingPhase (f : ℝ → 𝕜) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x => normingPhase (f x)) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let : BorelSpace 𝕜 := ⟨rfl⟩
  have hc : Measurable (fun x => conj (f x)) :=
    RCLike.continuous_conj.measurable.comp hf.measurable
  have hn : Measurable (fun x => (‖f x‖ : 𝕜)) :=
    RCLike.continuous_ofReal.measurable.comp hf.measurable.norm
  exact (hc.div hn).stronglyMeasurable

theorem norming_test_L1 (f : L 𝕜 1) :
    ∃ g : L 𝕜 ∞, ‖g‖ ≤ 1 ∧ pairing f g = (‖f‖ : 𝕜) := by
  have hmeas : AEStronglyMeasurable (fun x => normingPhase (f x)) volume :=
    (stronglyMeasurable_normingPhase f (Lp.stronglyMeasurable f)).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ, ‖normingPhase (f x)‖ ≤ 1 :=
    Eventually.of_forall fun x => norm_normingPhase_le (f x)
  have hg := memLp_top_of_bound hmeas 1 hbound
  refine ⟨hg.toLp _, ?_, ?_⟩
  · rw [Lp.norm_toLp]
    have he : eLpNorm (fun x => normingPhase (f x)) ∞ volume ≤ 1 := by
      simpa only [eLpNorm_exponent_top, ENNReal.ofReal_one] using
        eLpNormEssSup_le_of_ae_bound hbound
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top he
  · unfold pairing
    calc
      (∫ x : ℝ, f x * hg.toLp _ x) = ∫ x : ℝ, (‖f x‖ : 𝕜) := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp] with x hx
        rw [hx, mul_normingPhase]
      _ = (‖f‖ : 𝕜) := by rw [integral_ofReal, ← L1.norm_eq_integral_norm]

theorem norming_bound_L1 (f : L 𝕜 1) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ g : L 𝕜 ∞, ‖pairing f g‖ ≤ C * ‖g‖) : ‖f‖ ≤ C := by
  obtain ⟨g, hg, hfg⟩ := norming_test_L1 f
  have h := hbound g
  rw [hfg, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg f)] at h
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hg hC)

theorem norm_top_le_of_ae_bound (f : L 𝕜 ∞) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x : ℝ, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def]
  have he : eLpNorm f ∞ volume ≤ ENNReal.ofReal C := by
    simpa only [eLpNorm_exponent_top] using eLpNormEssSup_le_of_ae_bound hf
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hC)

theorem norming_bound_top (f : L 𝕜 ∞) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ g : L 𝕜 1, ‖pairing f g‖ ≤ C * ‖g‖) : ‖f‖ ≤ C := by
  by_contra! hlt
  let a := (C + ‖f‖) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hCa : C < a := by dsimp [a]; linarith
  have haf : a < ‖f‖ := by dsimp [a]; linarith
  let E := {x : ℝ | a < ‖f x‖}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).norm.measurable
  have hEpos : 0 < volume E := by
    by_contra! hzero
    have hae : ∀ᵐ x : ℝ, ‖f x‖ ≤ a := by
      rw [ae_iff]
      simpa only [not_le] using le_antisymm hzero bot_le
    exact haf.not_ge (norm_top_le_of_ae_bound f a ha.le hae)
  obtain ⟨F, hF, hFE, hFpos, hFfin⟩ := volume.exists_subset_measure_lt_top hE hEpos
  let raw := F.indicator (fun x => normingPhase (f x))
  have hraw : MemLp raw 1 volume := by
    apply (memLp_indicator_const 1 hF (1 : 𝕜) (Or.inr hFfin.ne)).of_le
      ((stronglyMeasurable_normingPhase f (Lp.stronglyMeasurable f)).indicator hF).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ F
    · simpa only [raw, Set.indicator_of_mem hx, norm_one] using norm_normingPhase_le (f x)
    · simp [hx]
  let g : L 𝕜 1 := hraw.toLp raw
  have hgBound : ‖g‖ ≤ volume.real F := by
    have hle : ‖g‖ ≤ ‖indicatorConstLp 1 hF hFfin.ne (1 : 𝕜)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hraw.coeFn_toLp,
        indicatorConstLp_coeFn (p := (1 : ℝ≥0∞)) (hs := hF) (hμs := hFfin.ne) (c := (1 : 𝕜))]
        with x hx hy
      change ‖hraw.toLp raw x‖ ≤ _
      rw [hx, hy]
      by_cases hxs : x ∈ F
      · simpa only [raw, Set.indicator_of_mem hxs, norm_one] using norm_normingPhase_le (f x)
      · simp [raw, hxs]
    simpa [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top] using hle
  have he : (fun x : ℝ => f x * g x) =ᵐ[volume]
      (fun x => ((F.indicator (fun y => ‖f y‖) x : ℝ) : 𝕜)) := by
    filter_upwards [hraw.coeFn_toLp] with x hx
    change f x * hraw.toLp raw x = _
    rw [hx]
    by_cases hxs : x ∈ F
    · simpa only [raw, Set.indicator_of_mem hxs] using mul_normingPhase (f x)
    · simp [raw, hxs]
  have hi : Integrable (fun x : ℝ => f x * g x) volume :=
    (Lp.memLp f).integrable_mul (Lp.memLp g)
  have hre : (fun x : ℝ => RCLike.re (f x * g x)) =ᵐ[volume]
      F.indicator (fun y => ‖f y‖) := by
    filter_upwards [he] with x hx
    rw [hx]
    simp
  have hreal := hi.re.congr hre
  have hpair : pairing f g = (∫ x : ℝ, F.indicator (fun y => ‖f y‖) x : ℝ) := by
    unfold pairing
    rw [integral_congr_ae he, integral_ofReal]
  have hnonneg : 0 ≤ ∫ x : ℝ, F.indicator (fun y => ‖f y‖) x := by
    apply integral_nonneg
    intro x
    by_cases hx : x ∈ F <;> simp [hx]
  have hupper := hbound g
  rw [hpair, RCLike.norm_ofReal, abs_of_nonneg hnonneg] at hupper
  have hconst : Integrable (F.indicator (fun _ => a)) volume :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 hF a (Or.inr hFfin.ne))
  have hlower := integral_mono hconst hreal (show F.indicator (fun _ => a) ≤
      F.indicator (fun y => ‖f y‖) from fun x => by
    by_cases hx : x ∈ F
    · simpa only [Set.indicator_of_mem hx] using (hFE hx).le
    · simp [hx])
  rw [integral_indicator_const a hF, smul_eq_mul] at hlower
  have hmeasure : 0 < volume.real F := ENNReal.toReal_pos hFpos.ne' hFfin.ne
  have hmul := mul_le_mul_of_nonneg_left hgBound hC
  nlinarith

def powerNormingPhase (z : 𝕜) (t : ℝ) : 𝕜 := normingPhase z * (‖z‖ ^ t : ℝ)

theorem norm_powerNormingPhase (z : 𝕜) (t : ℝ) (ht : 0 < t) :
    ‖powerNormingPhase z t‖ = ‖z‖ ^ t := by
  by_cases hz : z = 0
  · simp [powerNormingPhase, normingPhase, hz, Real.zero_rpow ht.ne']
  simp [powerNormingPhase, normingPhase, norm_mul, norm_div, norm_ne_zero_iff.mpr hz,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) t)]

theorem mul_powerNormingPhase (z : 𝕜) (t : ℝ) (ht : 0 < t) :
    z * powerNormingPhase z t = (‖z‖ ^ (t + 1) : ℝ) := by
  rw [powerNormingPhase, ← mul_assoc, mul_normingPhase, ← RCLike.ofReal_mul]
  congr 1
  rw [Real.rpow_add_one' (norm_nonneg z) (by linarith)]
  ring

theorem stronglyMeasurable_powerNormingPhase (f : ℝ → 𝕜)
    (hf : StronglyMeasurable f) (t : ℝ) :
    StronglyMeasurable (fun x => powerNormingPhase (f x) t) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let : BorelSpace 𝕜 := ⟨rfl⟩
  have hph := (stronglyMeasurable_normingPhase f hf).measurable
  have hpw : Measurable (fun x => ((‖f x‖ ^ t : ℝ) : 𝕜)) :=
    RCLike.continuous_ofReal.measurable.comp (hf.norm.measurable.pow_const t)
  exact (hph.mul hpw).stronglyMeasurable

theorem norming_bound_interior [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (f : L 𝕜 p) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ g : L 𝕜 q, ‖pairing f g‖ ≤ C * ‖g‖) : ‖f‖ ≤ C := by
  let : Fact (1 ≤ p) := ⟨hp1.le⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  have hreal := ENNReal.HolderConjugate.toReal_of_ne_top hpfin hqfin
  have hpt : 1 < p.toReal := hreal.lt
  let t := p.toReal - 1
  have ht : 0 < t := by dsimp [t]; linarith
  have he_exp : q * ENNReal.ofReal t = p := by
    rw [← ENNReal.ofReal_toReal hqfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_toReal hpfin]
    congr 1
    simpa only [t, mul_comm] using hreal.sub_one_mul_conj
  let raw := fun x : ℝ => powerNormingPhase (f x) t
  have he_norm : eLpNorm raw q volume = eLpNorm f p volume ^ t := by
    calc
      eLpNorm raw q volume = eLpNorm (fun x => ‖f x‖ ^ t) q volume := by
        apply eLpNorm_congr_norm_ae
        apply Eventually.of_forall
        intro x
        rw [norm_powerNormingPhase (f x) t ht,
          Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      _ = eLpNorm f (q * ENNReal.ofReal t) volume ^ t := eLpNorm_norm_rpow f ht
      _ = eLpNorm f p volume ^ t := by rw [he_exp]
  have hraw : MemLp raw q volume := by
    refine ⟨(stronglyMeasurable_powerNormingPhase f (Lp.stronglyMeasurable f) t).aestronglyMeasurable, ?_⟩
    rw [he_norm]
    exact ENNReal.rpow_lt_top_of_nonneg ht.le (Lp.memLp f).2.ne
  let g : L 𝕜 q := hraw.toLp raw
  have hg_norm : ‖g‖ = ‖f‖ ^ t := by
    rw [Lp.norm_toLp, he_norm, ← ENNReal.toReal_rpow, Lp.norm_def]
  have hpair : pairing f g = (‖f‖ ^ p.toReal : ℝ) := by
    unfold pairing
    calc
      (∫ x : ℝ, f x * g x) = ∫ x : ℝ, ((‖f x‖ ^ p.toReal : ℝ) : 𝕜) := by
        apply integral_congr_ae
        filter_upwards [hraw.coeFn_toLp] with x hx
        change f x * hraw.toLp raw x = _
        rw [hx]
        simpa only [t, sub_add_cancel] using mul_powerNormingPhase (f x) t ht
      _ = (‖f‖ ^ p.toReal : ℝ) := by
        rw [integral_ofReal, ← norm_rpow_eq_integral f hp0 hpfin]
  have h := hbound g
  rw [hpair, RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg f) _), hg_norm] at h
  by_cases hf : ‖f‖ = 0
  · simpa only [hf] using hC
  have hfpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf)
  have hpow : 0 < ‖f‖ ^ t := Real.rpow_pos_of_pos hfpos t
  have hid : ‖f‖ ^ p.toReal = ‖f‖ ^ t * ‖f‖ := by
    convert Real.rpow_add_one hf t using 1
    simp [t]
  rw [hid] at h
  nlinarith

/-- Norm detection by the bilinear pairing, including both endpoints. -/
theorem norming_bound [ENNReal.HolderConjugate p q] (f : L 𝕜 p) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ g : L 𝕜 q, ‖pairing f g‖ ≤ C * ‖g‖) : ‖f‖ ≤ C := by
  by_cases hp : p = 1
  · subst p
    have hq : q = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q 1).mpr rfl
    subst q
    exact norming_bound_L1 f C hC hbound
  by_cases hpfin : p = ∞
  · subst p
    have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    subst q
    exact norming_bound_top f C hC hbound
  exact norming_bound_interior (lt_of_le_of_ne (ENNReal.HolderConjugate.one_le p q) (Ne.symm hp))
    hpfin f C hC hbound

theorem pairing_comm (f : L 𝕜 p) (g : L 𝕜 q) : pairing f g = pairing g f := by
  simp only [pairing, mul_comm]

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def pairingCLM : L 𝕜 p →L[𝕜] L 𝕜 q →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing volume p q

@[simp] theorem pairingCLM_apply (f : L 𝕜 p) (g : L 𝕜 q) :
    pairingCLM f g = pairing f g := by
  simpa [pairingCLM, pairing] using
    (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing_eq_integral f g

theorem pairing_continuous_left (g : L 𝕜 q) :
    Continuous (fun f : L 𝕜 p => pairing f g) := by
  exact ((pairingCLM (𝕜 := 𝕜) (p := p) (q := q)).flip g).continuous.congr
    (fun f => pairingCLM_apply f g)

theorem pairing_continuous_right (f : L 𝕜 p) :
    Continuous (fun g : L 𝕜 q => pairing f g) := by
  exact (pairingCLM (q := q) f).continuous.congr (fun g => pairingCLM_apply f g)

def representedFunctional (g : L 𝕜 q) : L 𝕜 p →L[𝕜] 𝕜 := pairingCLM.flip g

@[simp] theorem representedFunctional_apply (g : L 𝕜 q) (f : L 𝕜 p) :
    representedFunctional g f = pairing f g := pairingCLM_apply f g

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
theorem norm_pairing_le (f : L 𝕜 p) (g : L 𝕜 q) :
    ‖pairing f g‖ ≤ ‖f‖ * ‖g‖ := by
  have heq : pairing f g = ∫ x : ℝ, (f • g : L 𝕜 1) x := by
    unfold pairing
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) f g] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx.symm
  rw [heq]
  calc
    ‖∫ x : ℝ, (f • g : L 𝕜 1) x‖ ≤ ∫ x : ℝ, ‖(f • g : L 𝕜 1) x‖ :=
      norm_integral_le_integral_norm _
    _ = ‖(f • g : L 𝕜 1)‖ := (L1.norm_eq_integral_norm _).symm
    _ ≤ ‖f‖ * ‖g‖ := Lp.norm_smul_le f g

theorem norm_representedFunctional_le (g : L 𝕜 q) :
    ‖representedFunctional (p := p) g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  simpa only [representedFunctional_apply, mul_comm] using norm_pairing_le f g

theorem norm_representedFunctional (g : L 𝕜 q) :
    ‖representedFunctional (p := p) g‖ = ‖g‖ := by
  apply le_antisymm (norm_representedFunctional_le g)
  apply norming_bound (q := p) g _ (norm_nonneg _)
  intro f
  rw [pairing_comm g f, ← representedFunctional_apply g f]
  exact (representedFunctional g).le_opNorm f

theorem paired_operator_norm_le (A : L 𝕜 p →L[𝕜] L 𝕜 p)
    (D : L 𝕜 q →L[𝕜] L 𝕜 q)
    (h : ∀ f g, pairing (A f) g = pairing f (D g)) : ‖D‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  apply norming_bound (q := p) (D g) _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro f
  rw [pairing_comm (D g) f, ← h]
  calc
    ‖pairing (A f) g‖ ≤ ‖A f‖ * ‖g‖ := norm_pairing_le _ _
    _ ≤ (‖A‖ * ‖f‖) * ‖g‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm f) (norm_nonneg _)
    _ = (‖A‖ * ‖g‖) * ‖f‖ := by ring

theorem paired_operator_norm_eq (A : L 𝕜 p →L[𝕜] L 𝕜 p)
    (D : L 𝕜 q →L[𝕜] L 𝕜 q)
    (h : ∀ f g, pairing (A f) g = pairing f (D g)) : ‖A‖ = ‖D‖ := by
  apply le_antisymm _ (paired_operator_norm_le A D h)
  apply paired_operator_norm_le D A
  intro g f
  rw [pairing_comm (D g) f, ← h, pairing_comm (A f) g]

theorem represented_rank_one_norm (v : L 𝕜 p) (g : L 𝕜 q) :
    ‖(representedFunctional (p := p) g).smulRight v‖ = ‖v‖ * ‖g‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_representedFunctional, mul_comm]

omit [Fact (1 ≤ q)] in
theorem pairing_separates_left (f : L 𝕜 p) (h : ∀ g : L 𝕜 q, pairing f g = 0) : f = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact norming_bound (q := q) f 0 le_rfl (by intro g; simp [h])

omit [Fact (1 ≤ p)] in
theorem pairing_separates_right (g : L 𝕜 q) (h : ∀ f : L 𝕜 p, pairing f g = 0) : g = 0 := by
  apply pairing_separates_left (q := p) g
  intro f
  rw [pairing_comm, h]

omit [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] in
theorem rank_one_norm (v : L 𝕜 p) (c : L 𝕜 p →L[𝕜] 𝕜) :
    ‖c.smulRight v‖ = ‖c‖ * ‖v‖ :=
  ContinuousLinearMap.norm_smulRight_apply c v

omit [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] in
theorem represented_pairing_biorthogonal (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ) (n l : ℕ) :
    pairing (B.b n) (γ l) = if n = l then 1 else 0 := by
  rw [← hγ, B.biorthogonal]

omit [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] in
theorem represented_expansion (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ) (f : L 𝕜 p) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, pairing f (γ n) • B.b n)
      atTop (𝓝 f) := by
  unfold Represents at hγ
  simpa only [hγ] using B.expansion f

end PositiveBiorthogonal
