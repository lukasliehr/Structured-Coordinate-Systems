import Lean_Code.PositiveBiorthogonal.PairingNorms
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The local norm-power derivative used for arbitrary positive bases. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators ComplexOrder

namespace PositiveBiorthogonal

def scalarPowerDerivative (r a c t : ℝ) : ℝ :=
  -(r * |a - t * c| ^ (r - 2) * (a - t * c) * c)

theorem scalar_power_derivative (r : ℝ) (hr : 1 < r) (a c t : ℝ) :
    HasDerivAt (fun s : ℝ => |a - s * c| ^ r) (scalarPowerDerivative r a c t) t := by
  simpa only [scalarPowerDerivative, zero_sub, one_mul, mul_neg, neg_mul,
    Function.comp_def, Pi.sub_apply, id_eq] using
    (hasDerivAt_abs_rpow (a - t * c) hr).comp t
      ((hasDerivAt_const t a).sub ((hasDerivAt_id t).mul_const c))

theorem rpow_mul_self (a r : ℝ) (_ha : 0 ≤ a) (hr : 1 < r) :
    a ^ (r - 2) * a = a ^ (r - 1) := by
  by_cases hz : a = 0
  · simp [hz, Real.zero_rpow (by linarith : r - 1 ≠ 0)]
  · have he := Real.rpow_add_one hz (r - 2)
    convert he.symm using 1
    congr 1
    ring

theorem scalarPowerDerivative_norm (r : ℝ) (hr : 1 < r)
    (a c t : ℝ) (hc : 0 ≤ c) :
    ‖scalarPowerDerivative r a c t‖ = r * |a - t * c| ^ (r - 1) * c := by
  rw [scalarPowerDerivative, norm_neg]
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by linarith : 0 ≤ r), abs_of_nonneg hc,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rw [mul_assoc r, rpow_mul_self _ r (abs_nonneg _) hr]

theorem scalarPowerDerivative_zero (r : ℝ) (hr : 1 < r)
    (a c : ℝ) (ha : 0 ≤ a) :
    scalarPowerDerivative r a c 0 = -r * a ^ (r - 1) * c := by
  simp only [scalarPowerDerivative, zero_mul, sub_zero, abs_of_nonneg ha]
  rw [mul_assoc r, rpow_mul_self a r ha hr]
  ring

theorem scalarPowerDerivative_bound (r : ℝ) (hr : 1 < r)
    (a c t : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (ht : |t| ≤ 1) :
    ‖scalarPowerDerivative r a c t‖ ≤ r * (a + c) ^ (r - 1) * c := by
  rw [scalarPowerDerivative_norm r hr a c t hc]
  have hy : |a - t * c| ≤ a + c := by
    calc
      |a - t * c| ≤ |a| + |t * c| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le a (t * c)
      _ ≤ a + c := by rw [abs_of_nonneg ha, abs_mul, abs_of_nonneg hc]; nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hy (by linarith)) (by linarith)) hc

theorem scalar_difference_quotient_bound (r : ℝ) (hr : 1 < r)
    (a c t : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (ht0 : t ≠ 0) (ht : |t| ≤ 1) :
    |(|a - t * c| ^ r - a ^ r) / t| ≤ r * (a + c) ^ (r - 1) * c := by
  have hb := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ Set.Icc (-1 : ℝ) 1) => (scalar_power_derivative r hr a c s).hasDerivWithinAt)
    (fun s (hs : s ∈ Set.Icc (-1 : ℝ) 1) =>
      scalarPowerDerivative_bound r hr a c s ha hc (abs_le.mpr hs))
    (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (abs_le.mp ht)
  simp only [zero_mul, sub_zero, abs_of_nonneg ha, Real.norm_eq_abs] at hb
  rw [abs_div]
  exact (div_le_iff₀ (abs_pos.mpr ht0)).mpr hb

variable {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]

theorem memLp_positive_conjugate_power (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {b : ℝ → ℝ} (hb : MemLp b p volume) (hbpos : ∀ᵐ x : ℝ, 0 ≤ b x) :
    MemLp (fun x => b x ^ (p.toReal - 1)) q volume := by
  have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  have hreal := ENNReal.HolderConjugate.toReal_of_ne_top hpfin hqfin
  have ht : 0 < p.toReal - 1 := sub_pos.mpr hreal.lt
  have he_exp : q * ENNReal.ofReal (p.toReal - 1) = p := by
    rw [← ENNReal.ofReal_toReal hqfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_toReal hpfin]
    congr 1
    simpa only [mul_comm, ENNReal.toReal_ofReal ENNReal.toReal_nonneg] using hreal.sub_one_mul_conj
  refine ⟨(hb.1.aemeasurable.pow_const _).aestronglyMeasurable, ?_⟩
  have he : (fun x => b x ^ (p.toReal - 1)) =ᵐ[volume]
      (fun x => ‖b x‖ ^ (p.toReal - 1)) := by
    filter_upwards [hbpos] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  rw [eLpNorm_congr_ae he, eLpNorm_norm_rpow b ht, he_exp]
  exact ENNReal.rpow_lt_top_of_nonneg ht.le hb.2.ne

include q

theorem positive_power_product_integrable (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {b h : ℝ → ℝ} (hb : MemLp b p volume) (hh : MemLp h p volume)
    (hbpos : ∀ᵐ x : ℝ, 0 ≤ b x) :
    Integrable (fun x => b x ^ (p.toReal - 1) * h x) volume :=
  (memLp_positive_conjugate_power (q := q) hp1 hpfin hb hbpos).integrable_mul hh

theorem positive_derivative_majorant_integrable (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {b h : ℝ → ℝ} (hb : MemLp b p volume) (hh : MemLp h p volume)
    (hbpos : ∀ᵐ x : ℝ, 0 ≤ b x) (hhpos : ∀ᵐ x : ℝ, 0 ≤ h x) :
    Integrable (fun x => p.toReal * (b x + h x) ^ (p.toReal - 1) * h x) volume := by
  have hsumpos : ∀ᵐ x : ℝ, 0 ≤ (b + h) x := by
    filter_upwards [hbpos, hhpos] with x hx hy
    exact add_nonneg hx hy
  have hi := positive_power_product_integrable (q := q) hp1 hpfin (hb.add hh) hh hsumpos
  simpa only [Pi.add_apply, mul_assoc] using hi.const_mul p.toReal

theorem integrated_positive_derivative (hp1 : 1 < p) (hpfin : p ≠ ∞)
    {b h : ℝ → ℝ} (hb : MemLp b p volume) (hh : MemLp h p volume)
    (hbpos : ∀ᵐ x : ℝ, 0 ≤ b x) (hhpos : ∀ᵐ x : ℝ, 0 ≤ h x) :
    HasDerivAt (fun t : ℝ => ∫ x : ℝ, |b x - t * h x| ^ p.toReal)
      (-p.toReal * ∫ x : ℝ, b x ^ (p.toReal - 1) * h x) 0 := by
  have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  have hr : 1 < p.toReal := (ENNReal.HolderConjugate.toReal_of_ne_top hpfin hqfin).lt
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  let F := fun t x : ℝ => |b x - t * h x| ^ p.toReal
  let F' := fun t x : ℝ => scalarPowerDerivative p.toReal (b x) (h x) t
  let D := fun x : ℝ => p.toReal * (b x + h x) ^ (p.toReal - 1) * h x
  have hFmeas (t : ℝ) : AEStronglyMeasurable (F t) volume := by
    simpa only [F, Real.norm_eq_abs, Pi.sub_apply] using
      ((hb.1.sub (hh.1.const_mul t)).norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable
  have hFint : Integrable (F 0) volume := by
    simpa only [F, zero_mul, sub_zero, Real.norm_eq_abs] using hb.integrable_norm_rpow hp0 hpfin
  have hF'eq : F' 0 =ᵐ[volume] (fun x => -p.toReal * (b x ^ (p.toReal - 1) * h x)) := by
    filter_upwards [hbpos] with x hx
    simpa only [F', mul_assoc] using scalarPowerDerivative_zero p.toReal hr (b x) (h x) hx
  have hF'int := (positive_power_product_integrable (q := q) hp1 hpfin hb hh hbpos).const_mul (-p.toReal)
  have hF'meas : AEStronglyMeasurable (F' 0) volume := hF'int.1.congr hF'eq.symm
  have hbound : ∀ᵐ x : ℝ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖F' t x‖ ≤ D x := by
    filter_upwards [hbpos, hhpos] with x hx hy t ht
    exact scalarPowerDerivative_bound p.toReal hr (b x) (h x) t hx hy
      (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  have hdiff : ∀ᵐ x : ℝ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (F · x) (F' t x) t :=
    Eventually.of_forall fun x t _ => scalar_power_derivative p.toReal hr (b x) (h x) t
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hFmeas) hFint hF'meas hbound
    (positive_derivative_majorant_integrable (q := q) hp1 hpfin hb hh hbpos hhpos) hdiff
  have he_int : (∫ x : ℝ, F' 0 x) = -p.toReal * ∫ x : ℝ, b x ^ (p.toReal - 1) * h x := by
    rw [integral_congr_ae hF'eq, integral_const_mul]
  simpa only [he_int] using hi.2

variable {𝕜 : Type*} [RCLike 𝕜]

omit q [ENNReal.HolderConjugate p q] in
theorem memLp_real_part (f : L 𝕜 p) : MemLp (fun x : ℝ => RCLike.re (f x)) p volume := by
  apply (Lp.memLp f).of_le
    (RCLike.continuous_re.comp_stronglyMeasurable (Lp.stronglyMeasurable f)).aestronglyMeasurable
  exact Eventually.of_forall fun x => RCLike.norm_re_le_norm (f x)

omit q [ENNReal.HolderConjugate p q] in
theorem positive_norm_power_integral [Fact (1 ≤ p)] (hpfin : p ≠ ∞)
    (b h : L 𝕜 p) (hb : Nonnegative b) (hh : Nonnegative h) (t : ℝ) :
    ‖b - (t : 𝕜) • h‖ ^ p.toReal =
      ∫ x : ℝ, |RCLike.re (b x) - t * RCLike.re (h x)| ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  rw [norm_rpow_eq_integral _ hp0 hpfin]
  apply integral_congr_ae
  filter_upwards [hb, hh, Lp.coeFn_sub b ((t : 𝕜) • h), Lp.coeFn_smul (t : 𝕜) h]
    with x hbx hhx hsub hsm
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hsm
  rw [hsub, hsm]
  have he_b : (RCLike.re (b x) : 𝕜) = b x := by
    apply RCLike.ext <;> simp [(RCLike.nonneg_iff.mp hbx).2]
  have he_h : (RCLike.re (h x) : 𝕜) = h x := by
    apply RCLike.ext <;> simp [(RCLike.nonneg_iff.mp hhx).2]
  rw [← he_b, ← he_h, ← RCLike.ofReal_mul, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
  simp

theorem positive_Lp_norm_power_derivative [Fact (1 ≤ p)] (hp1 : 1 < p) (hpfin : p ≠ ∞)
    (b h : L 𝕜 p) (hb : Nonnegative b) (hh : Nonnegative h) :
    HasDerivAt (fun t : ℝ => ‖b - (t : 𝕜) • h‖ ^ p.toReal)
      (-p.toReal * ∫ x : ℝ, RCLike.re (b x) ^ (p.toReal - 1) * RCLike.re (h x)) 0 := by
  have he : (fun t : ℝ => ‖b - (t : 𝕜) • h‖ ^ p.toReal) =
      (fun t : ℝ => ∫ x : ℝ, |RCLike.re (b x) - t * RCLike.re (h x)| ^ p.toReal) := by
    funext t
    exact positive_norm_power_integral hpfin b h hb hh t
  rw [he]
  exact integrated_positive_derivative (q := q) hp1 hpfin (memLp_real_part b) (memLp_real_part h)
    (hb.mono fun _ hx => (RCLike.nonneg_iff.mp hx).1)
    (hh.mono fun _ hx => (RCLike.nonneg_iff.mp hx).1)

end PositiveBiorthogonal
