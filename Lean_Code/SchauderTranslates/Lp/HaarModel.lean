import Lean_Code.SchauderTranslates.Lp.DyadicIntervals

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Lebesgue measure on the half-open unit interval. Endpoint choices have
no effect on the Lᵖ classes, but the cell partition identities are exact. -/
def haarMeasure : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

theorem haarMeasure_eq_open_interval : haarMeasure = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
  Measure.restrict_congr_set (Ioo_ae_eq_Ico (μ := volume)).symm

instance haarMeasure_isProbabilityMeasure : IsProbabilityMeasure haarMeasure :=
  ⟨by simp [haarMeasure]⟩

abbrev HaarLp (p : ℝ≥0∞) := Lp ℂ p haarMeasure
abbrev HaarIndex := Option (Σ n, Fin (2 ^ n))

def haarIntervalAtom (p : ℝ≥0∞) (n k : ℕ) : HaarLp p :=
  indicatorConstLp p (dyadicInterval_measurable n k) (measure_ne_top haarMeasure _) (1 : ℂ)

def haarScale (n : ℕ) : ℝ := ((2 : ℝ) ^ n) ^ (1 / 2 : ℝ)

def haarConstant (p : ℝ≥0∞) : HaarLp p := haarIntervalAtom p 0 0

def haarFunction (p : ℝ≥0∞) (n k : ℕ) : HaarLp p :=
  haarScale n • (haarIntervalAtom p (n + 1) (2 * k) - haarIntervalAtom p (n + 1) (2 * k + 1))

def haarAtom (p : ℝ≥0∞) : HaarIndex → HaarLp p
  | none => haarConstant p
  | some ⟨n, k⟩ => haarFunction p n k

theorem haarScale_pos (n : ℕ) : 0 < haarScale n :=
  Real.rpow_pos_of_pos (dyadic_denominator_pos n) _

theorem haarIntervalAtom_ae (p : ℝ≥0∞) (n k : ℕ) :
    (haarIntervalAtom p n k : ℝ → ℂ) =ᵐ[haarMeasure]
      (dyadicInterval n k).indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn

theorem haarIntervalAtom_supported (p : ℝ≥0∞) (n k : ℕ) :
    SupportedOn (haarIntervalAtom p n k) (dyadicInterval n k) :=
  indicatorConstLp_coeFn_notMem

theorem haarInterval_measure (n k : ℕ) (hk : k < 2 ^ n) :
    haarMeasure (dyadicInterval n k) = ENNReal.ofReal (1 / (2 : ℝ) ^ n) := by
  rw [haarMeasure, Measure.restrict_apply (dyadicInterval_measurable n k),
    Set.inter_eq_left.mpr (dyadicInterval_subset_unit n k hk), dyadicInterval_volume]

theorem norm_haarIntervalAtom (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (n k : ℕ) (hk : k < 2 ^ n) :
    ‖haarIntervalAtom p n k‖ = (1 / (2 : ℝ) ^ n) ^ (1 / p.toReal) := by
  rw [haarIntervalAtom, norm_indicatorConstLp hp0 hpfin]
  simp only [norm_one, one_mul, measureReal_def, haarInterval_measure n k hk,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 : ℝ) ^ n)]

theorem norm_haarConstant (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ‖haarConstant p‖ = 1 := by
  rw [haarConstant, norm_haarIntervalAtom p hp0 hpfin 0 0 (by norm_num)]
  norm_num

theorem haarFunction_ae (p : ℝ≥0∞) (n k : ℕ) :
    (haarFunction p n k : ℝ → ℂ) =ᵐ[haarMeasure] (fun x => (haarScale n : ℂ) *
      ((dyadicInterval (n + 1) (2 * k)).indicator (fun _ => (1 : ℂ)) x -
       (dyadicInterval (n + 1) (2 * k + 1)).indicator (fun _ => (1 : ℂ)) x)) := by
  filter_upwards [Lp.coeFn_smul (haarScale n)
    (haarIntervalAtom p (n + 1) (2 * k) - haarIntervalAtom p (n + 1) (2 * k + 1)),
    Lp.coeFn_sub (haarIntervalAtom p (n + 1) (2 * k)) (haarIntervalAtom p (n + 1) (2 * k + 1)),
    haarIntervalAtom_ae p (n + 1) (2 * k), haarIntervalAtom_ae p (n + 1) (2 * k + 1)]
      with x hsm hsub hl hr
  change (haarScale n •
    (haarIntervalAtom p (n + 1) (2 * k) - haarIntervalAtom p (n + 1) (2 * k + 1))) x = _
  rw [hsm, Pi.smul_apply, hsub, Pi.sub_apply, hl, hr]
  exact Complex.real_smul

theorem haarFunction_supported (p : ℝ≥0∞) (n k : ℕ) :
    SupportedOn (haarFunction p n k) (dyadicInterval n k) := by
  filter_upwards [haarFunction_ae p n k] with x hx
  intro hnot
  have hnl : x ∉ dyadicInterval (n + 1) (2 * k) := fun hin => hnot (dyadicInterval_child_left_subset n k hin)
  have hnr : x ∉ dyadicInterval (n + 1) (2 * k + 1) := fun hin => hnot (dyadicInterval_child_right_subset n k hin)
  simp [hx, hnl, hnr]

theorem haarIntervalAtom_children_sum (p : ℝ≥0∞) (n k : ℕ) :
    haarIntervalAtom p n k =
      haarIntervalAtom p (n + 1) (2 * k) + haarIntervalAtom p (n + 1) (2 * k + 1) := by
  apply Lp.ext
  filter_upwards [haarIntervalAtom_ae p n k, haarIntervalAtom_ae p (n + 1) (2 * k),
    haarIntervalAtom_ae p (n + 1) (2 * k + 1),
    Lp.coeFn_add (haarIntervalAtom p (n + 1) (2 * k)) (haarIntervalAtom p (n + 1) (2 * k + 1))]
      with x hp hl hr ha
  rw [hp, ha, Pi.add_apply, hl, hr, ← dyadicInterval_children_union n k]
  by_cases hxl : x ∈ dyadicInterval (n + 1) (2 * k)
  · have hxr : x ∉ dyadicInterval (n + 1) (2 * k + 1) := fun h =>
      Set.disjoint_left.mp (dyadicInterval_children_disjoint n k) hxl h
    simp [hxl, hxr]
  · by_cases hxr : x ∈ dyadicInterval (n + 1) (2 * k + 1) <;> simp [hxl, hxr]

theorem haarFunction_eq_complex_smul (p : ℝ≥0∞) (n k : ℕ) :
    haarFunction p n k = (haarScale n : ℂ) •
      (haarIntervalAtom p (n + 1) (2 * k) - haarIntervalAtom p (n + 1) (2 * k + 1)) := by
  apply Lp.ext
  filter_upwards [haarFunction_ae p n k,
    Lp.coeFn_smul (haarScale n : ℂ)
      (haarIntervalAtom p (n + 1) (2 * k) - haarIntervalAtom p (n + 1) (2 * k + 1)),
    Lp.coeFn_sub (haarIntervalAtom p (n + 1) (2 * k)) (haarIntervalAtom p (n + 1) (2 * k + 1)),
    haarIntervalAtom_ae p (n + 1) (2 * k), haarIntervalAtom_ae p (n + 1) (2 * k + 1)]
      with x hf hs hsub hl hr
  rw [hf, hs, Pi.smul_apply, hsub, Pi.sub_apply, hl, hr, smul_eq_mul]

end SchauderTranslates.LpConstruction
