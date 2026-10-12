import Lean_Code.PositiveBiorthogonal.Interpretation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Local indicator, restriction, and positive-measure-set tools. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ComplexOrder

namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}

def cut (s : Set ℝ) (hs : MeasurableSet s) (f : L 𝕜 p) : L 𝕜 p :=
  (MemLp.indicator hs (Lp.memLp f)).toLp (s.indicator f)

theorem coeFn_cut (s : Set ℝ) (hs : MeasurableSet s) (f : L 𝕜 p) :
    (cut s hs f : ℝ → 𝕜) =ᵐ[volume] s.indicator f :=
  MemLp.coeFn_toLp _

theorem cut_norm_le (s : Set ℝ) (hs : MeasurableSet s) (f : L 𝕜 p) :
    ‖cut s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_cut s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem cut_eq_self (s : Set ℝ) (hs : MeasurableSet s) (f : L 𝕜 p)
    (hf : ∀ᵐ x : ℝ, x ∉ s → f x = 0) : cut s hs f = f := by
  apply Lp.ext
  filter_upwards [coeFn_cut s hs f, hf] with x hx hfx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs, hfx]

theorem cut_eq_zero (s : Set ℝ) (hs : MeasurableSet s) (f : L 𝕜 p)
    (hf : ∀ᵐ x : ℝ, x ∈ s → f x = 0) : cut s hs f = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_cut s hs f, hf, Lp.coeFn_zero 𝕜 p (volume : Measure ℝ)]
    with x hx hfx hzero
  rw [hx, hzero]
  by_cases hxs : x ∈ s <;> simp [hxs, hfx]

theorem cut_add (s : Set ℝ) (hs : MeasurableSet s) (f g : L 𝕜 p) :
    cut s hs (f + g) = cut s hs f + cut s hs g := by
  apply Lp.ext
  filter_upwards [coeFn_cut s hs (f + g), coeFn_cut s hs f, coeFn_cut s hs g,
    Lp.coeFn_add f g, Lp.coeFn_add (cut s hs f) (cut s hs g)] with x hfg hf hg hadd hsum
  rw [hfg, hsum]
  by_cases hx : x ∈ s <;> simp_all

theorem cut_smul (s : Set ℝ) (hs : MeasurableSet s) (a : 𝕜) (f : L 𝕜 p) :
    cut s hs (a • f) = a • cut s hs f := by
  apply Lp.ext
  filter_upwards [coeFn_cut s hs (a • f), coeFn_cut s hs f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (cut s hs f)] with x haf hf hsm hsm'
  rw [haf, hsm']
  by_cases hx : x ∈ s <;> simp_all

def restriction [Fact (1 ≤ p)] (s : Set ℝ) (hs : MeasurableSet s) :
    L 𝕜 p →L[𝕜] L 𝕜 p :=
  LinearMap.mkContinuous
    { toFun := cut s hs
      map_add' := cut_add s hs
      map_smul' := cut_smul s hs }
    1 (fun f => by simpa using cut_norm_le s hs f)

@[simp] theorem restriction_apply [Fact (1 ≤ p)] (s : Set ℝ)
    (hs : MeasurableSet s) (f : L 𝕜 p) : restriction s hs f = cut s hs f := rfl

theorem restriction_norm_le [Fact (1 ≤ p)] (s : Set ℝ) (hs : MeasurableSet s) :
    ‖restriction (𝕜 := 𝕜) (p := p) s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using cut_norm_le s hs f

theorem indicator_norm (s : Set ℝ) (hs : MeasurableSet s) (hfin : volume s ≠ ∞)
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ‖indicatorConstLp p hs hfin (1 : 𝕜)‖ = (volume.real s) ^ (1 / p.toReal) := by
  simpa using norm_indicatorConstLp (c := (1 : 𝕜)) (hs := hs) (hμs := hfin) hp0 hpfin

theorem indicator_top_norm (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (hpos : volume s ≠ 0) :
    ‖indicatorConstLp ∞ hs hfin (1 : 𝕜)‖ = 1 := by
  simpa using norm_indicatorConstLp_top (c := (1 : 𝕜)) (hs := hs) (hμs := hfin) hpos

theorem interval_indicator_step (a b : ℝ) (c : 𝕜) :
    CompactlySupportedStep
      (indicatorConstLp p (measurableSet_Ioc (a := a) (b := b)) (measure_Ioc_lt_top.ne) c) := by
  refine ⟨1, fun _ => a, fun _ => b, fun _ => c, ?_⟩
  filter_upwards [indicatorConstLp_coeFn (p := p) (c := c)
    (hs := measurableSet_Ioc (a := a) (b := b)) (hμs := measure_Ioc_lt_top.ne)] with x hx
  simpa using hx

theorem step_zero : CompactlySupportedStep (0 : L 𝕜 p) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  filter_upwards [Lp.coeFn_zero 𝕜 p (volume : Measure ℝ)] with x hx
  simp

theorem step_smul {f : L 𝕜 p} (hf : CompactlySupportedStep f) (a : 𝕜) :
    CompactlySupportedStep (a • f) := by
  obtain ⟨m, l, r, c, hc⟩ := hf
  refine ⟨m, l, r, fun j => a * c j, ?_⟩
  filter_upwards [hc, Lp.coeFn_smul a f] with x hx hs
  rw [hs, Pi.smul_apply, smul_eq_mul, hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : x ∈ Ioc (l j) (r j) <;> simp [hj]

theorem two_positive_subsets (B : Set ℝ) (hB : MeasurableSet B) (hpos : 0 < volume B) :
    ∃ E₀ E₁ : Set ℝ, MeasurableSet E₀ ∧ MeasurableSet E₁ ∧ E₀ ⊆ B ∧ E₁ ⊆ B ∧
      Disjoint E₀ E₁ ∧ 0 < volume E₀ ∧ volume E₀ < ∞ ∧
      0 < volume E₁ ∧ volume E₁ < ∞ := by
  obtain ⟨E, hE, hEB, hEpos, hEfin⟩ := volume.exists_subset_measure_lt_top hB hpos
  let d := (volume E).toReal / 2
  have hd : 0 < d := div_pos (ENNReal.toReal_pos hEpos.ne' hEfin.ne) (by norm_num)
  let pieces : ℤ → Set ℝ := fun j => E ∩ Ico ((j : ℝ) * d) (((j : ℝ) + 1) * d)
  have hcover : E ⊆ ⋃ j : ℤ, pieces j := by
    intro x hx
    refine mem_iUnion.mpr ⟨⌊x / d⌋, hx, ?_, ?_⟩
    · exact (le_div_iff₀ hd).mp (Int.floor_le (x / d))
    · exact (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (x / d))
  have hex : ∃ j : ℤ, 0 < volume (pieces j) := by
    by_contra! h
    have hz : volume (⋃ j : ℤ, pieces j) = 0 :=
      measure_iUnion_null (fun j => le_antisymm (h j) bot_le)
    exact hEpos.ne' (measure_mono_null hcover hz)
  obtain ⟨j, hj⟩ := hex
  have hsub : pieces j ⊆ E := inter_subset_left
  have hm : MeasurableSet (pieces j) := hE.inter measurableSet_Ico
  have hlt : volume (pieces j) < volume E := by
    calc
      volume (pieces j) ≤ volume (Ico ((j : ℝ) * d) (((j : ℝ) + 1) * d)) :=
        measure_mono inter_subset_right
      _ = ENNReal.ofReal d := by rw [Real.volume_Ico]; congr 1; ring
      _ < volume E := by
        apply (ENNReal.ofReal_lt_iff_lt_toReal hd.le hEfin.ne).mpr
        dsimp [d]
        linarith [ENNReal.toReal_pos hEpos.ne' hEfin.ne]
  have hjfin : volume (pieces j) < ∞ := hlt.trans hEfin
  refine ⟨pieces j, E \ pieces j, hm, hE.diff hm, hsub.trans hEB,
    sdiff_subset.trans hEB, disjoint_sdiff_right, hj, hjfin, ?_, ?_⟩
  · rw [measure_sdiff hsub hm.nullMeasurableSet hjfin.ne]
    exact tsub_pos_iff_lt.mpr hlt
  · exact (measure_mono sdiff_subset).trans_lt hEfin

theorem exists_mem_of_ae {s : Set ℝ} (hs : 0 < volume s) {Q : ℝ → Prop}
    (hQ : ∀ᵐ x : ℝ, Q x) : ∃ x ∈ s, Q x := by
  by_contra! h
  exact hs.ne' (measure_mono_null h (ae_iff.mp hQ))

theorem indicator_ne_zero (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (hpos : 0 < volume s) :
    indicatorConstLp p hs hfin (1 : 𝕜) ≠ 0 := by
  intro h
  have he : ∀ᵐ x : ℝ, s.indicator (fun _ => (1 : 𝕜)) x = 0 := by
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hfin) (c := (1 : 𝕜)),
      Lp.coeFn_zero 𝕜 p (volume : Measure ℝ)] with x hx hz
    rw [h] at hx
    exact hx.symm.trans hz
  obtain ⟨x, hx, heq⟩ := exists_mem_of_ae hpos he
  simp [hx] at heq

theorem disjoint_indicators_not_smul (s t : Set ℝ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hsfin : volume s ≠ ∞) (htfin : volume t ≠ ∞)
    (hdis : Disjoint s t) (htpos : 0 < volume t) (a : 𝕜) :
    indicatorConstLp p ht htfin (1 : 𝕜) ≠ a • indicatorConstLp p hs hsfin (1 : 𝕜) := by
  intro h
  have he : ∀ᵐ x : ℝ, t.indicator (fun _ => (1 : 𝕜)) x =
      a * s.indicator (fun _ => (1 : 𝕜)) x := by
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := htfin) (c := (1 : 𝕜)),
      indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hsfin) (c := (1 : 𝕜)),
      Lp.coeFn_smul a (indicatorConstLp p hs hsfin (1 : 𝕜)), Lp.ext_iff.mp h]
      with x hxt hxs hsm heq
    simpa [hxs, hxt, Pi.smul_apply, smul_eq_mul] using heq.trans hsm
  obtain ⟨x, hxt, heq⟩ := exists_mem_of_ae htpos he
  have hxs : x ∉ s := fun hx => Set.disjoint_left.mp hdis hx hxt
  simp [hxt, hxs] at heq

theorem disjoint_indicators_independent (s t : Set ℝ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hsfin : volume s ≠ ∞) (htfin : volume t ≠ ∞)
    (hdis : Disjoint s t) (hspos : 0 < volume s) (htpos : 0 < volume t) :
    LinearIndependent 𝕜
      ![indicatorConstLp p hs hsfin (1 : 𝕜), indicatorConstLp p ht htfin (1 : 𝕜)] := by
  apply linearIndependent_fin2.mpr
  constructor
  · exact indicator_ne_zero t ht htfin htpos
  · intro a he
    exact disjoint_indicators_not_smul t s ht hs htfin hsfin hdis.symm hspos a he.symm

theorem indicator_difference_norm [Fact (1 ≤ p)] (s t : Set ℝ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hsfin : volume s ≠ ∞) (htfin : volume t ≠ ∞)
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ‖indicatorConstLp p hs hsfin (1 : 𝕜) - indicatorConstLp p ht htfin (1 : 𝕜)‖ =
      (volume.real (symmDiff s t)) ^ (1 / p.toReal) := by
  rw [← dist_eq_norm, dist_indicatorConstLp_eq_norm]
  exact indicator_norm (symmDiff s t) (hs.symmDiff ht) _ hp0 hpfin

theorem norm_rpow_eq_integral (f : L 𝕜 p) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ‖f‖ ^ p.toReal = ∫ x : ℝ, ‖f x‖ ^ p.toReal := by
  have hpow : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ p.toReal :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hp0 hpfin,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hpow _), ← Real.rpow_mul hpow,
    inv_mul_cancel₀ (ENNReal.toReal_pos hp0 hpfin).ne', Real.rpow_one]

theorem ae_norm_eq_of_le_of_norm_eq (u v : L 𝕜 p) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (hle : ∀ᵐ x : ℝ, ‖u x‖ ≤ ‖v x‖) (heq : ‖u‖ = ‖v‖) :
    ∀ᵐ x : ℝ, ‖u x‖ = ‖v x‖ := by
  have hpow : (fun x => ‖u x‖ ^ p.toReal) ≤ᵐ[volume] (fun x => ‖v x‖ ^ p.toReal) := by
    filter_upwards [hle] with x hx
    exact Real.rpow_le_rpow (norm_nonneg _) hx ENNReal.toReal_nonneg
  have hiu := (Lp.memLp u).integrable_norm_rpow hp0 hpfin
  have hiv := (Lp.memLp v).integrable_norm_rpow hp0 hpfin
  have hieq : (∫ x : ℝ, ‖u x‖ ^ p.toReal) = ∫ x : ℝ, ‖v x‖ ^ p.toReal := by
    rw [← norm_rpow_eq_integral u hp0 hpfin, ← norm_rpow_eq_integral v hp0 hpfin, heq]
  have hae := (integral_eq_iff_of_ae_le hiu hiv hpow).mp hieq
  filter_upwards [hae] with x hx
  exact (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _)
    (ENNReal.toReal_pos hp0 hpfin).ne').mp hx

theorem ordered_norm_eq (u v : L ℝ p) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (hu : Nonnegative u) (huv : ∀ᵐ x : ℝ, u x ≤ v x) (hnorm : ‖u‖ = ‖v‖) : u = v := by
  have hle : ∀ᵐ x : ℝ, ‖u x‖ ≤ ‖v x‖ := by
    filter_upwards [hu, huv] with x hx hxy
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)] using hxy
  have he := ae_norm_eq_of_le_of_norm_eq u v hp0 hpfin hle hnorm
  apply Lp.ext
  filter_upwards [hu, huv, he] with x hx hxy heq
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)] using heq

theorem ordered_norm_eq_rclike (u v : L 𝕜 p) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (hu : Nonnegative u) (huv : ∀ᵐ x : ℝ, u x ≤ v x) (hnorm : ‖u‖ = ‖v‖) : u = v := by
  have hle : ∀ᵐ x : ℝ, ‖u x‖ ≤ ‖v x‖ := by
    filter_upwards [hu, huv] with x hx hxy
    apply (RCLike.ofReal_le_ofReal (K := 𝕜)).mp
    simpa only [RCLike.norm_of_nonneg' hx, RCLike.norm_of_nonneg' (hx.trans hxy)] using hxy
  have he := ae_norm_eq_of_le_of_norm_eq u v hp0 hpfin hle hnorm
  apply Lp.ext
  filter_upwards [hu, huv, he] with x hx hxy heq
  rw [← RCLike.norm_of_nonneg' hx, ← RCLike.norm_of_nonneg' (hx.trans hxy), heq]

end PositiveBiorthogonal
