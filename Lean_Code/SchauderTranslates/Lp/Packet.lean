import Lean_Code.SchauderTranslates.Lp.StepFunctions
import Lean_Code.SchauderTranslates.Lp.PacketSupport
import Lean_Code.SchauderTranslates.Lp.PacketNumerics

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def packetEdit {N : ℕ} (p : ℝ≥0∞) (Λ : Fin N → ℝ) (a : ℝ) (h : LebesgueLp p) :
    LebesgueLp p := a • ∑ j, translate p (-Λ j) h

def packetNoise {N : ℕ} (p : ℝ≥0∞) (Λ : Fin N → ℝ) (a : ℝ)
    (v h : LebesgueLp p) (i : Fin N) : LebesgueLp p :=
  translate p (Λ i) v + a • ∑ j ∈ Finset.univ.erase i, translate p (Λ i - Λ j) h

theorem packet_identity {N : ℕ} (p : ℝ≥0∞) (Λ : Fin N → ℝ) (a : ℝ)
    (v h : LebesgueLp p) (i : Fin N) :
    translate p (Λ i) (v + packetEdit p Λ a h) = a • h + packetNoise p Λ a v h i := by
  classical
  rw [packetEdit, translate_add, translate_real_smul, translate_finset_sum]
  simp_rw [translate_comp, ← sub_eq_add_neg]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => translate p (Λ i - Λ j) h)
    (Finset.mem_univ i)
  simp only [sub_self, translate_zero] at hsum
  rw [← hsum, smul_add]
  unfold packetNoise
  abel

theorem packetEdit_isCompactStep {N : ℕ} (p : ℝ≥0∞) (Λ : Fin N → ℝ) (a : ℝ)
    {h : LebesgueLp p} (hh : IsCompactStep p h) : IsCompactStep p (packetEdit p Λ a h) :=
  (IsCompactStep.finset_sum Finset.univ _ (fun j _ => hh.translate (-Λ j))).smul a

theorem packetNoise_isCompactStep {N : ℕ} (p : ℝ≥0∞) (Λ : Fin N → ℝ) (a : ℝ)
    {v h : LebesgueLp p} (hv : IsCompactStep p v) (hh : IsCompactStep p h) (i : Fin N) :
    IsCompactStep p (packetNoise p Λ a v h i) :=
  (hv.translate (Λ i)).add
    ((IsCompactStep.finset_sum (Finset.univ.erase i) _
      (fun j _ => hh.translate (Λ i - Λ j))).smul a)

theorem packetNoise_supported {N : ℕ} (p : ℝ≥0∞) {R : ℝ} (Λ : Fin N → ℝ) (a : ℝ)
    {v h : LebesgueLp p} (hv : SupportedOn v (Set.Icc (-R) R))
    (hh : SupportedOn h (Set.Icc (-R) R)) (i : Fin N) :
    SupportedOn (packetNoise p Λ a v h i) (modesRegion R Λ (privateModes i)) := by
  classical
  have hv' : SupportedOn (translate p (Λ i) v) (modesRegion R Λ (privateModes i)) := by
    have hsupport := translate_supported_interval hv (Λ i)
    have hreg := modeInterval_subset_region (R := R) (Λ := Λ) (Finset.mem_insert_self
      (Pi.single i (1 : ℤ)) ((Finset.univ.erase i).image
        (fun j => (Pi.single i (1 : ℤ) : Fin N → ℤ) - Pi.single j (1 : ℤ))))
    apply hsupport.mono
    simpa only [modeInterval, frequencyDot_single, privateModes] using hreg
  have hh' : ∀ j ∈ Finset.univ.erase i,
      SupportedOn (translate p (Λ i - Λ j) h) (modesRegion R Λ (privateModes i)) := by
    intro j hj
    have hreg := modeInterval_subset_region (R := R) (Λ := Λ)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩) :
        (Pi.single i (1 : ℤ) : Fin N → ℤ) - Pi.single j (1 : ℤ) ∈ privateModes i)
    apply (translate_supported_interval hh (Λ i - Λ j)).mono
    simpa only [modeInterval, SchauderTranslates.frequencyDot_sub, frequencyDot_single, privateModes] using hreg
  exact hv'.add ((SupportedOn.finset_sum (Finset.univ.erase i) _ hh').real_smul a)

theorem packetEdit_supported_outside {N : ℕ} (p : ℝ≥0∞) {R : ℝ}
    (Λ : Fin N → ℝ) (a : ℝ) (hsep : SeparatedModeIntervals R Λ)
    {h : LebesgueLp p} (hh : SupportedOn h (Set.Icc (-R) R)) :
    SupportedOn (packetEdit p Λ a h) (Set.Icc (-R) R)ᶜ := by
  have hf (i : Fin N) : SupportedOn (translate p (-Λ i) h) (Set.Icc (-R) R)ᶜ := by
    have hm : -(Pi.single i (1 : ℤ) : Fin N → ℤ) ≠ 0 :=
      neg_ne_zero.mpr (single_mode_ne_zero i)
    have hd := hsep _ (neg_single_mem_packetModes i) 0 (zero_mem_packetModes N) hm
    have hd' : Disjoint (Set.Icc (-Λ i - R) (-Λ i + R)) (Set.Icc (-R) R) := by
      simpa only [modeInterval, frequencyDot_neg, frequencyDot_single, frequencyDot_zero,
        zero_sub, zero_add] using hd
    apply (translate_supported_interval hh (-Λ i)).mono
    intro x hx hy
    exact Set.disjoint_left.mp hd' hx hy
  exact (SupportedOn.finset_sum Finset.univ _ (fun i _ => hf i)).real_smul a

theorem packetEdit_norm_power {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) {R : ℝ} (Λ : Fin N → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (hsep : SeparatedModeIntervals R Λ)
    {h : LebesgueLp p} (hh : SupportedOn h (Set.Icc (-R) R)) (hn : ‖h‖ = 1) :
    ‖packetEdit p Λ a h‖ ^ p.toReal = (N : ℝ) * a ^ p.toReal := by
  have hdis : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ j ∈ Finset.univ, i ≠ j →
      ∀ᵐ x ∂volume, translate p (-Λ i) h x = 0 ∨ translate p (-Λ j) h x = 0 := by
    intro i _ j _ hij
    have hm : -(Pi.single i (1 : ℤ) : Fin N → ℤ) ≠ -Pi.single j (1 : ℤ) := by
      intro he
      exact hij (single_mode_injective (neg_injective he))
    have hd := hsep _ (neg_single_mem_packetModes i) _ (neg_single_mem_packetModes j) hm
    apply (translate_supported_interval hh (-Λ i)).ae_disjoint (translate_supported_interval hh (-Λ j))
    simpa only [modeInterval, frequencyDot_neg, frequencyDot_single] using hd
  have hsum : ‖∑ j, translate p (-Λ j) h‖ ^ p.toReal = (N : ℝ) := by
    rw [norm_finset_sum_rpow Finset.univ _ hp0 hpfin hdis]
    simp [norm_translate, hn]
  rw [packetEdit, norm_real_smul_rpow, abs_of_nonneg ha, hsum]
  ring

theorem packetNoise_norm_power {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) {R : ℝ} (Λ : Fin N → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (hsep : SeparatedModeIntervals R Λ)
    {v h : LebesgueLp p} (hv : SupportedOn v (Set.Icc (-R) R))
    (hh : SupportedOn h (Set.Icc (-R) R)) (hn : ‖h‖ = 1) (i : Fin N) :
    ‖packetNoise p Λ a v h i‖ ^ p.toReal =
      ‖v‖ ^ p.toReal + ((N - 1 : ℕ) : ℝ) * a ^ p.toReal := by
  classical
  have hdis : ∀ j ∈ Finset.univ.erase i, ∀ k ∈ Finset.univ.erase i, j ≠ k →
      ∀ᵐ x ∂volume, translate p (Λ i - Λ j) h x = 0 ∨ translate p (Λ i - Λ k) h x = 0 := by
    intro j hj k hk hjk
    have hm : (Pi.single i (1 : ℤ) : Fin N → ℤ) - Pi.single j (1 : ℤ) ≠
        Pi.single i (1 : ℤ) - Pi.single k (1 : ℤ) := by
      intro he
      exact hjk (difference_mode_injective (Ne.symm (Finset.mem_erase.mp hj).1)
        (Ne.symm (Finset.mem_erase.mp hk).1) he).2
    have hd := hsep _ (difference_mem_packetModes i j) _ (difference_mem_packetModes i k) hm
    apply (translate_supported_interval hh (Λ i - Λ j)).ae_disjoint
      (translate_supported_interval hh (Λ i - Λ k))
    simpa only [modeInterval, SchauderTranslates.frequencyDot_sub, frequencyDot_single] using hd
  have hsum : ‖∑ j ∈ Finset.univ.erase i, translate p (Λ i - Λ j) h‖ ^ p.toReal =
      ((N - 1 : ℕ) : ℝ) := by
    rw [norm_finset_sum_rpow _ _ hp0 hpfin hdis]
    simp [norm_translate, hn]
  have hvs : ∀ j ∈ Finset.univ.erase i,
      ∀ᵐ x ∂volume, translate p (Λ i) v x = 0 ∨ translate p (Λ i - Λ j) h x = 0 := by
    intro j _
    have hd := hsep _ (single_mem_packetModes i) _ (difference_mem_packetModes i j)
      (single_mode_ne_difference i i j)
    apply (translate_supported_interval hv (Λ i)).ae_disjoint (translate_supported_interval hh (Λ i - Λ j))
    simpa only [modeInterval, SchauderTranslates.frequencyDot_sub, frequencyDot_single] using hd
  have hvsSum := ae_disjoint_finset_sum (Finset.univ.erase i) (translate p (Λ i) v) _ hvs
  have hvsScaled := ae_disjoint_real_smul_right _ _ a hvsSum
  rw [packetNoise, norm_add_rpow_of_ae_disjoint _ _ hp0 hpfin hvsScaled,
    norm_translate, norm_real_smul_rpow, abs_of_nonneg ha, hsum]
  ring

/-- Blueprint `lp:packet`. The displayed coupling exponent is `-1/q`,
written as `-(P - 1)/P` for the finite real exponent `P = p.toReal`.
All norms here are the norms of the actual Lebesgue Lᵖ classes. -/
theorem exact_packet {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 < p) (hpfin : p ≠ ∞)
    {R : ℝ} (hR : 0 ≤ R) (v h : LebesgueLp p)
    (hvstep : IsCompactStep p v) (hhstep : IsCompactStep p h) (hv0 : v ≠ 0)
    (hhnorm : ‖h‖ = 1) (hv : SupportedOn v (Set.Icc (-R) R))
    (hh : SupportedOn h (Set.Icc (-R) R)) (old : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (Λ : Fin N → ℝ) (d : ℝ) (g : LebesgueLp p) (e : Fin N → LebesgueLp p),
      1 ≤ N ∧ 0 < d ∧ Function.Injective Λ ∧ (∀ i, 0 < Λ i ∧ Λ i ∉ old) ∧
      IsCompactStep p g ∧
      (∀ i, IsCompactStep p (e i) ∧ ‖e i‖ = 1 ∧
        SupportedOn (e i) (modesRegion R Λ (privateModes i))) ∧
      (∀ i, Disjoint (modesRegion R Λ (privateModes i)) (Set.Icc (-R) R)) ∧
      (∀ i j, i ≠ j → Disjoint (modesRegion R Λ (privateModes i)) (modesRegion R Λ (privateModes j))) ∧
      (∀ i, translate p (Λ i) g =
        d • (e i + (N : ℝ) ^ (-(p.toReal - 1) / p.toReal) • h)) ∧
      ‖g - v‖ ≤ ε ∧ SupportedOn (g - v) (Set.Icc (-R) R)ᶜ ∧
      ‖g‖ ^ p.toReal = ‖v‖ ^ p.toReal + ‖g - v‖ ^ p.toReal := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 2).trans hp)
  have hpR : (2 : ℝ) < p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp
  have hpR0 : 0 < p.toReal := by linarith
  obtain ⟨N, d, hN, hden, hde, hd, hcost⟩ := packet_scales hpR (norm_pos_iff.mpr hv0) hε
  obtain ⟨Λ, hΛpos, hΛold, hΛinj, hΛsep⟩ := support_placement hR N old
  have hsep : SeparatedModeIntervals R Λ := fun k hk l hl hkl => (hΛsep k hk l hl hkl).2
  let a := packetAmplitude p.toReal d N
  have ha : 0 < a := packet_amplitude_pos hd hN
  have hbal : d ^ p.toReal * (1 - packetDeficit p.toReal N) = ‖v‖ ^ p.toReal :=
    packet_scale_balance hpR0 (norm_nonneg v) (by linarith) hde
  have hw (i : Fin N) : ‖packetNoise p Λ a v h i‖ = d := by
    apply (Real.rpow_left_inj (norm_nonneg _) hd.le (ne_of_gt hpR0)).mp
    rw [packetNoise_norm_power p hp0 hpfin Λ a ha.le hsep hv hh hhnorm i]
    exact packet_noise_power hpR0 hd.le hN hbal
  have hecost : ‖packetEdit p Λ a h‖ = d * (N : ℝ) ^ (2 / p.toReal - 1) := by
    apply (Real.rpow_left_inj (norm_nonneg _) (by positivity) (ne_of_gt hpR0)).mp
    exact (packetEdit_norm_power p hp0 hpfin Λ a ha.le hsep hh hhnorm).trans
      (packet_edit_cost_power hpR0 hd.le hN).symm
  let g := v + packetEdit p Λ a h
  let e : Fin N → LebesgueLp p := fun i => d⁻¹ • packetNoise p Λ a v h i
  have hsub : g - v = packetEdit p Λ a h := by dsimp [g]; abel
  have heout := packetEdit_supported_outside p Λ a hsep hh
  refine ⟨N, Λ, d, g, e, hN, hd, hΛinj, fun i => ⟨hΛpos i, hΛold i⟩,
    hvstep.add (packetEdit_isCompactStep p Λ a hhstep), ?_,
    private_region_disjoint_base hsep, fun i j hij => private_regions_disjoint hsep hij,
    ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(packetNoise_isCompactStep p Λ a hvstep hhstep i).smul d⁻¹, ?_,
      (packetNoise_supported p Λ a hv hh i).real_smul d⁻¹⟩
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), hw, inv_mul_cancel₀ (ne_of_gt hd)]
  · intro i
    simp [g, e, packet_identity, smul_add, smul_smul, ne_of_gt hd, a, packetAmplitude, add_comm]
  · rw [hsub, hecost]
    exact hcost
  · rwa [hsub]
  · calc
      ‖g‖ ^ p.toReal = ‖v‖ ^ p.toReal + ‖packetEdit p Λ a h‖ ^ p.toReal :=
        norm_add_rpow_of_ae_disjoint _ _ hp0 hpfin
          (hv.ae_disjoint heout disjoint_compl_right)
      _ = ‖v‖ ^ p.toReal + ‖g - v‖ ^ p.toReal := by rw [hsub]

end SchauderTranslates.LpConstruction
