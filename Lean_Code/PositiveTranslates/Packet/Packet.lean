import Lean_Code.PositiveTranslates.Packet.Placement
import Lean_Code.PositiveTranslates.Packet.Scales
import Lean_Code.PositiveTranslates.Packet.Nonneg

/-!
# The positive packet

Paper, proof of `thm:translate-properties`(iii) (lines 3364–3377), the non-negative variant
of Lemma `tr:lem:packet`. For non-negative `v, h` supported in `I = [-R, R]`, with
`‖h‖ = 1`, and separated positive parameters `Λ 0, …, Λ (N-1)` put

`d = posScale p.toReal ‖v‖ N`,  `a = posAmplitude p.toReal d N = 2 d N^{-1/q}`,
`V = referenceFunction p v h Λ = v + a ∑ᵢ T_{-Λᵢ} h`.

Then `T_{Λᵢ} V = d (eᵢ + 2 N^{-1/q} h)` with non-negative unit step functions

`eᵢ = d⁻¹ (T_{Λᵢ} v + a ∑_{j ≠ i} T_{Λᵢ - Λⱼ} h)`   (`posRemainder`),

supported in the pairwise disjoint private regions `modesRegion R Λ (privateModes i)`,
which are disjoint from `I`; moreover `‖V - v‖ = a N^{1/p}` and `V - v` is supported to
the left of `I`.

Main declarations (namespace `StructuredBases.PositiveTranslates`):

* `posRemainder p v h Λ i` : the remainder `eᵢ`;
* `PositivePacket p R v h Λ e` : the list of conclusions, as a `Prop`-valued structure;
* `positive_packet` : `PositivePacket p R v h Λ (posRemainder p v h Λ)`;
* `exists_positive_remainders` : the existential form.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates SchauderTranslates.LpConstruction

/-! ### Geometry of the supports -/

/-- A positive parameter of a separated family is larger than `2R`. -/
theorem two_mul_lt_of_separated {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ) {i : Fin N} (hi : 0 < Λ i) : 2 * R < Λ i := by
  by_contra hle
  have hle' : Λ i ≤ 2 * R := not_lt.mp hle
  have hd := hsep _ (single_mem_packetModes i) 0 (zero_mem_packetModes N)
    (single_mode_ne_zero i)
  have hx1 : Λ i - R ∈ modeInterval R Λ (Pi.single i (1 : ℤ)) := by
    rw [modeInterval, frequencyDot_single]
    exact ⟨le_rfl, by linarith [hi, hle']⟩
  have hx2 : Λ i - R ∈ modeInterval R Λ 0 := by
    rw [modeInterval, frequencyDot_zero]
    exact ⟨by linarith [hi], by linarith [hle']⟩
  exact Set.disjoint_left.mp hd hx1 hx2

/-- The edit `a ∑ᵢ T_{-Λᵢ} h` is supported to the left of `I = [-R, R]`, inside
`[-(R + ρ), -R)` for every upper bound `ρ` of the parameters. -/
theorem packetEdit_supported_left {p : ℝ≥0∞} {N : ℕ} {R ρ : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ) (hpos : ∀ i, 0 < Λ i)
    (hρ : ∀ i, Λ i ≤ ρ) (a : ℝ) {h : LebesgueLp p} (hh : SupportedOn h (Set.Icc (-R) R)) :
    SupportedOn (packetEdit p Λ a h) (Set.Ico (-(R + ρ)) (-R)) := by
  refine (SupportedOn.finset_sum Finset.univ _ (fun i _ => ?_)).real_smul a
  apply (translate_supported_interval hh (-Λ i)).mono
  intro x hx
  have h2 := two_mul_lt_of_separated hsep (hpos i)
  have hx' : -Λ i - R ≤ x ∧ x ≤ -Λ i + R := hx
  exact ⟨by linarith [hx'.1, hρ i], by linarith [hx'.2]⟩

/-- The private region of index `i` lies in `[-(R + ρ), R + ρ]` for every upper bound `ρ`
of the (non-negative) parameters. -/
theorem privateRegion_subset_Icc {N : ℕ} {R ρ : ℝ} {Λ : Fin N → ℝ}
    (hpos : ∀ i, 0 ≤ Λ i) (hρ : ∀ i, Λ i ≤ ρ) (i : Fin N) :
    modesRegion R Λ (privateModes i) ⊆ Set.Icc (-(R + ρ)) (R + ρ) := by
  classical
  intro x hx
  obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hk, hx⟩ := Set.mem_iUnion.mp hx
  have hx' : frequencyDot k Λ - R ≤ x ∧ x ≤ frequencyDot k Λ + R := hx
  have hc : -ρ ≤ frequencyDot k Λ ∧ frequencyDot k Λ ≤ ρ := by
    rcases Finset.mem_insert.mp hk with rfl | hk
    · rw [frequencyDot_single]
      exact ⟨by linarith [hpos i, hρ i], hρ i⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk
      rw [frequencyDot_sub, frequencyDot_single, frequencyDot_single]
      exact ⟨by linarith [hpos i, hρ j], by linarith [hpos j, hρ i]⟩
  exact ⟨by linarith [hx'.1, hc.1], by linarith [hx'.2, hc.2]⟩

/-- A nonzero function supported in `[-R, R]` forces `0 ≤ R`. -/
theorem radius_nonneg_of_supported {p : ℝ≥0∞} {R : ℝ} {v : LebesgueLp p} (hv0 : v ≠ 0)
    (hv : SupportedOn v (Set.Icc (-R) R)) : 0 ≤ R := by
  by_contra hR
  apply hv0
  apply Lp.ext
  filter_upwards [hv, Lp.coeFn_zero (E := ℂ) (p := p) (μ := (volume : Measure ℝ))]
    with x hx h0
  rw [h0]
  exact hx (fun hmem => hR (by linarith [hmem.1, hmem.2]))

/-- Positive parameters are bounded by their sum. -/
theorem le_sum_of_pos {N : ℕ} {Λ : Fin N → ℝ} (hpos : ∀ i, 0 < Λ i) (i : Fin N) :
    Λ i ≤ ∑ j, Λ j :=
  Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)

/-! ### Exact norms of the two building blocks (arbitrary amplitude) -/

section Norms

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {N : ℕ}

/-- If `‖v‖^p + (N-1) a^p = d^p` then every remainder
`T_{Λᵢ} v + a ∑_{j ≠ i} T_{Λᵢ - Λⱼ} h` has norm exactly `d`. -/
theorem norm_packetNoise_eq (hp0 : p ≠ 0) (hpfin : p ≠ ∞) {R : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ) {v h : LebesgueLp p}
    (hv : SupportedOn v (Set.Icc (-R) R)) (hh : SupportedOn h (Set.Icc (-R) R))
    (hn : ‖h‖ = 1) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hbal : ‖v‖ ^ p.toReal + ((N - 1 : ℕ) : ℝ) * a ^ p.toReal = d ^ p.toReal) (i : Fin N) :
    ‖packetNoise p Λ a v h i‖ = d := by
  have hpR : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩
  apply (Real.rpow_left_inj (norm_nonneg _) hd hpR).mp
  rw [packetNoise_norm_power p hp0 hpfin Λ a ha hsep hv hh hn i, hbal]

/-- The edit `a ∑ᵢ T_{-Λᵢ} h` has norm exactly `a N^{1/p}`. -/
theorem norm_packetEdit_eq (hp0 : p ≠ 0) (hpfin : p ≠ ∞) {R : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ) {h : LebesgueLp p}
    (hh : SupportedOn h (Set.Icc (-R) R)) (hn : ‖h‖ = 1) {a : ℝ} (ha : 0 ≤ a) :
    ‖packetEdit p Λ a h‖ = a * (N : ℝ) ^ (1 / p.toReal) := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  apply (Real.rpow_left_inj (norm_nonneg _)
    (mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg N) _)) (ne_of_gt hpR)).mp
  rw [packetEdit_norm_power p hp0 hpfin Λ a ha hsep hh hn, mul_rpow_one_div_rpow hpR ha]

end Norms

/-! ### The positive packet -/

/-- The remainders of the positive packet:
`eᵢ = d⁻¹ (T_{Λᵢ} v + a ∑_{j ≠ i} T_{Λᵢ - Λⱼ} h)` with `d = posScale p.toReal ‖v‖ N` and
`a = posAmplitude p.toReal d N`. -/
def posRemainder (p : ℝ≥0∞) {N : ℕ} (v h : LebesgueLp p) (Λ : Fin N → ℝ) (i : Fin N) :
    LebesgueLp p :=
  (posScale p.toReal ‖v‖ N)⁻¹ •
    packetNoise p Λ (posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N) v h i

theorem posRemainder_eq {p : ℝ≥0∞} {N : ℕ} (v h : LebesgueLp p) (Λ : Fin N → ℝ)
    (i : Fin N) :
    posRemainder p v h Λ i = (posScale p.toReal ‖v‖ N)⁻¹ •
      (translate p (Λ i) v + posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N •
        ∑ j ∈ Finset.univ.erase i, translate p (Λ i - Λ j) h) := rfl

/-- The conclusions of the positive packet lemma for the data `(R, v, h, Λ)` and the
remainders `e`. Throughout, `d = posScale p.toReal ‖v‖ N` is the scale,
`a = posAmplitude p.toReal d N` the amplitude and
`V = referenceFunction p v h Λ = v + a ∑ᵢ T_{-Λᵢ} h` the reference function. -/
structure PositivePacket (p : ℝ≥0∞) [Fact (1 ≤ p)] {N : ℕ} (R : ℝ) (v h : LebesgueLp p)
    (Λ : Fin N → ℝ) (e : Fin N → LebesgueLp p) : Prop where
  /-- Each remainder is a compactly supported step function. -/
  remainder_step : ∀ i, IsCompactStep p (e i)
  /-- Each remainder is non-negative. -/
  remainder_nonneg : ∀ i, IsNonneg (e i)
  /-- Each remainder is a unit vector. -/
  remainder_norm : ∀ i, ‖e i‖ = 1
  /-- The remainder `e i` lives in the private region of index `i`. -/
  remainder_supported : ∀ i, SupportedOn (e i) (modesRegion R Λ (privateModes i))
  /-- The private regions are pairwise disjoint. -/
  regions_disjoint : ∀ i j, i ≠ j →
    Disjoint (modesRegion R Λ (privateModes i)) (modesRegion R Λ (privateModes j))
  /-- The private regions are disjoint from `I = [-R, R]`. -/
  region_disjoint_base : ∀ i, Disjoint (modesRegion R Λ (privateModes i)) (Set.Icc (-R) R)
  /-- The exact packet identity `T_{Λᵢ} V = d (eᵢ + 2 N^{-1/q} h)`. -/
  translate_eq : ∀ i, translate p (Λ i) (referenceFunction p v h Λ) =
    posScale p.toReal ‖v‖ N • (e i + (2 * (N : ℝ) ^ (-(p.toReal - 1) / p.toReal)) • h)
  /-- The cost of the edit: `‖V - v‖ = a N^{1/p}`. -/
  edit_norm : ‖referenceFunction p v h Λ - v‖ =
    posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N * (N : ℝ) ^ (1 / p.toReal)
  /-- `‖V‖^p = ‖v‖^p + ‖V - v‖^p`. -/
  norm_rpow : ‖referenceFunction p v h Λ‖ ^ p.toReal =
    ‖v‖ ^ p.toReal + ‖referenceFunction p v h Λ - v‖ ^ p.toReal
  /-- `‖v‖ ≤ ‖V‖`. -/
  norm_le : ‖v‖ ≤ ‖referenceFunction p v h Λ‖
  /-- `V` is a compactly supported step function. -/
  reference_step : IsCompactStep p (referenceFunction p v h Λ)
  /-- `V` is non-negative. -/
  reference_nonneg : IsNonneg (referenceFunction p v h Λ)
  /-- `V - v` vanishes on `I = [-R, R]`. -/
  edit_supported : SupportedOn (referenceFunction p v h Λ - v) (Set.Icc (-R) R)ᶜ
  /-- `V - v` is supported to the left of `I`, in `[-(R + ρ), -R)` for every upper bound
  `ρ` of the parameters. -/
  edit_supported_left : ∀ ρ : ℝ, (∀ i, Λ i ≤ ρ) →
    SupportedOn (referenceFunction p v h Λ - v) (Set.Ico (-(R + ρ)) (-R))
  /-- `V` is supported in the bounded interval `[-(R + ρ), R]` for every upper bound `ρ`
  of the parameters (for instance `ρ = max_i Λ i` or `ρ = ∑ i, Λ i`). -/
  reference_supported : ∀ ρ : ℝ, (∀ i, Λ i ≤ ρ) →
    SupportedOn (referenceFunction p v h Λ) (Set.Icc (-(R + ρ)) R)
  /-- `0 < d`. -/
  scale_pos : 0 < posScale p.toReal ‖v‖ N
  /-- `0 < a`. -/
  amplitude_pos : 0 < posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N
  /-- `d ≤ 2^{1/p} ‖v‖` when the deficit is at most `1/2`. -/
  scale_le : posDeficit p.toReal N ≤ 1 / 2 →
    posScale p.toReal ‖v‖ N ≤ 2 ^ (1 / p.toReal) * ‖v‖

section Packet

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {N : ℕ}

theorem referenceFunction_eq (v h : LebesgueLp p) (Λ : Fin N → ℝ) :
    referenceFunction p v h Λ =
      v + packetEdit p Λ (posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N) h := rfl

theorem referenceFunction_sub (v h : LebesgueLp p) (Λ : Fin N → ℝ) :
    referenceFunction p v h Λ - v =
      packetEdit p Λ (posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N) h := by
  rw [referenceFunction_eq, add_sub_cancel_left]

/-- **The positive packet** (paper, lines 3364–3377; non-negative variant of Lemma
`tr:lem:packet`). Let `2 < p < ∞` and let `v, h` be non-negative compactly supported step
functions supported in `[-R, R]` with `v ≠ 0`, `‖h‖ = 1`. Let `N ≥ 1` with
`posDeficit p.toReal N < 1` and let `Λ : Fin N → ℝ` be positive and separated. Then the
explicit remainders `posRemainder p v h Λ` satisfy all the conclusions collected in
`PositivePacket`.

The hypothesis `0 ≤ R` of the paper is not needed here: it follows from `v ≠ 0` and the
support hypothesis, see `radius_nonneg_of_supported`. -/
theorem positive_packet (hp : 2 < p) (hpfin : p ≠ ∞) {R : ℝ}
    {v h : LebesgueLp p} (hvstep : IsCompactStep p v) (hhstep : IsCompactStep p h)
    (hvnn : IsNonneg v) (hhnn : IsNonneg h)
    (hv : SupportedOn v (Set.Icc (-R) R)) (hh : SupportedOn h (Set.Icc (-R) R))
    (hv0 : v ≠ 0) (hhnorm : ‖h‖ = 1) (hN : 1 ≤ N) (hdef : posDeficit p.toReal N < 1)
    {Λ : Fin N → ℝ} (hsep : SeparatedModeIntervals R Λ) (hpos : ∀ i, 0 < Λ i) :
    PositivePacket p R v h Λ (posRemainder p v h Λ) := by
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 2).trans hp)
  have hpR0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hd : 0 < posScale p.toReal ‖v‖ N := posScale_pos hvpos hdef
  have ha : 0 < posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N := posAmplitude_pos hd hN
  have hw (i : Fin N) :
      ‖packetNoise p Λ (posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N) v h i‖ =
        posScale p.toReal ‖v‖ N :=
    norm_packetNoise_eq hp0 hpfin hsep hv hh hhnorm ha.le hd.le
      (pos_noise_power hpR0 hvpos.le hN hdef) i
  have hedit := norm_packetEdit_eq hp0 hpfin hsep hh hhnorm ha.le
  have heout := packetEdit_supported_outside p Λ
    (posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N) hsep hh
  have hnorm : ‖referenceFunction p v h Λ‖ ^ p.toReal =
      ‖v‖ ^ p.toReal + ‖referenceFunction p v h Λ - v‖ ^ p.toReal := by
    rw [referenceFunction_sub, referenceFunction_eq]
    exact norm_add_rpow_of_ae_disjoint _ _ hp0 hpfin
      (hv.ae_disjoint heout disjoint_compl_right)
  have hleft : ∀ ρ : ℝ, (∀ i, Λ i ≤ ρ) →
      SupportedOn (referenceFunction p v h Λ - v) (Set.Ico (-(R + ρ)) (-R)) := by
    intro ρ hρ
    rw [referenceFunction_sub]
    exact packetEdit_supported_left hsep hpos hρ _ hh
  exact
    { remainder_step := fun i => (packetNoise_isCompactStep p Λ _ hvstep hhstep i).smul _
      remainder_nonneg := fun i =>
        (packetNoise_isNonneg Λ ha.le hvnn hhnn i).smul (inv_nonneg.mpr hd.le)
      remainder_norm := fun i => by
        rw [posRemainder, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), hw,
          inv_mul_cancel₀ (ne_of_gt hd)]
      remainder_supported := fun i => (packetNoise_supported p Λ _ hv hh i).real_smul _
      regions_disjoint := fun i j hij => private_regions_disjoint hsep hij
      region_disjoint_base := private_region_disjoint_base hsep
      translate_eq := fun i => by
        rw [referenceFunction_eq, packet_identity, posRemainder, smul_add, smul_smul,
          smul_smul, mul_inv_cancel₀ (ne_of_gt hd), one_smul, ← posAmplitude_eq_mul,
          add_comm]
      edit_norm := by
        rw [referenceFunction_sub]
        exact hedit
      norm_rpow := hnorm
      norm_le := by
        have hle : ‖v‖ ^ p.toReal ≤ ‖referenceFunction p v h Λ‖ ^ p.toReal := by
          rw [hnorm]
          exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)
        exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hpR0).mp hle
      reference_step := hvstep.add (packetEdit_isCompactStep p Λ _ hhstep)
      reference_nonneg := hvnn.add (packetEdit_isNonneg Λ ha.le hhnn)
      edit_supported := by
        rw [referenceFunction_sub]
        exact heout
      edit_supported_left := hleft
      reference_supported := fun ρ hρ => by
        have hρ0 : 0 ≤ ρ := (hpos ⟨0, hN⟩).le.trans (hρ ⟨0, hN⟩)
        have hR0 : 0 ≤ R := radius_nonneg_of_supported hv0 hv
        have hvs : SupportedOn v (Set.Icc (-(R + ρ)) R) :=
          hv.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
        have hes : SupportedOn (referenceFunction p v h Λ - v) (Set.Icc (-(R + ρ)) R) :=
          (hleft ρ hρ).mono (fun x hx => ⟨hx.1, by linarith [hx.2, hR0]⟩)
        have hsum := hvs.add hes
        rwa [add_sub_cancel] at hsum
      scale_pos := hd
      amplitude_pos := ha
      scale_le := fun hhalf => posScale_le hpR0 (norm_nonneg v) hhalf }

/-- Existential form of `positive_packet`. -/
theorem exists_positive_remainders (hp : 2 < p) (hpfin : p ≠ ∞) {R : ℝ}
    {v h : LebesgueLp p} (hvstep : IsCompactStep p v) (hhstep : IsCompactStep p h)
    (hvnn : IsNonneg v) (hhnn : IsNonneg h)
    (hv : SupportedOn v (Set.Icc (-R) R)) (hh : SupportedOn h (Set.Icc (-R) R))
    (hv0 : v ≠ 0) (hhnorm : ‖h‖ = 1) (hN : 1 ≤ N) (hdef : posDeficit p.toReal N < 1)
    {Λ : Fin N → ℝ} (hsep : SeparatedModeIntervals R Λ) (hpos : ∀ i, 0 < Λ i) :
    ∃ e : Fin N → LebesgueLp p, PositivePacket p R v h Λ e :=
  ⟨posRemainder p v h Λ,
    positive_packet hp hpfin hvstep hhstep hvnn hhnn hv hh hv0 hhnorm hN hdef hsep hpos⟩

end Packet

/-! ### Consequences: everything lives in a bounded interval -/

namespace PositivePacket

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {N : ℕ} {R : ℝ} {v h : LebesgueLp p} {Λ : Fin N → ℝ}
  {e : Fin N → LebesgueLp p}

/-- The cost of the edit in the form of the paper: `‖V - v‖ = 2 d N^{2/p - 1}`. -/
theorem edit_norm_eq (P : PositivePacket p R v h Λ e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (hN : 1 ≤ N) :
    ‖referenceFunction p v h Λ - v‖ =
      2 * posScale p.toReal ‖v‖ N * (N : ℝ) ^ (2 / p.toReal - 1) := by
  rw [P.edit_norm, posAmplitude_mul_rpow (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩) hN]

/-- `V` is supported in the symmetric interval `[-(R + ρ), R + ρ]`. -/
theorem reference_supported_symm (P : PositivePacket p R v h Λ e) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ i, Λ i ≤ ρ) :
    SupportedOn (referenceFunction p v h Λ) (Set.Icc (-(R + ρ)) (R + ρ)) :=
  (P.reference_supported ρ hρ).mono (Set.Icc_subset_Icc le_rfl (by linarith))

/-- `V` is supported in `[-(R + ∑ᵢ Λᵢ), R + ∑ᵢ Λᵢ]`: an explicit radius. -/
theorem reference_supported_sum (P : PositivePacket p R v h Λ e) (hpos : ∀ i, 0 < Λ i) :
    SupportedOn (referenceFunction p v h Λ)
      (Set.Icc (-(R + ∑ i, Λ i)) (R + ∑ i, Λ i)) :=
  P.reference_supported_symm (Finset.sum_nonneg (fun i _ => (hpos i).le)) (le_sum_of_pos hpos)

/-- For increasing parameters `V` is supported in `[-(R + Λ_max), R + Λ_max]`, where
`Λ_max = Λ (N-1)` is the largest parameter. -/
theorem reference_supported_last (P : PositivePacket p R v h Λ e) (hpos : ∀ i, 0 < Λ i)
    (hmono : Monotone Λ) (hN : 1 ≤ N) :
    SupportedOn (referenceFunction p v h Λ)
      (Set.Icc (-(R + Λ ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩))
        (R + Λ ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩)) :=
  P.reference_supported_symm (hpos _).le (le_last_of_monotone hmono hN)

/-- Each remainder is supported in `[-(R + ρ), R + ρ]`. -/
theorem remainder_supported_Icc (P : PositivePacket p R v h Λ e) (hpos : ∀ i, 0 < Λ i)
    {ρ : ℝ} (hρ : ∀ i, Λ i ≤ ρ) (i : Fin N) :
    SupportedOn (e i) (Set.Icc (-(R + ρ)) (R + ρ)) :=
  (P.remainder_supported i).mono (privateRegion_subset_Icc (fun j => (hpos j).le) hρ i)

/-- Each new translate `T_{Λᵢ} V` is supported in `[-(R + ρ), R + ρ]`. -/
theorem translate_supported_Icc (P : PositivePacket p R v h Λ e) (hpos : ∀ i, 0 < Λ i)
    (hh : SupportedOn h (Set.Icc (-R) R)) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ i, Λ i ≤ ρ)
    (i : Fin N) :
    SupportedOn (translate p (Λ i) (referenceFunction p v h Λ))
      (Set.Icc (-(R + ρ)) (R + ρ)) := by
  rw [P.translate_eq i]
  have hh' : SupportedOn h (Set.Icc (-(R + ρ)) (R + ρ)) :=
    hh.mono (Set.Icc_subset_Icc (by linarith) (by linarith))
  exact ((P.remainder_supported_Icc hpos hρ i).add (hh'.real_smul _)).real_smul _

end PositivePacket

end StructuredBases.PositiveTranslates
