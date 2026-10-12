import Lean_Code.PositiveTranslates.Packet.Packet

/-!
# The positive packet with parameters in a prescribed set

This is the top file of `Lean_Code/PositiveTranslates/Packet/`. It combines

* (A) `exists_placement` (file `Placement.lean`): inside a set `Γ ⊆ ℝ` that is unbounded
  above one can choose `N` strictly increasing positive parameters above any threshold
  that satisfy `SeparatedModeIntervals R Λ`;
* (B) `positive_packet` (file `Packet.lean`): for separated positive parameters the
  non-negative reference function `V = v + a ∑ᵢ T_{-Λᵢ} h` satisfies
  `T_{Λᵢ} V = d (eᵢ + 2 N^{-1/q} h)` with non-negative unit remainders `eᵢ` in disjoint
  private regions, and `‖V - v‖ = a N^{1/p}`

into the statements used by an inductive construction:

* `positive_packet_placement` : (B) for the explicit parameters `placement hΓ R T N`;
* `exists_positive_packet` : existence of `Λ` (in `Γ`, above `T`, strictly increasing) and
  `e` with all the properties, for a given size `N`;
* `exists_positive_packet_small` : for every `ε > 0` all sufficiently large sizes `N` have
  deficit at most `1/2` and carry such a packet with `‖V - v‖ ≤ ε` (the non-negative
  variant of Lemma `tr:lem:packet` of the paper).

The scale facts (`posDeficit_tendsto`, `exists_posDeficit_le_half`,
`posAmplitude_mul_rpow`, `posCost_tendsto`, `exists_packet_size`, `posScale_le`) are in
`Scales.lean`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {N : ℕ}

/-- The positive packet for the explicit parameters `placement hΓ R T N ⊆ Γ` and the
explicit remainders `posRemainder`. -/
theorem positive_packet_placement (hp : 2 < p) (hpfin : p ≠ ∞) {Γ : Set ℝ}
    (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (T : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {v h : LebesgueLp p} (hvstep : IsCompactStep p v) (hhstep : IsCompactStep p h)
    (hvnn : IsNonneg v) (hhnn : IsNonneg h)
    (hv : SupportedOn v (Set.Icc (-R) R)) (hh : SupportedOn h (Set.Icc (-R) R))
    (hv0 : v ≠ 0) (hhnorm : ‖h‖ = 1) (hN : 1 ≤ N) (hdef : posDeficit p.toReal N < 1) :
    PositivePacket p R v h (placement hΓ R T N)
      (posRemainder p v h (placement hΓ R T N)) :=
  positive_packet hp hpfin hvstep hhstep hvnn hhnn hv hh hv0 hhnorm hN hdef
    (placement_separated hΓ hR T N) (placement_pos hΓ R T N)

/-- **The positive packet inside a prescribed set.** Let `Γ ⊆ ℝ` be unbounded above,
`T` a threshold, `2 < p < ∞`, `R ≥ 0`, and let `v, h` be non-negative compactly supported
step functions supported in `[-R, R]` with `v ≠ 0`, `‖h‖ = 1`. For every `N ≥ 1` with
`posDeficit p.toReal N < 1` there are parameters `Λ 0 < ⋯ < Λ (N-1)` in `Γ`, above `T`
and positive, satisfying the separation property, and remainders `e` with all the
properties collected in `PositivePacket`. -/
theorem exists_positive_packet (hp : 2 < p) (hpfin : p ≠ ∞) {Γ : Set ℝ}
    (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (T : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {v h : LebesgueLp p} (hvstep : IsCompactStep p v) (hhstep : IsCompactStep p h)
    (hvnn : IsNonneg v) (hhnn : IsNonneg h)
    (hv : SupportedOn v (Set.Icc (-R) R)) (hh : SupportedOn h (Set.Icc (-R) R))
    (hv0 : v ≠ 0) (hhnorm : ‖h‖ = 1) (hN : 1 ≤ N) (hdef : posDeficit p.toReal N < 1) :
    ∃ (Λ : Fin N → ℝ) (e : Fin N → LebesgueLp p),
      (∀ i, Λ i ∈ Γ) ∧ (∀ i, T < Λ i) ∧ (∀ i, 0 < Λ i) ∧ StrictMono Λ ∧
      SeparatedModeIntervals R Λ ∧ PositivePacket p R v h Λ e :=
  ⟨placement hΓ R T N, posRemainder p v h (placement hΓ R T N),
    placement_mem hΓ R T N, lt_placement hΓ R T N, placement_pos hΓ R T N,
    placement_strictMono hΓ hR T N, placement_separated hΓ hR T N,
    positive_packet_placement hp hpfin hΓ T hR hvstep hhstep hvnn hhnn hv hh hv0 hhnorm
      hN hdef⟩

/-- **Non-negative variant of Lemma `tr:lem:packet`.** With the data of
`exists_positive_packet` and `ε > 0`, every sufficiently large size `N` has deficit at
most `1/2`, and there are parameters in `Γ` above `T` and remainders `e` forming a
positive packet whose edit costs at most `ε`: `‖V - v‖ ≤ ε`. -/
theorem exists_positive_packet_small (hp : 2 < p) (hpfin : p ≠ ∞) {Γ : Set ℝ}
    (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (T : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {v h : LebesgueLp p} (hvstep : IsCompactStep p v) (hhstep : IsCompactStep p h)
    (hvnn : IsNonneg v) (hhnn : IsNonneg h)
    (hv : SupportedOn v (Set.Icc (-R) R)) (hh : SupportedOn h (Set.Icc (-R) R))
    (hv0 : v ≠ 0) (hhnorm : ‖h‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N → posDeficit p.toReal N ≤ 1 / 2 ∧
      ∃ (Λ : Fin N → ℝ) (e : Fin N → LebesgueLp p),
        (∀ i, Λ i ∈ Γ) ∧ (∀ i, T < Λ i) ∧ (∀ i, 0 < Λ i) ∧ StrictMono Λ ∧
        SeparatedModeIntervals R Λ ∧ PositivePacket p R v h Λ e ∧
        ‖referenceFunction p v h Λ - v‖ ≤ ε := by
  obtain ⟨N₀, hN₀, hsize⟩ := exists_packet_size (two_lt_toReal hp hpfin) ‖v‖ hε
  refine ⟨N₀, hN₀, fun N hN => ?_⟩
  obtain ⟨hhalf, hcost⟩ := hsize N hN
  refine ⟨hhalf, ?_⟩
  obtain ⟨Λ, e, hmem, hT, hpos, hmono, hsep, hP⟩ :=
    exists_positive_packet hp hpfin hΓ T hR hvstep hhstep hvnn hhnn hv hh hv0 hhnorm
      (hN₀.trans hN) (lt_of_le_of_lt hhalf (by norm_num))
  refine ⟨Λ, e, hmem, hT, hpos, hmono, hsep, hP, ?_⟩
  rw [hP.edit_norm]
  exact hcost ‖v‖ (norm_nonneg v) le_rfl

end StructuredBases.PositiveTranslates
