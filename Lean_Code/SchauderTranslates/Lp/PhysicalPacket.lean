import Lean_Code.SchauderTranslates.Lp.PhysicalLayerNorm
import Lean_Code.SchauderTranslates.Lp.StepCellAvoidance

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- One actual packet, with permanent step-cell geometry. The old interval
and the edit budget are inputs, fixed before its finite size is selected. -/
structure PhysicalPacket (p : ℝ≥0∞) [Fact (1 ≤ p)] (R : ℝ)
    (v h : LebesgueLp p) (old : Finset ℝ) (ε : ℝ) where
  size : ℕ
  size_pos : 1 ≤ size
  parameter : Fin size → ℝ
  parameter_injective : Function.Injective parameter
  parameter_positive : ∀ i, 0 < parameter i
  parameter_fresh : ∀ i, parameter i ∉ old
  scale : ℝ
  scale_pos : 0 < scale
  generator : LebesgueLp p
  generator_step : IsCompactStep p generator
  privateVector : Fin size → LebesgueLp p
  privateStep : ∀ i, IsCompactStep p (privateVector i)
  privateUnit : ∀ i, ‖privateVector i‖ = 1
  privateData : ∀ i, DisjointStepData p (privateVector i)
  privateCellDisjoint : ∀ i j, i ≠ j →
    Disjoint (privateData i).supportSet (privateData j).supportSet
  privateCellFresh : ∀ i, Disjoint (privateData i).supportSet (Set.Ico (-R) R)
  privateOutside : ∀ i, SupportedOn (privateVector i) (Set.Icc (-R) R)ᶜ
  privateDisjoint : ∀ i j, i ≠ j →
    ∀ᵐ x ∂volume, privateVector i x = 0 ∨ privateVector j x = 0
  residualDisjoint : ∀ i, ∀ᵐ x ∂volume, h x = 0 ∨ privateVector i x = 0
  birthIdentity : ∀ i, translate p (parameter i) generator =
    scale • (privateVector i + layerDualScale p.toReal size • h)
  editBound : ‖generator - v‖ ≤ ε
  editOutside : SupportedOn (generator - v) (Set.Icc (-R) R)ᶜ
  normBalance : ‖generator‖ ^ p.toReal = ‖v‖ ^ p.toReal + ‖generator - v‖ ^ p.toReal

theorem physical_packet_exists {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 < p) (hpfin : p ≠ ∞)
    {R : ℝ} (hR : 0 ≤ R) (v h : LebesgueLp p)
    (hvstep : IsCompactStep p v) (hhstep : IsCompactStep p h) (hv0 : v ≠ 0)
    (hhnorm : ‖h‖ = 1) (hv : SupportedOn v (Set.Icc (-R) R))
    (hh : SupportedOn h (Set.Icc (-R) R)) (old : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (PhysicalPacket p R v h old ε) := by
  classical
  obtain ⟨N, Λ, d, g, e, hN, hd, hΛ, hΛold, hg, he, hbase, hregions,
    hbirth, hedit, hout, hbalance⟩ := exact_packet hp hpfin hR v h hvstep hhstep hv0 hhnorm hv hh old hε
  let D : ∀ i, DisjointStepData p (e i) := fun i => Classical.choice (he i).1.disjoint_data
  have hdis (i j : Fin N) (hij : i ≠ j) : ∀ᵐ x ∂volume, e i x = 0 ∨ e j x = 0 :=
    (he i).2.2.ae_disjoint (he j).2.2 (hregions i j hij)
  have hhd (i : Fin N) : ∀ᵐ x ∂volume, h x = 0 ∨ e i x = 0 :=
    hh.ae_disjoint (he i).2.2 (hbase i).symm
  refine ⟨{
    size := N
    size_pos := hN
    parameter := Λ
    parameter_injective := hΛ
    parameter_positive := fun i => (hΛold i).1
    parameter_fresh := fun i => (hΛold i).2
    scale := d
    scale_pos := hd
    generator := g
    generator_step := hg
    privateVector := e
    privateStep := fun i => (he i).1
    privateUnit := fun i => (he i).2.1
    privateData := D
    privateCellDisjoint := fun i j hij => (D i).supportSet_disjoint (D j) (hdis i j hij)
    privateCellFresh := ?_
    privateOutside := fun i => (he i).2.2.mono (fun _ hx hI =>
      Set.disjoint_left.mp (hbase i) hx hI)
    privateDisjoint := hdis
    residualDisjoint := hhd
    birthIdentity := by simpa only [layerDualScale] using hbirth
    editBound := hedit
    editOutside := hout
    normBalance := hbalance }⟩
  intro i
  apply (D i).supportSet_disjoint_ico (-R) R
  apply (he i).2.2.mono
  intro x hx hI
  exact Set.disjoint_left.mp (hbase i) hx ⟨hI.1, hI.2.le⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ} {v h : LebesgueLp p}
    {old : Finset ℝ} {ε : ℝ} (P : PhysicalPacket p R v h old ε)

def PhysicalPacket.mean : LebesgueLp p := physicalLayerMean p P.privateVector
def PhysicalPacket.nextResidual : LebesgueLp p := physicalNextResidual p h P.mean

theorem PhysicalPacket.mean_unit (hp0 : p ≠ 0) (hpfin : p ≠ ∞) : ‖P.mean‖ = 1 :=
  physical_layer_mean_unit hp0 hpfin P.size_pos P.privateVector P.privateUnit P.privateDisjoint

theorem PhysicalPacket.mean_step : IsCompactStep p P.mean :=
  physicalLayerMean_isCompactStep P.privateVector P.privateStep

theorem PhysicalPacket.residual_mean_disjoint : ∀ᵐ x ∂volume, h x = 0 ∨ P.mean x = 0 :=
  ae_disjoint_real_smul_right h (∑ i, P.privateVector i) (layerPrimalScale p.toReal P.size)
    (ae_disjoint_finset_sum Finset.univ h P.privateVector (fun i _ => P.residualDisjoint i))

theorem PhysicalPacket.nextResidual_unit (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (hh : ‖h‖ = 1) :
    ‖P.nextResidual‖ = 1 :=
  physical_next_residual_unit hp0 hpfin h P.mean hh (P.mean_unit hp0 hpfin) P.residual_mean_disjoint

theorem PhysicalPacket.nextResidual_step (hh : IsCompactStep p h) : IsCompactStep p P.nextResidual :=
  physicalNextResidual_isCompactStep hh P.mean_step

theorem PhysicalPacket.generator_norm_ge (hp0 : p ≠ 0) (hpfin : p ≠ ∞) : ‖v‖ ≤ ‖P.generator‖ := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _)
    (ENNReal.toReal_pos hp0 hpfin)).mp
  rw [P.normBalance]
  exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)

theorem PhysicalPacket.generator_ne_zero (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (hv : v ≠ 0) :
    P.generator ≠ 0 :=
  norm_pos_iff.mp ((norm_pos_iff.mpr hv).trans_le (P.generator_norm_ge hp0 hpfin))

end SchauderTranslates.LpConstruction
