import Lean_Code.SchauderTranslates.Lp.Packet
import Lean_Code.SchauderTranslates.Lp.BranchScalars

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def physicalLayerMean {N : ℕ} (p : ℝ≥0∞) (e : Fin N → LebesgueLp p) : LebesgueLp p :=
  layerPrimalScale p.toReal N • ∑ i, e i

def physicalNextResidual (p : ℝ≥0∞) (h u : LebesgueLp p) : LebesgueLp p :=
  branchBeta p.toReal • (h - u)

theorem physical_layer_mean_unit {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) {N : ℕ} (hN : 1 ≤ N)
    (e : Fin N → LebesgueLp p) (he : ∀ i, ‖e i‖ = 1)
    (hdis : ∀ i j, i ≠ j → ∀ᵐ x ∂volume, e i x = 0 ∨ e j x = 0) :
    ‖physicalLayerMean p e‖ = 1 := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  apply (Real.rpow_left_inj (norm_nonneg _) (by norm_num) hpR.ne').mp
  rw [physicalLayerMean, norm_real_smul_rpow,
    abs_of_pos (layer_scale_pos p.toReal hN).1,
    norm_finset_sum_rpow Finset.univ _ hp0 hpfin (fun i _ j _ hij => hdis i j hij)]
  simp only [he, Real.one_rpow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  rw [mul_comm, layer_primal_power hpR hN]

theorem physical_next_residual_unit {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (h u : LebesgueLp p)
    (hh : ‖h‖ = 1) (hu : ‖u‖ = 1) (hdis : ∀ᵐ x ∂volume, h x = 0 ∨ u x = 0) :
    ‖physicalNextResidual p h u‖ = 1 := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  have hd : ∀ᵐ x ∂volume, h x = 0 ∨ (-u) x = 0 := by
    filter_upwards [hdis, Lp.coeFn_neg u] with x hx hn
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by rw [hn]; simp [hx])
  apply (Real.rpow_left_inj (norm_nonneg _) (by norm_num) hpR.ne').mp
  rw [physicalNextResidual, norm_real_smul_rpow, abs_of_pos (branch_beta_pos _),
    branch_beta_power hpR, sub_eq_add_neg,
    norm_add_rpow_of_ae_disjoint h (-u) hp0 hpfin hd, norm_neg, hh, hu, Real.one_rpow]
  norm_num

theorem physicalLayerMean_isCompactStep {p : ℝ≥0∞} {N : ℕ} (e : Fin N → LebesgueLp p)
    (he : ∀ i, IsCompactStep p (e i)) : IsCompactStep p (physicalLayerMean p e) :=
  (IsCompactStep.finset_sum Finset.univ _ (fun i _ => he i)).smul _

theorem physicalNextResidual_isCompactStep {p : ℝ≥0∞} {h u : LebesgueLp p}
    (hh : IsCompactStep p h) (hu : IsCompactStep p u) : IsCompactStep p (physicalNextResidual p h u) :=
  IsCompactStep.smul ((stepSpace p).sub_mem hh hu) _

end SchauderTranslates.LpConstruction
