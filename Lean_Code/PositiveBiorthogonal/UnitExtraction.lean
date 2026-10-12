import Lean_Code.PositiveBiorthogonal.UnitTransfer
import Lean_Code.PositiveBiorthogonal.Auxiliary

/-! Contractive extraction and transport of every finite auxiliary partial projection. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ComplexOrder
namespace PositiveBiorthogonal
namespace UnitBlock
variable {m : ℕ} (B : UnitBlock m) {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def extract (f : L 𝕜 p) : FiniteLp 𝕜 p m :=
  WithLp.toLp p (fun i => ∫ t in (B.cell i).carrier, f t)

@[simp] theorem extract_apply (f : L 𝕜 p) (i : Fin m) :
    B.extract f i = ∫ t in (B.cell i).carrier, f t := rfl

def averageCLM : L 𝕜 p →L[𝕜] L 𝕜 p := ∑ i : Fin m, (B.cell i).averageCLM (q := q)

theorem averageCLM_localized_and_norm :
    LocalizedOperator B.carrier B.measurable (B.averageCLM (𝕜 := 𝕜) (p := p) (q := q)) ∧
      ‖B.averageCLM (𝕜 := 𝕜) (p := p) (q := q)‖ ≤ 1 := by
  have h := disjoint_operator_sum Finset.univ (fun i : Fin m => (B.cell i).carrier)
    (fun i => (B.cell i).measurable) B.disjoint
    (fun i => (B.cell i).averageCLM (𝕜 := 𝕜) (p := p) (q := q))
    (fun i => (B.cell i).averageCLM_localized) 1 zero_le_one
    (fun i => (B.cell i).averageCLM_norm.le)
  simpa only [Finset.mem_univ, iUnion_true, averageCLM, carrier] using h

theorem averageCLM_apply (f : L 𝕜 p) : B.averageCLM (q := q) f = B.transfer (B.extract f) := by
  simp [averageCLM, transfer, extract, B.cell_length]

include q in
theorem extract_norm_le (f : L 𝕜 p) : ‖B.extract f‖ ≤ ‖f‖ := by
  let T : L 𝕜 p →L[𝕜] L 𝕜 p := B.averageCLM (q := q)
  have hb : ‖T‖ ≤ 1 := (B.averageCLM_localized_and_norm (𝕜 := 𝕜) (p := p) (q := q)).2
  have h : ‖T f‖ ≤ ‖f‖ := (T.le_opNorm f).trans (by
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg f)).trans_eq (one_mul _))
  change ‖B.averageCLM (q := q) f‖ ≤ ‖f‖ at h
  rw [B.averageCLM_apply (q := q), B.transfer_norm] at h
  exact h

include q in
theorem extract_transfer (x : FiniteLp 𝕜 p m) : B.extract (B.transfer x) = x := by
  ext i
  rw [B.extract_apply, ← (B.cell i).pairing_indicator (q := q), B.transfer_pairing_indicator]

theorem extract_pairing (f : L 𝕜 p) (y : FiniteLp 𝕜 q m) :
    pairing f (B.transfer y) = finitePairing (B.extract f) y := by
  rw [← pairingCLM_apply]
  change pairingCLM (q := q) f (∑ i : Fin m, y i • (B.cell i).indicator) = _
  rw [map_sum]
  simp only [map_smul, pairingCLM_apply, IntervalCell.pairing_indicator,
    smul_eq_mul, finitePairing, extract_apply, mul_comm]

def extractLinear : L 𝕜 p →ₗ[𝕜] FiniteLp 𝕜 p m where
  toFun := B.extract
  map_add' f g := by
    ext i
    simp only [PiLp.add_apply, extract_apply, ← (B.cell i).pairing_indicator (q := q),
      ← representedFunctional_apply]
    exact map_add _ f g
  map_smul' c f := by
    ext i
    simp only [PiLp.smul_apply, extract_apply, RingHom.id_apply,
      ← (B.cell i).pairing_indicator (q := q), ← representedFunctional_apply]
    exact map_smul _ c f

def extractCLM : L 𝕜 p →L[𝕜] FiniteLp 𝕜 p m :=
  (B.extractLinear (q := q)).mkContinuous 1 (fun f => by
    change ‖B.extract f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using B.extract_norm_le (q := q) f)

@[simp] theorem extractCLM_apply (f : L 𝕜 p) : B.extractCLM (q := q) f = B.extract f := rfl

theorem extractCLM_norm_le : ‖B.extractCLM (𝕜 := 𝕜) (p := p) (q := q)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖B.extract f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using B.extract_norm_le (q := q) f

theorem extract_cut (f : L 𝕜 p) : B.extract (cut B.carrier B.measurable f) = B.extract f := by
  ext i
  simp only [extract_apply]
  apply setIntegral_congr_ae (B.cell i).measurable
  filter_upwards [coeFn_cut B.carrier B.measurable f] with t ht
  intro hti
  simp [ht, B.cell_subset i hti]

def projection (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m) (h : ℕ) :
    L 𝕜 p →L[𝕜] L 𝕜 p :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < h),
    (representedFunctional (B.transfer (s j))).smulRight (B.transfer (d j))

theorem projection_apply (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m)
    (h : ℕ) (f : L 𝕜 p) :
    B.projection d s h f = B.transfer (finiteRankProjection d s h (B.extract f)) := by
  rw [finiteRankProjection_apply]
  change _ = B.transferLinear (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < h),
    finitePairing (B.extract f) (s j) • d j)
  rw [map_sum]
  simp only [projection, sum_apply, ContinuousLinearMap.smulRight_apply,
    representedFunctional_apply, B.extract_pairing, map_smul]
  rfl

theorem projection_localized (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m)
    (h : ℕ) : LocalizedOperator B.carrier B.measurable (B.projection d s h) where
  input f := by rw [B.projection_apply, B.projection_apply, B.extract_cut]
  output f := by rw [B.projection_apply]; exact B.transfer_supported _

theorem projection_norm_le (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m)
    (h : ℕ) (C : ℝ) (hC : ‖finiteRankProjection d s h‖ ≤ C) : ‖B.projection d s h‖ ≤ C := by
  have hc : 0 ≤ C := (norm_nonneg _).trans hC
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro f
  rw [B.projection_apply, B.transfer_norm]
  exact ((finiteRankProjection d s h).le_opNorm _).trans
    (mul_le_mul hC (B.extract_norm_le (q := q) f) (norm_nonneg _) hc)

end UnitBlock

theorem finiteRankProjection_full {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] {m : ℕ}
    (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m)
    (hbi : ∀ i j, finitePairing (d i) (s j) = if i = j then 1 else 0) :
    finiteRankProjection d s m = ContinuousLinearMap.id 𝕜 (FiniteLp 𝕜 p m) := by
  classical
  have hfix : ∀ x ∈ Submodule.span 𝕜 (range d), finiteRankProjection d s m x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp [finiteRankProjection_apply, hbi]
    | zero => exact map_zero _
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_smul, hx]
  apply ContinuousLinearMap.ext
  intro x
  exact hfix x (by rw [finiteBiorthogonal_span d s hbi]; trivial)

namespace UnitBlock
variable {m : ℕ} (B : UnitBlock m) {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem projection_full (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m)
    (hbi : ∀ i j, finitePairing (d i) (s j) = if i = j then 1 else 0) :
    B.projection d s m = B.averageCLM (q := q) := by
  ext f
  rw [B.projection_apply, finiteRankProjection_full d s hbi, ContinuousLinearMap.id_apply,
    B.averageCLM_apply]

@[simp] theorem projection_zero (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m) :
    B.projection d s 0 = 0 := by simp [projection]

theorem auxiliary_projection_bound {N : ℕ} (F : UnitBlock (2 * N)) (hN : 0 < N)
    {δ : ℝ} (A : AuxiliaryFamily 𝕜 p q δ) (h : ℕ) (hh : h ≤ 2 * N) :
    ‖F.projection (A.d N) (A.s N) h‖ ≤ 1 + δ :=
  F.projection_norm_le _ _ _ _ (A.projection_bound N hN h hh)

end UnitBlock
end PositiveBiorthogonal
