import Lean_Code.PositiveBiorthogonal.LocalCorrection

/-! The common correction size and its decay as the splitting parameter increases. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace PositiveBiorthogonal

theorem correction_power_identity (r s θ V ℓ R n C Z : ℝ)
    (hrs : r + s = 1) (hθ : 0 < θ) (hV : 0 < V) (hℓ : 0 < ℓ)
    (hR : 0 < R) (hn : 0 < n) (he : θ = (R / 2) / (R * n)) :
    (C * θ ^ (-s) * ℓ ^ (-s)) * θ * V ^ s * Z =
      (C * (R / 2) ^ r * (V / ℓ) ^ s) * ((R * n) ^ (-r) * Z) := by
  have ht : θ ^ (-s) * θ = θ ^ r := by
    calc
      _ = θ ^ (-s) * θ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = θ ^ (-s + 1) := (Real.rpow_add hθ _ _).symm
      _ = θ ^ r := by congr 1; linarith
  have hv : ℓ ^ (-s) * V ^ s = (V / ℓ) ^ s := by
    rw [Real.div_rpow hV.le hℓ.le, Real.rpow_neg hℓ.le]
    ring
  have hp : θ ^ r = (R / 2) ^ r * (R * n) ^ (-r) := by
    rw [he, Real.div_rpow (by positivity) (mul_pos hR hn).le, Real.rpow_neg (mul_pos hR hn).le]
    rfl
  calc
    _ = C * (θ ^ (-s) * θ) * (ℓ ^ (-s) * V ^ s) * Z := by ring
    _ = _ := by rw [ht, hv, hp]; ring

namespace AuxiliaryFamily
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  {δ : ℝ} (A : AuxiliaryFamily 𝕜 p q δ)

def correctionSize (P : ActivePartition) (η : ℝ) (steps : ℕ) : ℝ :=
  A.batchScale P steps η * splitTheta steps *
    (volume.real P.active) ^ (1 / q.toReal) * ‖A.z (P.R * steps)‖

def correctionFactor (P : ActivePartition) (η : ℝ) : ℝ :=
  (2 * A.M / η) * ((P.R : ℝ) / 2) ^ (1 / p.toReal) *
    (volume.real P.active / P.minLength) ^ (1 / q.toReal)

theorem correctionSize_formula (P : ActivePartition) (η : ℝ) (steps : ℕ) (hs : 2 ≤ steps) :
    A.correctionSize P η steps = A.correctionFactor P η *
      ((P.R * steps : ℕ) : ℝ) ^ (-(1 / p.toReal)) * ‖A.z (P.R * steps)‖ := by
  have hR : (0 : ℝ) < P.R := by exact_mod_cast P.R_pos
  have hn : (0 : ℝ) < steps := by exact_mod_cast (show 0 < steps by omega)
  have he : splitTheta steps = ((P.R : ℝ) / 2) / ((P.R : ℝ) * steps) := by
    unfold splitTheta
    field_simp
  have h := correction_power_identity (1 / p.toReal) (1 / q.toReal) (splitTheta steps)
    (volume.real P.active) P.minLength P.R steps (2 * A.M / η) ‖A.z (P.R * steps)‖
    (holder_reciprocal_reals (p := p) (q := q)) (splitTheta_pos steps hs)
    P.active_volume_real_pos P.minLength_pos hR hn he
  simpa only [correctionSize, batchScale, correctionFactor, Nat.cast_mul, mul_assoc] using h

theorem correctionSize_tendsto_zero (P : ActivePartition) (η : ℝ) :
    Tendsto (A.correctionSize P η) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => P.R * n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hnb
    have hr := P.R_pos
    nlinarith
  have h := (A.small_correction.comp hn).const_mul (A.correctionFactor P η)
  have hlim : Tendsto (fun n : ℕ => A.correctionFactor P η *
      (((P.R * n : ℕ) : ℝ) ^ (-(1 / p.toReal)) * ‖A.z (P.R * n)‖)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using h
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [A.correctionSize_formula P η n hn, mul_assoc]

theorem correctionSize_nonneg (P : ActivePartition) (η : ℝ) (hη : 0 < η)
    (steps : ℕ) (hs : 2 ≤ steps) : 0 ≤ A.correctionSize P η steps := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (A.batchScale_pos P steps hs η hη).le
    (splitTheta_pos steps hs).le) (Real.rpow_nonneg P.active_volume_real_pos.le _)) (norm_nonneg _)

theorem local_correction_norms (P : ActivePartition) (η : ℝ) (hη : 0 < η)
    (steps : ℕ) (hs : 2 ≤ steps) (F : UnitBlock (2 * (P.R * steps))) :
    ‖localS (q := q) P (F.transfer (A.z (P.R * steps)))
        (A.batchScale P steps η * splitTheta steps)‖ = A.correctionSize P η steps ∧
    ‖localR (q := q) P (F.transfer (A.z (P.R * steps)))
        (A.batchScale P steps η * splitTheta steps)‖ = A.correctionSize P η steps := by
  have hc : 0 ≤ A.batchScale P steps η * splitTheta steps :=
    mul_nonneg (A.batchScale_pos P steps hs η hη).le (splitTheta_pos steps hs).le
  rw [localS_norm _ _ _ hc, localR_norm _ _ _ hc, F.transfer_norm]
  exact ⟨rfl, rfl⟩

theorem exists_small_splitting (P : ActivePartition) (η ε : ℝ) (hε : 0 < ε) :
    ∃ steps : ℕ, 2 ≤ steps ∧ A.correctionSize P η steps < ε := by
  have he := (A.correctionSize_tendsto_zero P η).eventually (gt_mem_nhds hε)
  obtain ⟨steps, hs, hbound⟩ := (Filter.Eventually.and (eventually_ge_atTop 2) he).exists
  exact ⟨steps, hs, hbound⟩

end AuxiliaryFamily
end PositiveBiorthogonal
