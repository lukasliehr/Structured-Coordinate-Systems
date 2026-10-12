import Lean_Code.SchauderTranslates.ProjectionPair

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Active and inactive axes obtained by rotating a two-projection eigenplane. -/
def projectionPlaneActive (t : ℝ) (v w : K) : K := Real.sqrt t • v + Real.sqrt (1 - t) • w

def projectionPlaneInactive (t : ℝ) (v w : K) : K := Real.sqrt (1 - t) • v - Real.sqrt t • w

/-- Rotation interchanges the diagonal projection and the displayed two-by-two projection. -/
theorem projectionPlane_rotation (F Q : K →L[ℝ] K) (v w : K)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : inner ℝ v w = 0)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hFv : F v = v) (hFw : F w = 0)
    (hQv : Q v = t • v + Real.sqrt (t * (1 - t)) • w)
    (hQw : Q w = Real.sqrt (t * (1 - t)) • v + (1 - t) • w) :
    let a := projectionPlaneActive t v w
    let b := projectionPlaneInactive t v w
    ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ inner ℝ a b = 0 ∧ Q a = a ∧ Q b = 0 ∧
      F a = t • a + Real.sqrt (t * (1 - t)) • b ∧
      F b = Real.sqrt (t * (1 - t)) • a + (1 - t) • b ∧
      v = Real.sqrt t • a + Real.sqrt (1 - t) • b ∧
      w = Real.sqrt (1 - t) • a - Real.sqrt t • b := by
  let c := Real.sqrt t
  let d := Real.sqrt (1 - t)
  have hc : c ^ 2 = t := Real.sq_sqrt ht
  have hd : d ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hcd : c ^ 2 + d ^ 2 = 1 := by linarith
  have hs : Real.sqrt (t * (1 - t)) = c * d := Real.sqrt_mul ht _
  have hwv : inner ℝ w v = 0 := by rw [real_inner_comm, hvw]
  change ‖c • v + d • w‖ = 1 ∧ ‖d • v - c • w‖ = 1 ∧
    inner ℝ (c • v + d • w) (d • v - c • w) = 0 ∧
    Q (c • v + d • w) = c • v + d • w ∧ Q (d • v - c • w) = 0 ∧
    F (c • v + d • w) = t • (c • v + d • w) + Real.sqrt (t * (1 - t)) • (d • v - c • w) ∧
    F (d • v - c • w) = Real.sqrt (t * (1 - t)) • (c • v + d • w) + (1 - t) • (d • v - c • w) ∧
    v = c • (c • v + d • w) + d • (d • v - c • w) ∧
    w = d • (c • v + d • w) - c • (d • v - c • w)
  have hna : ‖c • v + d • w‖ ^ 2 = 1 := by
    rw [norm_add_sq_real]
    simp [norm_smul, hv, hw, inner_smul_left, inner_smul_right, hvw, hcd]
  have hnb : ‖d • v - c • w‖ ^ 2 = 1 := by
    rw [norm_sub_sq_real]
    simpa [norm_smul, mul_pow, hv, hw, inner_smul_left, inner_smul_right, hvw, add_comm] using hcd
  refine ⟨by nlinarith [norm_nonneg (c • v + d • w)],
    by nlinarith [norm_nonneg (d • v - c • w)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hvw, hwv, hv, hw]
    ring
  · simp only [map_add, map_smul, hQv, hQw]
    rw [hs, ← hd, ← hc]
    match_scalars <;> nlinarith [congrArg (fun r : ℝ => c * r) hcd,
      congrArg (fun r : ℝ => d * r) hcd]
  · simp only [map_sub, map_smul, hQv, hQw]
    rw [hs, ← hd, ← hc]
    module
  · simp only [map_add, map_smul, hFv, hFw, smul_zero, add_zero]
    rw [hs, ← hc]
    match_scalars <;> nlinarith [congrArg (fun r : ℝ => c * r) hcd]
  · simp only [map_sub, map_smul, hFv, hFw, smul_zero, sub_zero]
    rw [hs, ← hd]
    match_scalars <;> nlinarith [congrArg (fun r : ℝ => d * r) hcd]
  · match_scalars <;> nlinarith
  · match_scalars <;> nlinarith

end SchauderTranslates
