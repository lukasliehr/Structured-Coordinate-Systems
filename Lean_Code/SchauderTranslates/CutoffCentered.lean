import Lean_Code.SchauderTranslates.CutoffMatrix
import Lean_Code.SchauderTranslates.MarkedScalarGram

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- All retained coordinates except the initial constant character. -/
abbrev CutoffNonconstant (n N : ℕ) :=
  {q : (Unit ⊕ Fin n) × CircleWindow N // q ≠ cutoffConstantIndex n N}

/-- The actual finite Fourier Gram, with its constant first and its true product mass. -/
def cutoffScalarGram (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    FiniteScalarGram (CutoffNonconstant n N) :=
  markedScalarGram (s.cutoffGram p N) (s.cutoffGram_posDef hb hfloor p N)
    (cutoffConstantIndex n N) (1 - p * (1 - s.mass)) (s.activationMass_pos hp0 hp1)
    (s.cutoffGram_diagonal hp0 hp1 N _)

/-- The centered raw inverse is the nonconstant principal block of the original cutoff inverse. -/
theorem cutoffScalarGram_centered_inverse (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    (s.cutoffScalarGram hb hfloor hp0 hp1 N).rawCenteredGram⁻¹ =
      (s.cutoffGram p N)⁻¹.submatrix (fun q : CutoffNonconstant n N => q.1) (fun q => q.1) :=
  markedScalarGram_centered_inverse _ _ _ _ _ _

/-- The individual centered inverse estimate, with no accidental normalization by the new mass. -/
theorem cutoffScalarGram_centered_inverse_diagonal_le (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (q : CutoffNonconstant n N) :
    ((s.cutoffScalarGram hb hfloor hp0 hp1 N).rawCenteredGram⁻¹ q q).re ≤
      1 + p * ((s.rawGram⁻¹ q.1.1 q.1.1).re - 1) := by
  rw [s.cutoffScalarGram_centered_inverse]
  exact s.cutoffGram_inverse_diagonal_le hb hfloor hp0 hp1 N q.1

/-- The normalized centered quadratic gain equals the quantity whose convergence was proved. -/
theorem cutoffScalarGram_gain (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    (s.cutoffScalarGram hb hfloor hp0 hp1 N).gain = s.cutoffGain hb hfloor p N := by
  unfold cutoffScalarGram
  rw [markedScalarGram_gain, s.cutoffGram_constant_inverse hb hfloor]
  rfl

/-- Increasing convergence of the actual centered gains for the concrete finite windows. -/
theorem cutoffScalarGram_gain_tendsto (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Monotone (fun N => (s.cutoffScalarGram hb hfloor hp0 hp1 N).gain) ∧
    Tendsto (fun N => (s.cutoffScalarGram hb hfloor hp0 hp1 N).gain) atTop
      (𝓝 (s.activationLimitGain p)) := by
  simp only [s.cutoffScalarGram_gain]
  exact s.cutoffGain_tendsto hb hfloor hp0 hp1

/-- Every strict gain target below the full value is achieved by a concrete finite centered Gram. -/
theorem exists_cutoffScalarGram_gain_gt (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {z : ℝ} (hz : z < s.activationLimitGain p) :
    ∃ N, z < (s.cutoffScalarGram hb hfloor hp0 hp1 N).gain := by
  simpa only [s.cutoffScalarGram_gain] using s.exists_cutoffGain_gt hb hfloor hp0 hp1 hz

end ScalarData

/-- Rare activation cutoff: centered inverse diagonals, actual gain convergence and finite
attainment, the exact gain formula, and the augmented Euclidean inverse norm bound. -/
theorem rare_activation_cutoff {d n : ℕ} (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ N (q : ScalarData.CutoffNonconstant n N),
      ((s.cutoffScalarGram hb hfloor hp0 hp1 N).rawCenteredGram⁻¹ q q).re ≤
        1 + p * ((s.rawGram⁻¹ q.1.1 q.1.1).re - 1)) ∧
    Monotone (fun N => (s.cutoffScalarGram hb hfloor hp0 hp1 N).gain) ∧
    Tendsto (fun N => (s.cutoffScalarGram hb hfloor hp0 hp1 N).gain) atTop
      (𝓝 (s.activationLimitGain p)) ∧
    (∀ z : ℝ, z < s.activationLimitGain p →
      ∃ N, z < (s.cutoffScalarGram hb hfloor hp0 hp1 N).gain) ∧
    s.activationLimitGain p = p / s.mass *
      (s.gain + (1 - s.mass) ^ 2 - p * (1 - s.mass) * (s.gain + (1 - s.mass))) ∧
    (∀ N, ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := (Unit ⊕ Fin n) × CircleWindow N))
      (s.cutoffGram p N)⁻¹‖ ≤
        ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹‖) := by
  exact ⟨s.cutoffScalarGram_centered_inverse_diagonal_le hb hfloor hp0 hp1,
    (s.cutoffScalarGram_gain_tendsto hb hfloor hp0 hp1).1,
    (s.cutoffScalarGram_gain_tendsto hb hfloor hp0 hp1).2,
    fun _ hz => s.exists_cutoffScalarGram_gain_gt hb hfloor hp0 hp1 hz,
    s.activationLimitGain_formula p, s.cutoffGram_inverse_norm_le hb hfloor p⟩

end SchauderTranslates
