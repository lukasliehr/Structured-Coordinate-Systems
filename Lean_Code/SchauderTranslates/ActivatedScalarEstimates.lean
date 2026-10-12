import Lean_Code.SchauderTranslates.ActivatedScalarData
import Lean_Code.SchauderTranslates.FiniteScalarReindex
import Lean_Code.SchauderTranslates.CutoffCentered

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ} {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The actual activated torus data and the algebraic marked Gram agree, including their mass. -/
theorem activationData_finiteGram (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).finiteGram =
      (s.finiteActivatedScalarGram hb hfloor hp0 hp1 freq hfreq a₀).reindex e := by
  apply FiniteScalarGram.ext
  · exact s.activationData_mass hp0 hp1 freq hfreq a₀ hzero e
  · change (s.activationData p freq hfreq a₀ hzero e).rawGram = _
    rw [s.activationData_rawGram]
    rfl

/-- Finite activation gain is unchanged when the actual characters are flattened and relabeled. -/
theorem activationData_gain (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).gain =
      (s.finiteActivatedScalarGram hb hfloor hp0 hp1 freq hfreq a₀).gain := by
  change (s.activationData p freq hfreq a₀ hzero e).finiteGram.gain = _
  rw [activationData_finiteGram s hb hfloor hp0 hp1, FiniteScalarGram.reindex_gain]

/-- The centered matrix used for prefix bounds is the actual centered matrix of the torus block. -/
theorem activationData_centeredGram (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).centeredGram =
      (s.finiteActivatedScalarGram hb hfloor hp0 hp1 freq hfreq a₀).centeredGram.submatrix e e := by
  change (s.activationData p freq hfreq a₀ hzero e).finiteGram.centeredGram = _
  rw [activationData_finiteGram s hb hfloor hp0 hp1, FiniteScalarGram.reindex_centeredGram]

/-- The raw centered inverse entries also retain their original normalization. -/
theorem activationData_rawCenteredInverse (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).rawCenteredGram⁻¹ =
      (s.finiteActivatedScalarGram hb hfloor hp0 hp1 freq hfreq a₀).rawCenteredGram⁻¹.submatrix e e := by
  change (s.activationData p freq hfreq a₀ hzero e).finiteGram.rawCenteredGram⁻¹ = _
  rw [activationData_finiteGram s hb hfloor hp0 hp1, FiniteScalarGram.reindex_rawCenteredGram,
    Matrix.inv_submatrix_equiv]

/-- The entire augmented inverse has precisely the finite activation operator norm. -/
theorem activationData_rawInverse_norm (s : ScalarData d n) (p : ℝ)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (s.activationData p freq hfreq a₀ hzero e).rawGram⁻¹‖ =
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (s.finiteActivatedGram p freq)⁻¹‖ := by
  rw [s.activationData_rawGram, Matrix.inv_submatrix_equiv, matrix_reindex_norm]

/-- The concrete finite symmetric window as data suitable for scalar induction. -/
def cutoffData (s : ScalarData d n) (p : ℝ) (N : ℕ) {m : ℕ}
    (e : Fin m ≃ CutoffNonconstant n N) : ScalarData (d + 1) m :=
  s.activationData p (fun k : CircleWindow N => k.1) Subtype.val_injective
    (cutoffConstantIndex n N).2 rfl e

theorem finiteActivatedGram_window (s : ScalarData d n) (p : ℝ) (N : ℕ) :
    s.finiteActivatedGram p (fun k : CircleWindow N => k.1) = s.cutoffGram p N := by
  ext q r
  exact (s.cutoffGram_entry p N q r).symm

theorem cutoffData_finiteGram (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) {m : ℕ} (e : Fin m ≃ CutoffNonconstant n N) :
    (s.cutoffData p N e).finiteGram = (s.cutoffScalarGram hb hfloor hp0 hp1 N).reindex e := by
  rw [cutoffData, s.activationData_finiteGram hb hfloor hp0 hp1]
  congr 1
  apply FiniteScalarGram.ext
  · rfl
  · change (s.finiteActivatedGram p (fun k : CircleWindow N => k.1)).submatrix _ _ = _
    rw [s.finiteActivatedGram_window]
    rfl

/-- The gain convergence theorem now applies to the actual scalar torus cutoff. -/
theorem cutoffData_gain (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) {m : ℕ} (e : Fin m ≃ CutoffNonconstant n N) :
    (s.cutoffData p N e).gain = s.cutoffGain hb hfloor p N := by
  change (s.cutoffData p N e).finiteGram.gain = _
  rw [s.cutoffData_finiteGram hb hfloor hp0 hp1, FiniteScalarGram.reindex_gain,
    s.cutoffScalarGram_gain]

/-- This is the cutoff inverse norm input required by the spectral-floor step. -/
theorem cutoffData_rawInverse_norm_le (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ)
    {m : ℕ} (e : Fin m ≃ CutoffNonconstant n N) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (s.cutoffData p N e).rawGram⁻¹‖ ≤
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ := by
  rw [cutoffData, s.activationData_rawInverse_norm, s.finiteActivatedGram_window]
  exact s.cutoffGram_inverse_norm_le hb hfloor p N

/-- Exact raw inverse diagonal control for all retained nonconstant characters. -/
theorem cutoffData_rawCenteredInverse_diagonal_le (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) {m : ℕ} (e : Fin m ≃ CutoffNonconstant n N) (i : Fin m) :
    ((s.cutoffData p N e).rawCenteredGram⁻¹ i i).re ≤
      1 + p * ((s.rawGram⁻¹ (e i).1.1 (e i).1.1).re - 1) := by
  change ((s.cutoffData p N e).finiteGram.rawCenteredGram⁻¹ i i).re ≤ _
  rw [s.cutoffData_finiteGram hb hfloor hp0 hp1, FiniteScalarGram.reindex_rawCenteredGram,
    Matrix.inv_submatrix_equiv]
  exact s.cutoffScalarGram_centered_inverse_diagonal_le hb hfloor hp0 hp1 N (e i)

end ScalarData
end SchauderTranslates
