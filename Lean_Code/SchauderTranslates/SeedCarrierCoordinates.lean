import Lean_Code.SchauderTranslates.SelectiveSource
import Lean_Code.SchauderTranslates.SelectiveBlocks
import Lean_Code.SchauderTranslates.CarrierSourceMatrices
import Lean_Code.SchauderTranslates.NormalizedCapture

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SeedCarrier
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ] (c : SeedCarrier (ι := ι) ρ)

/-- Bounded representatives of the orthonormal computation coordinates. -/
def representative (i : ι) : BoundedMeasurableComplex S where
  toFun := c.row i
  measurable := c.measurable i
  bound := max (Classical.choose (c.bounded i)) 0
  bound_nonneg := le_max_right _ _
  norm_le := fun x => (Classical.choose_spec (c.bounded i) x).trans (le_max_left _ _)

theorem representatives_gram : Matrix.gram ℂ (fun i => (c.representative i).toL2 ρ) = 1 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.gram_apply, BoundedMeasurableComplex.inner_toL2]
  exact c.reference_entry i j

theorem representatives_independent : LinearIndependent ℂ (fun i => (c.representative i).toL2 ρ) := by
  apply Matrix.posDef_gram_iff_linearIndependent.mp
  rw [c.representatives_gram]
  exact Matrix.PosDef.one

theorem packetRows_representative (L : ℕ) (i : ι ⊕ Fin L) (p : S × UnitAddTorus (Fin L)) :
    SelectiveKernelData.packetRows c.representative i p = c.rows L i p := by
  cases i <;> rfl

theorem packetRows_gram (L : ℕ) :
    Matrix.gram ℂ (fun i => (SelectiveKernelData.packetRows c.representative i).toL2
      (ρ.prod (torusMeasure L))) = 1 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.gram_apply, BoundedMeasurableComplex.inner_toL2]
  simp_rw [c.packetRows_representative]
  have h := congrFun (congrFun (c.rows_reference L) i) j
  simpa only [integralGram, Complex.ofReal_one, one_mul] using h

def selectiveData {d n : ℕ} (s : ScalarData d n) (L : ℕ) (m κ : ℝ)
    (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L) (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) :
    SelectiveKernelData S L d n where
  scalar := s
  e := c.representative c.distinguished
  m := m
  κ := κ
  mass_pos := hm
  mass_le := hm1
  coupling_bound := hκ

variable {d n : ℕ} (s : ScalarData d n) (L : ℕ) (m κ : ℝ)
  (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L) (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4)

theorem selective_seedGram :
    (c.selectiveData s L m κ hm hm1 hκ).rawSeedGram ρ
      (SelectiveKernelData.packetRows c.representative) = c.gram L m κ := by
  apply Matrix.ext
  intro i j
  change (∫ p, (seedKernel L m ((κ : ℂ) * c.e p.1) p.2 : ℂ) *
      star (SelectiveKernelData.packetRows c.representative i p) *
      SelectiveKernelData.packetRows c.representative j p ∂ρ.prod (torusMeasure L)) = _
  simp_rw [c.packetRows_representative]
  rfl

theorem selective_tensorGram :
    let a := c.selectiveData s L m κ hm hm1 hκ
    Matrix.gram ℂ (a.kernel.atoms ρ (a.packet c.representative)) =
      (a.mass : ℂ)⁻¹ • tensorGram s.nonconstantGram ((m : ℂ) • seedBlock c.distinguished L κ) := by
  let a := c.selectiveData s L m κ hm hm1 hκ
  change a.rowColumnGram ρ (SelectiveKernelData.packetRows c.representative) = _
  rw [a.rowColumnGram_orthonormal _ _ (c.packetRows_gram L), c.selective_seedGram,
    c.gram_eq_seedBlock L hm.le hκ]
  rfl

theorem selective_source :
    let a := c.selectiveData s L m κ hm hm1 hκ
    ((hilbertSynthesis (a.kernel.atoms ρ (a.packet c.representative)))†).comp
        (a.kernel.slowLift ρ).toContinuousLinearMap =
      (a.mass : ℂ)⁻¹ • (euclideanMatrixOperator (carrierSource s.moment c.distinguished κ m L)).comp
        ((hilbertSynthesis (fun i => (c.representative i).toL2 ρ))†) := by
  let a := c.selectiveData s L m κ hm hm1 hκ
  ext h p
  have hs := congrArg (fun z : EuclideanSpace ℂ (Fin n × (ι ⊕ Fin L)) => z p)
    (a.packet_source_adjoint ρ c.representative h)
  change (((hilbertSynthesis (𝕜 := ℂ) (a.kernel.atoms ρ (a.packet c.representative)))†)
    (a.kernel.slowLift ρ h)) p = _
  rw [hs]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, euclideanMatrixOperator_apply, hilbertSynthesis_adjoint_apply,
    WithLp.ofLp_toLp, carrierSource_mulVec, PiLp.smul_apply, smul_eq_mul]
  change s.moment p.1 / (a.mass : ℂ) *
    Sum.elim (fun i => (1 - (m : ℂ)) * inner ℂ ((c.representative i).toL2 ρ) h)
      (fun _ => -(m : ℂ) * κ * inner ℂ ((c.representative c.distinguished).toL2 ρ) h) p.2 =
    (a.mass : ℂ)⁻¹ * (s.moment p.1 *
      Sum.elim (fun i => (1 - (m : ℂ)) * inner ℂ ((c.representative i).toL2 ρ) h)
        (fun _ => -(m : ℂ) * κ * inner ℂ ((c.representative c.distinguished).toL2 ρ) h) p.2)
  ring

end SchauderTranslates.SeedCarrier
