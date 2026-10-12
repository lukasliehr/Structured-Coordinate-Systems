import Lean_Code.SchauderTranslates.BoundedSpan
import Lean_Code.SchauderTranslates.SeedCarrierCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open MeasureTheory Matrix
open scoped InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable (ρ : Measure S) [IsProbabilityMeasure ρ]

/-- Computation coordinates for an arbitrary independent bounded carrier. The
prescribed unit vector is retained pointwise, so its seed kernel is unchanged. -/
theorem exists_orthonormal_carrier (φ : ι → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
    (e : BoundedMeasurableComplex S) (he : e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ))
    (he1 : ‖e.toL2 ρ‖ = 1) (i0 : ι) :
    ∃ c : SeedCarrier (ι := ι) ρ, c.distinguished = i0 ∧ c.e = e ∧
      atomSpan (fun i => (c.representative i).toL2 ρ) = atomSpan (fun i => (φ i).toL2 ρ) := by
  classical
  let V := atomSpan (fun i => (φ i).toL2 ρ)
  let ev : V := ⟨e.toL2 ρ, he⟩
  have hcard : Module.finrank ℂ V = Fintype.card ι := finrank_span_eq_card hφ
  have hone : Orthonormal ℂ (({i0} : Set ι).domRestrict (fun _ : ι => ev)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact he1
  obtain ⟨b, hb⟩ := hone.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb0 : (b i0 : Lp ℂ 2 ρ) = e.toL2 ρ := congrArg Subtype.val (hb i0 (Set.mem_singleton i0))
  have hr (i : ι) : ∃ g : BoundedMeasurableComplex S, g.toL2 ρ = (b i : Lp ℂ 2 ρ) :=
    BoundedMeasurableComplex.exists_representative_of_mem_span φ ρ (b i).property
  choose r hr using hr
  let ψ : ι → BoundedMeasurableComplex S := fun i => if i = i0 then e else r i
  have hψ (i : ι) : (ψ i).toL2 ρ = (b i : Lp ℂ 2 ρ) := by
    by_cases hi : i = i0
    · subst i; simpa only [ψ, if_pos rfl] using hb0.symm
    · simpa only [ψ, if_neg hi] using hr i
  have hgram : Matrix.gram ℂ (fun i => (ψ i).toL2 ρ) = 1 := by
    ext i j
    rw [Matrix.gram_apply, hψ, hψ]
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  let c : SeedCarrier (ι := ι) ρ := {
    row := fun i => ψ i
    measurable := fun i => (ψ i).measurable
    bounded := fun i => ⟨(ψ i).bound, (ψ i).norm_le⟩
    reference := by
      ext i j
      have hh := congrFun (congrFun hgram i) j
      rw [Matrix.gram_apply, BoundedMeasurableComplex.inner_toL2] at hh
      simpa only [integralGram, Complex.ofReal_one, one_mul] using hh
    distinguished := i0 }
  have hrep (i : ι) : (c.representative i).toL2 ρ = (ψ i).toL2 ρ := by
    apply BoundedMeasurableComplex.toL2_congr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  refine ⟨c, rfl, ?_, ?_⟩
  · funext x
    change (if i0 = i0 then e else r i0) x = e x
    simp
  · have hspan : atomSpan (fun i => (b i : Lp ℂ 2 ρ)) = V := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact (b i).property
      · intro x hx
        let xv : V := ⟨x, hx⟩
        have hh := b.sum_repr xv
        have hv : (∑ i, b.repr xv i • (b i : Lp ℂ 2 ρ)) = x := by
          simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using congrArg Subtype.val hh
        exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨fun i => b.repr xv i, hv⟩
    simpa only [hrep, hψ] using hspan

end SchauderTranslates
