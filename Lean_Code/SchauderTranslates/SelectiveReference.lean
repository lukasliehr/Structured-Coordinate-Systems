import Lean_Code.SchauderTranslates.BoundedTensor

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open BoundedMeasurableComplex

theorem torusCharacter_inner {d : ℕ} (k l : Fin d → ℤ) :
    inner ℂ ((torusCharacterRepresentative k).toL2 (torusMeasure d))
      ((torusCharacterRepresentative l).toL2 (torusMeasure d)) = if k = l then 1 else 0 := by
  rw [inner_toL2]
  simp only [torusCharacterRepresentative, Complex.star_def, ← UnitAddTorus.mFourier_neg,
    ← UnitAddTorus.mFourier_add, integral_torus_character]
  congr 1
  apply propext
  exact neg_add_eq_zero

theorem seedPhase_inner {L : ℕ} (i j : Fin L) :
    inner ℂ ((seedPhaseRepresentative i).toL2 (torusMeasure L))
      ((seedPhaseRepresentative j).toL2 (torusMeasure L)) = if i = j then 1 else 0 := by
  have hi : (seedPhaseRepresentative i).toL2 (torusMeasure L) =
      (torusCharacterRepresentative (Pi.single i 1)).toL2 (torusMeasure L) := by
    apply toL2_congr
    exact Filter.Eventually.of_forall (fun z => (UnitAddTorus.mFourier_single z i).symm)
  have hj : (seedPhaseRepresentative j).toL2 (torusMeasure L) =
      (torusCharacterRepresentative (Pi.single j 1)).toL2 (torusMeasure L) := by
    apply toL2_congr
    exact Filter.Eventually.of_forall (fun z => (UnitAddTorus.mFourier_single z j).symm)
  rw [hi, hj, torusCharacter_inner]
  congr 1
  apply propext
  constructor
  · intro h
    by_contra hij
    have hh := congrFun h i
    simp [Pi.single_eq_same, Pi.single_eq_of_ne hij] at hh
  · intro h; subst j; rfl

namespace BoundedMeasurableComplex
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem inner_pullbackSnd (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (f g : BoundedMeasurableComplex B) :
    inner ℂ ((f.comp Prod.snd measurable_snd).toL2 (μ.prod ν))
      ((g.comp Prod.snd measurable_snd).toL2 (μ.prod ν)) = inner ℂ (f.toL2 ν) (g.toL2 ν) := by
  have h := inner_tensor μ ν (const A 1) (const A 1) f g
  have hf := toL2_congr ((const A 1).tensor f) (f.comp Prod.snd measurable_snd) (μ.prod ν)
    (Filter.Eventually.of_forall (fun p => by change 1 * f p.2 = f p.2; ring))
  have hg := toL2_congr ((const A 1).tensor g) (g.comp Prod.snd measurable_snd) (μ.prod ν)
    (Filter.Eventually.of_forall (fun p => by change 1 * g p.2 = g p.2; ring))
  have hc : inner ℂ ((const A 1).toL2 μ) ((const A 1).toL2 μ) = 1 := by
    rw [inner_toL2]
    simp [const]
  rw [hf, hg, hc, one_mul] at h
  exact h

end BoundedMeasurableComplex

namespace SelectiveKernelData
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsProbabilityMeasure ρ]

/-- Retain the given carrier rows, without orthonormalizing or changing their order. -/
def packetRows (φ : ι → BoundedMeasurableComplex S) :
    ι ⊕ Fin L → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)) :=
  Sum.elim (fun i => (φ i).pullbackFst (UnitAddTorus (Fin L)))
    (fun j => (seedPhaseRepresentative j).comp Prod.snd measurable_snd)

theorem packetRows_independent (φ : ι → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ)) :
    LinearIndependent ℂ (fun i => (packetRows φ i).toL2 (ρ.prod (torusMeasure L))) := by
  let u := fun i => ((φ i).pullbackFst (UnitAddTorus (Fin L))).toL2 (ρ.prod (torusMeasure L))
  let v := fun j : Fin L => ((seedPhaseRepresentative j).comp Prod.snd measurable_snd).toL2 (ρ.prod (torusMeasure L))
  have hu : LinearIndependent ℂ u := by
    apply Matrix.posDef_gram_iff_linearIndependent.mp
    have he : Matrix.gram ℂ u = Matrix.gram ℂ (fun i => (φ i).toL2 ρ) := by
      ext i j
      exact inner_pullbackFst ρ (torusMeasure L) (φ i) (φ j)
    rw [he]
    exact Matrix.posDef_gram_iff_linearIndependent.mpr hφ
  have hv : LinearIndependent ℂ v := by
    apply Orthonormal.linearIndependent
    rw [orthonormal_iff_ite]
    intro i j
    exact (inner_pullbackSnd ρ (torusMeasure L) _ _).trans (seedPhase_inner i j)
  have huv : ∀ i j, inner ℂ (u i) (v j) = 0 := by
    intro i j
    rw [inner_toL2]
    change (∫ p, star (φ i p.1) * seedPhaseRepresentative j p.2 ∂ρ.prod (torusMeasure L)) = 0
    have h := (φ i).conjugate.integral_tensor (seedPhaseRepresentative j) ρ (torusMeasure L)
    dsimp only [conjugate] at h
    rw [h, seedPhase_integral, mul_zero]
  have hd : Disjoint (Submodule.span ℂ (Set.range u)) (Submodule.span ℂ (Set.range v)) := by
    apply Submodule.IsOrtho.disjoint
    rw [Submodule.isOrtho_span]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact huv i j
  have h := hu.sum_type hv hd
  have he : (fun i => (packetRows φ i).toL2 (ρ.prod (torusMeasure L))) = Sum.elim u v := by
    funext i
    cases i <;> rfl
  rw [he]
  exact h

theorem auxiliary_independent :
    LinearIndependent ℂ (fun k => (torusCharacterRepresentative (a.scalar.frequencies k)).toL2 (torusMeasure d)) := by
  apply Orthonormal.linearIndependent
  rw [orthonormal_iff_ite]
  intro i j
  rw [torusCharacter_inner]
  simp only [a.scalar.injective.eq_iff]

/-- Auxiliary column first, original carrier/seed row second. -/
def packet (φ : ι → BoundedMeasurableComplex S) : Fin n × (ι ⊕ Fin L) →
    BoundedMeasurableComplex (S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) :=
  fun i => rowColumn (packetRows φ i.2) (torusCharacterRepresentative (a.scalar.frequencies i.1))

theorem packet_independent (φ : ι → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ)) :
    LinearIndependent ℂ (fun i => (a.packet φ i).toL2 (ρ.prod ((torusMeasure L).prod (torusMeasure d)))) := by
  unfold packet
  exact rowColumn_independent ρ (packetRows φ)
    (fun k => torusCharacterRepresentative (a.scalar.frequencies k))
    (packetRows_independent ρ φ hφ) a.auxiliary_independent

theorem packet_reference_mean_zero (φ : ι → BoundedMeasurableComplex S)
    (i : Fin n × (ι ⊕ Fin L)) (x : S) :
    (∫ y, a.packet φ i (x, y) ∂(torusMeasure L).prod (torusMeasure d)) = 0 := by
  have h := ((packetRows φ i.2).comp (fun z => (x, z)) measurable_prodMk_left).integral_tensor
    (torusCharacterRepresentative (a.scalar.frequencies i.1)) (torusMeasure L) (torusMeasure d)
  dsimp only [BoundedMeasurableComplex.comp, torusCharacterRepresentative] at h
  change (∫ y, packetRows φ i.2 (x, y.1) * UnitAddTorus.mFourier (a.scalar.frequencies i.1) y.2
    ∂(torusMeasure L).prod (torusMeasure d)) = 0
  rw [h, a.scalar.character_integral_zero, mul_zero]

end SelectiveKernelData
end SchauderTranslates
