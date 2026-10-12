import Lean_Code.PositiveBiorthogonal.FiniteCoordinates

/-! A finite rank projection with a minimal number of rank-one summands is biorthogonal. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PositiveBiorthogonal

section Algebra
variable {𝕜 X V : Type*} [Field 𝕜] [AddCommGroup X] [Module 𝕜 X]
  [FiniteDimensional 𝕜 X] [AddCommGroup V] [Module 𝕜 V]

theorem finite_split_identity (B D : X →ₗ[𝕜] V) (L G : V →ₗ[𝕜] X)
    (hLB : ∀ x, L (B x) = x) (hproj : ∀ v, D (G v) = B (L v)) :
    ∀ x, G (D x) = x := by
  let A := G.comp B
  let R := L.comp D
  have hDA (x : X) : D (A x) = B x := by
    change D (G (B x)) = B x
    rw [hproj, hLB]
  have hRA (x : X) : R (A x) = x := by
    change L (D (A x)) = x
    rw [hDA, hLB]
  have hsurj : Function.Surjective A := LinearMap.surjective_of_injective
    (Function.LeftInverse.injective hRA)
  have hAR (x : X) : A (R x) = x := by
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hRA]
  intro x
  calc
    G (D x) = G (D (A (R x))) := congrArg (fun y => G (D y)) (hAR x).symm
    _ = G (B (R x)) := congrArg G (hDA (R x))
    _ = x := hAR x

end Algebra

section Families
variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Fintype ι] [DecidableEq ι]

def finiteSynthesis (v : ι → V) : (ι → 𝕜) →ₗ[𝕜] V where
  toFun x := ∑ i, x i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

omit [DecidableEq ι] in
@[simp] theorem finiteSynthesis_apply (v : ι → V) (x : ι → 𝕜) :
    finiteSynthesis v x = ∑ i, x i • v i := rfl

@[simp] theorem finiteSynthesis_single (v : ι → V) (i : ι) :
    finiteSynthesis v (Pi.single i (1 : 𝕜)) = v i := by
  simp [finiteSynthesis, Pi.single_apply]

theorem finiteBiorthogonal_of_equal_projectors (b d : ι → V)
    (l g : ι → V →ₗ[𝕜] 𝕜)
    (hbl : ∀ i j, l j (b i) = if i = j then 1 else 0)
    (hproj : ∀ v, (∑ i, g i v • d i) = ∑ i, l i v • b i) :
    ∀ i j, g j (d i) = if i = j then 1 else 0 := by
  have hsplit := finite_split_identity (finiteSynthesis b) (finiteSynthesis d)
    (LinearMap.pi l) (LinearMap.pi g) (fun x => by
      ext j
      simp [finiteSynthesis, hbl]) (fun v => hproj v)
  intro i j
  have h := congrFun (hsplit (Pi.single i 1)) j
  simpa [Pi.single_apply, eq_comm] using h

end Families
end PositiveBiorthogonal
