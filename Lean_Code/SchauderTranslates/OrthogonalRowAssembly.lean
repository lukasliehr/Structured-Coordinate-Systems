import Lean_Code.SchauderTranslates.RowCutRemainder

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ η K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

@[simp] theorem familyRowCut_zero (e : κ → ι) (j : ι) (F : K →L[ℝ] K) :
    familyRowCut e j F (0 : ι → K) = 0 := by
  ext i
  simp [familyRowCut, familyCoordinateSelection, Pi.single_apply]

theorem familyRowCut_add (e : κ → ι) (j : ι) (F : K →L[ℝ] K) (f g : ι → K) :
    familyRowCut e j F (f + g) = familyRowCut e j F f + familyRowCut e j F g := by
  ext i
  simp only [familyRowCut, familyCoordinateSelection, Pi.add_apply, map_add, Pi.single_apply]
  have hi (k) : (if i = e k then f (e k) + g (e k) else 0) =
      (if i = e k then f (e k) else 0) + (if i = e k then g (e k) else 0) := by
    split_ifs <;> simp
  simp only [hi, Finset.sum_add_distrib]
  split_ifs <;> abel

theorem familyRowCut_sum [DecidableEq η] (e : κ → ι) (j : ι) (F : K →L[ℝ] K)
    (s : Finset η) (f : η → ι → K) :
    familyRowCut e j F (∑ a ∈ s, f a) = ∑ a ∈ s, familyRowCut e j F (f a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, familyRowCut_add, ih]

/-- A row cut preserves any spatial subspace preserved by its within-row projection. -/
theorem familyRowCut_mem (e : κ → ι) (j : ι) (F : K →L[ℝ] K) (S : Submodule ℝ K)
    (hF : ∀ x ∈ S, F x ∈ S) (f : ι → K) (hf : ∀ i, f i ∈ S) (i : ι) :
    familyRowCut e j F f i ∈ S := by
  apply S.add_mem
  · apply S.sum_mem
    intro k _
    change (if i = e k then f (e k) else 0) ∈ S
    split_ifs
    · exact hf _
    · exact S.zero_mem
  · change (Pi.single j (F (f j)) : ι → K) i ∈ S
    by_cases hi : i = j
    · subst i
      simpa using hF _ (hf j)
    · simpa [Pi.single_apply, hi] using S.zero_mem

/-- Activation energies decompose over finite mutually orthogonal reducing spatial subspaces. -/
theorem activationEnergy_sum_subspaces [Fintype η] [DecidableEq η]
    (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K) (S : η → Submodule ℝ K)
    (hS : ∀ a b, a ≠ b → ∀ x ∈ S a, ∀ y ∈ S b, inner ℝ x y = 0)
    (hQ : ∀ a, ∀ x ∈ S a, Q x ∈ S a) (f : η → ι → K)
    (hf : ∀ a i, f a i ∈ S a) :
    activationEnergy B Q (∑ a, f a) = ∑ a, activationEnergy B Q (f a) := by
  have hq : (fun i => Q ((∑ a, f a) i)) = ∑ a, (fun i => Q (f a i)) := by
    ext i
    simp
  have hi : (fun i => (∑ a, f a) i - Q ((∑ a, f a) i)) =
      ∑ a, (fun i => f a i - Q (f a i)) := by
    ext i
    simp [Finset.sum_sub_distrib]
  have hqo : ∀ a b, a ≠ b → ∀ i j, inner ℝ (Q (f a i)) (Q (f b j)) = 0 :=
    fun a b hab i j => hS a b hab _ (hQ a _ (hf a i)) _ (hQ b _ (hf b j))
  have hio : ∀ a b, a ≠ b → ∀ i j,
      inner ℝ (f a i - Q (f a i)) (f b j - Q (f b j)) = 0 :=
    fun a b hab i j => hS a b hab _ ((S a).sub_mem (hf a i) (hQ a _ (hf a i)))
      _ ((S b).sub_mem (hf b j) (hQ b _ (hf b j)))
  rw [activationEnergy, hq, hi, matrixEnergy_sum_orthogonal B _ _ hqo,
    matrixEnergy_sum_orthogonal 1 _ _ hio]
  simp only [activationEnergy, Finset.sum_add_distrib]

/-- Combining the bounds on orthogonal reducing pieces introduces no extra constant. -/
theorem familyRowCut_bound_of_subspaces [Fintype η] [DecidableEq η]
    (B : Matrix ι ι ℝ) (e : κ → ι) (j : ι) (F Q : K →L[ℝ] K)
    (S : η → Submodule ℝ K)
    (hS : ∀ a b, a ≠ b → ∀ x ∈ S a, ∀ y ∈ S b, inner ℝ x y = 0)
    (hF : ∀ a, ∀ x ∈ S a, F x ∈ S a) (hQ : ∀ a, ∀ x ∈ S a, Q x ∈ S a)
    (f : η → ι → K) (hf : ∀ a i, f a i ∈ S a) (C : ℝ)
    (hbound : ∀ a, activationEnergy B Q (familyRowCut e j F (f a)) ≤ C * activationEnergy B Q (f a)) :
    activationEnergy B Q (familyRowCut e j F (∑ a, f a)) ≤ C * activationEnergy B Q (∑ a, f a) := by
  rw [familyRowCut_sum, activationEnergy_sum_subspaces B Q S hS hQ _
    (fun a i => familyRowCut_mem e j F (S a) (hF a) (f a) (hf a) i),
    activationEnergy_sum_subspaces B Q S hS hQ f hf, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => hbound a)

end SchauderTranslates
