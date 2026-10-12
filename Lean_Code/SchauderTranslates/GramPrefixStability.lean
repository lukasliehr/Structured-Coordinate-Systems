import Lean_Code.SchauderTranslates.OrderedGramPrefixes

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gramDifference_posDef_of_strict_bound {B : Matrix ι ι ℂ} (hB : B.PosDef)
    (D : Matrix ι ι ℂ) {q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (hp : ‖gramConjugate B D‖ ^ 2 ≤ q) : (gramDifference r D B).PosDef := by
  have hs : (gramDifference q D B).PosSemidef := by
    have hi := gram_prefix_iff hB D (Real.sqrt q)
    rw [Real.sq_sqrt hq] at hi
    exact hi.mp hp
  have hd : ((r - q) • B).PosDef := hB.smul (sub_pos.mpr hqr)
  have he : gramDifference r D B = (r - q) • B + gramDifference q D B := by
    unfold gramDifference
    rw [sub_smul]
    abel
  rw [he]
  exact hd.add_posSemidef hs

/-- A strict slack in a finite Gram prefix bound survives a convergent positive definite sequence. -/
theorem eventually_gram_prefix_bound {A : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (hA : ∀ N, (A N).PosDef) (hB : B.PosDef) (hlim : Tendsto A atTop (𝓝 B))
    (D : Matrix ι ι ℂ) {q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (hp : ‖gramConjugate B D‖ ^ 2 ≤ q) :
    ∀ᶠ N in atTop, ‖gramConjugate (A N) D‖ ^ 2 ≤ r := by
  have hr : 0 ≤ r := hq.trans hqr.le
  have hpos := gramDifference_posDef_of_strict_bound hB D hq hqr hp
  have hc : Continuous (gramDifference r D) := by unfold gramDifference; fun_prop
  have he := (hc.continuousAt.tendsto.comp hlim).eventually (gram_posDef_eventually hpos)
  filter_upwards [he] with N hN
  have hh : (gramDifference r D (A N)).IsHermitian :=
    ((hA N).isHermitian.smul (IsSelfAdjoint.all r)).sub
      (Matrix.isHermitian_conjTranspose_mul_mul D (hA N).isHermitian)
  have hs := (hN hh).posSemidef
  have hi := gram_prefix_iff (hA N) D (Real.sqrt r)
  rw [Real.sq_sqrt hr] at hi
  exact hi.mpr hs

/-- It suffices to check the finitely many prefixes, including the empty and complete ones. -/
theorem finitePrefixMatrix_min (n k : ℕ) : finitePrefixMatrix n k = finitePrefixMatrix n (min k n) := by
  ext i j
  have he : (i.val < k) = (i.val < min k n) := propext (by simp [i.isLt])
  simp only [finitePrefixMatrix, Matrix.diagonal_apply, he]

theorem eventually_all_finite_prefix_bounds {n : ℕ} {A : ℕ → Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ N, (A N).PosDef) (hB : B.PosDef)
    (hlim : Tendsto A atTop (𝓝 B)) {q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (hp : ∀ k, ‖gramConjugate B (finitePrefixMatrix n k)‖ ^ 2 ≤ q) :
    ∀ᶠ N in atTop, ∀ k, ‖gramConjugate (A N) (finitePrefixMatrix n k)‖ ^ 2 ≤ r := by
  have he (k : Fin (n + 1)) := eventually_gram_prefix_bound hA hB hlim
    (finitePrefixMatrix n k.val) hq hqr (hp k.val)
  filter_upwards [Filter.eventually_all.mpr he] with N hN k
  rw [finitePrefixMatrix_min]
  exact hN ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

end SchauderTranslates
