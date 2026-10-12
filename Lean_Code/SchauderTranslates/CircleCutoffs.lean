import Lean_Code.SchauderTranslates.CircleRowsTotal

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric finite Fourier window, with the zero mode included at every stage. -/
abbrev CircleWindow (N : ℕ) := {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N}

def circleCutoffSpace (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    Submodule ℂ (Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1))) :=
  Submodule.span ℂ (Set.range (fun q : ι × CircleWindow N =>
    circleRow (EuclideanSpace.single q.1 1) q.2.1))

instance circleCutoffSpace_finite (N : ℕ) : FiniteDimensional ℂ (circleCutoffSpace ι N) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem circleRow_mem_cutoff (i : ι) (k : ℤ) (N : ℕ)
    (hk : -(N : ℤ) ≤ k ∧ k ≤ N) :
    circleRow (EuclideanSpace.single i 1) k ∈ circleCutoffSpace ι N :=
  Submodule.subset_span ⟨(i, ⟨k, Finset.mem_Icc.mpr hk⟩), rfl⟩

theorem circleCutoffSpace_mono : Monotone (circleCutoffSpace ι) := by
  intro a b hab
  apply Submodule.span_le.mpr
  rintro f ⟨⟨i,k⟩, rfl⟩
  apply circleRow_mem_cutoff
  change -(b : ℤ) ≤ k.val ∧ k.val ≤ b
  have hk := Finset.mem_Icc.mp k.property
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  constructor <;> omega

/-- These concrete finite-dimensional symmetric cutoffs exhaust the full coefficient space. -/
theorem circleCutoffSpace_dense : Dense (⋃ N, (circleCutoffSpace ι N : Set
    (Lp (EuclideanSpace ℂ ι) 2 (AddCircle.haarAddCircle (T := 1))))) := by
  have hspan : Submodule.span ℂ (Set.range (fun q : ι × ℤ =>
      circleRow (EuclideanSpace.single q.1 1) q.2)) ≤ ⨆ N, circleCutoffSpace ι N := by
    apply Submodule.span_le.mpr
    rintro f ⟨⟨i,k⟩, rfl⟩
    apply (le_iSup (circleCutoffSpace ι) k.natAbs)
    apply circleRow_mem_cutoff
    have h1 := Int.le_natAbs (a := k)
    have h2 := Int.le_natAbs (a := -k)
    simp only [Int.natAbs_neg] at h2
    constructor <;> omega
  have htop : (⨆ N, circleCutoffSpace ι N).topologicalClosure = ⊤ := by
    apply top_unique
    rw [← circleRows_total (ι := ι)]
    exact Submodule.topologicalClosure_mono hspan
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr htop
  have hdir : Directed (· ≤ ·) (circleCutoffSpace ι) := by
    intro a b
    exact ⟨max a b, circleCutoffSpace_mono (le_max_left _ _),
      circleCutoffSpace_mono (le_max_right _ _)⟩
  rwa [Submodule.coe_iSup_of_directed _ hdir] at hd

end SchauderTranslates
