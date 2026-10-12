import Lean_Code.Main.TranslatesL2
import Lean_Code.Basis.RealScalars
import Lean_Code.PositiveTranslates.Analytic.Main
import Lean_Code.PositiveTranslates.Machine.Main

/-!
# Translates in `Lᵖ(ℝ)`, `2 ≤ p < ∞`: assembly

* `translate_basis_nonneg_main`: for `p > 2` and an unbounded set `S`, a non-negative
  generator extending to an entire function whose translates by distinct parameters in `S`
  form a Schauder basis of `Lᵖ(ℝ)` over both scalar fields. It combines the analytic half
  (`Lean_Code/PositiveTranslates/Analytic`) with the reference construction
  (`Lean_Code/PositiveTranslates/Machine`), which are linked by the interface `StageMachine`.
* `translate_basis_entire_main`: for `2 ≤ p < ∞`, a nonzero real-valued generator
  extending to an entire function, over both scalar fields (`p = 2` from the weighted
  Fourier construction, `p > 2` from the previous item with `S = ℝ`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace StructuredBases

open PositiveTranslates

/-- The hypothesis that the reference construction exists for every admissible parameter
set. -/
def MachinesExist (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∀ Γ : Set ℝ, (0 : ℝ) ∈ Γ → (∀ x : ℝ, ∃ γ ∈ Γ, x < γ) → Nonempty (StageMachine p Γ)

/-- `p > 2`: non-negative entire generator, parameters in a prescribed unbounded set,
both scalar fields. -/
theorem translate_basis_nonneg_of_machines (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p)
    (hp' : p ≠ ∞) (hM : MachinesExist p) (S : Set ℝ) (hS : ¬ Bornology.IsBounded S) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ (∀ x, 0 ≤ f x) ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ S) ∧
      (∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
      (∃ b : SchauderBasis ℝ (Lp ℝ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) := by
  obtain ⟨f, lam, hf, hf0, hfne, hF, hinj, hS', b, hb⟩ :=
    exists_nonneg_entire_translate_basis p hp hp' hM S hS
  obtain ⟨b', hb', -⟩ := exists_real_translate_basis f lam b hb
  exact ⟨f, lam, hf, hf0, hfne, hF, hinj, hS', ⟨b, hb⟩, ⟨b', hb'⟩⟩

/-- `2 ≤ p < ∞`: a nonzero real-valued generator extending to an entire function whose
translates form a Schauder basis of `Lᵖ(ℝ)` over both scalar fields. -/
theorem translate_basis_entire_of_machines (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (hp' : p ≠ ∞) (hM : 2 < p → MachinesExist p) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      (∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
      (∃ b : SchauderBasis ℝ (Lp ℝ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) := by
  rcases eq_or_lt_of_le hp with h2 | h2
  · subst h2
    obtain ⟨f, lam, hf, hf0, hF, -, ⟨b, hb, -⟩, ⟨b', hb', -⟩⟩ :=
      translate_basis_L2 (ε := 1) one_pos
    exact ⟨f, lam, hf, hf0, hF, ⟨b, hb⟩, ⟨b', hb'⟩⟩
  · have hS : ¬ Bornology.IsBounded (Set.univ : Set ℝ) := by
      intro hb
      obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hb
      have h := hC (Set.mem_univ (|C| + 1))
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      have h1 : |C| + 1 ≤ C := (le_abs_self _).trans h
      linarith [le_abs_self C]
    obtain ⟨f, lam, hf, -, hf0, hF, -, -, hb, hb'⟩ :=
      translate_basis_nonneg_of_machines p h2 hp' (hM h2) Set.univ hS
    exact ⟨f, lam, hf, hf0, hF, hb, hb'⟩

/-- The reference construction exists for every `2 < p < ∞`. -/
theorem machinesExist (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞) :
    MachinesExist p :=
  fun Γ h0 hΓ => nonempty_stageMachine p hp hp' Γ h0 hΓ

/-- **Theorem 1.4 (iii).** For `2 < p < ∞` and an unbounded set `S ⊆ ℝ` there are distinct
parameters `λₙ ∈ S` and a non-negative function `f ∈ Lᵖ(ℝ)` extending to an entire function
whose translates `f(· - λₙ)` form a Schauder basis of `Lᵖ(ℝ)`, over `ℂ` and over `ℝ`. -/
theorem translate_basis_nonneg_main (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞)
    (S : Set ℝ) (hS : ¬ Bornology.IsBounded S) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ (∀ x, 0 ≤ f x) ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ S) ∧
      (∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
      (∃ b : SchauderBasis ℝ (Lp ℝ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) :=
  translate_basis_nonneg_of_machines p hp hp' (machinesExist p hp hp') S hS

/-- **Theorems 1.3 and 1.4 (i).** For `2 ≤ p < ∞` there are a nonzero real-valued function
`f ∈ Lᵖ(ℝ)` extending to an entire function and real numbers `λₙ` whose translates
`f(· - λₙ)` form a Schauder basis of `Lᵖ(ℝ)`, over `ℂ` and over `ℝ`. -/
theorem translate_basis_entire_main (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      (∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
      (∃ b : SchauderBasis ℝ (Lp ℝ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) :=
  translate_basis_entire_of_machines p hp hp' (fun h => machinesExist p h hp')

end StructuredBases
