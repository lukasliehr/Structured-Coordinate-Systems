import Lean_Code.SchauderTranslates.Lp.IndexMaps
import Lean_Code.SchauderTranslates.Lp.BranchProjections

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- The initial coordinate and every private coordinate of every branch. -/
abbrev ForestPrivateIndex (N : ℕ → ℕ → ℕ) := Option (Σ j, Σ n, Fin (N j n))
abbrev ForestPrivateSpace (p : ℝ≥0∞) (N : ℕ → ℕ → ℕ) :=
  lp (fun _ : ForestPrivateIndex N => ℂ) p

def forestInitial (p : ℝ≥0∞) (N : ℕ → ℕ → ℕ) : ForestPrivateSpace p N :=
  lp.single p none 1

def forestUnit (p : ℝ≥0∞) (N : ℕ → ℕ → ℕ) (j n : ℕ) (i : Fin (N j n)) :
    ForestPrivateSpace p N := lp.single p (some ⟨j, ⟨n, i⟩⟩) 1

def branchPrivateEmbedding (N : ℕ → ℕ) : (Σ n, Fin (N n)) ↪ BranchIndex N where
  toFun := some
  inj' := fun _ _ h => Option.some.inj h

def forestPrivateEmbedding (N : ℕ → ℕ → ℕ) (j : ℕ) :
    (Σ n, Fin (N j n)) ↪ ForestPrivateIndex N where
  toFun k := some ⟨j, k⟩
  inj' := by
    intro a b h
    simpa only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (N : ℕ → ℕ → ℕ)

def forestExtract (j : ℕ) : ForestPrivateSpace p N →L[ℂ] BranchSpace p (N j) :=
  (lpExtend hp (branchPrivateEmbedding (N j))).toContinuousLinearMap.comp
    (lpRestrict hp (forestPrivateEmbedding N j))

def forestInsert (j : ℕ) : BranchSpace p (N j) →L[ℂ] ForestPrivateSpace p N :=
  (lpExtend hp (forestPrivateEmbedding N j)).toContinuousLinearMap.comp
    (lpRestrict hp (branchPrivateEmbedding (N j)))

@[simp] theorem forestExtract_none (j : ℕ) (y : ForestPrivateSpace p N) :
    forestExtract hp N j y none = 0 := by
  change lpExtend hp (branchPrivateEmbedding (N j)) _ none = 0
  exact lpExtend_apply_outside hp _ _ _ (by rintro ⟨a, h⟩; cases h)

@[simp] theorem forestExtract_private (j n : ℕ) (i : Fin (N j n))
    (y : ForestPrivateSpace p N) :
    forestExtract hp N j y (some ⟨n, i⟩) = y (some ⟨j, ⟨n, i⟩⟩) := by
  change lpExtend hp (branchPrivateEmbedding (N j)) _
    (branchPrivateEmbedding (N j) ⟨n, i⟩) = _
  simp [forestPrivateEmbedding]

@[simp] theorem forestInsert_none (j : ℕ) (z : BranchSpace p (N j)) :
    forestInsert hp N j z none = 0 := by
  change lpExtend hp (forestPrivateEmbedding N j) _ none = 0
  exact lpExtend_apply_outside hp _ _ _ (by rintro ⟨a, h⟩; cases h)

@[simp] theorem forestInsert_private (j n : ℕ) (i : Fin (N j n))
    (z : BranchSpace p (N j)) :
    forestInsert hp N j z (some ⟨j, ⟨n, i⟩⟩) = z (some ⟨n, i⟩) := by
  change lpExtend hp (forestPrivateEmbedding N j) _
    (forestPrivateEmbedding N j ⟨n, i⟩) = _
  simp [branchPrivateEmbedding]

theorem forestInsert_other {j k : ℕ} (hkj : k ≠ j) (n : ℕ) (i : Fin (N k n))
    (z : BranchSpace p (N j)) : forestInsert hp N j z (some ⟨k, ⟨n, i⟩⟩) = 0 := by
  change lpExtend hp (forestPrivateEmbedding N j) _ _ = 0
  apply lpExtend_apply_outside
  rintro ⟨a, ha⟩
  have h := congrArg (fun t : ForestPrivateIndex N => t.map Sigma.fst) ha
  exact hkj (Option.some.inj h).symm

theorem forestExtract_bound (j : ℕ) (y : ForestPrivateSpace p N) :
    ‖forestExtract hp N j y‖ ≤ ‖y‖ := by
  change ‖lpExtend hp (branchPrivateEmbedding (N j))
    (lpRestrict hp (forestPrivateEmbedding N j) y)‖ ≤ ‖y‖
  rw [LinearIsometry.norm_map]
  exact lpRestrictLinear_bound hp _ y

theorem forestInsert_bound (j : ℕ) (z : BranchSpace p (N j)) :
    ‖forestInsert hp N j z‖ ≤ ‖z‖ := by
  change ‖lpExtend hp (forestPrivateEmbedding N j)
    (lpRestrict hp (branchPrivateEmbedding (N j)) z)‖ ≤ ‖z‖
  rw [LinearIsometry.norm_map]
  exact lpRestrictLinear_bound hp _ z

@[simp] theorem forestExtract_insert (j : ℕ) (z : BranchSpace p (N j)) :
    forestExtract hp N j (forestInsert hp N j z) = branchPrivateProjection p (N j) z := by
  apply lp.ext
  funext k
  rcases k with _ | ⟨n, i⟩ <;> simp

theorem forestExtract_insert_other {j k : ℕ} (hjk : j ≠ k)
    (z : BranchSpace p (N k)) : forestExtract hp N j (forestInsert hp N k z) = 0 := by
  apply lp.ext
  funext a
  rcases a with _ | ⟨n, i⟩
  · simp
  · simp [forestInsert_other hp N hjk]

@[simp] theorem forestExtract_initial (j : ℕ) :
    forestExtract hp N j (forestInitial p N) = 0 := by
  apply lp.ext
  funext a
  rcases a with _ | ⟨n, i⟩ <;> simp [forestInitial, Pi.single_apply]

@[simp] theorem forestExtract_unit (j n : ℕ) (i : Fin (N j n)) :
    forestExtract hp N j (forestUnit p N j n i) = branchUnit p (N j) n i := by
  change lpExtend hp (branchPrivateEmbedding (N j))
    (lpRestrict hp (forestPrivateEmbedding N j)
      (lp.single p (forestPrivateEmbedding N j ⟨n, i⟩) 1)) = _
  simp [branchPrivateEmbedding, branchUnit]

theorem forestExtract_unit_other {j k : ℕ} (hjk : j ≠ k) (n : ℕ) (i : Fin (N k n)) :
    forestExtract hp N j (forestUnit p N k n i) = 0 := by
  change lpExtend hp (branchPrivateEmbedding (N j))
    (lpRestrict hp (forestPrivateEmbedding N j) (lp.single p _ 1)) = 0
  rw [lpRestrict_single_outside hp _ _ ?_]
  exact map_zero _
  rintro ⟨a, ha⟩
  have h := congrArg (fun t : ForestPrivateIndex N => t.map Sigma.fst) ha
  exact hjk (Option.some.inj h)

@[simp] theorem forestInsert_root (j : ℕ) :
    forestInsert hp N j (branchRoot p (N j)) = 0 := by
  change lpExtend hp (forestPrivateEmbedding N j)
    (lpRestrict hp (branchPrivateEmbedding (N j)) (lp.single p none 1)) = 0
  rw [lpRestrict_single_outside hp _ _ (by rintro ⟨a, h⟩; cases h)]
  exact map_zero _

@[simp] theorem forestInsert_unit (j n : ℕ) (i : Fin (N j n)) :
    forestInsert hp N j (branchUnit p (N j) n i) = forestUnit p N j n i := by
  change lpExtend hp (forestPrivateEmbedding N j)
    (lpRestrict hp (branchPrivateEmbedding (N j))
      (lp.single p (branchPrivateEmbedding (N j) ⟨n, i⟩) 1)) = _
  simp [forestPrivateEmbedding, forestUnit]

end SchauderTranslates.LpConstruction
