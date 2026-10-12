import Lean_Code.PositiveTranslates.Forest.Norms

/-!
# Synthesis: combinations of atoms in terms of coordinates and roots

For a coefficient family `v` living on the stages `< T` we compute the combination of atoms
`F.synth T v = ∑_{s < T} ∑ᵢ v s i • atom s i`:

`F.synth T v = F.lin T (synthCoord r F.N v) + ∑_{j < T} rootCoef r F.N v j • root j`
(`synth_eq`), i.e. the block of stage `s` of the `Y`-part is `v s + 2 m(v (succStage s)) u_s`
and the coefficient of `root j` is `2 m(v (stageOf (j, 0)))`.

We also express the partial sums of the sequence `F.seq` through `F.synth`
(`sum_range_offset_eq`), identify the coefficient family of a partial sum as a `cut`
(`coefOf_indicator`), and reduce the finite prefix inequality for `F.seq` to an inequality
between `F.synth T (cut s⋆ k v)` and `F.synth T v` (`prefix_bound_of_cut_bound`).
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates.PositiveForest

open Forest

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {r : ℝ} (F : PositiveForest Z r)

/-- The combination `∑_{s < T} ∑ᵢ v s i • atom s i` of the atoms of the stages `< T`. -/
def synth (T : ℕ) (v : Coef F.N) : Z := ∑ s ∈ Finset.range T, ∑ i, v s i • F.atom s i

/-- **Synthesis formula.** A combination of atoms, sorted into coordinates and roots. -/
theorem synth_eq {T : ℕ} {v : Coef F.N} (hv : ∀ s, T ≤ s → v s = 0) :
    F.synth T v = F.lin T (synthCoord r F.N v) +
      ∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j := by
  have hzero : ∀ (f : ℕ → Z) (s : ℕ), T ≤ s → (2 * blockMean r (v s)) • f s = 0 := by
    intro f s hs
    rw [hv s hs, map_zero, mul_zero, zero_smul]
  have h1 : F.synth T v =
      F.lin T v + ∑ s ∈ Finset.range T, (2 * blockMean r (v s)) • F.target s := by
    rw [synth, lin_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => F.sum_smul_atom s (v s)
  have h2 : ∀ s, (2 * blockMean r (v s)) • F.target s =
      (if (stagePair s).2 = 0 then (2 * blockMean r (v s)) • F.root (stagePair s).1 else 0) +
        (if (stagePair s).2 = 0 then 0 else (2 * blockMean r (v s)) • F.avg (predStage s)) := by
    intro s
    rw [target_eq]
    split_ifs <;> simp
  have h3 : ∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j =
      ∑ s ∈ Finset.range T,
        if (stagePair s).2 = 0 then (2 * blockMean r (v s)) • F.root (stagePair s).1 else 0 := by
    have h := sum_range_firstStage T (fun s => (2 * blockMean r (v s)) • F.root (stagePair s).1)
      (hzero fun s => F.root (stagePair s).1)
    simp only [stagePair_stageOf] at h
    exact h
  have h4 : ∑ s ∈ Finset.range T, (2 * blockMean r (v (succStage s))) • F.avg s =
      ∑ s ∈ Finset.range T,
        if (stagePair s).2 = 0 then 0 else (2 * blockMean r (v s)) • F.avg (predStage s) := by
    have h := sum_range_succStage T (fun s => (2 * blockMean r (v s)) • F.avg (predStage s))
      (hzero fun s => F.avg (predStage s))
    simp only [predStage_succStage] at h
    exact h
  have h5 : F.lin T (synthCoord r F.N v) =
      F.lin T v + ∑ s ∈ Finset.range T, (2 * blockMean r (v (succStage s))) • F.avg s := by
    rw [lin_apply, lin_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [synthCoord_apply, map_add, map_smul, avg_eq_blk]
  rw [h1, h5, h3, h4, Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_add_distrib]
  abel

/-- The `Y`-component of a combination of `e0` and atoms. -/
theorem PY_e0_add_synth (c0 : ℂ) {T : ℕ} {v : Coef F.N} (hv : ∀ s, T ≤ s → v s = 0) :
    F.PY (c0 • F.e0 + F.synth T v) = c0 • F.e0 + F.lin T (synthCoord r F.N v) := by
  rw [F.synth_eq hv, map_add, map_add, map_smul, F.PY_e0, F.PY_lin, F.PY_sum_root, add_zero]

/-- The `X`-component of a combination of `e0` and atoms. -/
theorem e0_add_synth_sub_PY (c0 : ℂ) {T : ℕ} {v : Coef F.N} (hv : ∀ s, T ≤ s → v s = 0) :
    c0 • F.e0 + F.synth T v - F.PY (c0 • F.e0 + F.synth T v) =
      ∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j := by
  rw [F.PY_e0_add_synth c0 hv, F.synth_eq hv]
  abel

/-! ### Partial sums of the sequence -/

/-- The coefficient family of a scalar sequence: the atom `atom s i` receives the
coefficient number `offset s + i`. -/
def coefOf (a : ℕ → ℂ) : Coef F.N := fun s i => a (F.offset s + i)

theorem coefOf_apply (a : ℕ → ℂ) (s : ℕ) (i : Fin (F.N s)) :
    F.coefOf a s i = a (F.offset s + i) := rfl

theorem sum_range_offset_eq (a : ℕ → ℂ) (T : ℕ) :
    ∑ n ∈ Finset.range (F.offset T), a n • F.seq n = a 0 • F.e0 + F.synth T (F.coefOf a) :=
  F.sum_range_offset a T

theorem coefOf_eq_zero (a : ℕ → ℂ) {T : ℕ} (ha : ∀ n, F.offset T ≤ n → a n = 0) (s : ℕ)
    (hs : T ≤ s) : F.coefOf a s = 0 := by
  funext i
  have h : F.offset T ≤ F.offset s := F.offset_strictMono.monotone hs
  exact ha _ (by omega)

/-- Cutting a scalar sequence at the index `offset s⋆ + k` cuts its coefficient family. -/
theorem coefOf_indicator (a : ℕ → ℂ) (sStar : ℕ) {k : ℕ} (hk : k ≤ F.N sStar) :
    F.coefOf (fun n => if n < F.offset sStar + k then a n else 0) = cut sStar k (F.coefOf a) := by
  funext s i
  rw [cut_apply]
  simp only [coefOf_apply]
  have hi := i.2
  by_cases h1 : s < sStar
  · have h : F.offset (s + 1) ≤ F.offset sStar := F.offset_strictMono.monotone h1
    rw [offset_succ] at h
    rw [if_pos h1, if_pos (by omega)]
    rfl
  · rw [if_neg h1]
    by_cases h2 : s = sStar
    · subst h2
      rw [if_pos rfl, trunc_apply]
      simp only [add_lt_add_iff_left]
      rfl
    · have h : F.offset (sStar + 1) ≤ F.offset s := F.offset_strictMono.monotone (by omega)
      rw [offset_succ] at h
      rw [if_neg h2, if_neg (by omega)]
      rfl

/-- **Reduction of the prefix inequality.** If cutting a coefficient family never increases
the norm of the combination of `e0` and the atoms by more than the factor `C`, then the
sequence `F.seq` satisfies the finite prefix inequality with constant `C`. -/
theorem prefix_bound_of_cut_bound {C : ℝ} (hC : 0 ≤ C)
    (hmain : ∀ (T : ℕ) (c0 : ℂ) (v : Coef F.N), (∀ s, T ≤ s → v s = 0) →
      ∀ sStar, sStar < T → ∀ k,
        ‖c0 • F.e0 + F.synth T (cut sStar k v)‖ ≤ C * ‖c0 • F.e0 + F.synth T v‖)
    (M : ℕ) (a : ℕ →₀ ℂ) :
    ‖∑ n ∈ Finset.range M, a n • F.seq n‖ ≤ C * ‖Finsupp.linearCombination ℂ F.seq a‖ := by
  classical
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simpa using mul_nonneg hC (norm_nonneg _)
  set T := max M (a.support.sup id + 1) with hT
  have hT1 : M < F.offset T := lt_of_le_of_lt (le_max_left _ _) (F.lt_offset T)
  have hsupp : ∀ n, F.offset T ≤ n → a n = 0 := by
    intro n hn
    by_contra hne
    have h1 : n ≤ a.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr hne)
    have h2 : a.support.sup id + 1 ≤ T := le_max_right _ _
    have h3 := F.lt_offset T
    omega
  have hfull : Finsupp.linearCombination ℂ F.seq a =
      ∑ n ∈ Finset.range (F.offset T), a n • F.seq n := by
    rw [← finitePrefix_apply]
    refine (finitePrefix_eq_linearCombination F.seq a fun n hn => ?_).symm
    by_contra hlt
    exact (Finsupp.mem_support_iff.mp hn) (hsupp n (not_lt.mp hlt))
  -- the position of the cut
  have hk := F.sub_offset_stageIdx_lt hM
  have hle := F.offset_stageIdx_le hM
  set sStar := F.stageIdx M with hsStar
  set k := M - F.offset sStar with hkdef
  have hMk : M = F.offset sStar + k := by omega
  have hsT : sStar < T := by
    by_contra h
    have : F.offset T ≤ F.offset sStar := F.offset_strictMono.monotone (not_lt.mp h)
    omega
  have hpre : ∑ n ∈ Finset.range M, a n • F.seq n =
      ∑ n ∈ Finset.range (F.offset T), (if n < M then a n else 0) • F.seq n := by
    have hfil : (Finset.range (F.offset T)).filter (fun n => n < M) = Finset.range M := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← hfil, Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
  have hcut : F.coefOf (fun n => if n < M then a n else 0) = cut sStar k (F.coefOf a) := by
    have h := F.coefOf_indicator a sStar hk.le
    rwa [← hMk] at h
  rw [hpre, hfull, F.sum_range_offset_eq, F.sum_range_offset_eq, hcut, if_pos hM]
  exact hmain T (a 0) (F.coefOf a) (F.coefOf_eq_zero a hsupp) sStar hsT k

end StructuredBases.PositiveTranslates.PositiveForest
