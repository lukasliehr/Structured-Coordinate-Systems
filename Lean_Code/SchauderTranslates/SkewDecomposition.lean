import Lean_Code.SchauderTranslates.HilbertBlocks

noncomputable section
open Module
open scoped InnerProductSpace InnerProduct

namespace SchauderTranslates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Moving a power of a real skew operator across the inner product. -/
theorem skew_power_inner (J : E →ₗ[ℝ] E)
    (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (n : ℕ) (x y : E) :
    inner ℝ ((J ^ n) x) y = (-1 : ℝ) ^ n * inner ℝ x ((J ^ n) y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    have hm : (J ^ n) (J y) = (J ^ (n + 1)) y := by
      rw [pow_succ, Module.End.mul_apply]
    calc
      inner ℝ ((J ^ (n + 1)) x) y = -inner ℝ ((J ^ n) x) (J y) := by
        rw [pow_succ', Module.End.mul_apply, hJ]
      _ = -((-1 : ℝ) ^ n * inner ℝ x ((J ^ (n + 1)) y)) := by rw [ih, hm]
      _ = (-1 : ℝ) ^ (n + 1) * inner ℝ x ((J ^ (n + 1)) y) := by
        rw [pow_succ]
        ring

theorem skew_odd_power_self (J : E →ₗ[ℝ] E)
    (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (n : ℕ) (x : E) :
    inner ℝ x ((J ^ (2 * n + 1)) x) = 0 := by
  have h := skew_power_inner J hJ (2 * n + 1) x x
  have he : (-1 : ℝ) ^ (2 * n + 1) = -1 := by simp [pow_add, pow_mul]
  rw [he, real_inner_comm x] at h
  linarith

/-- The even cyclic subspace of a vector. It needs no spectral decomposition. -/
def evenCyclic (J : E →ₗ[ℝ] E) (b : E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun n : ℕ => (J ^ (2 * n)) b))

theorem mem_evenCyclic (J : E →ₗ[ℝ] E) (b : E) : b ∈ evenCyclic J b := by
  have := Submodule.subset_span (R := ℝ) (Set.mem_range_self 0 (f := fun n : ℕ => (J ^ (2 * n)) b))
  simpa [evenCyclic] using this

theorem evenCyclic_square_invariant (J : E →ₗ[ℝ] E) (b : E)
    (x : E) (hx : x ∈ evenCyclic J b) : J (J x) ∈ evenCyclic J b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    have he : J (J ((J ^ (2 * n)) b)) = (J ^ (2 * (n + 1))) b := by
      rw [show 2 * (n + 1) = 1 + (1 + 2 * n) by omega, pow_add, pow_add]
      simp only [pow_one, Module.End.mul_apply]
    rw [he]
    exact Submodule.subset_span ⟨n + 1, rfl⟩
  | zero => simp [evenCyclic]
  | add x y hx hy ihx ihy => simpa only [map_add] using (evenCyclic J b).add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using (evenCyclic J b).smul_mem a ih

theorem evenCyclic_isotropic (J : E →ₗ[ℝ] E)
    (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (b : E)
    (x : E) (hx : x ∈ evenCyclic J b) (y : E) (hy : y ∈ evenCyclic J b) :
    inner ℝ x (J y) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [skew_power_inner J hJ]
      have he : (J ^ (2 * n)) (J ((J ^ (2 * m)) b)) =
          (J ^ (2 * (n + m) + 1)) b := by
        rw [show 2 * (n + m) + 1 = 2 * n + (1 + 2 * m) by omega, pow_add, pow_add]
        simp only [pow_one, Module.End.mul_apply]
      rw [he, skew_odd_power_self J hJ]
      exact mul_zero _
    | zero => simp
    | add y z hy hz ihy ihz => simp only [map_add, inner_add_right, ihy, ihz, add_zero]
    | smul a y hy ih => simp only [map_smul, real_inner_smul_right, ih, mul_zero]
  | zero => simp
  | add x z hx hz ihx ihz => simp only [inner_add_left, ihx, ihz, add_zero]
  | smul a x hx ih => simp only [real_inner_smul_left, ih, mul_zero]

def SquareInvariant (J : E →ₗ[ℝ] E) (S : Submodule ℝ E) : Prop :=
  ∀ x ∈ S, J (J x) ∈ S

def SkewIsotropic (J : E →ₗ[ℝ] E) (S : Submodule ℝ E) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, inner ℝ x (J y) = 0

theorem squareInvariant_sup (J : E →ₗ[ℝ] E) (S T : Submodule ℝ E)
    (hS : SquareInvariant J S) (hT : SquareInvariant J T) : SquareInvariant J (S ⊔ T) := by
  rintro x hx
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, map_add]
  exact Submodule.mem_sup.mpr ⟨J (J s), hS s hs, J (J t), hT t ht, rfl⟩

theorem squareInvariant_map (J : E →ₗ[ℝ] E) (S : Submodule ℝ E)
    (hS : SquareInvariant J S) : SquareInvariant J (S.map J) := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨J (J y), hS y hy, rfl⟩

theorem squareInvariant_orthogonal (J : E →ₗ[ℝ] E)
    (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y))
    (S : Submodule ℝ E) (hS : SquareInvariant J S) : SquareInvariant J Sᗮ := by
  intro x hx y hy
  have h0 := hx (J (J y)) (hS y hy)
  have h1 := hJ y (J x)
  have h2 := hJ (J y) x
  linarith

theorem evenCyclic_le_of_squareInvariant (J : E →ₗ[ℝ] E) (b : E)
    (S : Submodule ℝ E) (hb : b ∈ S) (hS : SquareInvariant J S) : evenCyclic J b ≤ S := by
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  induction n with
  | zero => simpa using hb
  | succ n ih =>
    have he : (J ^ (2 * (n + 1))) b = J (J ((J ^ (2 * n)) b)) := by
      rw [show 2 * (n + 1) = 1 + (1 + 2 * n) by omega, pow_add, pow_add]
      simp only [pow_one, Module.End.mul_apply]
    change (J ^ (2 * (n + 1))) b ∈ S
    rw [he]
    exact hS _ ih

theorem skewIsotropic_sup (J : E →ₗ[ℝ] E)
    (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (S T : Submodule ℝ E)
    (hS : SkewIsotropic J S) (hT : SkewIsotropic J T)
    (hTS : T ≤ (S ⊔ S.map J)ᗮ) : SkewIsotropic J (S ⊔ T) := by
  intro x hx y hy
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨s', hs', t', ht', rfl⟩ := Submodule.mem_sup.mp hy
  have hst : inner ℝ s (J t') = 0 := by
    have h0 := hTS ht' (J s) ((show S.map J ≤ S ⊔ S.map J from le_sup_right) ⟨s, hs, rfl⟩)
    have h1 := hJ s t'
    linarith
  have hts : inner ℝ t (J s') = 0 := by
    rw [real_inner_comm]
    exact hTS ht (J s') ((show S.map J ≤ S ⊔ S.map J from le_sup_right) ⟨s', hs', rfl⟩)
  simp only [map_add, inner_add_left, inner_add_right, hS s hs s' hs', hT t ht t' ht',
    hst, hts, add_zero]

/-- A maximal even-invariant isotropic space contains the prescribed vector and covers
the ambient space together with its skew image. -/
theorem exists_maximal_even_isotropic [FiniteDimensional ℝ E]
    (J : E →ₗ[ℝ] E) (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (b : E) :
    ∃ S : Submodule ℝ E, b ∈ S ∧ SquareInvariant J S ∧ SkewIsotropic J S ∧
      S ⊔ S.map J = ⊤ := by
  classical
  let good : Set (Submodule ℝ E) := {S | b ∈ S ∧ SquareInvariant J S ∧ SkewIsotropic J S}
  have hnonempty : good.Nonempty := ⟨evenCyclic J b, mem_evenCyclic J b,
    evenCyclic_square_invariant J b, evenCyclic_isotropic J hJ b⟩
  have hfinite : ((fun S : Submodule ℝ E => finrank ℝ S) '' good).Finite := by
    apply (Set.finite_Iic (finrank ℝ E)).subset
    rintro n ⟨S, hS, rfl⟩
    exact Submodule.finrank_le S
  obtain ⟨S, hS, hmax⟩ := hfinite.exists_maximalFor' (fun S : Submodule ℝ E => finrank ℝ S)
    good hnonempty
  refine ⟨S, hS.1, hS.2.1, hS.2.2, ?_⟩
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  by_contra hw0
  let T := evenCyclic J w
  have hTle : T ≤ (S ⊔ S.map J)ᗮ :=
    evenCyclic_le_of_squareInvariant J w _ hw
      (squareInvariant_orthogonal J hJ _
        (squareInvariant_sup J S (S.map J) hS.2.1 (squareInvariant_map J S hS.2.1)))
  have hgood : S ⊔ T ∈ good := ⟨(show S ≤ S ⊔ T from le_sup_left) hS.1,
    squareInvariant_sup J S T hS.2.1 (evenCyclic_square_invariant J w),
    skewIsotropic_sup J hJ S T hS.2.2 (evenCyclic_isotropic J hJ w) hTle⟩
  have hnot : w ∉ S := by
    intro hwS
    have hz := hw w ((show S ≤ S ⊔ S.map J from le_sup_left) hwS)
    exact hw0 (inner_self_eq_zero.mp hz)
  have hlt : S < S ⊔ T := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    apply hnot
    rw [he]
    exact (show T ≤ S ⊔ T from le_sup_right) (mem_evenCyclic J w)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  exact (not_le_of_gt hdim) (hmax hgood hdim.le)

/-- A real skew operator has an orthogonal two-block form with `b` in the first block. -/
theorem skew_orthogonal_grading [FiniteDimensional ℝ E]
    (J : E →ₗ[ℝ] E) (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (b : E) :
    ∃ S : Submodule ℝ E, b ∈ S ∧
      (∀ x ∈ S, J x ∈ Sᗮ) ∧ (∀ x ∈ Sᗮ, J x ∈ S) := by
  obtain ⟨S, hb, hsq, hiso, htop⟩ := exists_maximal_even_isotropic J hJ b
  refine ⟨S, hb, ?_, ?_⟩
  · intro x hx y hy
    exact hiso y hy x hx
  · intro x hx
    have hmem : x ∈ S ⊔ S.map J := by rw [htop]; trivial
    obtain ⟨s, hs, t, ⟨u, hu, rfl⟩, he⟩ := Submodule.mem_sup.mp hmem
    have hs0 : s = 0 := by
      have hh := hx s hs
      rw [← he, inner_add_right, hiso s hs u hu, add_zero] at hh
      exact inner_self_eq_zero.mp hh
    rw [hs0, zero_add] at he
    rw [← he]
    exact hsq u hu

/-- The grading realizes the skew map as the standard off-diagonal Hilbert block. -/
theorem skew_normal_form_with_vector [FiniteDimensional ℝ E] [CompleteSpace E]
    (J : E →L[ℝ] E) (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (b : E) :
    ∃ (S : Submodule ℝ E) (_hb : b ∈ S) (Z : Sᗮ →L[ℝ] S),
      S.orthogonalDecomposition.conjStarAlgEquiv J =
        hilbertBlockProjection Z - (hilbertBlockProjection Z)† := by
  obtain ⟨S, hb, hleft, hright⟩ := skew_orthogonal_grading J.toLinearMap hJ b
  let Z : Sᗮ →L[ℝ] S := (J.comp Sᗮ.subtypeL).codRestrict S (fun x => hright x x.property)
  refine ⟨S, hb, Z, ?_⟩
  have hadj (x : S) : ((Z†) x : E) = -J (x : E) := by
    have he : (Z†) x = ⟨-J (x : E), Sᗮ.neg_mem (hleft x x.property)⟩ := by
      apply ext_inner_right ℝ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_left]
      change inner ℝ (x : E) (J (y : E)) = inner ℝ (-J (x : E)) (y : E)
      rw [inner_neg_left, hJ, neg_neg]
    exact congrArg Subtype.val he
  ext x
  apply S.orthogonalDecomposition.symm.injective
  change S.orthogonalDecomposition.symm
    (S.orthogonalDecomposition (J (S.orthogonalDecomposition.symm x))) =
    S.orthogonalDecomposition.symm
      ((hilbertBlockProjection Z - (hilbertBlockProjection Z)†) x)
  rw [LinearIsometryEquiv.symm_apply_apply, hilbertBlockProjection_skew_apply]
  simp only [Submodule.orthogonalDecomposition_symm_apply]
  change J ((x.fst : E) + (x.snd : E)) = J (x.snd : E) + -((Z†) x.fst : E)
  rw [map_add, hadj, neg_neg, add_comm]

end SchauderTranslates
