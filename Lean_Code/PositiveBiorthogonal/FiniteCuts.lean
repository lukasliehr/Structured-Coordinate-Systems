import Lean_Code.PositiveBiorthogonal.FiniteCoordinates

/-! Contractive coordinate cuts and coordinate inclusions for the genuine finite ℓᵖ spaces. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem finiteLp_norm_mono {m : ℕ} (x y : FiniteLp 𝕜 p m)
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  by_cases hp : p = ∞
  · subst p
    rw [← PiLp.norm_ofLp]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
    intro i
    exact (h i).trans (PiLp.norm_apply_le y i)
  · have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    rw [PiLp.norm_eq_sum hr, PiLp.norm_eq_sum hr]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hr.le

def finiteCut (m h : ℕ) (x : FiniteLp 𝕜 p m) : FiniteLp 𝕜 p m :=
  WithLp.toLp p fun i => if i.val < h then x i else 0

theorem finiteCut_norm_le (m h : ℕ) (x : FiniteLp 𝕜 p m) : ‖finiteCut m h x‖ ≤ ‖x‖ := by
  apply finiteLp_norm_mono
  intro i
  change ‖if i.val < h then x i else 0‖ ≤ ‖x i‖
  split_ifs <;> simp

def coordinateCut (m h : ℕ) : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  LinearMap.mkContinuous
    { toFun := finiteCut m h
      map_add' := by intro x y; ext i; simp only [finiteCut, PiLp.add_apply]; split_ifs <;> simp
      map_smul' := by intro c x; ext i; simp only [finiteCut, PiLp.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
    1 (fun x => by simpa using finiteCut_norm_le (𝕜 := 𝕜) (p := p) m h x)

@[simp] theorem coordinateCut_apply (m h : ℕ) (x : FiniteLp 𝕜 p m) (i : Fin m) :
    coordinateCut m h x i = if i.val < h then x i else 0 := rfl

theorem coordinateCut_norm_le (m h : ℕ) : ‖coordinateCut (𝕜 := 𝕜) (p := p) m h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖finiteCut (p := p) m h x‖ ≤ 1 * ‖x‖
  simpa using finiteCut_norm_le (𝕜 := 𝕜) (p := p) m h x

theorem coordinateCut_eq_sum (m h : ℕ) (x : FiniteLp 𝕜 p m) :
    coordinateCut m h x = ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < h),
      x i • PiLp.single p i 1 := by
  classical
  ext i
  simp [Pi.single_apply]

def finiteGather {I J : ℕ} (f : Fin I → Fin J) (x : FiniteLp 𝕜 p J) : FiniteLp 𝕜 p I :=
  WithLp.toLp p fun i => x (f i)

theorem finiteGather_norm_le {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f)
    (x : FiniteLp 𝕜 p J) : ‖finiteGather f x‖ ≤ ‖x‖ := by
  classical
  by_cases hp : p = ∞
  · subst p
    rw [← PiLp.norm_ofLp]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    exact PiLp.norm_apply_le x (f i)
  · have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    rw [PiLp.norm_eq_sum hr, PiLp.norm_eq_sum hr]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    change ∑ i : Fin I, ‖x (f i)‖ ^ p.toReal ≤ _
    rw [← Finset.sum_image (f := fun j : Fin J => ‖x j‖ ^ p.toReal) (s := Finset.univ) (fun i _ j _ hij => hf hij)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)

def coordinateGather {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f) :
    FiniteLp 𝕜 p J →L[𝕜] FiniteLp 𝕜 p I :=
  LinearMap.mkContinuous
    { toFun := finiteGather f
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
    1 (fun x => by
      change ‖finiteGather (p := p) f x‖ ≤ 1 * ‖x‖
      simpa using finiteGather_norm_le (𝕜 := 𝕜) (p := p) f hf x)

@[simp] theorem coordinateGather_apply {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f)
    (x : FiniteLp 𝕜 p J) (i : Fin I) : coordinateGather f hf x i = x (f i) := rfl

theorem coordinateGather_norm_le {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f) :
    ‖coordinateGather (𝕜 := 𝕜) (p := p) f hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖finiteGather (p := p) f x‖ ≤ 1 * ‖x‖
  simpa using finiteGather_norm_le (𝕜 := 𝕜) (p := p) f hf x

def finiteScatter {I J : ℕ} (f : Fin I → Fin J) (x : FiniteLp 𝕜 p I) : FiniteLp 𝕜 p J :=
  ∑ i : Fin I, x i • PiLp.single p (f i) 1

omit [Fact (1 ≤ p)] in
@[simp] theorem finiteScatter_image {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f)
    (x : FiniteLp 𝕜 p I) (i : Fin I) : finiteScatter f x (f i) = x i := by
  classical
  simp [finiteScatter, Pi.single_apply, hf.eq_iff]

omit [Fact (1 ≤ p)] in
theorem finiteScatter_not_image {I J : ℕ} (f : Fin I → Fin J)
    (x : FiniteLp 𝕜 p I) (j : Fin J) (hj : j ∉ Set.range f) : finiteScatter f x j = 0 := by
  classical
  have hji (i : Fin I) : j ≠ f i := fun he => hj ⟨i, he.symm⟩
  simp [finiteScatter, hji]

theorem finiteScatter_norm_le {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f)
    (x : FiniteLp 𝕜 p I) : ‖finiteScatter f x‖ ≤ ‖x‖ := by
  classical
  by_cases hp : p = ∞
  · subst p
    rw [← PiLp.norm_ofLp]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [finiteScatter_image f hf]
      exact PiLp.norm_apply_le x i
    · rw [finiteScatter_not_image f x j hj]
      exact (norm_zero : ‖(0 : 𝕜)‖ = 0).le.trans (norm_nonneg x)
  · have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    rw [PiLp.norm_eq_sum hr, PiLp.norm_eq_sum hr]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    have he : (∑ j : Fin J, ‖finiteScatter f x j‖ ^ p.toReal) =
        ∑ j ∈ Finset.univ.image f, ‖finiteScatter f x j‖ ^ p.toReal := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hj' : j ∉ Set.range f := by simpa using hj
      rw [finiteScatter_not_image f x j hj', norm_zero, Real.zero_rpow hr.ne']
    rw [he, Finset.sum_image (fun i _ j _ hij => hf hij)]
    simp only [finiteScatter_image f hf, le_refl]

def coordinateScatter {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f) :
    FiniteLp 𝕜 p I →L[𝕜] FiniteLp 𝕜 p J :=
  LinearMap.mkContinuous
    { toFun := finiteScatter f
      map_add' := by
        intro x y
        simp [finiteScatter, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [finiteScatter, smul_smul, Finset.smul_sum] }
    1 (fun x => by
      change ‖finiteScatter (p := p) f x‖ ≤ 1 * ‖x‖
      simpa using finiteScatter_norm_le (𝕜 := 𝕜) (p := p) f hf x)

@[simp] theorem coordinateScatter_apply {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f)
    (x : FiniteLp 𝕜 p I) : coordinateScatter f hf x = finiteScatter f x := rfl

theorem coordinateScatter_norm_le {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f) :
    ‖coordinateScatter (𝕜 := 𝕜) (p := p) f hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using finiteScatter_norm_le (𝕜 := 𝕜) (p := p) f hf x

omit [Fact (1 ≤ p)] in
theorem finiteMap_ext_on_single {m n : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (A B : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 q n)
    (h : ∀ j : Fin m, A (PiLp.single p j 1) = B (PiLp.single p j 1)) : A = B := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  have hx : (∑ j : Fin m, x j • PiLp.single p j (1 : 𝕜)) = x := by
    simpa using (PiLp.basisFun p 𝕜 (Fin m)).sum_repr x
  rw [← hx]
  simp only [map_sum, map_smul, h]

theorem coordinateCut_single (m h : ℕ) (j : Fin m) :
    coordinateCut (𝕜 := 𝕜) (p := p) m h (PiLp.single p j 1) =
      if j.val < h then PiLp.single p j 1 else 0 := by
  ext i
  by_cases hij : i = j
  · subst i
    by_cases hj : j.val < h <;> simp [hj]
  · by_cases hj : j.val < h <;> by_cases hi : i.val < h <;> simp [hj, hi, hij]

omit [Fact (1 ≤ p)] in
theorem finiteGather_single_image {I J : ℕ} (f : Fin I → Fin J) (hf : Function.Injective f)
    (j : Fin I) : finiteGather (𝕜 := 𝕜) (p := p) f (PiLp.single p (f j) 1) = PiLp.single p j 1 := by
  ext i
  change (PiLp.single p (f j) 1 : FiniteLp 𝕜 p J) (f i) = (PiLp.single p j 1 : FiniteLp 𝕜 p I) i
  simp [PiLp.single_apply, hf.eq_iff]

omit [Fact (1 ≤ p)] in
theorem finiteGather_single_not_image {I J : ℕ} (f : Fin I → Fin J)
    (j : Fin J) (hj : j ∉ Set.range f) :
    finiteGather (𝕜 := 𝕜) (p := p) f (PiLp.single p j 1) = 0 := by
  ext i
  have hi : f i ≠ j := fun he => hj ⟨i, he⟩
  change (PiLp.single p j 1 : FiniteLp 𝕜 p J) (f i) = 0
  simp [hi]

end PositiveBiorthogonal
