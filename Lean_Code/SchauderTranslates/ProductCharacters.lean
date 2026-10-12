import Lean_Code.SchauderTranslates.ScalarProductSpace

noncomputable section
open MeasureTheory Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Concatenate frequencies in independent coordinate blocks. -/
def flattenFrequency {L d : ℕ} (k : Fin L → Fin d → ℤ) : Fin (L * d) → ℤ :=
  fun q => k (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

@[simp] theorem flattenFrequency_apply {L d : ℕ} (k : Fin L → Fin d → ℤ)
    (i : Fin L) (j : Fin d) : flattenFrequency k (finProdFinEquiv (i, j)) = k i j := by
  simp only [flattenFrequency, Equiv.symm_apply_apply]

/-- Characters factor exactly, with the same flattening as the product measure. -/
theorem flattenFrequency_character {L d : ℕ} (k : Fin L → Fin d → ℤ)
    (x : UnitAddTorus (Fin (L * d))) :
    UnitAddTorus.mFourier (flattenFrequency k) x =
      ∏ i : Fin L, UnitAddTorus.mFourier (k i) (torusCopiesEquiv L d x i) := by
  change (∏ q, fourier (flattenFrequency k q) (x q)) = _
  rw [← finProdFinEquiv.prod_comp]
  simp only [Fintype.prod_prod_type, flattenFrequency_apply]
  rfl

/-- Embed a nonconstant frequency in just one coordinate block. -/
def copyFrequency {L d : ℕ} (i : Fin L) (k : Fin d → ℤ) : Fin (L * d) → ℤ :=
  flattenFrequency (fun a => if a = i then k else 0)

@[simp] theorem copyFrequency_apply_same {L d : ℕ} (i : Fin L) (k : Fin d → ℤ)
    (j : Fin d) : copyFrequency i k (finProdFinEquiv (i, j)) = k j := by
  simp [copyFrequency]

@[simp] theorem copyFrequency_apply_ne {L d : ℕ} {i a : Fin L} (h : a ≠ i)
    (k : Fin d → ℤ) (j : Fin d) : copyFrequency i k (finProdFinEquiv (a, j)) = 0 := by
  simp [copyFrequency, h]

theorem copyFrequency_nonzero {L d : ℕ} (i : Fin L) {k : Fin d → ℤ} (hk : k ≠ 0) :
    copyFrequency i k ≠ 0 := by
  intro h
  apply hk
  funext j
  simpa using congrFun h (finProdFinEquiv (i, j))

theorem copyFrequency_injective {L d n : ℕ} (s : ScalarData d n) :
    Function.Injective (fun p : Fin L × Fin n => copyFrequency p.1 (s.frequencies p.2)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := by
    by_contra hij
    apply s.nonconstant a
    funext q
    simpa [copyFrequency_apply_ne hij] using congrFun h (finProdFinEquiv (i, q))
  subst j
  congr 1
  apply s.injective
  funext q
  simpa using congrFun h (finProdFinEquiv (i, q))

namespace ScalarData
variable {d n : ℕ}

/-- The list is ordered copy by copy, using `finProdFinEquiv`. -/
def product (s : ScalarData d n) (L : ℕ) : ScalarData (L * d) (L * n) where
  toTorusWeight := s.toTorusWeight.product L
  frequencies q := copyFrequency (finProdFinEquiv.symm q).1
    (s.frequencies (finProdFinEquiv.symm q).2)
  injective := (copyFrequency_injective s).comp finProdFinEquiv.symm.injective
  nonconstant _q := copyFrequency_nonzero _ (s.nonconstant _)

@[simp] theorem product_frequency (s : ScalarData d n) (L : ℕ) (i : Fin L) (a : Fin n) :
    (s.product L).frequencies (finProdFinEquiv (i, a)) = copyFrequency i (s.frequencies a) := by
  simp only [product, Equiv.symm_apply_apply]

@[simp] theorem product_mass (s : ScalarData d n) (L : ℕ) :
    (s.product L).mass = s.mass ^ L := s.toTorusWeight.product_mass L

theorem product_even (s : ScalarData d n) (hs : s.IsEven) (L : ℕ) :
    (s.product L).IsEven := s.toTorusWeight.product_even hs L

theorem product_positiveFloor (s : ScalarData d n) (hs : s.HasPositiveFloor) (L : ℕ) :
    (s.product L).HasPositiveFloor := by
  obtain ⟨b, hb, h⟩ := hs
  exact ⟨b ^ L, pow_pos hb _, s.toTorusWeight.product_floor hb.le h L⟩

end ScalarData

namespace TorusWeight
variable {d : ℕ}

/-- A normalized weighted character inner product. -/
def normalizedMoment (w : TorusWeight d) (k l : Fin d → ℤ) : ℂ :=
  (w.mass : ℂ)⁻¹ * inner ℂ (w.vector k) (w.vector l)

@[simp] theorem normalizedMoment_zero (w : TorusWeight d) : w.normalizedMoment 0 0 = 1 := by
  have hm : (w.mass : ℂ) ≠ 0 := by exact_mod_cast w.mass_pos.ne'
  have h : inner ℂ (w.vector 0) (w.vector 0) = (w.mass : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖w.vector 0‖ : ℂ) ^ 2 = (w.mass : ℂ)
    rw [← Complex.ofReal_pow, w.vector_norm_sq]
  simp only [normalizedMoment, h, inv_mul_cancel₀ hm]

/-- All normalized moments factor, not only the entries in the retained list. -/
theorem product_normalizedMoment (w : TorusWeight d) (L : ℕ)
    (k l : Fin L → Fin d → ℤ) :
    (w.product L).normalizedMoment (flattenFrequency k) (flattenFrequency l) =
      ∏ i, w.normalizedMoment (k i) (l i) := by
  have hi : inner ℂ ((w.product L).vector (flattenFrequency k))
      ((w.product L).vector (flattenFrequency l)) =
      ∏ i, inner ℂ (w.vector (k i)) (w.vector (l i)) := by
    simp only [vector_inner]
    calc
      _ = ∫ x, ∏ i, (w.density (torusCopiesEquiv L d x i) : ℂ) *
          star (UnitAddTorus.mFourier (k i) (torusCopiesEquiv L d x i)) *
          UnitAddTorus.mFourier (l i) (torusCopiesEquiv L d x i)
          ∂torusMeasure (L * d) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [product, flattenFrequency_character, Complex.ofReal_prod,
          star_prod, Finset.prod_mul_distrib]
      _ = _ := integral_torus_copies_prod L d (fun i x =>
        (w.density x : ℂ) * star (UnitAddTorus.mFourier (k i) x) *
          UnitAddTorus.mFourier (l i) x)
  simp only [normalizedMoment, hi, product_mass, Complex.ofReal_pow,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]

end TorusWeight
end SchauderTranslates
