import Lean_Code.PositiveBiorthogonal.FinitePolynomial
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Finite weighted Hilbert estimates; all comparisons at zero use open intervals. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace PositiveBiorthogonal

theorem sum_samples_le_integral (f : ℝ → ℝ) (g : ℕ → ℝ) (N : ℕ)
    (hint : IntervalIntegrable f volume 0 N)
    (hcomp : ∀ k < N, ∀ t ∈ Set.Ioo (k : ℝ) (k + 1), g (k + 1) ≤ f t) :
    (∑ k ∈ Finset.range N, g (k + 1)) ≤ ∫ t in (0 : ℝ)..N, f t := by
  have hpiece (k : ℕ) (hk : k < N) : IntervalIntegrable f volume (k : ℝ) (k + 1) := by
    apply hint.mono_set
    rw [uIcc_of_le (by linarith : (k : ℝ) ≤ k + 1), uIcc_of_le (Nat.cast_nonneg N)]
    intro t ht
    have hkreal : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    exact ⟨(Nat.cast_nonneg k).trans ht.1, ht.2.trans hkreal⟩
  calc
    (∑ k ∈ Finset.range N, g (k + 1)) ≤
        ∑ k ∈ Finset.range N, ∫ t in (k : ℝ)..(k + 1), f t := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := Finset.mem_range.mp hk
      calc
        g (k + 1) = ∫ t in (k : ℝ)..(k + 1), g (k + 1) := by simp
        _ ≤ ∫ t in (k : ℝ)..(k + 1), f t :=
          intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) intervalIntegrable_const
            (hpiece k hkN) (hcomp k hkN)
    _ = ∫ t in (0 : ℝ)..N, f t := by
      simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using
        intervalIntegral.sum_integral_adjacent_intervals
          (a := fun k : ℕ => (k : ℝ)) (fun k hk => by simpa using hpiece k hk)

theorem power_prefix_bound (u : ℝ) (hu : 0 < u) (hu1 : u < 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (-u)) ≤ (N : ℝ) ^ (1 - u) / (1 - u) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-u)) volume 0 N :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hbound := sum_samples_le_integral (fun t : ℝ => t ^ (-u)) (fun k => (k : ℝ) ^ (-u)) N hint
    (fun k _ t ht => by
      have htpos : 0 < t := (Nat.cast_nonneg k).trans_lt ht.1
      simp only [Nat.cast_add, Nat.cast_one]
      exact Real.rpow_le_rpow_of_nonpos htpos ht.2.le (by linarith))
  rw [integral_rpow (Or.inl (by linarith : -1 < -u))] at hbound
  simpa only [Nat.cast_add, Nat.cast_one, show -u + 1 = 1 - u by ring,
    Real.zero_rpow (by linarith : 1 - u ≠ 0), sub_zero] using hbound

theorem power_tail_bound (u : ℝ) (hu : 0 < u) (i J : ℕ) (hi : 0 < i) :
    (∑ k ∈ Finset.Ico i J, ((k : ℝ) + 1) ^ (-u - 1)) ≤ (i : ℝ) ^ (-u) / u := by
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-u - 1)) (Set.Icc (i : ℝ) J) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hipos.trans_le hx.1) hxy (by linarith)
  have hint : IntegrableOn (fun t : ℝ => t ^ (-u - 1)) (Set.Ioi (i : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hipos
  have hb := hanti.sum_Ico_le_integral hint (fun t ht => Real.rpow_nonneg (hipos.trans ht).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -u - 1 < -1) hipos] at hb
  simpa only [Nat.cast_add, Nat.cast_one, sub_add_cancel, neg_div_neg_eq] using hb

/-- The finite weight estimate, indexed from zero while sampling positive integers. -/
theorem finite_kernel_weight (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (i J : ℕ) (hi : 0 < i) :
    (∑ k ∈ Finset.range J, ((k : ℝ) + 1) ^ (-u) / ((i : ℝ) + (k + 1))) ≤
      (1 / (1 - u) + 1 / u) * (i : ℝ) ^ (-u) := by
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  let w := fun k : ℕ => ((k : ℝ) + 1) ^ (-u) / ((i : ℝ) + (k + 1))
  have hw (k : ℕ) : 0 ≤ w k := by
    apply div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hext : (∑ k ∈ Finset.range J, w k) ≤ ∑ k ∈ Finset.range (i + J), w k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro k _ _
    exact hw k
  have hsplit : (∑ k ∈ Finset.range (i + J), w k) =
      (∑ k ∈ Finset.range i, w k) + ∑ k ∈ Finset.Ico i (i + J), w k :=
    (Finset.sum_range_add_sum_Ico w (by omega : i ≤ i + J)).symm
  have hfirst : (∑ k ∈ Finset.range i, w k) ≤
      ((i : ℝ) ^ (1 - u) / (1 - u)) / i := by
    calc
      (∑ k ∈ Finset.range i, w k) ≤
          ∑ k ∈ Finset.range i, ((k : ℝ) + 1) ^ (-u) / (i : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _) hipos (by
          have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
          linarith)
      _ = (∑ k ∈ Finset.range i, ((k : ℝ) + 1) ^ (-u)) / i := (Finset.sum_div ..).symm
      _ ≤ ((i : ℝ) ^ (1 - u) / (1 - u)) / i :=
        div_le_div_of_nonneg_right (power_prefix_bound u hu hu1 i) hipos.le
  have hlast : (∑ k ∈ Finset.Ico i (i + J), w k) ≤ (i : ℝ) ^ (-u) / u := by
    calc
      (∑ k ∈ Finset.Ico i (i + J), w k) ≤
          ∑ k ∈ Finset.Ico i (i + J), ((k : ℝ) + 1) ^ (-u - 1) := by
        apply Finset.sum_le_sum
        intro k _
        rw [Real.rpow_sub_one (by positivity : (k : ℝ) + 1 ≠ 0)]
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _) (by positivity) (by
          linarith)
      _ ≤ (i : ℝ) ^ (-u) / u := power_tail_bound u hu i (i + J) hi
  have hpow : (i : ℝ) ^ (1 - u) = (i : ℝ) ^ (-u) * i := by
    simpa only [show -u + 1 = 1 - u by ring] using Real.rpow_add_one hipos.ne' (-u)
  change (∑ k ∈ Finset.range J, w k) ≤ _
  calc
    (∑ k ∈ Finset.range J, w k) ≤
        ((i : ℝ) ^ (1 - u) / (1 - u)) / i + (i : ℝ) ^ (-u) / u :=
      hext.trans (hsplit ▸ add_le_add hfirst hlast)
    _ = (1 / (1 - u) + 1 / u) * (i : ℝ) ^ (-u) := by
      rw [hpow]
      field_simp

/-- A weighted finite Hölder estimate, kept separate from the Hilbert kernel. -/
theorem weighted_holder_row {ι : Type*} [Fintype ι] (r s : ℝ)
    (hrs : r.HolderConjugate s) (K w x : ι → ℝ)
    (hK : ∀ j, 0 < K j) (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 ≤ x j) :
    (∑ j, K j * x j) ^ r ≤
      (∑ j, K j * w j) ^ (r / s) * ∑ j, K j * (w j) ^ (-r / s) * (x j) ^ r := by
  let A := fun j => (K j * w j) ^ (1 / s)
  let B := fun j => (K j) ^ (1 / r) * (w j) ^ (-1 / s) * x j
  have hA (j : ι) : 0 ≤ A j := Real.rpow_nonneg (mul_nonneg (hK j).le (hw j).le) _
  have hB (j : ι) : 0 ≤ B j := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (hK j).le _) (Real.rpow_nonneg (hw j).le _)) (hx j)
  have hab (j : ι) : A j * B j = K j * x j := by
    dsimp [A, B]
    rw [Real.mul_rpow (hK j).le (hw j).le]
    calc
      (K j) ^ (1 / s) * (w j) ^ (1 / s) *
          ((K j) ^ (1 / r) * (w j) ^ (-1 / s) * x j) =
          ((K j) ^ (1 / s) * (K j) ^ (1 / r)) *
            ((w j) ^ (1 / s) * (w j) ^ (-1 / s)) * x j := by ring
      _ = K j * x j := by
        rw [← Real.rpow_add (hK j), ← Real.rpow_add (hw j)]
        have he : 1 / s + 1 / r = 1 := by simpa only [one_div] using hrs.symm.inv_add_inv_eq_one
        rw [he, show 1 / s + -1 / s = 0 by ring, Real.rpow_one, Real.rpow_zero, mul_one]
  have haPow (j : ι) : (A j) ^ s = K j * w j := by
    dsimp [A]
    rw [← Real.rpow_mul (mul_nonneg (hK j).le (hw j).le),
      one_div_mul_cancel hrs.symm.ne_zero, Real.rpow_one]
  have hbPow (j : ι) : (B j) ^ r = K j * (w j) ^ (-r / s) * (x j) ^ r := by
    dsimp [B]
    rw [Real.mul_rpow
      (mul_nonneg (Real.rpow_nonneg (hK j).le _) (Real.rpow_nonneg (hw j).le _)) (hx j),
      Real.mul_rpow (Real.rpow_nonneg (hK j).le _) (Real.rpow_nonneg (hw j).le _),
      ← Real.rpow_mul (hK j).le, ← Real.rpow_mul (hw j).le,
      one_div_mul_cancel hrs.ne_zero, Real.rpow_one]
    rw [show -1 / s * r = -r / s by ring]
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (f := A) (g := B) Finset.univ hrs.symm
    (fun j _ => hA j) (fun j _ => hB j)
  simp_rw [hab, haPow, hbPow] at hH
  have hsumA : 0 ≤ ∑ j, K j * w j := Finset.sum_nonneg fun j _ => mul_nonneg (hK j).le (hw j).le
  have hsumB : 0 ≤ ∑ j, K j * (w j) ^ (-r / s) * (x j) ^ r :=
    Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (hK j).le (Real.rpow_nonneg (hw j).le _)) (Real.rpow_nonneg (hx j) _)
  have hPower := Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => mul_nonneg (hK j).le (hx j))
    hH hrs.pos.le
  rw [Real.mul_rpow (Real.rpow_nonneg hsumA _) (Real.rpow_nonneg hsumB _),
    ← Real.rpow_mul hsumA, ← Real.rpow_mul hsumB,
    one_div_mul_cancel hrs.ne_zero, Real.rpow_one] at hPower
  simpa only [show 1 / s * r = r / s by ring] using hPower

def hilbertKernel (i j : ℕ) : ℝ := 1 / ((i : ℝ) + 1 + ((j : ℝ) + 1))

theorem hilbertKernel_pos (i j : ℕ) : 0 < hilbertKernel i j := by
  unfold hilbertKernel
  positivity

theorem hilbertKernel_symm (i j : ℕ) : hilbertKernel i j = hilbertKernel j i := by
  unfold hilbertKernel
  congr 1
  ring

theorem hilbert_weight_conjugate (r s : ℝ) (hrs : r.HolderConjugate s) (i J : ℕ) :
    (∑ j : Fin J, hilbertKernel i j.val * ((j.val : ℝ) + 1) ^ (-(1 / r))) ≤
      (r + s) * ((i : ℝ) + 1) ^ (-(1 / r)) := by
  have hu : 0 < 1 / r := one_div_pos.mpr hrs.pos
  have hu1 : 1 / r < 1 := (div_lt_one hrs.pos).mpr hrs.lt
  have hb := finite_kernel_weight (1 / r) hu hu1 (i + 1) J (by omega)
  have hC : 1 / (1 - 1 / r) + 1 / (1 / r) = r + s := by
    simp only [one_div, hrs.one_sub_inv, inv_inv]
    ring
  rw [hC, Finset.sum_range] at hb
  simpa only [hilbertKernel, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul,
    mul_comm] using hb

theorem hilbert_row_bound (r s : ℝ) (hrs : r.HolderConjugate s)
    (i J : ℕ) (x : Fin J → ℝ) (hx : ∀ j, 0 ≤ x j) :
    (∑ j, hilbertKernel i j.val * x j) ^ r ≤
      (r + s) ^ (r / s) * ((i : ℝ) + 1) ^ (-(1 / s)) *
        ∑ j, hilbertKernel i j.val * ((j.val : ℝ) + 1) ^ (1 / s) * (x j) ^ r := by
  let w := fun j : Fin J => ((j.val : ℝ) + 1) ^ (-(1 / r))
  have hw (j : Fin J) : 0 < w j := Real.rpow_pos_of_pos (by positivity) _
  have hweightPow (j : Fin J) : (w j) ^ (-r / s) = ((j.val : ℝ) + 1) ^ (1 / s) := by
    dsimp [w]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (j.val : ℝ) + 1)]
    congr 1
    field_simp [hrs.ne_zero, hrs.symm.ne_zero]
  have hb := weighted_holder_row r s hrs (fun j : Fin J => hilbertKernel i j.val) w x
    (fun j => hilbertKernel_pos _ _) hw hx
  simp_rw [hweightPow] at hb
  have hsum0 : 0 ≤ ∑ j : Fin J, hilbertKernel i j.val * w j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hilbertKernel_pos _ _).le (hw j).le
  have ht0 : 0 ≤ ∑ j : Fin J, hilbertKernel i j.val * ((j.val : ℝ) + 1) ^ (1 / s) * (x j) ^ r :=
    Finset.sum_nonneg fun j _ => by
      exact mul_nonneg (mul_nonneg (hilbertKernel_pos _ _).le (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (hx j) _)
  have hfirst := Real.rpow_le_rpow hsum0 (hilbert_weight_conjugate r s hrs i J)
    (div_nonneg hrs.pos.le hrs.symm.pos.le)
  have hCpos : 0 < r + s := add_pos hrs.pos hrs.symm.pos
  have he : ((r + s) * ((i : ℝ) + 1) ^ (-(1 / r))) ^ (r / s) =
      (r + s) ^ (r / s) * ((i : ℝ) + 1) ^ (-(1 / s)) := by
    rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)]
    congr 2
    field_simp [hrs.ne_zero, hrs.symm.ne_zero]
  rw [he] at hfirst
  exact hb.trans (mul_le_mul_of_nonneg_right hfirst ht0)

theorem hilbert_sum_rpow_bound (r s : ℝ) (hrs : r.HolderConjugate s)
    (I J : ℕ) (x : Fin J → ℝ) (hx : ∀ j, 0 ≤ x j) :
    (∑ i : Fin I, (∑ j : Fin J, hilbertKernel i.val j.val * x j) ^ r) ≤
      (r + s) ^ r * ∑ j : Fin J, (x j) ^ r := by
  let C := r + s
  let a := fun i : Fin I => ((i.val : ℝ) + 1) ^ (-(1 / s))
  let b := fun j : Fin J => ((j.val : ℝ) + 1) ^ (1 / s) * (x j) ^ r
  have hCpos : 0 < C := add_pos hrs.pos hrs.symm.pos
  have hb (j : Fin J) : 0 ≤ b j :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (hx j) _)
  have hcol (j : Fin J) : (∑ i : Fin I, hilbertKernel i.val j.val * a i) ≤
      C * ((j.val : ℝ) + 1) ^ (-(1 / s)) := by
    have he : (∑ i : Fin I, hilbertKernel i.val j.val * a i) =
        ∑ i : Fin I, hilbertKernel j.val i.val * ((i.val : ℝ) + 1) ^ (-(1 / s)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hilbertKernel_symm]
    rw [he]
    simpa only [C, add_comm] using hilbert_weight_conjugate s r hrs.symm j.val I
  have hcolBound (j : Fin J) : b j * (∑ i : Fin I, hilbertKernel i.val j.val * a i) ≤
      C * (x j) ^ r := by
    have hc : ((j.val : ℝ) + 1) ^ (1 / s) * ((j.val : ℝ) + 1) ^ (-(1 / s)) = 1 := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < (j.val : ℝ) + 1), add_neg_cancel, Real.rpow_zero]
    calc
      b j * (∑ i : Fin I, hilbertKernel i.val j.val * a i) ≤
          b j * (C * ((j.val : ℝ) + 1) ^ (-(1 / s))) := mul_le_mul_of_nonneg_left (hcol j) (hb j)
      _ = C * (x j) ^ r := by
        dsimp [b]
        calc
          _ = C * (((j.val : ℝ) + 1) ^ (1 / s) * ((j.val : ℝ) + 1) ^ (-(1 / s))) * (x j) ^ r := by ring
          _ = C * (x j) ^ r := by rw [hc, mul_one]
  have heSum :
      (∑ i : Fin I, C ^ (r / s) * a i * ∑ j : Fin J, hilbertKernel i.val j.val * b j) =
        C ^ (r / s) * ∑ j : Fin J, b j * ∑ i : Fin I, hilbertKernel i.val j.val * a i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrExp : r / s + 1 = r := by
    field_simp [hrs.symm.ne_zero]
    nlinarith [hrs.sub_one_mul_conj]
  calc
    (∑ i : Fin I, (∑ j : Fin J, hilbertKernel i.val j.val * x j) ^ r) ≤
        ∑ i : Fin I, C ^ (r / s) * a i * ∑ j : Fin J, hilbertKernel i.val j.val * b j := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [C, a, b, mul_assoc] using hilbert_row_bound r s hrs i.val J x hx
    _ = C ^ (r / s) * ∑ j : Fin J, b j * ∑ i : Fin I, hilbertKernel i.val j.val * a i := heSum
    _ ≤ C ^ (r / s) * ∑ j : Fin J, C * (x j) ^ r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hcolBound j) (Real.rpow_nonneg hCpos.le _)
    _ = C ^ r * ∑ j : Fin J, (x j) ^ r := by
      rw [← Finset.mul_sum, ← mul_assoc, ← Real.rpow_add_one hCpos.ne', hrExp]

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def hilbertAction (I J : ℕ) (x : FiniteLp 𝕜 p J) : FiniteLp 𝕜 p I :=
  WithLp.toLp p fun i => ∑ j : Fin J, (hilbertKernel i.val j.val : 𝕜) * x j

omit [Fact (1 ≤ p)] in
theorem hilbertAction_coordinate_bound (I J : ℕ) (x : FiniteLp 𝕜 p J) (i : Fin I) :
    ‖hilbertAction I J x i‖ ≤ ∑ j : Fin J, hilbertKernel i.val j.val * ‖x j‖ := by
  change ‖∑ j : Fin J, (hilbertKernel i.val j.val : 𝕜) * x j‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (hilbertKernel_pos _ _)]

theorem hilbertAction_norm_le {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (I J : ℕ) (x : FiniteLp 𝕜 p J) :
    ‖hilbertAction I J x‖ ≤ (p.toReal + q.toReal) * ‖x‖ := by
  have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  have hreal := ENNReal.HolderConjugate.toReal_of_ne_top hpfin hqfin
  have hC : 0 ≤ p.toReal + q.toReal := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)) hreal.pos).mp
  rw [finiteLp_norm_rpow hpfin, Real.mul_rpow hC (norm_nonneg _), finiteLp_norm_rpow hpfin]
  calc
    (∑ i : Fin I, ‖hilbertAction I J x i‖ ^ p.toReal) ≤
        ∑ i : Fin I, (∑ j : Fin J, hilbertKernel i.val j.val * ‖x j‖) ^ p.toReal := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow (norm_nonneg _) (hilbertAction_coordinate_bound I J x i) hreal.pos.le
    _ ≤ (p.toReal + q.toReal) ^ p.toReal * ∑ j : Fin J, ‖x j‖ ^ p.toReal :=
      hilbert_sum_rpow_bound _ _ hreal I J (fun j => ‖x j‖) (fun j => norm_nonneg _)

def hilbertOperator {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (I J : ℕ) :
    FiniteLp 𝕜 p J →L[𝕜] FiniteLp 𝕜 p I :=
  LinearMap.mkContinuous
    { toFun := hilbertAction I J
      map_add' := by
        intro x y
        ext i
        simp [hilbertAction, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext i
        simp [hilbertAction, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm] }
    (p.toReal + q.toReal) (hilbertAction_norm_le (q := q) hp1 hpfin I J)

theorem hilbertOperator_norm_le {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (I J : ℕ) :
    ‖hilbertOperator (𝕜 := 𝕜) (q := q) hp1 hpfin I J‖ ≤ p.toReal + q.toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  exact hilbertAction_norm_le hp1 hpfin I J

end PositiveBiorthogonal
