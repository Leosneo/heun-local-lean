import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open scoped BoundedContinuousFunction
noncomputable section
namespace Heun

abbrev BoundedSeq := ℕ →ᵇ ℂ

def boundedWeightedShift (a : ℕ → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (ha : ∀ n, ‖a n‖ ≤ q) : BoundedSeq →L[ℂ] BoundedSeq :=
  LinearMap.mkContinuous
    { toFun := fun x => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun n => a n * x (n+1)) (q*‖x‖) (fun n => by
          rw [norm_mul]
          exact mul_le_mul (ha n) (x.norm_coe_le_norm (n+1)) (norm_nonneg _) hq)
      map_add' := by intro x y; ext n; simp; ring
      map_smul' := by intro c x; ext n; simp; ring }
    q (fun x => (BoundedContinuousFunction.norm_le (mul_nonneg hq (norm_nonneg x))).mpr
      (fun n => by
        change ‖a n*x (n+1)‖ ≤ _
        rw [norm_mul]
        exact mul_le_mul (ha n) (x.norm_coe_le_norm (n+1)) (norm_nonneg _) hq))

@[simp] theorem boundedWeightedShift_apply (a : ℕ → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (ha : ∀ n, ‖a n‖ ≤ q) (x : BoundedSeq) (n : ℕ) :
    boundedWeightedShift a q hq ha x n = a n*x (n+1) := rfl

theorem boundedWeightedShift_norm_le (a : ℕ → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (ha : ∀ n, ‖a n‖ ≤ q) : ‖boundedWeightedShift a q hq ha‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro x
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hq (norm_nonneg x))).mpr
  intro n
  rw [boundedWeightedShift_apply, norm_mul]
  exact mul_le_mul (ha n) (x.norm_coe_le_norm (n+1)) (norm_nonneg _) hq

theorem boundedWeightedShift_one_add_invertible (a : ℕ → ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ n, ‖a n‖ ≤ q) :
    (ContinuousLinearMap.id ℂ BoundedSeq + boundedWeightedShift a q hq ha).IsInvertible := by
  have hn : ‖-boundedWeightedShift a q hq ha‖ < 1 := by
    rw [norm_neg]
    exact (boundedWeightedShift_norm_le a q hq ha).trans_lt hq1
  have hu := isUnit_one_sub_of_norm_lt_one (x := -boundedWeightedShift a q hq ha) hn
  rw [sub_neg_eq_add] at hu
  obtain ⟨u, he⟩ := hu
  exact ⟨ContinuousLinearEquiv.ofUnit u, he⟩

#print axioms boundedWeightedShift_one_add_invertible

/-- Every bounded inhomogeneous sequence has a unique bounded solution for a
uniformly contracting upper shift. -/
theorem bounded_shift_solve (a : ℕ → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hq1 : q < 1) (ha : ∀ n, ‖a n‖ ≤ q) (y : BoundedSeq) :
    ∃! x : BoundedSeq, ∀ n, x n + a n*x (n+1) = y n := by
  obtain ⟨e, he⟩ := boundedWeightedShift_one_add_invertible a q hq hq1 ha
  refine ⟨e.symm y, ?_, ?_⟩
  · intro n
    have h := congrArg (fun z : BoundedSeq => z n) (e.apply_symm_apply y)
    change (e : BoundedSeq →L[ℂ] BoundedSeq) (e.symm y) n = y n at h
    rw [he] at h
    exact h
  · intro x hx
    apply e.injective
    rw [e.apply_symm_apply]
    change (e : BoundedSeq →L[ℂ] BoundedSeq) x = y
    rw [he]
    ext n
    exact hx n

/-- Bounded homogeneous tails cannot carry an additional solution. -/
theorem bounded_shift_homogeneous_zero (a : ℕ → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hq1 : q < 1) (ha : ∀ n, ‖a n‖ ≤ q) (x : BoundedSeq)
    (hx : ∀ n, x n + a n*x (n+1) = 0) : x = 0 := by
  obtain ⟨z, hz, hu⟩ := bounded_shift_solve a q hq hq1 ha 0
  exact (hu x hx).trans (hu 0 (by intro n; simp)).symm

/-- Uniformly invertible diagonal times a contracting upper shift. -/
theorem bounded_bidiagonal_solve (a b : ℕ → ℂ) (C q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ n, a n ≠ 0) (hai : ∀ n, ‖(a n)⁻¹‖ ≤ C)
    (hr : ∀ n, ‖b n/a n‖ ≤ q) (y : BoundedSeq) :
    ∃! x : BoundedSeq, ∀ n, a n*x n+b n*x (n+1)=y n := by
  let yn : BoundedSeq := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (a n)⁻¹*y n) (C*‖y‖) (fun n => by
      rw [norm_mul]
      exact mul_le_mul (hai n) (y.norm_coe_le_norm n) (norm_nonneg _) hC)
  obtain ⟨x, hx, hu⟩ := bounded_shift_solve (fun n => b n/a n) q hq hq1 hr yn
  have iff_eq (z : BoundedSeq) :
      (∀ n, z n+(b n/a n)*z (n+1)=yn n) ↔
      (∀ n, a n*z n+b n*z (n+1)=y n) := by
    constructor <;> intro h n
    · have hh := h n
      change z n+(b n/a n)*z (n+1)=(a n)⁻¹*y n at hh
      field_simp [ha n] at hh
      linear_combination hh
    · have hh := h n
      change z n+(b n/a n)*z (n+1)=(a n)⁻¹*y n
      field_simp [ha n]
      linear_combination hh
  exact ⟨x, (iff_eq x).mp hx, fun z hz => hu z ((iff_eq z).mpr hz)⟩

#print axioms bounded_bidiagonal_solve
#print axioms bounded_shift_homogeneous_zero

def boundedSeqDrop (x : BoundedSeq) : BoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => x (n+1)) ‖x‖
    (fun n => x.norm_coe_le_norm (n+1))

@[simp] theorem boundedSeqDrop_apply (x : BoundedSeq) (n : ℕ) :
    boundedSeqDrop x n = x (n+1) := rfl

def boundedSeqCons (c : ℂ) (x : BoundedSeq) : BoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (Nat.rec c (fun n _ => x n))
    (max ‖c‖ ‖x‖) (fun n => by
      cases n with
      | zero => exact le_max_left _ _
      | succ n => exact (x.norm_coe_le_norm n).trans (le_max_right _ _))

@[simp] theorem boundedSeqCons_zero (c : ℂ) (x : BoundedSeq) :
    boundedSeqCons c x 0 = c := rfl
@[simp] theorem boundedSeqCons_succ (c : ℂ) (x : BoundedSeq) (n : ℕ) :
    boundedSeqCons c x (n+1) = x n := rfl

/-- A finite exceptional prefix does not affect invertibility of a
nonresonant bidiagonal recurrence with a contracting high tail. -/
theorem bounded_bidiagonal_eventually_solve (L : ℕ) (a b : ℕ → ℂ) (C q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ n, a n ≠ 0) (hai : ∀ n, L ≤ n → ‖(a n)⁻¹‖ ≤ C)
    (hr : ∀ n, L ≤ n → ‖b n/a n‖ ≤ q) (y : BoundedSeq) :
    ∃! x : BoundedSeq, ∀ n, a n*x n+b n*x (n+1)=y n := by
  induction L generalizing a b y with
  | zero =>
    exact bounded_bidiagonal_solve a b C q hC hq hq1 ha
      (fun n => hai n (Nat.zero_le n)) (fun n => hr n (Nat.zero_le n)) y
  | succ L ih =>
    obtain ⟨z, hz, hu⟩ := ih (fun n => a (n+1)) (fun n => b (n+1))
      (fun n => ha (n+1))
      (fun n hn => hai (n+1) (Nat.succ_le_succ hn))
      (fun n hn => hr (n+1) (Nat.succ_le_succ hn)) (boundedSeqDrop y)
    let c := (y 0-b 0*z 0)/a 0
    refine ⟨boundedSeqCons c z, ?_, ?_⟩
    · intro n
      cases n with
      | zero =>
        simp only [boundedSeqCons_zero, boundedSeqCons_succ]
        dsimp [c]
        field_simp [ha 0]
        ring
      | succ n => exact hz n
    · intro w hw
      have he : boundedSeqDrop w = z := hu (boundedSeqDrop w) (fun n => hw (n+1))
      ext n
      cases n with
      | zero =>
        have h0 := hw 0
        have h1 : w 1 = z 0 := congrArg (fun x : BoundedSeq => x 0) he
        rw [h1] at h0
        change w 0 = (y 0-b 0*z 0)/a 0
        apply (eq_div_iff (ha 0)).mpr
        linear_combination h0
      | succ n => exact congrArg (fun x : BoundedSeq => x n) he

#print axioms bounded_bidiagonal_eventually_solve

def boundedSeqDropN (m : ℕ) (x : BoundedSeq) : BoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => x (n+m)) ‖x‖
    (fun n => x.norm_coe_le_norm (n+m))

def boundedSeqPad (m : ℕ) (x : BoundedSeq) : BoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => if m ≤ n then x (n-m) else 0) ‖x‖ (fun n => by
      dsimp only
      split_ifs
      · exact x.norm_coe_le_norm _
      · simpa using norm_nonneg x)

/-- Tail inverse in the exact interface used by finite resonant-head assembly. -/
theorem bounded_bidiagonal_tail_solve (k L : ℕ) (a b : ℕ → ℂ) (C q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ n, k < n → a n ≠ 0)
    (hai : ∀ n, L ≤ n → ‖(a n)⁻¹‖ ≤ C)
    (hr : ∀ n, L ≤ n → ‖b n/a n‖ ≤ q) (y : BoundedSeq) :
    ∃ x : BoundedSeq,
      (∀ n, k<n → a n*x n+b n*x (n+1)=y n) ∧
      (∀ z : BoundedSeq, (∀ n,k<n→a n*z n+b n*z (n+1)=y n) →
        ∀ n,k<n→z n=x n) := by
  obtain ⟨x, hx, hu⟩ := bounded_bidiagonal_eventually_solve L
    (fun n => a (n+(k+1))) (fun n => b (n+(k+1))) C q hC hq hq1
    (fun n => ha _ (by omega))
    (fun n hn => hai _ (by omega))
    (fun n hn => hr _ (by omega)) (boundedSeqDropN (k+1) y)
  refine ⟨boundedSeqPad (k+1) x, ?_, ?_⟩
  · intro n hn
    have hn1 : k+1 ≤ n := by omega
    have hn2 : k+1 ≤ n+1 := by omega
    have hi : n-(k+1)+(k+1)=n := by omega
    have hi2 : n+1-(k+1)=n-(k+1)+1 := by omega
    have hh := hx (n-(k+1))
    change a (n-(k+1)+(k+1))*x (n-(k+1)) +
      b (n-(k+1)+(k+1))*x (n-(k+1)+1) = y (n-(k+1)+(k+1)) at hh
    simpa [boundedSeqPad, hn1, hn2, hn, Nat.le_of_lt hn, hi, hi2] using hh
  · intro z hz n hn
    have he : boundedSeqDropN (k+1) z = x := by
      apply hu
      intro i
      simpa [boundedSeqDropN, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz (i+(k+1)) (by omega)
    have hn1 : k+1 ≤ n := by omega
    have hi : n-(k+1)+(k+1)=n := by omega
    have hh := congrArg (fun w : BoundedSeq => w (n-(k+1))) he
    simpa [boundedSeqDropN, boundedSeqPad, hn1, hn, hi] using hh

#print axioms bounded_bidiagonal_tail_solve
end Heun
