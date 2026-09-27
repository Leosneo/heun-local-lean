import HeunProblem
import JetPropagation
import FiniteRoot
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Formal-power-series specialization of the exact Heun recurrence.
This file proves polynomial support of finite-root jets, not analytic convergence. -/
noncomputable section
namespace Heun
open PowerSeries
abbrev Series := PowerSeries ℂ

def formalPair (f : Family) (p : Parameters) (B : Series) : ℕ → Series × Series
  | 0 => (0, 1)
  | m + 1 =>
    let q := formalPair f p B m
    (q.2, ((B + C (D p m) + X * C (E f p m)) * q.2 -
      X * C (F f p m) * q.1) * C ((((m : ℂ) + 1) * ((m : ℂ) + p.gamma))⁻¹))

def formalCoefficient (f : Family) (p : Parameters) (B : Series) (m : ℕ) : Series :=
  (formalPair f p B m).2

theorem formalPair_constant (f : Family) (p : Parameters) (B : Series) (m : ℕ) :
    (constantCoeff (formalPair f p B m).1, constantCoeff (formalPair f p B m).2) =
      coefficientPair f p (constantCoeff B) 0 m := by
  induction m with
  | zero => simp [formalPair, coefficientPair]
  | succ m ih =>
    have h1 := congrArg Prod.fst ih
    have h2 := congrArg Prod.snd ih
    simp only [formalPair, coefficientPair]
    simp only [map_mul, map_sub, map_add, constantCoeff_C, constantCoeff_X,
      zero_mul, add_zero, sub_zero, div_eq_mul_inv]
    exact Prod.ext h2 (congrArg (fun z => (constantCoeff B + D p m) * z *
      (((m : ℂ) + 1) * ((m : ℂ) + p.gamma))⁻¹) h2)

theorem formalCoefficient_constant (f : Family) (p : Parameters) (B : Series) (m : ℕ) :
    constantCoeff (formalCoefficient f p B m) = coefficient f p (constantCoeff B) 0 m :=
  congrArg Prod.snd (formalPair_constant f p B m)

theorem formal_recurrence {f : Family} {p : Parameters} (hp : Admissible f p)
    (B : Series) (m : ℕ) :
    C (((m : ℂ) + 2) * ((m : ℂ) + 1 + p.gamma)) * formalCoefficient f p B (m + 2) =
      (B + C (D p (m + 1)) + X * C (E f p (m + 1))) *
        formalCoefficient f p B (m + 1) -
      X * C (F f p (m + 1)) * formalCoefficient f p B m := by
  have hd := recurrence_denominator_ne_zero hp (m + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hd
  have hd' : ((m : ℂ) + 2) * ((m : ℂ) + 1 + p.gamma) ≠ 0 := by
    convert hd using 1 <;> ring
  unfold formalCoefficient
  rw [formalPair]
  simp only [Nat.cast_add, Nat.cast_one]
  have he : (m : ℂ) + 1 + 1 = (m : ℂ) + 2 := by ring
  rw [he]
  rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ hd', map_one, mul_one]
  rfl

theorem formal_diagonal_unit {f : Family} {p : Parameters} (hp : Admissible f p)
    {B : Series} {k m : ℕ} (hB : constantCoeff B = -D p k) (hm : m ≠ k) :
    IsUnit (B + C (D p m) + X * C (E f p m)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp only [map_add, map_mul, constantCoeff_C, constantCoeff_X, zero_mul, add_zero, hB]
  apply isUnit_iff_ne_zero.mpr
  intro h
  have he : D p m = D p k := by linear_combination h
  exact hm (D_injective hp he)

/-- A finite root forces every coefficient in the tail to gain one order
per backward step away from the unperturbed degree k. No tail vanishing
hypothesis is supplied: only the actual root equation is used. -/
theorem formal_root_tail {f : Family} {p : Parameters} (hp : Admissible f p)
    {B : Series} {k N : ℕ} (hB : constantCoeff B = -D p k)
    (hroot : formalCoefficient f p B N = 0) :
    ∀ j m, k + j ≤ m → m ≤ N → (X : Series) ^ j ∣ formalCoefficient f p B m := by
  intro j
  induction j with
  | zero => intro m _ _; simp
  | succ j ih =>
    have descend : ∀ m, m ≤ N → k + (j + 1) ≤ m →
        (X : Series) ^ (j + 1) ∣ formalCoefficient f p B m := by
      apply Nat.decreasingInduction
      · intro m hm hn hkm
        have hmpos : 0 < m := by omega
        have heq : m - 1 + 1 = m := by omega
        have heq2 : m - 1 + 2 = m + 1 := by omega
        have hr := formal_recurrence hp B (m - 1)
        rw [heq, heq2] at hr
        apply MoriTakemura.unit_cancel_vanishing (formal_diagonal_unit hp (k := k) (m := m) hB (by omega))
        have hsum : (B + C (D p m) + X * C (E f p m)) * formalCoefficient f p B m =
            C (((((m - 1 : ℕ) : ℂ)) + 2) * ((((m - 1 : ℕ) : ℂ)) + 1 + p.gamma)) *
              formalCoefficient f p B (m + 1) +
            X * C (F f p m) * formalCoefficient f p B (m - 1) := by
          linear_combination -hr
        rw [hsum]
        apply dvd_add
        · exact dvd_mul_of_dvd_right (hn (by omega)) _
        · have ht := MoriTakemura.parameter_raises_order (ih (m - 1) (by omega) (by omega))
          simpa only [mul_assoc, mul_left_comm, mul_comm] using dvd_mul_of_dvd_left ht (C (F f p m))
      · intro _
        rw [hroot]
        exact dvd_zero _
    intro m hm hN
    exact descend m hN hm

/-- The support bound holds for the whole infinite recurrence, not merely
for the coefficients before the finite truncation. -/
theorem formal_root_all_tail {f : Family} {p : Parameters} (hp : Admissible f p)
    {B : Series} {k N j : ℕ} (hB : constantCoeff B = -D p k)
    (hroot : formalCoefficient f p B N = 0) (hN : k + j ≤ N) :
    ∀ m, k + j ≤ m → (X : Series) ^ j ∣ formalCoefficient f p B m := by
  cases j with
  | zero => intro m _; simp
  | succ j =>
    intro m hm
    by_cases hmN : m ≤ N
    · exact formal_root_tail hp hB hroot (j + 1) m hm hmN
    · have hprev := formal_root_tail hp hB hroot j (N - 1) (by omega) (by omega)
      have hcurrent : (X : Series) ^ (j + 1) ∣ formalCoefficient f p B (N - 1 + 1) := by
        have he : N - 1 + 1 = N := by omega
        rw [he, hroot]
        exact dvd_zero _
      have ht := MoriTakemura.tail_vanishing (X : Series) (formalCoefficient f p B)
        (fun n => C (((n : ℂ) + 2) * ((n : ℂ) + 1 + p.gamma)))
        (fun n => B + C (D p (n + 1)) + X * C (E f p (n + 1)))
        (fun n => C (F f p (n + 1))) (N - 1) j
        (fun n => by
          apply PowerSeries.isUnit_iff_constantCoeff.mpr
          rw [constantCoeff_C]
          apply isUnit_iff_ne_zero.mpr
          have hd := recurrence_denominator_ne_zero hp (n + 1)
          convert hd using 1 <;> push_cast <;> ring)
        (formal_recurrence hp B) hprev hcurrent (m - N)
      have he : N - 1 + 1 + (m - N) = m := by omega
      rwa [he] at ht

/-- Exact polynomial-jet support: the order-j perturbation coefficient of
the normalized solution has no z-monomials above degree k+j, whenever the
finite root truncation lies past that degree. -/
theorem formal_root_polynomial_jet {f : Family} {p : Parameters} (hp : Admissible f p)
    {B : Series} {k N j : ℕ} (hB : constantCoeff B = -D p k)
    (hroot : formalCoefficient f p B N = 0) (hN : k + j + 1 ≤ N)
    {m : ℕ} (hm : k + j < m) :
    PowerSeries.coeff j (formalCoefficient f p B m) = 0 := by
  have hv := formal_root_all_tail hp hB hroot (j := j + 1) (by omega) m (by omega)
  exact PowerSeries.X_pow_dvd_iff.mp hv j (by omega)

/-- Exact divided difference, defined recursively without division by B-C. -/
def formalDifferencePair (f : Family) (p : Parameters) (B T : Series) : ℕ → Series × Series
  | 0 => (0, 0)
  | m + 1 =>
    let q := formalDifferencePair f p B T m
    (q.2, ((B + C (D p m) + X * C (E f p m)) * q.2 +
      formalCoefficient f p T m - X * C (F f p m) * q.1) *
      C ((((m : ℂ) + 1) * ((m : ℂ) + p.gamma))⁻¹))

theorem formal_difference_factor (f : Family) (p : Parameters) (B T : Series) (m : ℕ) :
    (formalPair f p B m).1 - (formalPair f p T m).1 =
      (B - T) * (formalDifferencePair f p B T m).1 ∧
    formalCoefficient f p B m - formalCoefficient f p T m =
      (B - T) * (formalDifferencePair f p B T m).2 := by
  induction m with
  | zero => simp [formalPair, formalCoefficient, formalDifferencePair]
  | succ m ih =>
    constructor
    · exact ih.2
    · dsimp [formalCoefficient, formalPair, formalDifferencePair]
      dsimp [formalCoefficient] at ih
      linear_combination
        (B + C (D p m) + X * C (E f p m)) *
          C ((((m : ℂ) + 1) * ((m : ℂ) + p.gamma))⁻¹) * ih.2 -
        X * C (F f p m) * C ((((m : ℂ) + 1) * ((m : ℂ) + p.gamma))⁻¹) * ih.1

/-- The reduction of the exact divided difference is the ordinary derivative. -/
theorem formal_difference_derivative (f : Family) (p : Parameters)
    (B T : Series) (hbase : constantCoeff B = constantCoeff T) (m : ℕ) :
    HasDerivAt (fun z => (coefficientPair f p z 0 m).1)
      (constantCoeff (formalDifferencePair f p B T m).1) (constantCoeff B) ∧
    HasDerivAt (fun z => coefficient f p z 0 m)
      (constantCoeff (formalDifferencePair f p B T m).2) (constantCoeff B) := by
  induction m with
  | zero =>
    constructor
    · simpa [coefficientPair, coefficient, formalDifferencePair] using
        (hasDerivAt_const (constantCoeff B) (0 : ℂ))
    · simpa [coefficientPair, coefficient, formalDifferencePair] using
        (hasDerivAt_const (constantCoeff B) (1 : ℂ))
  | succ m ih =>
    constructor
    · exact ih.2
    · have ht := (((hasDerivAt_id (constantCoeff B)).add_const (D p m)).mul ih.2).mul_const
        ((((m : ℂ) + 1) * ((m : ℂ) + p.gamma))⁻¹)
      convert ht using 1
      · ext z
        simp [coefficient, coefficientPair, div_eq_mul_inv]
      · simp only [formalDifferencePair, map_mul, map_sub, map_add,
          constantCoeff_C, constantCoeff_X, zero_mul, add_zero, sub_zero,
          formalCoefficient_constant]
        rw [← hbase]
        simp only [id_eq]
        ring

theorem formal_difference_unit {f : Family} {p : Parameters} (hp : Admissible f p)
    {B T : Series} {k M : ℕ} (hB : constantCoeff B = -D p k)
    (hT : constantCoeff T = -D p k) (hk : k < M) :
    IsUnit (formalDifferencePair f p B T M).2 := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  apply isUnit_iff_ne_zero.mpr
  let den : ℂ := ∏ m ∈ Finset.range M, (((m : ℂ) + 1) * ((m : ℂ) + p.gamma))
  let a : ℂ := (∏ m ∈ (Finset.range M).erase k, (D p m - D p k)) / den
  have hden : den ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro m _
    exact recurrence_denominator_ne_zero hp m
  have ha : a ≠ 0 := by
    apply div_ne_zero _ hden
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hm).1 (D_injective hp h))
  have hd : HasDerivAt (fun z : ℂ => coefficient f p z 0 M) a (-D p k) := by
    simpa only [coefficient_at_s_zero] using
      MoriTakemura.complex_scaled_product_hasDerivAt
        (Finset.range M) (D p) (Finset.mem_range.mpr hk) den
  have hr := (formal_difference_derivative f p B T (hB.trans hT.symm) M).2
  rw [hB] at hr
  rw [hr.unique hd]
  exact ha

/-- Finite-root stabilization for the actual formal Heun recurrence.
The truncations may be in either order, and no divided-difference or
vanishing assumptions are supplied. -/
theorem formal_root_jet_stabilization {f : Family} {p : Parameters}
    (hp : Admissible f p) {B T : Series} {k N M j : ℕ}
    (hB : constantCoeff B = -D p k) (hT : constantCoeff T = -D p k)
    (hrootB : formalCoefficient f p B N = 0)
    (hrootT : formalCoefficient f p T M = 0)
    (hN : k + j + 1 ≤ N) (hM : k + j + 1 ≤ M) :
    (X : Series) ^ (j + 1) ∣ B - T := by
  apply MoriTakemura.unit_cancel_vanishing
    (formal_difference_unit hp (M := M) hB hT (by omega))
  rw [mul_comm, ← (formal_difference_factor f p B T M).2, hrootT, sub_zero]
  exact formal_root_all_tail hp hB hrootB (j := j + 1) (by omega) M (by omega)

/-- Consequently, every Taylor coefficient through order j is independent
of the finite truncation index once both indices exceed k+j. -/
theorem formal_root_coeff_stabilization {f : Family} {p : Parameters}
    (hp : Admissible f p) {B T : Series} {k N M j i : ℕ}
    (hB : constantCoeff B = -D p k) (hT : constantCoeff T = -D p k)
    (hrootB : formalCoefficient f p B N = 0)
    (hrootT : formalCoefficient f p T M = 0)
    (hN : k + j + 1 ≤ N) (hM : k + j + 1 ≤ M) (hi : i ≤ j) :
    PowerSeries.coeff i B = PowerSeries.coeff i T := by
  have hv := formal_root_jet_stabilization hp hB hT hrootB hrootT hN hM
  have he := PowerSeries.X_pow_dvd_iff.mp hv i (by omega)
  simpa only [map_sub, sub_eq_zero] using he

#print axioms formal_root_coeff_stabilization
#print axioms formal_root_tail
#print axioms formal_root_polynomial_jet
end Heun
