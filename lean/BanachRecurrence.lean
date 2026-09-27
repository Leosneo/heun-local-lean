import BanachOperators
import BanachODE

noncomputable section
namespace Heun

theorem seqA_decode (p : Parameters) (k : ℕ) (x : SeqSpace) (n : ℕ) :
    seqA p k x n = (2:ℂ)^n * ((D p k-D p n)*decode x n+
      ((n:ℂ)+1)*((n:ℂ)+p.gamma)*decode x (n+1)) := by
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n:ℂ)+2 ≠ 0 := by exact_mod_cast (by omega : n+2≠0)
  rw [seqA_apply, seqDiag_apply, seqUpper_apply]
  simp only [decode, seqWeight, Nat.cast_add, Nat.cast_one, pow_succ, show (n:ℂ)+1+1=(n:ℂ)+2 by ring]
  field_simp [hn, hn2]

theorem seqJ_decode (x : SeqSpace) (n : ℕ) :
    seqJ x n = (2:ℂ)^n*decode x n := by
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [seqJ, seqInvNat, decode, seqWeight]
  field_simp

@[simp] theorem seqV_zero (f : Family) (p : Parameters) (x : SeqSpace) :
    seqV f p x 0=0 := by
  cases f <;> simp [seqV, seqVdiag, seqVlower, seqInvNat, seqConst] <;> ring

theorem seqV_decode_succ (f : Family) (p : Parameters) (x : SeqSpace) (n : ℕ) :
    seqV f p x (n+1) = (2:ℂ)^(n+1)*
      (-E f p (n+1)*decode x (n+1)+F f p (n+1)*decode x n) := by
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n:ℂ)+2 ≠ 0 := by exact_mod_cast (by omega : n+2≠0)
  change seqVdiag f p (n+1)*x (n+1)+seqVlower f p n*x n = _
  cases f <;> simp [seqVdiag, seqVlower, seqInvNat, seqConst, decode, seqWeight, E, F,
    Nat.cast_add, Nat.cast_one, pow_succ, show (n:ℂ)+1+1=(n:ℂ)+2 by ring] <;> field_simp <;> ring

theorem residual_coefficients (f : Family) (p : Parameters) (hp : Admissible f p)
    (k : ℕ) (x : SeqSpace) (b s : ℂ)
    (hx : seqA p k x-b • seqJ x+s • seqV f p x=0) (hx0 : x 0=1) :
    ∀ n, decode x n=coefficient f p (-D p k+b) s n := by
  apply coefficient_eq_of_recurrence f p (fun n => by simpa using hp.1 (-(n:ℤ)))
  · simpa [decode, seqWeight] using hx0
  · have h := congrArg (fun v : SeqSpace => v 0) hx
    change seqA p k x 0-b*seqJ x 0+s*seqV f p x 0=0 at h
    rw [seqA_decode, seqJ_decode, seqV_zero] at h
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, show D p 0=0 by simp [D], zero_mul, sub_zero,
      add_zero] at h
    have hc0 : decode x 0=1 := by simpa [decode,seqWeight] using hx0
    rw [hc0, mul_one] at h
    linear_combination h
  · intro n
    have h := congrArg (fun v : SeqSpace => v (n+1)) hx
    change seqA p k x (n+1)-b*seqJ x (n+1)+s*seqV f p x (n+1)=0 at h
    rw [seqA_decode, seqJ_decode, seqV_decode_succ] at h
    have hpow : (2:ℂ)^(n+1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have he : (2:ℂ)^(n+1) *
        (((n:ℂ)+2)*((n:ℂ)+1+p.gamma)*decode x (n+2)-
        ((-D p k+b+D p (n+1)+s*E f p (n+1))*decode x (n+1)-
          s*F f p (n+1)*decode x n)) = 0 := by
      simp only [Nat.cast_add, Nat.cast_one] at h
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hpow)

theorem seqA_encoded_base_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    seqA p k (encodePolynomial (basePolynomial f p k))=0 := by
  apply BoundedContinuousFunction.ext
  intro n
  change seqA p k (encodePolynomial (basePolynomial f p k)) n=0
  rw [seqA_decode, decode_encodePolynomial, decode_encodePolynomial,
    coeff_basePolynomial, coeff_basePolynomial]
  have hr := coefficient_zero_parameter_cleared f p
    (fun n => by simpa using hp.1 (-(n:ℤ))) (-D p k) n
  rw [hr]
  ring

theorem residual_connection_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (x : SeqSpace) (b s : ℂ)
    (hs : ‖s‖ ≤ (1/1000:ℝ))
    (hx : seqA p k x-b • seqJ x+s • seqV f p x=0) (hx0 : x 0=1)
    (hval : (∑' n, decode x n) ≠ 0) :
    IsConnectionCoefficient f p (-D p k+b) s 0 := by
  have he := residual_coefficients f p hp k x b s hx hx0
  apply fast_frobenius_connection_zero f p hp _ _ hs ‖x‖ (norm_nonneg _)
  · intro n
    rw [← he n]
    exact decode_bound x n
  · simpa only [frobeniusSum, one_pow, mul_one, ← he] using hval

end Heun
#print axioms Heun.seqA_encoded_base_zero
#print axioms Heun.residual_connection_zero

#print axioms Heun.residual_coefficients
