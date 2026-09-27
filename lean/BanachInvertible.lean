import BanachInverse
import BanachOperators
import BanachHead
import BaseEigenfunction

noncomputable section
namespace Heun

def seqBase (f : Family) (p : Parameters) (k : ℕ) : SeqSpace :=
  encodePolynomial (basePolynomial f p k)

def seqBaseResidual (f : Family) (p : Parameters) (k : ℕ) : SeqSpace :=
  seqJ (seqBase f p k)

theorem seqBaseResidual_apply (f : Family) (p : Parameters) (k n : ℕ) :
    seqBaseResidual f p k n = (2:ℂ)^n*(basePolynomial f p k).coeff n := by
  change (seqInvNat n)^2 * (seqWeight n*(basePolynomial f p k).coeff n) = _
  rw [seqInvNat_apply]
  dsimp [seqWeight]
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

@[simp] theorem seqBase_zero (f : Family) (p : Parameters) (k : ℕ) :
    seqBase f p k 0 = 1 := by
  simp [seqBase, seqWeight, basePolynomial_normalized]

def borderT (f : Family) (p : Parameters) (k : ℕ) :
    (SeqSpace × ℂ) →L[ℂ] (SeqSpace × ℂ) :=
  ((seqA p k).comp (ContinuousLinearMap.fst ℂ SeqSpace ℂ) -
    (ContinuousLinearMap.snd ℂ SeqSpace ℂ).smulRight (seqBaseResidual f p k)).prod
    ((BoundedContinuousFunction.evalCLM ℂ 0).comp (ContinuousLinearMap.fst ℂ SeqSpace ℂ))

@[simp] theorem borderT_apply (f : Family) (p : Parameters) (k : ℕ) (x : SeqSpace × ℂ) :
    borderT f p k x = (seqA p k x.1-x.2 • seqBaseResidual f p k, x.1 0) := rfl

theorem borderT_bijective (f : Family) (p : Parameters) (hp : Admissible f p) (k : ℕ) :
    Function.Bijective (borderT f p k) := by
  obtain ⟨L, hL, hb⟩ := seq_tail_bounds p k
  have htail : ∀ y : SeqSpace, ∃ x : SeqSpace,
      (∀ n, k<n → seqDiag p k n*x n+seqUpper p n*x (n+1)=y n) ∧
      (∀ z : SeqSpace,
        (∀ n, k<n → seqDiag p k n*z n+seqUpper p n*z (n+1)=y n) →
        ∀ n,k<n → z n=x n) := by
    intro y
    exact bounded_bidiagonal_tail_solve k L (seqDiag p k) (seqUpper p) 2 (3/4)
      (by norm_num) (by norm_num) (by norm_num)
      (fun n hn => fun he => (by omega : n≠k) ((seqDiag_zero_iff hp k n).mp he))
      (fun n hn => (hb n hn).1) (fun n hn => (hb n hn).2) y
  have hhead := resonant_head_bijection (seqDiag p k) (seqUpper p)
    (seqBaseResidual f p k) k ((seqDiag_zero_iff hp k k).mpr rfl)
    (fun n _ => seqUpper_ne_zero hp n)
    (by
      rw [seqBaseResidual_apply]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (basePolynomial_top_ne_zero f p hp k))
    (by
      intro n hn
      rw [seqBaseResidual_apply, coeff_basePolynomial, coefficient_base_root f p hn]
      simp) htail
  have heq (x : SeqSpace × ℂ) (y : SeqSpace × ℂ) :
      borderT f p k x = y ↔
        (∀ n, seqDiag p k n*x.1 n+seqUpper p n*x.1 (n+1)-x.2*seqBaseResidual f p k n=y.1 n) ∧
        x.1 0=y.2 := by
    rw [Prod.ext_iff]
    change (seqA p k x.1-x.2 • seqBaseResidual f p k = y.1) ∧ x.1 0=y.2 ↔ _
    apply and_congr_left
    intro _
    constructor
    · intro he n
      exact congrArg (fun v : SeqSpace => v n) he
    · intro he
      ext n
      exact he n
  constructor
  · intro x z he
    obtain ⟨w, hw, hu⟩ := hhead (borderT f p k x).1 (borderT f p k x).2
    exact (hu x ((heq x _).mp rfl)).trans
      (hu z ((heq z _).mp he.symm)).symm
  · intro y
    obtain ⟨x, hx, _⟩ := hhead y.1 y.2
    exact ⟨x, (heq x y).mpr hx⟩

theorem borderT_isInvertible (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) : (borderT f p k).IsInvertible := by
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr (borderT_bijective f p hp k)
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

#print axioms borderT_isInvertible
end Heun
