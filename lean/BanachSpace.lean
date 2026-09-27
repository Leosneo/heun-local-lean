import BaseEigenfunction
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Mul

noncomputable section
open scoped Topology
open Filter
namespace Heun

abbrev SeqSpace := BoundedContinuousFunction ℕ ℂ

def seqWeight (n : ℕ) : ℂ := ((n : ℂ) + 1)^2 * 2^n

theorem seqWeight_ne_zero (n : ℕ) : seqWeight n ≠ 0 := by
  unfold seqWeight
  have h : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact mul_ne_zero (pow_ne_zero _ h) (pow_ne_zero _ (by norm_num))

def decode (x : SeqSpace) (n : ℕ) : ℂ := x n / seqWeight n

theorem decode_bound (x : SeqSpace) (n : ℕ) :
    ‖decode x n‖ ≤ ‖x‖ * (1/2 : ℝ)^n := by
  have hn : (1 : ℝ) ≤ ((n : ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ), Nat.cast_nonneg (α := ℝ) n]
  have hw : ‖seqWeight n‖ = ((n : ℝ)+1)^2 * 2^n := by
    simp only [seqWeight, norm_mul, norm_pow]
    rw [← Nat.cast_add_one, Complex.norm_natCast]
    norm_num
  rw [decode, norm_div, hw]
  calc
    _ ≤ ‖x‖ / (2:ℝ)^n := div_le_div₀ (norm_nonneg _) (x.norm_coe_le_norm n)
      (by positivity) (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n])
    _ = _ := by rw [div_pow]; simp [div_eq_mul_inv]

def seqConst (c : ℂ) : SeqSpace := BoundedContinuousFunction.const ℕ c

@[simp] theorem seqConst_apply (c : ℂ) (n : ℕ) : seqConst c n = c := rfl

def seqInvNat : SeqSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n : ℕ => ((n:ℂ)+1)⁻¹) 1 (by
      intro n
      simp only [norm_inv]
      have hn : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by rw [← Nat.cast_add_one, Complex.norm_natCast]; simp
      rw [hn]
      exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))

@[simp] theorem seqInvNat_apply (n : ℕ) : seqInvNat n = ((n:ℂ)+1)⁻¹ := rfl

def seqUp : SeqSpace →L[ℂ] SeqSpace where
  toFun x := x.compContinuous ⟨fun n => n+1, continuous_of_discreteTopology⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := BoundedContinuousFunction.continuous_compContinuous _

@[simp] theorem seqUp_apply (x : SeqSpace) (n : ℕ) : seqUp x n = x (n+1) := rfl

def seqDown : SeqSpace →L[ℂ] SeqSpace :=
  LinearMap.mkContinuous
    { toFun := fun (x : SeqSpace) => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun n : ℕ => match n with | 0 => (0:ℂ) | m+1 => x m) ‖x‖ (by
          intro n; cases n with
          | zero => simp
          | succ n => exact x.norm_coe_le_norm n)
      map_add' := by intros; ext n; cases n <;> simp
      map_smul' := by intros; ext n; cases n <;> simp }
    1 (by
      intro x
      simp only [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
      intro n
      cases n with
      | zero => simp
      | succ n => exact x.norm_coe_le_norm n)

@[simp] theorem seqDown_zero (x : SeqSpace) : seqDown x 0 = 0 := rfl
@[simp] theorem seqDown_succ (x : SeqSpace) (n : ℕ) : seqDown x (n+1) = x n := rfl

def seqDiag (p : Parameters) (k : ℕ) : SeqSpace :=
  -1 + seqConst (3-p.gamma-p.delta) * seqInvNat +
    seqConst (D p k+p.gamma+p.delta-2) * seqInvNat^2

def seqUpper (p : Parameters) : SeqSpace :=
  seqConst (1/2) * (1-seqUp seqInvNat) *
    (1+seqConst (p.gamma-2)*seqUp seqInvNat)

def seqVdiag (f : Family) (p : Parameters) : SeqSpace :=
  match f with
  | .heun => -(1+seqConst (p.gamma+p.epsilon-3)*seqInvNat +
      seqConst (2-p.gamma-p.epsilon)*seqInvNat^2)
  | .confluent => -(seqInvNat-seqInvNat^2)
  | .reduced => 0

def seqVlower (f : Family) (p : Parameters) : SeqSpace :=
  match f with
  | .heun => seqConst 2*(1+seqConst (p.alpha-1)*seqInvNat)*
      (1+seqConst (p.beta-1)*seqInvNat)
  | .confluent => seqConst 2*(seqInvNat+seqConst (p.alpha-1)*seqInvNat^2)
  | .reduced => seqConst 2*seqInvNat^2

def seqA (p : Parameters) (k : ℕ) : SeqSpace →L[ℂ] SeqSpace :=
  ContinuousLinearMap.mul ℂ SeqSpace (seqDiag p k) +
    (ContinuousLinearMap.mul ℂ SeqSpace (seqUpper p)).comp seqUp

def seqV (f : Family) (p : Parameters) : SeqSpace →L[ℂ] SeqSpace :=
  ContinuousLinearMap.mul ℂ SeqSpace (seqVdiag f p) +
    seqDown.comp (ContinuousLinearMap.mul ℂ SeqSpace (seqVlower f p))

def seqJ : SeqSpace →L[ℂ] SeqSpace :=
  ContinuousLinearMap.mul ℂ SeqSpace (seqInvNat^2)

end Heun
