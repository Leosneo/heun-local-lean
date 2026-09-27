import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! The elementary ℓ¹ estimate behind the proposed Banach tail inverse.
This is not the construction of the Banach inverse or the final conjecture. -/
noncomputable section
namespace Heun

def normalizedTailShift (a u : ℕ → ℂ) (n : ℕ) : ℂ := a n * u (n + 1)

theorem normalizedTailShift_summable {a u : ℕ → ℂ} {q : ℝ}
    (hq : 0 ≤ q) (ha : ∀ n, ‖a n‖ ≤ q)
    (hu : Summable (fun n => ‖u n‖)) :
    Summable (fun n => ‖normalizedTailShift a u n‖) := by
  have hs : Summable (fun n => ‖u (n + 1)‖) := (summable_nat_add_iff 1).mpr hu
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left q)
  intro n
  exact (norm_mul (a n) (u (n + 1))).trans_le
    (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _))

theorem normalizedTailShift_l1_bound {a u : ℕ → ℂ} {q : ℝ}
    (hq : 0 ≤ q) (ha : ∀ n, ‖a n‖ ≤ q)
    (hu : Summable (fun n => ‖u n‖)) :
    (∑' n, ‖normalizedTailShift a u n‖) ≤ q * (∑' n, ‖u n‖) := by
  have hs : Summable (fun n => ‖u (n + 1)‖) := (summable_nat_add_iff 1).mpr hu
  calc
    _ ≤ ∑' n, q * ‖u (n + 1)‖ :=
      (normalizedTailShift_summable hq ha hu).tsum_le_tsum
        (fun n => (norm_mul (a n) (u (n + 1))).trans_le
          (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _))) (hs.mul_left q)
    _ = q * ∑' n, ‖u (n + 1)‖ := tsum_mul_left
    _ ≤ q * ∑' n, ‖u n‖ := by
      apply mul_le_mul_of_nonneg_left _ hq
      have he := hu.sum_add_tsum_nat_add 1
      simp only [Finset.sum_range_one] at he
      linarith [norm_nonneg (u 0)]

#print axioms normalizedTailShift_l1_bound
end Heun
