import BanachSpace
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped Topology
open Filter
namespace Heun

theorem seqDiag_apply (p : Parameters) (k n : ℕ) :
    seqDiag p k n = (D p k-D p n)/((n:ℂ)+1)^2 := by
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [seqDiag, seqInvNat, seqConst, D]
  field_simp
  ring

theorem seqUpper_apply (p : Parameters) (n : ℕ) :
    seqUpper p n = ((n:ℂ)+1)*((n:ℂ)+p.gamma)/(2*((n:ℂ)+2)^2) := by
  have hn : (n:ℂ)+2 ≠ 0 := by exact_mod_cast (by omega : n+2 ≠ 0)
  simp [seqUpper, seqInvNat, seqConst, show (n:ℂ)+1+1=(n:ℂ)+2 by ring]
  field_simp
  ring

@[simp] theorem seqA_apply (p : Parameters) (k : ℕ) (x : SeqSpace) (n : ℕ) :
    seqA p k x n = seqDiag p k n*x n+seqUpper p n*x (n+1) := rfl

theorem seqDiag_zero_iff {f : Family} {p : Parameters} (hp : Admissible f p)
    (k n : ℕ) : seqDiag p k n = 0 ↔ n=k := by
  rw [seqDiag_apply, div_eq_zero_iff]
  have hn : ((n:ℂ)+1)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
  simp only [hn, or_false, sub_eq_zero]
  exact ⟨fun h => (D_injective hp h).symm, fun h => by subst n; rfl⟩

theorem seqUpper_ne_zero {f : Family} {p : Parameters} (hp : Admissible f p)
    (n : ℕ) : seqUpper p n ≠ 0 := by
  rw [seqUpper_apply]
  exact div_ne_zero (recurrence_denominator_ne_zero hp n)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast (by omega : n+2 ≠ 0))))

theorem seqInvNat_tendsto : Tendsto (fun n => seqInvNat n) atTop (𝓝 (0:ℂ)) := by
  simpa only [seqInvNat_apply, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))

theorem seqDiag_tendsto (p : Parameters) (k : ℕ) :
    Tendsto (fun n => seqDiag p k n) atTop (𝓝 (-1:ℂ)) := by
  have h := ((tendsto_const_nhds (x := (-1:ℂ))).add
    ((tendsto_const_nhds (x := 3-p.gamma-p.delta)).mul seqInvNat_tendsto)).add
    ((tendsto_const_nhds (x := D p k+p.gamma+p.delta-2)).mul (seqInvNat_tendsto.pow 2))
  simpa [seqDiag, seqConst] using (h : Tendsto
    (fun n => -1+(3-p.gamma-p.delta)*seqInvNat n+
      (D p k+p.gamma+p.delta-2)*seqInvNat n^2) atTop _)

theorem seqUpper_tendsto (p : Parameters) :
    Tendsto (fun n => seqUpper p n) atTop (𝓝 (1/2:ℂ)) := by
  have ht : Tendsto (fun n => seqInvNat (n+1)) atTop (𝓝 (0:ℂ)) :=
    seqInvNat_tendsto.comp (tendsto_add_atTop_nat 1)
  have h := ((tendsto_const_nhds (x := (1/2:ℂ))).mul ((tendsto_const_nhds (x := (1:ℂ))).sub ht)).mul
    ((tendsto_const_nhds (x := (1:ℂ))).add ((tendsto_const_nhds (x := p.gamma-2)).mul ht))
  simpa [seqUpper, seqConst] using (h : Tendsto
    (fun n => (1/2:ℂ)*(1-seqInvNat (n+1))*(1+(p.gamma-2)*seqInvNat (n+1))) atTop _)

theorem seq_tail_bounds (p : Parameters) (k : ℕ) :
    ∃ L : ℕ, k<L ∧ ∀ n, L≤n →
      ‖(seqDiag p k n)⁻¹‖ ≤ 2 ∧
      ‖seqUpper p n / seqDiag p k n‖ ≤ (3/4:ℝ) := by
  have hi := (seqDiag_tendsto p k).inv₀ (by norm_num : (-1:ℂ) ≠ 0)
  have hr := (seqUpper_tendsto p).div (seqDiag_tendsto p k) (by norm_num)
  have he1 : ∀ᶠ n in atTop, ‖(seqDiag p k n)⁻¹‖ < (2:ℝ) := by
    apply (hi.norm).eventually (gt_mem_nhds _)
    norm_num
  have he2 : ∀ᶠ n in atTop, ‖seqUpper p n / seqDiag p k n‖ < (3/4:ℝ) := by
    apply (hr.norm).eventually (gt_mem_nhds _)
    norm_num
  obtain ⟨L,hL⟩ := eventually_atTop.mp (he1.and he2)
  refine ⟨max L (k+1), by omega, ?_⟩
  intro n hn
  exact ⟨(hL n (by omega)).1.le, (hL n (by omega)).2.le⟩

def encodePolynomial (q : Polynomial ℂ) : SeqSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => seqWeight n*q.coeff n)
    (∑ i ∈ Finset.range (q.natDegree+1), ‖seqWeight i*q.coeff i‖) (by
      intro n
      by_cases hn : n≤q.natDegree
      · exact Finset.single_le_sum (s := Finset.range (q.natDegree+1)) (a := n) (f := fun i => ‖seqWeight i*q.coeff i‖) (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree<n)]
        positivity)

@[simp] theorem encodePolynomial_apply (q : Polynomial ℂ) (n : ℕ) :
    encodePolynomial q n = seqWeight n*q.coeff n := rfl

@[simp] theorem decode_encodePolynomial (q : Polynomial ℂ) (n : ℕ) :
    decode (encodePolynomial q) n = q.coeff n := by
  simp [decode, seqWeight_ne_zero]

end Heun
