import BanachSpace

noncomputable section
open scoped BigOperators
namespace Heun

/-- A unique bounded tail, a single resonant row, and a forward-solvable finite
head give a bijective bordered recurrence. -/
theorem resonant_head_bijection (a b P : ℕ → ℂ) (k : ℕ)
    (hak : a k = 0) (hb : ∀ n, n < k → b n ≠ 0) (hPk : P k ≠ 0)
    (hP : ∀ n, k < n → P n = 0)
    (htail : ∀ y : SeqSpace, ∃ x : SeqSpace,
      (∀ n, k < n → a n*x n+b n*x (n+1)=y n) ∧
      (∀ z : SeqSpace, (∀ n, k<n → a n*z n+b n*z (n+1)=y n) →
        ∀ n, k<n → z n=x n)) :
    ∀ y : SeqSpace, ∀ t : ℂ, ∃! xc : SeqSpace × ℂ,
      (∀ n, a n*xc.1 n+b n*xc.1 (n+1)-xc.2*P n=y n) ∧ xc.1 0=t := by
  intro y t
  obtain ⟨v,hv,hvu⟩ := htail y
  let c := (b k*v (k+1)-y k)/P k
  let H : ℕ → ℂ := fun n => Nat.rec t (fun i hi => (y i+c*P i-a i*hi)/b i) n
  have Hzero : H 0=t := rfl
  have Hstep (n : ℕ) : H (n+1)=(y n+c*P n-a n*H n)/b n := rfl
  let S := ∑ i ∈ Finset.range (k+1), ‖H i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i hi => norm_nonneg _)
  have hHS (n : ℕ) (hn : n ≤ k) : ‖H n‖ ≤ S := by
    exact Finset.single_le_sum (fun i hi => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  let x : SeqSpace := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => if n≤k then H n else v n) (‖v‖+S) (by
      intro n
      dsimp only
      split_ifs with hn
      · exact (hHS n hn).trans (le_add_of_nonneg_left (norm_nonneg v))
      · exact (v.norm_coe_le_norm n).trans (le_add_of_nonneg_right hS))
  have xhead (n : ℕ) (hn : n ≤ k) : x n=H n := by simp [x,hn]
  have xtail (n : ℕ) (hn : k<n) : x n=v n := by simp [x, show ¬n≤k by omega]
  have hxeq : ∀ n, a n*x n+b n*x (n+1)-c*P n=y n := by
    intro n
    rcases lt_trichotomy n k with hn|hn|hn
    · rw [xhead n (by omega), xhead (n+1) (by omega), Hstep]
      have hb' := hb n hn
      field_simp
      ring
    · subst n
      rw [hak, zero_mul, zero_add, xtail (k+1) (by omega)]
      dsimp [c]
      field_simp
      ring
    · rw [xtail n hn, xtail (n+1) (by omega), hP n hn, mul_zero, sub_zero]
      exact hv n hn
  refine ⟨(x,c), ⟨hxeq, ?_⟩, ?_⟩
  · rw [xhead 0 (by omega), Hzero]
  · rintro ⟨z,d⟩ ⟨hzeq,hz0⟩
    have hzTail : ∀ n, k<n → z n=v n := by
      apply hvu z
      intro n hn
      have h := hzeq n
      simpa [hP n hn] using h
    have hdc : d=c := by
      have h := hzeq k
      rw [hak, zero_mul, zero_add, hzTail (k+1) (by omega)] at h
      apply (eq_div_iff hPk).mpr
      dsimp [c] at *
      linear_combination -h
    have hzHead : ∀ n, n≤k → z n=H n := by
      intro n
      induction n with
      | zero => intro hn; exact hz0.trans Hzero.symm
      | succ n ih =>
        intro hn
        rw [Hstep]
        apply (eq_div_iff (hb n (by omega))).mpr
        have h := hzeq n
        rw [hdc, ih (by omega)] at h
        linear_combination h
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro n
      by_cases hn : n≤k
      · exact (hzHead n hn).trans (xhead n hn).symm
      · exact (hzTail n (by omega)).trans (xtail n (by omega)).symm
    · exact hdc

end Heun
#print axioms Heun.resonant_head_bijection
