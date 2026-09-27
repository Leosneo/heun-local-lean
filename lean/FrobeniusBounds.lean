import HeunProblem

/-! Uniform tail estimates for the literal Heun coefficient recurrence.
These estimates hold for complex parameters in all three families.
-/
noncomputable section
namespace Heun

def ParameterBound (p : Parameters) (M : ℝ) : Prop :=
  1 ≤ M ∧ ‖p.gamma‖ ≤ M ∧ ‖p.delta‖ ≤ M ∧
    ‖p.epsilon‖ ≤ M ∧ ‖p.alpha‖ ≤ M ∧ ‖p.beta‖ ≤ M

theorem exists_parameterBound (p : Parameters) : ∃ M, ParameterBound p M := by
  refine ⟨1 + ‖p.gamma‖ + ‖p.delta‖ + ‖p.epsilon‖ + ‖p.alpha‖ + ‖p.beta‖, ?_⟩
  have hγ := norm_nonneg p.gamma
  have hδ := norm_nonneg p.delta
  have hε := norm_nonneg p.epsilon
  have hα := norm_nonneg p.alpha
  have hβ := norm_nonneg p.beta
  unfold ParameterBound
  constructor <;> (try constructor) <;> (try constructor) <;>
    (try constructor) <;> (try constructor) <;> linarith

theorem norm_shifted_nat_le (m : ℕ) (a b : ℂ) :
    ‖(m : ℂ) - 1 + a + b‖ ≤ (m : ℝ) + 1 + ‖a‖ + ‖b‖ := by
  calc
    _ ≤ ‖(m : ℂ) - 1 + a‖ + ‖b‖ := norm_add_le _ _
    _ ≤ ‖(m : ℂ) - 1‖ + ‖a‖ + ‖b‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖(m : ℂ)‖ + ‖(1 : ℂ)‖ + ‖a‖ + ‖b‖ := by
      gcongr; exact norm_sub_le _ _
    _ = _ := by simp

theorem norm_D_bound (p : Parameters) {M : ℝ} (hM : ParameterBound p M) (m : ℕ) :
    ‖D p m‖ ≤ (m : ℝ) * ((m : ℝ) + 3 * M) := by
  rw [D, norm_mul, Complex.norm_natCast]
  gcongr
  have h := norm_shifted_nat_le m p.gamma p.delta
  rcases hM with ⟨h1,hγ,hδ,hε,hα,hβ⟩
  linarith

theorem norm_E_bound (f : Family) (p : Parameters) {M : ℝ}
    (hM : ParameterBound p M) (m : ℕ) :
    ‖E f p m‖ ≤ (m : ℝ) * ((m : ℝ) + 3 * M) := by
  have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases hM with ⟨h1,hγ,hδ,hε,hα,hβ⟩
  cases f with
  | heun =>
    rw [E, norm_mul, Complex.norm_natCast]
    gcongr
    have h := norm_shifted_nat_le m p.gamma p.epsilon
    linarith
  | confluent => simp only [E, Complex.norm_natCast]; nlinarith
  | reduced => simp only [E, norm_zero]; positivity

theorem norm_F_bound (f : Family) (p : Parameters) {M : ℝ}
    (hM : ParameterBound p M) (m : ℕ) :
    ‖F f p m‖ ≤ ((m : ℝ) + 2 * M) ^ 2 := by
  have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases hM with ⟨h1,hγ,hδ,hε,hα,hβ⟩
  have ha : ‖(m : ℂ) - 1 + p.alpha‖ ≤ (m : ℝ) + 2*M := by
    have h := norm_shifted_nat_le m p.alpha 0
    simp only [add_zero, norm_zero] at h
    linarith
  have hb : ‖(m : ℂ) - 1 + p.beta‖ ≤ (m : ℝ) + 2*M := by
    have h := norm_shifted_nat_le m p.beta 0
    simp only [add_zero, norm_zero] at h
    linarith
  cases f with
  | heun => simpa only [F, norm_mul, pow_two] using mul_le_mul ha hb (norm_nonneg _) (by positivity)
  | confluent => simp only [F]; nlinarith
  | reduced => simp only [F, norm_one]; nlinarith

theorem denominator_norm_lower (p : Parameters) {M : ℝ}
    (hM : ParameterBound p M) (m : ℕ) :
    ((m : ℝ) + 1) * ((m : ℝ) - M) ≤
      ‖((m : ℂ) + 1) * ((m : ℂ) + p.gamma)‖ := by
  have hγ := hM.2.1
  have h := norm_sub_norm_le ((m : ℂ) + p.gamma) p.gamma
  have hn : (m : ℝ) - M ≤ ‖(m : ℂ) + p.gamma‖ := by
    have ht := norm_add_le ((m : ℂ) + p.gamma) (-p.gamma)
    simp only [add_neg_cancel_right, norm_neg, Complex.norm_natCast] at ht
    linarith
  rw [norm_mul]
  have hc : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
    norm_cast
  rw [hc]
  gcongr

theorem recurrence_tail_bounds (f : Family) (p : Parameters) {M : ℝ}
    (hM : ParameterBound p M) (B s : ℂ) (hB : ‖B‖ ≤ M)
    (hs : ‖s‖ ≤ 1/100) (m : ℕ) (hm : 100*M ≤ (m : ℝ)) :
    ‖B + D p m + s * E f p m‖ ≤
      (9/8 : ℝ) * ‖((m : ℂ)+1)*((m : ℂ)+p.gamma)‖ ∧
    ‖s * F f p m‖ ≤
      (1/8 : ℝ) * ‖((m : ℂ)+1)*((m : ℂ)+p.gamma)‖ := by
  have h1 := hM.1
  have hn : 1 ≤ (m : ℝ) := by linarith
  have hn0 : 0 ≤ (m : ℝ) := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hD := norm_D_bound p hM m
  have hE := norm_E_bound f p hM m
  have hF := norm_F_bound f p hM m
  have hd := denominator_norm_lower p hM m
  have hd' : (99/100 : ℝ) * (m : ℝ)^2 ≤
      ‖((m : ℂ)+1)*((m : ℂ)+p.gamma)‖ := by
    have hprod : (m : ℝ) * M ≤ (m : ℝ)^2/100 := by nlinarith
    nlinarith
  have hm2 : M ≤ (m : ℝ)^2/100 := by nlinarith
  have hdnum : (m : ℝ) * ((m : ℝ)+3*M) ≤ (103/100 : ℝ)*(m : ℝ)^2 := by
    nlinarith
  have hfnum : ((m : ℝ)+2*M)^2 ≤ (102/100 : ℝ)^2*(m : ℝ)^2 := by
    have hlin : 0 ≤ (m : ℝ)+2*M := by positivity
    have hlin' : (m : ℝ)+2*M ≤ (102/100 : ℝ)*(m : ℝ) := by linarith
    nlinarith
  constructor
  · have ha : ‖B + D p m + s * E f p m‖ ≤ M +
        (101/100 : ℝ) * ((m : ℝ)*((m : ℝ)+3*M)) := by
      calc
        _ ≤ ‖B‖ + ‖D p m‖ + ‖s‖ * ‖E f p m‖ := by
          calc
            _ ≤ ‖B + D p m‖ + ‖s * E f p m‖ := norm_add_le _ _
            _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le _ _
        _ ≤ M + (m : ℝ)*((m : ℝ)+3*M) + (1/100 : ℝ)*((m : ℝ)*((m : ℝ)+3*M)) := by
          gcongr
        _ = _ := by ring
    nlinarith
  · have hb : ‖s * F f p m‖ ≤ (1/100 : ℝ)*((m : ℝ)+2*M)^2 := by
      rw [norm_mul]
      gcongr
    nlinarith

theorem coefficientPair_uniform_bound (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) {M : ℝ} (hM : ParameterBound p M) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B s : ℂ, ‖B‖ ≤ M → ‖s‖ ≤ 1/100 →
      ‖(coefficientPair f p B s N).1‖ ≤ C ∧
      ‖(coefficientPair f p B s N).2‖ ≤ C := by
  induction N with
  | zero => exact ⟨1, by norm_num, by intros; simp [coefficientPair]⟩
  | succ N ih =>
    obtain ⟨C,hC,hbound⟩ := ih
    let A : ℝ := M + ‖D p N‖ + (1/100 : ℝ)*‖E f p N‖
    let T : ℝ := (1/100 : ℝ)*‖F f p N‖
    let d : ℝ := ‖((N : ℂ)+1)*((N : ℂ)+p.gamma)‖
    have hd : 0 < d := norm_pos_iff.mpr (recurrence_denominator_ne_zero_of_nonresonant hgamma N)
    have hA : 0 ≤ A := by dsimp [A]; have := hM.1; positivity
    have hT : 0 ≤ T := by dsimp [T]; positivity
    let K : ℝ := (A+T)*C/d
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨C+K+1, by positivity, ?_⟩
    intro B s hB hs
    obtain ⟨hb1,hb2⟩ := hbound B s hB hs
    have hcoef : ‖B + D p N + s * E f p N‖ ≤ A := by
      calc
        _ ≤ ‖B‖ + ‖D p N‖ + ‖s‖*‖E f p N‖ := by
          calc
            _ ≤ ‖B + D p N‖ + ‖s * E f p N‖ := norm_add_le _ _
            _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le _ _
        _ ≤ A := by dsimp [A]; gcongr
    have hprev : ‖s * F f p N‖ ≤ T := by rw [norm_mul]; dsimp [T]; gcongr
    constructor
    · change ‖(coefficientPair f p B s N).2‖ ≤ _
      linarith
    · change ‖((B+D p N+s*E f p N)*(coefficientPair f p B s N).2 -
          s*F f p N*(coefficientPair f p B s N).1) /
          (((N : ℂ)+1)*((N : ℂ)+p.gamma))‖ ≤ _
      rw [norm_div]
      have hnum : ‖(B+D p N+s*E f p N)*(coefficientPair f p B s N).2 -
          s*F f p N*(coefficientPair f p B s N).1‖ ≤ (A+T)*C := by
        calc
          _ ≤ ‖B+D p N+s*E f p N‖*‖(coefficientPair f p B s N).2‖ +
            ‖s*F f p N‖*‖(coefficientPair f p B s N).1‖ := by
              simpa only [norm_mul] using norm_sub_le
                ((B+D p N+s*E f p N)*(coefficientPair f p B s N).2)
                (s*F f p N*(coefficientPair f p B s N).1)
          _ ≤ A*C+T*C := by gcongr
          _ = _ := by ring
      have hquot : ‖(B+D p N+s*E f p N)*(coefficientPair f p B s N).2 -
          s*F f p N*(coefficientPair f p B s N).1‖ / d ≤ K :=
        div_le_div_of_nonneg_right hnum hd.le
      change _ / d ≤ _
      linarith

theorem coefficient_prefix_uniform_bound (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) {M : ℝ} (hM : ParameterBound p M) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B s : ℂ, ‖B‖ ≤ M → ‖s‖ ≤ 1/100 →
      ∀ n ≤ N, ‖coefficient f p B s n‖ ≤ C := by
  induction N with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro B s hB hs n hn
    have he : n = 0 := by omega
    simp [he]
  | succ N ih =>
    obtain ⟨C,hC,hb⟩ := ih
    obtain ⟨K,hK,hk⟩ := coefficientPair_uniform_bound f p hgamma hM (N+1)
    refine ⟨C+K, by positivity, ?_⟩
    intro B s hB hs n hn
    by_cases hn' : n ≤ N
    · have h := hb B s hB hs n hn'; linarith
    · have he : n=N+1 := by omega
      subst n
      have h := (hk B s hB hs).2
      change ‖coefficient f p B s (N+1)‖ ≤ K at h
      linarith

theorem coefficient_tail_norm (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) {M : ℝ} (hM : ParameterBound p M)
    (B s : ℂ) (hB : ‖B‖ ≤ M) (hs : ‖s‖ ≤ 1/100)
    (n : ℕ) (hn : 100*M ≤ ((n+1 : ℕ) : ℝ)) :
    ‖coefficient f p B s (n+2)‖ ≤
      (9/8 : ℝ)*‖coefficient f p B s (n+1)‖ +
      (1/8 : ℝ)*‖coefficient f p B s n‖ := by
  obtain ⟨ha,hb⟩ := recurrence_tail_bounds f p hM B s hB hs (n+1) hn
  let d := ‖(((n+1 : ℕ) : ℂ)+1)*(((n+1 : ℕ) : ℂ)+p.gamma)‖
  have hd : 0 < d := norm_pos_iff.mpr (recurrence_denominator_ne_zero_of_nonresonant hgamma (n+1))
  rw [coefficient_recurrence, norm_div]
  change _ / d ≤ _
  calc
    _ ≤ (‖B+D p (n+1)+s*E f p (n+1)‖*‖coefficient f p B s (n+1)‖ +
      ‖s*F f p (n+1)‖*‖coefficient f p B s n‖) / d := by
        gcongr
        simpa only [norm_mul] using norm_sub_le
          ((B+D p (n+1)+s*E f p (n+1))*coefficient f p B s (n+1))
          (s*F f p (n+1)*coefficient f p B s n)
    _ ≤ (((9/8 : ℝ)*d)*‖coefficient f p B s (n+1)‖ +
      ((1/8 : ℝ)*d)*‖coefficient f p B s n‖) / d := by gcongr
    _ = _ := by field_simp

/-- A uniform positive-radius convergence majorant for the actual complex
Heun recurrence. The bound is simultaneous in B and s on the specified box. -/
theorem coefficient_geometric_bound (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) {M : ℝ} (hM : ParameterBound p M) :
    ∃ C : ℝ, 0 < C ∧ ∀ B s : ℂ, ‖B‖ ≤ M → ‖s‖ ≤ 1/100 →
      ∀ n, ‖coefficient f p B s n‖ ≤ C * (5/4 : ℝ)^n := by
  obtain ⟨N,hN⟩ := exists_nat_ge (100*M)
  obtain ⟨C,hC,hprefix⟩ := coefficient_prefix_uniform_bound f p hgamma hM (N+1)
  refine ⟨C,hC,?_⟩
  intro B s hB hs n
  have hbase : ∀ n ≤ N+1, ‖coefficient f p B s n‖ ≤ C*(5/4 : ℝ)^n := by
    intro n hn
    have h := hprefix B s hB hs n hn
    have hpow : 1 ≤ (5/4 : ℝ)^n := one_le_pow₀ (by norm_num)
    nlinarith
  induction n using Nat.twoStepInduction with
  | zero => exact hbase 0 (by omega)
  | one => exact hbase 1 (by omega)
  | more n ih0 ih1 =>
    by_cases hn : n+2 ≤ N+1
    · exact hbase (n+2) hn
    · have hnn : N ≤ n+1 := by omega
      have htail := coefficient_tail_norm f p hgamma hM B s hB hs n
        (hN.trans (by exact_mod_cast hnn))
      have ht : ‖coefficient f p B s (n+2)‖ ≤
          (9/8 : ℝ)*(C*(5/4 : ℝ)^(n+1)) + (1/8 : ℝ)*(C*(5/4 : ℝ)^n) := by
        linarith
      simp only [pow_succ] at ht ⊢
      have hpos : 0 ≤ C*(5/4 : ℝ)^n := by positivity
      nlinarith

end Heun
#print axioms Heun.coefficient_geometric_bound
