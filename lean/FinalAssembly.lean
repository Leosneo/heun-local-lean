import AnalyticTaylorBridge
import BanachRecurrence
import BanachInverse

/-! Scalar convergence assembly with the literal source indexing.
The strongest theorem derives polynomial jet support, finite-root derivative
matching and the exact convergence sum from an analytic encoded eigenbranch
and its eventual identity with the literal coefficient recurrence. Earlier
helpers retain explicit intermediate premises. This module itself does not
assert `LiteratureConjecture`; its existence and connection clauses are
assembled in the final completion module. -/
noncomputable section
open scoped Topology
open Filter
namespace Heun

/-- The positive-order Taylor series of an analytic scalar germ converges
locally to the germ minus its constant term. -/
theorem analytic_positive_taylor_hasSum {b : ℂ → ℂ} (hb : AnalyticAt ℂ b 0) :
    ∀ᶠ s : ℂ in 𝓝 0,
      HasSum (fun j : ℕ => iteratedDeriv (j + 1) b 0 /
        ((j + 1).factorial : ℂ) * s ^ (j + 1)) (b s - b 0) := by
  have he := hasFPowerSeriesAt_iff.mp hb.hasFPowerSeriesAt
  filter_upwards [he] with s hs
  have hs' : HasSum (fun j : ℕ => iteratedDeriv j b 0 /
      (j.factorial : ℂ) * s ^ j) (b s) := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      zero_add, mul_comm] using hs
  have ht := (hasSum_nat_add_iff' 1).mpr hs'
  simpa using ht

/-- This helper preserves the source's signs and truncation index exactly.
Derivative matching is explicit, rather than being disguised as convergence. -/
theorem final_hasSum_of_derivative_matching {p : Parameters}
    {k : ℕ} {roots : ℕ → ℂ → ℂ} {b : ℂ → ℂ}
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 = -D p k)
    (hmatch : ∀ j : ℕ,
      iteratedDeriv (j + 1) (roots (k + (j + 1) + 1)) 0 =
      iteratedDeriv (j + 1) b 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 4 ∧ ∀ s : ℂ, ‖s‖ < r →
      HasSum (fun j : ℕ =>
        -finiteRootTaylor roots (k + (j + 1) + 1) (j + 1) * s ^ (j + 1))
        (b s + D p k) := by
  have he := analytic_positive_taylor_hasSum hb
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min δ (1 / 8), lt_min hδ (by norm_num), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · intro s hs
    have hsδ : dist s 0 < δ := by
      simpa only [dist_zero_right] using lt_of_lt_of_le hs (min_le_left _ _)
    have ht := hball hsδ
    simpa only [finiteRootTaylor, neg_neg, hmatch, hb0, sub_neg_eq_add] using ht

/-- A genuine analytic approximate root determines the same jet as the
exact finite root. The hypothesis concerns the finite recurrence residual,
not equality of the roots' derivatives. -/
theorem finite_root_derivative_eq_of_residual_vanishing
    {f : Family} {p : Parameters} (hp : Admissible f p)
    {k N j i : ℕ} {b t : ℂ → ℂ} (hk : k < N)
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 = -D p k)
    (ht : IsFiniteRootGerm f p k N t)
    (hzero : ∀ l ≤ j,
      iteratedDeriv l (fun s => coefficient f p (b s) s N) 0 = 0)
    (hi : i ≤ j) : iteratedDeriv i b 0 = iteratedDeriv i t 0 := by
  have hB : PowerSeries.constantCoeff (analyticTaylor b) = -D p k := by simpa using hb0
  obtain ⟨hT, hrootT⟩ := analyticTaylor_finite_root ht
  have hres : (PowerSeries.X : Series) ^ (j + 1) ∣
      formalCoefficient f p (analyticTaylor b) N := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro l hl
    rw [← analyticTaylor_coefficient f p hb N, analyticTaylor_coeff,
      hzero l (by omega), zero_div]
  have hdif : (PowerSeries.X : Series) ^ (j + 1) ∣ analyticTaylor b - analyticTaylor t := by
    apply MoriTakemura.unit_cancel_vanishing
      (formal_difference_unit hp (M := N) hB hT hk)
    rw [mul_comm, ← (formal_difference_factor f p (analyticTaylor b) (analyticTaylor t) N).2,
      hrootT, sub_zero]
    exact hres
  have he := PowerSeries.X_pow_dvd_iff.mp hdif i (by omega)
  simp only [map_sub, analyticTaylor_coeff, sub_eq_zero] at he
  exact (div_left_inj' (by exact_mod_cast Nat.factorial_ne_zero i)).mp he

/-- Convergence assembly from polynomial support of the actual analytic
branch jets. That support must be supplied by the eigenpair construction. -/
theorem final_hasSum_of_coefficient_jet_support
    {f : Family} {p : Parameters} (hp : Admissible f p)
    {k : ℕ} {roots : ℕ → ℂ → ℂ} {b : ℂ → ℂ}
    (hroots : ∀ N, k + 1 ≤ N → IsFiniteRootGerm f p k N (roots N))
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 = -D p k)
    (hsupport : ∀ l m : ℕ, k + l < m →
      iteratedDeriv l (fun s => coefficient f p (b s) s m) 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 4 ∧ ∀ s : ℂ, ‖s‖ < r →
      HasSum (fun j : ℕ =>
        -finiteRootTaylor roots (k + (j + 1) + 1) (j + 1) * s ^ (j + 1))
        (b s + D p k) := by
  apply final_hasSum_of_derivative_matching hb hb0
  intro j
  symm
  apply finite_root_derivative_eq_of_residual_vanishing hp (j := j + 1)
    (by omega) hb hb0 (hroots _ (by omega))
  · intro l hl
    exact hsupport l _ (by omega)
  · exact le_refl _

/-- A bounded sequence cannot support a nonzero homogeneous contracting
tail. This is useful for polynomial support of Banach eigenbranch jets. -/
theorem bounded_tail_zero_of_contracting_step {x : ℕ → ℂ} {L : ℕ} {q M : ℝ}
    (hq0 : 0 ≤ q) (hq : q < 1)
    (hbound : ∀ n, L ≤ n → ‖x n‖ ≤ M)
    (hstep : ∀ n, L ≤ n → ‖x n‖ ≤ q * ‖x (n + 1)‖) :
    ∀ n, L ≤ n → x n = 0 := by
  have hiter : ∀ j n : ℕ, L ≤ n → ‖x n‖ ≤ q ^ j * M := by
    intro j
    induction j with
    | zero => intro n hn; simpa using hbound n hn
    | succ j ih =>
      intro n hn
      calc
        ‖x n‖ ≤ q * ‖x (n + 1)‖ := hstep n hn
        _ ≤ q * (q ^ j * M) := mul_le_mul_of_nonneg_left (ih (n + 1) (by omega)) hq0
        _ = q ^ (j + 1) * M := by rw [pow_succ]; ring
  intro n hn
  have hlim : Tendsto (fun j : ℕ => q ^ j * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const M
  have hz : ‖x n‖ ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall (fun j => hiter j n hn))
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))

/-- In a product jet whose second factor has no lower-order terms,
only the zeroth derivative of the first factor survives. -/
theorem iteratedDeriv_mul_of_lower_vanishing {g h : ℂ → ℂ} {j : ℕ}
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0)
    (hzero : ∀ i < j, iteratedDeriv i h 0 = 0) :
    iteratedDeriv j (fun s => g s * h s) 0 = g 0 * iteratedDeriv j h 0 := by
  rw [iteratedDeriv_fun_mul hg.contDiffAt hh.contDiffAt]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [hzero (j - i) (by have := Finset.mem_range.mp hi; omega), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

/-- The extra perturbation parameter removes the last possible term. -/
theorem iteratedDeriv_parameter_mul_of_lower_vanishing {h : ℂ → ℂ} {j : ℕ}
    (hh : AnalyticAt ℂ h 0) (hzero : ∀ i < j, iteratedDeriv i h 0 = 0) :
    iteratedDeriv j (fun s => s * h s) 0 = 0 := by
  simpa using iteratedDeriv_mul_of_lower_vanishing analyticAt_id hh hzero

/-- Above the finite propagation boundary, differentiation of the actual
recurrence leaves a homogeneous unperturbed tail. -/
theorem coefficient_jet_homogeneous_tail {f : Family} {p : Parameters}
    (hp : Admissible f p) {b : ℂ → ℂ} (hb : AnalyticAt ℂ b 0)
    {k j m : ℕ} (hb0 : b 0 = -D p k) (hm : k + j < m + 1)
    (hlower : ∀ i < j, ∀ n, k + i < n →
      iteratedDeriv i (fun s => coefficient f p (b s) s n) 0 = 0) :
    ((((m + 1 : ℕ) : ℂ) + 1) * (((m + 1 : ℕ) : ℂ) + p.gamma)) *
        iteratedDeriv j (fun s => coefficient f p (b s) s (m + 2)) 0 =
      (D p (m + 1) - D p k) *
        iteratedDeriv j (fun s => coefficient f p (b s) s (m + 1)) 0 := by
  have hc : ∀ n, AnalyticAt ℂ (fun s => coefficient f p (b s) s n) 0 := by
    intro n
    exact (coefficient_analytic f p n (0, b 0)).comp
      (f := fun s : ℂ => (s, b s)) (analyticAt_id.prod hb)
  have hd := recurrence_denominator_ne_zero hp (m + 1)
  have heq :
      (fun s => ((((m + 1 : ℕ) : ℂ) + 1) * (((m + 1 : ℕ) : ℂ) + p.gamma)) *
        coefficient f p (b s) s (m + 2)) =
      (fun s => (b s + D p (m + 1) + s * E f p (m + 1)) *
        coefficient f p (b s) s (m + 1) -
        (s * F f p (m + 1)) * coefficient f p (b s) s m) := by
    funext s
    rw [coefficient_recurrence]
    rw [mul_div_cancel₀ _ hd]
  have he := congrArg (fun g : ℂ → ℂ => iteratedDeriv j g 0) heq
  dsimp only at he
  have hg : AnalyticAt ℂ (fun s => b s + D p (m + 1) + s * E f p (m + 1)) 0 :=
    (hb.add analyticAt_const).add (analyticAt_id.mul analyticAt_const)
  have hf : AnalyticAt ℂ (fun s : ℂ => s * F f p (m + 1)) 0 :=
    analyticAt_id.mul analyticAt_const
  have hsub := iteratedDeriv_fun_sub (n := j)
    (hg.mul (hc (m + 1))).contDiffAt (hf.mul (hc m)).contDiffAt
  dsimp only [Pi.mul_apply] at hsub
  rw [iteratedDeriv_const_mul_field, hsub] at he
  simp only [Pi.mul_def] at he
  rw [iteratedDeriv_mul_of_lower_vanishing hg (hc (m + 1))
      (fun i hi => hlower i hi (m + 1) (by omega)),
    iteratedDeriv_mul_of_lower_vanishing hf (hc m)
      (fun i hi => hlower i hi m (by omega))] at he
  simpa only [hb0, zero_mul, add_zero, sub_zero, neg_add_eq_sub] using he

/-- Coordinate evaluation commutes with derivatives of a Banach-valued
analytic curve; the resulting derivative sequence remains bounded. -/
theorem seq_evaluation_iteratedDeriv {x : ℂ → SeqSpace}
    (hx : AnalyticAt ℂ x 0) (j n : ℕ) :
    iteratedDeriv j (fun s => x s n) 0 = (iteratedDeriv j x 0) n := by
  have hf : ContDiffAt ℂ j x 0 := hx.contDiffAt
  have he := (BoundedContinuousFunction.evalCLM ℂ n).iteratedFDeriv_comp_left hf (i := j) le_rfl
  have hv := congrArg (fun A => A (fun _ : Fin j => (1 : ℂ))) he
  exact hv

theorem decode_iteratedDeriv {x : ℂ → SeqSpace} (hx : AnalyticAt ℂ x 0) (j n : ℕ) :
    iteratedDeriv j (fun s => decode (x s) n) 0 = decode (iteratedDeriv j x 0) n := by
  simp only [decode, div_eq_mul_inv, iteratedDeriv_mul_const_field,
    seq_evaluation_iteratedDeriv hx]

/-- Actual bounded Heun tails beyond the resonant degree vanish. -/
theorem seqA_homogeneous_tail_zero {f : Family} {p : Parameters}
    (hp : Admissible f p) (k a : ℕ) (hka : k ≤ a) (x : SeqSpace)
    (hx : ∀ n, a < n → seqA p k x n = 0) :
    ∀ n, a < n → x n = 0 := by
  obtain ⟨L, _, hL⟩ := seq_tail_bounds p k
  obtain ⟨y, _, hy⟩ := bounded_bidiagonal_tail_solve a L
    (fun n => seqDiag p k n) (fun n => seqUpper p n) 2 (3/4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun n hn => by intro he; have := (seqDiag_zero_iff hp k n).mp he; omega)
    (fun n hn => (hL n hn).1) (fun n hn => (hL n hn).2) 0
  have hz := hy 0 (fun n _ => by simp)
  have hxy := hy x (fun n hn => by simpa only [seqA_apply] using hx n hn)
  intro n hn
  exact (hxy n hn).trans (hz n hn).symm

/-- Polynomial support of every jet of an actual analytic bounded-sequence
eigenbranch. The tail uniqueness theorem is instantiated, not assumed. -/
theorem analytic_encoded_branch_jet_support {f : Family} {p : Parameters}
    (hp : Admissible f p) {k : ℕ} {b : ℂ → ℂ} {x : ℂ → SeqSpace}
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 = -D p k) (hx : AnalyticAt ℂ x 0)
    (heq : ∀ᶠ s : ℂ in 𝓝 0, ∀ n, decode (x s) n = coefficient f p (b s) s n) :
    ∀ j m : ℕ, k + j < m →
      iteratedDeriv j (fun s => coefficient f p (b s) s m) 0 = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hjet : ∀ n, decode (iteratedDeriv j x 0) n =
        iteratedDeriv j (fun s => coefficient f p (b s) s n) 0 := by
      intro n
      rw [← decode_iteratedDeriv hx j n]
      have hen : (fun s => decode (x s) n) =ᶠ[𝓝 0]
          (fun s => coefficient f p (b s) s n) := heq.mono (fun s hs => hs n)
      exact hen.iteratedDeriv_eq j
    have htail : ∀ n, k + j < n → seqA p k (iteratedDeriv j x 0) n = 0 := by
      intro n hn
      have hn1 : n - 1 + 1 = n := by omega
      have hn2 : n - 1 + 2 = n + 1 := by omega
      have hr := coefficient_jet_homogeneous_tail hp hb hb0
        (m := n - 1) (j := j) (by omega) ih
      rw [hn1, hn2, ← hjet (n + 1), ← hjet n] at hr
      rw [seqA_decode]
      have hz : (D p k - D p n) * decode (iteratedDeriv j x 0) n +
          ((n : ℂ) + 1) * ((n : ℂ) + p.gamma) * decode (iteratedDeriv j x 0) (n + 1) = 0 := by
        linear_combination hr
      rw [hz, mul_zero]
    have hz := seqA_homogeneous_tail_zero hp k (k + j) (by omega)
      (iteratedDeriv j x 0) htail
    intro m hm
    rw [← hjet m]
    simp only [decode, hz m hm, zero_div]

/-- The literal convergence sum follows for an actual analytic encoded branch. -/
theorem final_hasSum_of_encoded_branch {f : Family} {p : Parameters}
    (hp : Admissible f p) {k : ℕ} {roots : ℕ → ℂ → ℂ}
    {b : ℂ → ℂ} {x : ℂ → SeqSpace}
    (hroots : ∀ N, k + 1 ≤ N → IsFiniteRootGerm f p k N (roots N))
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 = -D p k) (hx : AnalyticAt ℂ x 0)
    (heq : ∀ᶠ s : ℂ in 𝓝 0, ∀ n, decode (x s) n = coefficient f p (b s) s n) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 4 ∧ ∀ s : ℂ, ‖s‖ < r →
      HasSum (fun j : ℕ =>
        -finiteRootTaylor roots (k + (j + 1) + 1) (j + 1) * s ^ (j + 1))
        (b s + D p k) :=
  final_hasSum_of_coefficient_jet_support hp hroots hb hb0
    (analytic_encoded_branch_jet_support hp hb hb0 hx heq)

#print axioms analytic_encoded_branch_jet_support
#print axioms final_hasSum_of_encoded_branch
#print axioms bounded_tail_zero_of_contracting_step
#print axioms finite_root_derivative_eq_of_residual_vanishing
#print axioms final_hasSum_of_coefficient_jet_support
#print axioms analytic_positive_taylor_hasSum
#print axioms final_hasSum_of_derivative_matching
end Heun
