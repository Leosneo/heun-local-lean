import BanachBranch
import BanachInvertible
import BanachRecurrence
import BanachEndpoint
import FinalAssembly
import ConnectionUniqueness

noncomputable section
open scoped Topology
open Filter
namespace Heun

/-- The concrete bounded inverse produces an analytic normalized solution
sequence for the actual source recurrence. -/
theorem exists_analytic_encoded_branch (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    ∃ (x : ℂ → SeqSpace) (B : ℂ → ℂ),
      AnalyticAt ℂ x 0 ∧ AnalyticAt ℂ B 0 ∧
      x 0=encodePolynomial (basePolynomial f p k) ∧ B 0 = -D p k ∧
      ∀ᶠ s in 𝓝 (0:ℂ), ∀ n, decode (x s) n=coefficient f p (B s) s n := by
  have hi : (eigenLinearization (seqA p k) seqJ (seqBase f p k)).IsInvertible :=
    borderT_isInvertible f p hp k
  obtain ⟨x,b,hx,hb,hx0,hb0,he⟩ := exists_analytic_eigenpair
    (seqA p k) seqJ (seqV f p) (seqBase f p k)
    (seqA_encoded_base_zero f p hp k) (seqBase_zero f p k) hi
  refine ⟨x, fun s => -D p k+b s, hx, analyticAt_const.add hb,
    hx0, by simp [hb0], ?_⟩
  filter_upwards [he] with s hs
  exact residual_coefficients f p hp k (x s) (b s) s hs.1 hs.2

#print axioms exists_analytic_encoded_branch

/-- Mori--Takemura's local convergent-series conjecture for the three
implemented Heun families, with the exact source recurrence and actual
normalized endpoint connection relation. -/
theorem literatureConjecture : LiteratureConjecture := by
  classical
  intro f p hp k
  have hfinite : ∀ N : ℕ, ∃ b : ℂ → ℂ,
      k+1≤N → IsFiniteRootGerm f p k N b := by
    intro N
    by_cases hN : k+1≤N
    · obtain ⟨b,hb⟩ := finite_root_germ_exists f p hp k N (by omega)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨fun _ => 0, fun h => False.elim (hN h)⟩
  choose roots hroots using hfinite
  obtain ⟨x,B,hx,hB,hx0,hB0,he⟩ := exists_analytic_encoded_branch f p hp k
  obtain ⟨r,hr,hrquarter,hsum⟩ :=
    final_hasSum_of_encoded_branch hp hroots hB hB0 hx he
  have hconn := banach_branch_connection_zero f p hp k x B hx.continuousAt hx0 he
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hconn
  refine ⟨roots,B,min r δ,hroots,hB,hB0,lt_min hr hδ,
    lt_of_le_of_lt (min_le_left _ _) hrquarter, ?_⟩
  intro s hs
  have hc : IsConnectionCoefficient f p (B s) s 0 :=
    hball (by simpa only [dist_zero_right] using lt_of_lt_of_le hs (min_le_right _ _))
  exact ⟨hc, fun d hd => isConnectionCoefficient_unique f p hp (B s) s d 0 hd hc,
    hsum s (lt_of_lt_of_le hs (min_le_left _ _))⟩

#print axioms literatureConjecture
end Heun
