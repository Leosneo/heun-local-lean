import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic

/-!
# The singular-coefficient obstruction for finite connection jets

This file proves a reusable step of the Heun argument. It does NOT assume or
prove existence of Heun Frobenius solutions, analytic parameter dependence,
the Gauss connection formula, or the conjecture itself.

`regularGerms S z₀` consists of functions whose restriction toward `z₀` through
`S` agrees locally with an analytic function defined at `z₀`. This is suited
to a slit lens: equality at the endpoint itself is not required.

The finite convolution theorem says that a regular jet cannot contain a first
nonzero coefficient multiplying a nonextendable singular germ.
-/

open scoped Topology BigOperators ContDiff
open Filter

namespace Gcoy.AnalyticBridge

/-- Analytic implicit-function existence, including uniqueness on a neighborhood.

The second coordinate is the accessory parameter. Invertibility of its partial
derivative is a genuine hypothesis; no Heun simplicity assertion is assumed here.
-/
theorem exists_analytic_implicit_branch {f : ℂ × ℂ → ℂ} {u : ℂ × ℂ}
    (hf : AnalyticAt ℂ f u)
    (hi : (fderiv ℂ f u ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g u.1 ∧ g u.1 = u.2 ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ g v.1 = v.2) := by
  have hc : ContDiffAt ℂ ω f u := hf.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.implicitFunction hn hi, ?_, ?_, ?_⟩
  · exact (hc.contDiffAt_implicitFunction hn hi).analyticAt
  · exact hc.implicitFunction_apply_self hn hi
  · exact hc.eventually_apply_eq_iff_implicitFunction hn hi

def regularGerms (S : Set ℂ) (z₀ : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[S] z₀] g}
  zero_mem' := ⟨0, analyticAt_const, Filter.EventuallyEq.rfl⟩
  add_mem' := by
    rintro f g ⟨f', hf', hf⟩ ⟨g', hg', hg⟩
    refine ⟨f' + g', hf'.add hg', ?_⟩
    filter_upwards [hf, hg] with z h₁ h₂
    simp only [Pi.add_apply, h₁, h₂]
  smul_mem' := by
    rintro c f ⟨g, hg, hfg⟩
    refine ⟨c • g, analyticAt_const.smul hg, ?_⟩
    filter_upwards [hfg] with z hz
    simp only [Pi.smul_apply, hz]

theorem mem_regularGerms_of_analytic {S : Set ℂ} {z₀ : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f z₀) : f ∈ regularGerms S z₀ :=
  ⟨f, hf, Filter.EventuallyEq.rfl⟩

theorem mem_regularGerms_congr {S : Set ℂ} {z₀ : ℂ} {f g : ℂ → ℂ}
    (hfg : f =ᶠ[𝓝[S] z₀] g) (hf : f ∈ regularGerms S z₀) :
    g ∈ regularGerms S z₀ := by
  obtain ⟨h, hh, hfh⟩ := hf
  exact ⟨h, hh, hfg.symm.trans hfh⟩

section AlgebraicObstruction

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A nonzero scalar cannot turn a nonregular germ into a regular germ. -/
theorem scalar_eq_zero_of_smul_mem (R : Submodule K M) {v : M}
    (hv : v ∉ R) {c : K} (hc : c • v ∈ R) : c = 0 := by
  by_contra hne
  apply hv
  have h := R.smul_mem c⁻¹ hc
  simpa [smul_smul, inv_mul_cancel₀ hne] using h

/-- Finite jet version of the first-singular-coefficient argument.

The convolution is the coefficient of the product of a scalar connection
coefficient and a singular solution. `q n` collects the regular contribution.
-/
theorem connection_jets_vanish (R : Submodule K M)
    (p q v : ℕ → M) (c : ℕ → K) (J : ℕ)
    (hv : v 0 ∉ R)
    (hp : ∀ n ≤ J, p n ∈ R)
    (hq : ∀ n ≤ J, q n ∈ R)
    (hconn : ∀ n ≤ J,
      p n = q n + ∑ i ∈ Finset.range (n + 1), c i • v (n - i)) :
    ∀ n ≤ J, c n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hsum : (∑ i ∈ Finset.range n, c i • v (n - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hil : i < n := Finset.mem_range.mp hi
      rw [ih i hil (Nat.le_trans (Nat.le_of_lt hil) hn), zero_smul]
    have heq : p n = q n + c n • v 0 := by
      simpa [Finset.sum_range_succ, hsum] using hconn n hn
    have hmem : c n • v 0 ∈ R := by
      have h := R.sub_mem (hp n hn) (hq n hn)
      simpa [heq] using h
    exact scalar_eq_zero_of_smul_mem R hv hmem

end AlgebraicObstruction

/-- The same obstruction specialized to actual analytic extendability on a lens. -/
theorem analytic_connection_jets_vanish (S : Set ℂ) (z₀ : ℂ)
    (p q v : ℕ → ℂ → ℂ) (c : ℕ → ℂ) (J : ℕ)
    (hv : v 0 ∉ regularGerms S z₀)
    (hp : ∀ n ≤ J, p n ∈ regularGerms S z₀)
    (hq : ∀ n ≤ J, q n ∈ regularGerms S z₀)
    (hconn : ∀ n ≤ J,
      p n = q n + ∑ i ∈ Finset.range (n + 1), c i • v (n - i)) :
    ∀ n ≤ J, c n = 0 :=
  connection_jets_vanish (regularGerms S z₀) p q v c J hv hp hq hconn

/-- Connection identities need only hold on the slit lens near the endpoint. -/
theorem analytic_connection_germ_jets_vanish (S : Set ℂ) (z₀ : ℂ)
    (p q v : ℕ → ℂ → ℂ) (c : ℕ → ℂ) (J : ℕ)
    (hv : v 0 ∉ regularGerms S z₀)
    (hp : ∀ n ≤ J, p n ∈ regularGerms S z₀)
    (hq : ∀ n ≤ J, q n ∈ regularGerms S z₀)
    (hconn : ∀ n ≤ J,
      p n =ᶠ[𝓝[S] z₀] q n + ∑ i ∈ Finset.range (n + 1), c i • v (n - i)) :
    ∀ n ≤ J, c n = 0 := by
  apply connection_jets_vanish (regularGerms S z₀)
    (fun n => q n + ∑ i ∈ Finset.range (n + 1), c i • v (n - i)) q v c J hv
  · intro n hn
    exact mem_regularGerms_congr (hconn n hn) (hp n hn)
  · exact hq
  · intro n hn
    rfl

end Gcoy.AnalyticBridge

#print axioms Gcoy.AnalyticBridge.connection_jets_vanish
#print axioms Gcoy.AnalyticBridge.analytic_connection_jets_vanish
#print axioms Gcoy.AnalyticBridge.analytic_connection_germ_jets_vanish
#print axioms Gcoy.AnalyticBridge.exists_analytic_implicit_branch
