import BanachSpace
import JointAnalytic

noncomputable section
open scoped Topology
open Filter
namespace Heun

def eigenLinearization (A J : SeqSpace →L[ℂ] SeqSpace) (p₀ : SeqSpace) :
    (SeqSpace × ℂ) →L[ℂ] (SeqSpace × ℂ) :=
  ((A.comp (ContinuousLinearMap.fst ℂ SeqSpace ℂ)) -
    (ContinuousLinearMap.snd ℂ SeqSpace ℂ).smulRight (J p₀)).prod
    ((BoundedContinuousFunction.evalCLM ℂ 0).comp (ContinuousLinearMap.fst ℂ SeqSpace ℂ))

@[simp] theorem eigenLinearization_apply (A J : SeqSpace →L[ℂ] SeqSpace)
    (p₀ x : SeqSpace) (b : ℂ) :
    eigenLinearization A J p₀ (x,b) = (A x-b • J p₀, x 0) := rfl

def eigenEquation (A J V : SeqSpace →L[ℂ] SeqSpace) :
    ℂ × (SeqSpace × ℂ) → (SeqSpace × ℂ) :=
  fun v => (A v.2.1-v.2.2 • J v.2.1+v.1 • V v.2.1, v.2.1 0-1)

theorem eigenEquation_contDiff (A J V : SeqSpace →L[ℂ] SeqSpace) :
    ContDiff ℂ 1 (eigenEquation A J V) := by
  unfold eigenEquation
  have hEv : ContDiff ℂ 1 (fun x : SeqSpace => x 0) :=
    (BoundedContinuousFunction.evalCLM (β := ℂ) ℂ (0:ℕ)).contDiff
  have hx : ContDiff ℂ 1 (fun v : ℂ × (SeqSpace × ℂ) => v.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hb : ContDiff ℂ 1 (fun v : ℂ × (SeqSpace × ℂ) => v.2.2) :=
    contDiff_snd.comp contDiff_snd
  exact (((A.contDiff.comp hx).sub (hb.smul (J.contDiff.comp hx))).add
    (contDiff_fst.smul (V.contDiff.comp hx))).prodMk ((hEv.comp hx).sub contDiff_const)

theorem eigenEquation_partial (A J V : SeqSpace →L[ℂ] SeqSpace) (p₀ : SeqSpace) :
    fderiv ℂ (eigenEquation A J V) (0,(p₀,0)) ∘L
      ContinuousLinearMap.inr ℂ ℂ (SeqSpace × ℂ) = eigenLinearization A J p₀ := by
  let u : SeqSpace × ℂ := (p₀,0)
  have hfst := (ContinuousLinearMap.fst ℂ SeqSpace ℂ).hasFDerivAt (x := u)
  have hsnd := (ContinuousLinearMap.snd ℂ SeqSpace ℂ).hasFDerivAt (x := u)
  have hA := A.hasFDerivAt.comp u hfst
  have hJ := J.hasFDerivAt.comp u hfst
  have hE := (BoundedContinuousFunction.evalCLM ℂ (0:ℕ)).hasFDerivAt.comp u hfst
  have hd := (hA.sub (hsnd.smul hJ)).prodMk (hE.sub_const 1)
  have hd' : HasFDerivAt (fun v : SeqSpace × ℂ => eigenEquation A J V (0,v))
      (eigenLinearization A J p₀) u := by
    simpa [u, eigenEquation, eigenLinearization] using hd
  have hc := (eigenEquation_contDiff A J V).differentiable (by simp)
  have hh := (hc (0,u)).hasFDerivAt.comp u
    (hasFDerivAt_prodMk_right (𝕜 := ℂ) (0:ℂ) u)
  exact hh.unique hd'

/-- Analytic normalized eigenpair, once the concrete bordered inverse is supplied. -/
theorem exists_analytic_eigenpair (A J V : SeqSpace →L[ℂ] SeqSpace) (p₀ : SeqSpace)
    (hp : A p₀ = 0) (hp₀ : p₀ 0=1)
    (hi : (eigenLinearization A J p₀).IsInvertible) :
    ∃ (x : ℂ → SeqSpace) (b : ℂ → ℂ),
      AnalyticAt ℂ x 0 ∧ AnalyticAt ℂ b 0 ∧ x 0=p₀ ∧ b 0=0 ∧
      ∀ᶠ s in 𝓝 (0:ℂ), A (x s)-b s • J (x s)+s • V (x s)=0 ∧ x s 0=1 := by
  have hf := (eigenEquation_contDiff A J V).contDiffAt (x := (0,(p₀,0)))
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by simp
  have hinv : (fderiv ℂ (eigenEquation A J V) (0,(p₀,0)) ∘L
      ContinuousLinearMap.inr ℂ ℂ (SeqSpace × ℂ)).IsInvertible := by
    rw [eigenEquation_partial]; exact hi
  let g := hf.implicitFunction hn hinv
  have hg0 : g 0=(p₀,0) := hf.implicitFunction_apply_self hn hinv
  have hga : AnalyticAt ℂ g 0 := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    have hc := (hf.contDiffAt_implicitFunction hn hinv).eventually (by simp)
    filter_upwards [hc] with s hs
    exact hs.differentiableAt (by simp)
  refine ⟨fun s => (g s).1, fun s => (g s).2,
    analyticAt_fst.comp hga, analyticAt_snd.comp hga,
    congrArg Prod.fst hg0, congrArg Prod.snd hg0, ?_⟩
  filter_upwards [hf.eventually_apply_implicitFunction hn hinv] with s hs
  have he : eigenEquation A J V (s,g s) = (0,0) := by
    simpa [eigenEquation, hp, hp₀] using hs
  exact ⟨congrArg Prod.fst he, sub_eq_zero.mp (congrArg Prod.snd he)⟩

#print axioms exists_analytic_eigenpair
end Heun
