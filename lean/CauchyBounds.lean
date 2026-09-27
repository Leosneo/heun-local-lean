import FrobeniusAnalytic
import Mathlib.Analysis.Complex.Liouville

noncomputable section
open scoped Topology
open Filter

namespace Heun

theorem coefficient_differentiable_B (f : Family) (p : Parameters) (s : ℂ) (n : ℕ) :
    Differentiable ℂ (fun B : ℂ => coefficient f p B s n) := by
  intro B
  exact ((coefficient_analytic f p n (s, B)).comp_of_eq'
    (analyticAt_const.prod analyticAt_id) rfl).differentiableAt

theorem coefficient_differentiable_s (f : Family) (p : Parameters) (B : ℂ) (n : ℕ) :
    Differentiable ℂ (fun s : ℂ => coefficient f p B s n) := by
  intro s
  exact ((coefficient_analytic f p n (s, B)).comp_of_eq'
    (analyticAt_id.prod analyticAt_const) rfl).differentiableAt

theorem coefficient_deriv_B_bound (f : Family) (p : Parameters) (B s : ℂ)
    (M C ε : ℝ) (hε : 0 < ε)
    (hc : ∀ B s : ℂ, ‖B‖ ≤ M → ‖s‖ ≤ 1 / 100 →
      ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hB : ‖B‖ + ε ≤ M) (hs : ‖s‖ ≤ 1 / 100) (n : ℕ) :
    ‖deriv (fun b : ℂ => coefficient f p b s n) B‖ ≤
      (C * (5 / 4 : ℝ) ^ n) / ε := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε
    (coefficient_differentiable_B f p s n).diffContOnCl
  intro b hb
  apply hc b s _ hs n
  have hd : ‖b - B‖ = ε := by simpa [Metric.mem_sphere, dist_eq_norm] using hb
  calc
    ‖b‖ ≤ ‖b - B‖ + ‖B‖ := by simpa using norm_add_le (b - B) B
    _ ≤ M := by rw [hd]; linarith

theorem coefficient_deriv_s_bound (f : Family) (p : Parameters) (B s : ℂ)
    (M C ε : ℝ) (hε : 0 < ε)
    (hc : ∀ B s : ℂ, ‖B‖ ≤ M → ‖s‖ ≤ 1 / 100 →
      ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hB : ‖B‖ ≤ M) (hs : ‖s‖ + ε ≤ 1 / 100) (n : ℕ) :
    ‖deriv (fun t : ℂ => coefficient f p B t n) s‖ ≤
      (C * (5 / 4 : ℝ) ^ n) / ε := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε
    (coefficient_differentiable_s f p B n).diffContOnCl
  intro t ht
  apply hc B t hB _ n
  have hd : ‖t - s‖ = ε := by simpa [Metric.mem_sphere, dist_eq_norm] using ht
  calc
    ‖t‖ ≤ ‖t - s‖ + ‖s‖ := by simpa using norm_add_le (t - s) s
    _ ≤ 1 / 100 := by rw [hd]; linarith

theorem linearMap_prod_norm_bound (L : (ℂ × ℂ) →L[ℂ] ℂ) (K : ℝ)
    (hK : 0 ≤ K) (h₁ : ‖L (1, 0)‖ ≤ K) (h₂ : ‖L (0, 1)‖ ≤ K) :
    ‖L‖ ≤ 2 * K := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v = v.1 • ((1, 0) : ℂ × ℂ) + v.2 • ((0, 1) : ℂ × ℂ) := by
    ext <;> simp
  have hLv : L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
    calc
      L v = L (v.1 • ((1, 0) : ℂ × ℂ) + v.2 • ((0, 1) : ℂ × ℂ)) :=
        congrArg L hv
      _ = _ := by rw [L.map_add, L.map_smul, L.map_smul]; rfl
  rw [hLv]
  calc
    ‖v.1 * L (1, 0) + v.2 * L (0, 1)‖ ≤
        ‖v.1 * L (1, 0)‖ + ‖v.2 * L (0, 1)‖ := norm_add_le _ _
    _ ≤ ‖v.1‖ * K + ‖v.2‖ * K := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h₂ (norm_nonneg _))
    _ ≤ (2 * K) * ‖v‖ := by
      have hfst := norm_fst_le v
      have hsnd := norm_snd_le v
      nlinarith

theorem coefficient_fderiv_bound (f : Family) (p : Parameters) (B s : ℂ)
    (M C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hc : ∀ B s : ℂ, ‖B‖ ≤ M → ‖s‖ ≤ 1 / 100 →
      ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hB : ‖B‖ + ε ≤ M) (hs : ‖s‖ + ε ≤ 1 / 100) (n : ℕ) :
    ‖fderiv ℂ (fun v : ℂ × ℂ => coefficient f p v.2 v.1 n) (s, B)‖ ≤
      (2 * (C / ε)) * (5 / 4 : ℝ) ^ n := by
  let H : ℂ × ℂ → ℂ := fun v => coefficient f p v.2 v.1 n
  let L := fderiv ℂ H (s, B)
  have hH := (coefficient_analytic f p n (s, B)).differentiableAt.hasFDerivAt
  have h₁ : L (1, 0) = deriv (fun t : ℂ => coefficient f p B t n) s := by
    have hin : HasDerivAt (fun t : ℂ => (t, B)) ((1, 0) : ℂ × ℂ) s := by
      simpa using (hasFDerivAt_prodMk_left (𝕜 := ℂ) s B).hasDerivAt
    have hd := hH.comp_hasDerivAt s hin
    exact hd.deriv.symm
  have h₂ : L (0, 1) = deriv (fun b : ℂ => coefficient f p b s n) B := by
    have hin : HasDerivAt (fun b : ℂ => (s, b)) ((0, 1) : ℂ × ℂ) B := by
      simpa using (hasFDerivAt_prodMk_right (𝕜 := ℂ) s B).hasDerivAt
    have hd := hH.comp_hasDerivAt B hin
    exact hd.deriv.symm
  have hbound : ‖L‖ ≤ 2 * ((C * (5 / 4 : ℝ) ^ n) / ε) := by
    apply linearMap_prod_norm_bound L _ (by positivity)
    · rw [h₁]
      exact coefficient_deriv_s_bound f p B s M C ε hε hc (by linarith) hs n
    · rw [h₂]
      exact coefficient_deriv_B_bound f p B s M C ε hε hc hB (by linarith) n
  convert hbound using 1 <;> dsimp [L, H]
  ring

end Heun

#print axioms Heun.coefficient_fderiv_bound
