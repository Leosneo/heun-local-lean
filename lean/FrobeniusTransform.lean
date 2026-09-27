import HeunProblem

/-! Exact rational identities for the reflection and exponent-shift
transformations used to construct the two endpoint Frobenius solutions. -/
noncomputable section
namespace Heun

def reflectedParameters (p : Parameters) : Parameters :=
  { p with gamma := p.delta, delta := p.gamma }

def reflectedParameter (f : Family) (s : ℂ) : ℂ :=
  match f with | .heun => -s / (1-s) | _ => -s

def reflectedAccessory (f : Family) (p : Parameters) (B s : ℂ) : ℂ :=
  match f with
  | .heun => (B-s*p.alpha*p.beta)/(1-s)
  | .confluent => B-s*p.alpha
  | .reduced => B-s

theorem reflected_drift (f : Family) (p : Parameters) (s t : ℂ)
    (ht : t ≠ 0) (ht1 : t-1 ≠ 0) (hs : 1-s ≠ 0)
    (hst : 1-s*(1-t) ≠ 0) :
    drift f (reflectedParameters p) (reflectedParameter f s) t =
      -drift f p s (1-t) := by
  have ht' : 1-t ≠ 0 := by intro h; apply ht1; linear_combination -h
  have hden : 1 + s / (1-s) * t = (1-s*(1-t))/(1-s) := by field_simp; ring
  have hst' : 1 + t*s-s ≠ 0 := by convert hst using 1 <;> ring
  have hst'' : 1-s+s*t ≠ 0 := by convert hst using 1 <;> ring
  cases f <;> simp [drift, reflectedParameters, reflectedParameter, hden] <;>
    field_simp [ht, ht1, ht', hs, hst, hst', hst''] <;> ring_nf <;>
    field_simp [hst', hst''] <;> ring

theorem reflected_potential (f : Family) (p : Parameters) (B s t : ℂ)
    (ht : t ≠ 0) (ht1 : t-1 ≠ 0) (hs : 1-s ≠ 0)
    (hst : 1-s*(1-t) ≠ 0) :
    potential f (reflectedParameters p) (reflectedAccessory f p B s)
      (reflectedParameter f s) t = potential f p B s (1-t) := by
  have ht' : 1-t ≠ 0 := by intro h; apply ht1; linear_combination -h
  have hden : 1 + s / (1-s) * t = (1-s*(1-t))/(1-s) := by field_simp; ring
  have hst' : 1 + t*s-s ≠ 0 := by convert hst using 1 <;> ring
  have hst'' : 1-s+s*t ≠ 0 := by convert hst using 1 <;> ring
  cases f <;> simp [potential, reflectedParameters, reflectedAccessory,
    reflectedParameter, hden] <;> field_simp [ht, ht1, ht', hs, hst, hst', hst''] <;> ring

def exponentShiftParameters (p : Parameters) : Parameters :=
  { p with gamma := 2 - p.gamma
           alpha := p.alpha + 1 - p.gamma
           beta := p.beta + 1 - p.gamma }

def exponentShiftAccessory (f : Family) (p : Parameters) (B s : ℂ) : ℂ :=
  B + (1-p.gamma)*p.delta + match f with
  | .heun => (1-p.gamma)*s*p.epsilon
  | .confluent => (1-p.gamma)*s
  | .reduced => 0

theorem exponentShift_drift (f : Family) (p : Parameters) (s z : ℂ) :
    drift f (exponentShiftParameters p) s z =
      drift f p s z + 2*(1-p.gamma)/z := by
  cases f <;> simp [drift, exponentShiftParameters] <;> ring

theorem exponentShift_potential (f : Family) (p : Parameters)
    (hbalance : f = .heun → p.gamma+p.delta+p.epsilon=p.alpha+p.beta+1)
    (B s z : ℂ) (hz : z ≠ 0) (hz1 : z-1 ≠ 0) (hs : 1-s*z ≠ 0) :
    potential f (exponentShiftParameters p) (exponentShiftAccessory f p B s) s z =
      potential f p B s z + (1-p.gamma)*drift f p s z/z +
        (1-p.gamma)*((1-p.gamma)-1)/z^2 := by
  cases f with
  | heun =>
    have hb := hbalance rfl
    have heps : p.epsilon = p.alpha+p.beta+1-p.gamma-p.delta := by linear_combination hb
    simp [potential, exponentShiftParameters, exponentShiftAccessory, drift]
    field_simp [hz, hz1, hs]
    rw [heps]
    ring
  | confluent =>
    simp [potential, exponentShiftParameters, exponentShiftAccessory, drift]
    field_simp [hz, hz1]
    ring
  | reduced =>
    simp [potential, exponentShiftParameters, exponentShiftAccessory, drift]
    field_simp [hz, hz1]
    ring

theorem exponentShift_nonresonant (p : Parameters)
    (hgamma : ∀ m : ℤ, p.gamma ≠ (m : ℂ)) :
    ∀ n : ℕ, (exponentShiftParameters p).gamma ≠ -(n : ℂ) := by
  intro n hn
  apply hgamma ((n : ℤ)+2)
  dsimp [exponentShiftParameters] at hn
  push_cast
  linear_combination -hn

end Heun
