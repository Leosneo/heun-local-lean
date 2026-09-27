import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic.Ring

/-!
# Finite-jet propagation for the Mori–Takemura recurrence

The results in this file are algebraic.  They apply with `R = PowerSeries ℂ`
and `s = PowerSeries.X`.  Divisibility by `s ^ j` means vanishing modulo the
j-th power of the perturbation parameter.  No convergence or connection
coefficient theorem is assumed or asserted here.
-/

namespace MoriTakemura

variable {R : Type*} [CommRing R]

/-- Equality of two perturbation jets through orders strictly below `j`. -/
def JetEq (s : R) (j : ℕ) (a b : R) : Prop := s ^ j ∣ a - b

/-- One additional factor of the parameter raises the vanishing order. -/
theorem parameter_raises_order {s x : R} {j : ℕ}
    (hx : s ^ j ∣ x) : s ^ (j + 1) ∣ s * x := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y, ?_⟩
  rw [pow_succ]
  ring

/-- A higher-order vanishing statement implies the preceding one. -/
theorem lower_vanishing_order {s x : R} {j : ℕ}
    (hx : s ^ (j + 1) ∣ x) : s ^ j ∣ x := by
  exact dvd_trans (pow_dvd_pow s (Nat.le_succ j)) hx

/-- Multiplication by a unit does not conceal vanishing jets. -/
theorem unit_cancel_vanishing {s u x : R} {j : ℕ}
    (hu : IsUnit u) (hx : s ^ j ∣ u * x) : s ^ j ∣ x := by
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨y, hy⟩ := hx
  refine ⟨↑(v⁻¹) * y, ?_⟩
  calc
    x = ↑(v⁻¹) * (↑v * x) := by simp
    _ = ↑(v⁻¹) * (s ^ j * y) := by rw [hy]
    _ = s ^ j * (↑(v⁻¹) * y) := by ring

/-- The exact three-term step: the preceding coefficient needs one fewer
vanishing order because the recurrence supplies a factor of `s`. -/
theorem recurrence_step {s u a f previous current next : R} {j : ℕ}
    (hu : IsUnit u)
    (hrec : u * next = a * current - s * f * previous)
    (hprevious : s ^ j ∣ previous)
    (hcurrent : s ^ (j + 1) ∣ current) :
    s ^ (j + 1) ∣ next := by
  apply unit_cancel_vanishing hu
  rw [hrec]
  apply dvd_sub
  · exact dvd_mul_of_dvd_right hcurrent a
  · have h := parameter_raises_order hprevious
    simpa only [mul_assoc, mul_left_comm, mul_comm] using dvd_mul_of_dvd_left h f

/-- Tail propagation from two consecutive coefficients.  This is the
algebraic engine behind propagation between successive finite truncations.
The index convention is `c n`, `c (n+1)`, `c (n+2)`. -/
theorem tail_vanishing
    (s : R) (c u a f : ℕ → R) (start j : ℕ)
    (hu : ∀ n, IsUnit (u n))
    (hrec : ∀ n, u n * c (n + 2) =
      a n * c (n + 1) - s * f n * c n)
    (hprevious : s ^ j ∣ c start)
    (hcurrent : s ^ (j + 1) ∣ c (start + 1)) :
    ∀ offset, s ^ (j + 1) ∣ c (start + 1 + offset) := by
  have pair : ∀ offset,
      (s ^ j ∣ c (start + offset)) ∧
      (s ^ (j + 1) ∣ c (start + offset + 1)) := by
    intro offset
    induction offset with
    | zero => simpa using And.intro hprevious hcurrent
    | succ offset ih =>
      constructor
      · simpa [Nat.add_assoc] using lower_vanishing_order ih.2
      · have hnext := recurrence_step (hu (start + offset))
          (hrec (start + offset)) ih.1 ih.2
        simpa [Nat.add_assoc] using hnext
  intro offset
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (pair offset).2

/-- A unit divided difference detects equality of root jets.  This lemma
keeps the simple-root hypothesis explicit; it does not assume an analytic
implicit-function theorem. -/
theorem root_jet_unique
    {s x y u px py : R} {j : ℕ}
    (hu : IsUnit u)
    (hfactor : px - py = u * (x - y))
    (hx : s ^ j ∣ px) (hy : s ^ j ∣ py) : JetEq s j x y := by
  unfold JetEq
  apply unit_cancel_vanishing hu
  rw [← hfactor]
  exact dvd_sub hx hy

/-- The previous root and next root have the same prescribed jet when
three-term propagation and a unit divided difference are available. -/
theorem consecutive_root_jet
    {s u a f previous current next x y nextAtY v : R} {j : ℕ}
    (hu : IsUnit u)
    (hrec : u * next = a * current - s * f * previous)
    (hprevious : s ^ j ∣ previous)
    (hcurrent : s ^ (j + 1) ∣ current)
    (hv : IsUnit v)
    (hfactor : next - nextAtY = v * (x - y))
    (hy : s ^ (j + 1) ∣ nextAtY) : JetEq s (j + 1) x y := by
  exact root_jet_unique hv hfactor
    (recurrence_step hu hrec hprevious hcurrent) hy

/-- The paper's recurrence, at its positive indices `m = n + 1`.
The equation for `c 1` and the normalization `c 0 = 1` are separate;
neither is needed for propagation once the two initial jets are given. -/
def HeunRecurrence (s B gamma : R) (D E F c : ℕ → R) : Prop :=
  ∀ n, ((n + 2 : ℕ) : R) * (((n + 1 : ℕ) : R) + gamma) * c (n + 2) =
    (B + D (n + 1) + s * E (n + 1)) * c (n + 1) -
      s * F (n + 1) * c n

/-- Specialization to the exact positive-index Mori–Takemura recurrence.
Over complex formal power series, the denominator hypothesis follows when
`gamma` is not a nonpositive integer. -/
theorem heun_tail_vanishing
    (s B gamma : R) (D E F c : ℕ → R) (start j : ℕ)
    (hden : ∀ n, IsUnit
      (((n + 2 : ℕ) : R) * (((n + 1 : ℕ) : R) + gamma)))
    (hrec : HeunRecurrence s B gamma D E F c)
    (hprevious : s ^ j ∣ c start)
    (hcurrent : s ^ (j + 1) ∣ c (start + 1)) :
    ∀ offset, s ^ (j + 1) ∣ c (start + 1 + offset) := by
  exact tail_vanishing s c
    (fun n => ((n + 2 : ℕ) : R) * (((n + 1 : ℕ) : R) + gamma))
    (fun n => B + D (n + 1) + s * E (n + 1))
    (fun n => F (n + 1)) start j hden hrec hprevious hcurrent

/-- Stabilization at every later truncation, conditional only on the local
unit divided-difference certificate for its simple root.  Here `c` is the
coefficient sequence evaluated at `x`, and `rootValue` is the later
coefficient evaluated at `y`. -/
theorem tail_root_jet_stabilization
    (s : R) (c u a f : ℕ → R) (start j offset : ℕ)
    (hu : ∀ n, IsUnit (u n))
    (hrec : ∀ n, u n * c (n + 2) =
      a n * c (n + 1) - s * f n * c n)
    (hprevious : s ^ j ∣ c start)
    (hcurrent : s ^ (j + 1) ∣ c (start + 1))
    (x y rootValue v : R)
    (hv : IsUnit v)
    (hfactor : c (start + 1 + offset) - rootValue = v * (x - y))
    (hroot : rootValue = 0) : JetEq s (j + 1) x y := by
  apply root_jet_unique hv hfactor
  · exact tail_vanishing s c u a f start j hu hrec
      hprevious hcurrent offset
  · rw [hroot]
    exact dvd_zero _

end MoriTakemura
