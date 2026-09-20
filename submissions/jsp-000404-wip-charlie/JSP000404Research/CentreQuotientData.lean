import JSP000404Research.CentreProjectiveCycle
import JSP000404Research.TransitionGapAlignment
import Mathlib.Tactic

/-!
# Sendov quotients of the concrete projective gap cycle

For normalized projective gaps g_j and a positive angular parameter t, define

  q_j = floor(t * g_j).

The floor window gives

  q_j <= t*g_j < q_j+1,

so the quotient list is automatically aligned with the geometric gap list.
Because the normalized gaps sum to one, if

  t = n + delta,   0 <= delta < 1,

then the total quotient mass is at most n.

This closes the previously abstract hypothesis sum q <= n for the actual
canonical projective ray cycle.
-/

namespace JSP000404Research

/-- Natural Sendov quotients of a normalized gap list. -/
def quotientList (t : ℝ) (gaps : List ℝ) : List ℕ :=
  gaps.map fun g => Nat.floor (t * g)

/-- Exact upper half of the floor window. -/
def QuotientGapUpperAligned
    (t : ℝ) (qs : List ℕ) (gaps : List ℝ) : Prop :=
  List.Forall₂
    (fun q g => t * g < (q : ℝ) + 1)
    qs gaps

theorem quotientList_length
    (t : ℝ) (gaps : List ℝ) :
    (quotientList t gaps).length = gaps.length := by
  simp [quotientList]

/-- Pointwise floor lower bounds give the alignment used by the transition
rotation modules. -/
theorem quotientList_aligned
    (t : ℝ) (gaps : List ℝ)
    (hgaps0 : ∀ g ∈ gaps, 0 ≤ g)
    (ht0 : 0 ≤ t) :
    QuotientGapAligned t (quotientList t gaps) gaps := by
  induction gaps with
  | nil =>
      exact List.Forall₂.nil
  | cons g gs ih =>
      have hg0 : 0 ≤ g := hgaps0 g (by simp)
      have htg0 : 0 ≤ t * g := mul_nonneg ht0 hg0
      apply List.Forall₂.cons
      · exact Nat.floor_le htg0
      · apply ih
        intro x hx
        exact hgaps0 x (by simp [hx])

/-- Pointwise strict upper floor windows. -/
theorem quotientList_upper_aligned
    (t : ℝ) (gaps : List ℝ) :
    QuotientGapUpperAligned t (quotientList t gaps) gaps := by
  induction gaps with
  | nil =>
      exact List.Forall₂.nil
  | cons g gs ih =>
      apply List.Forall₂.cons
      · exact Nat.lt_floor_add_one (t * g)
      · exact ih

/-- Real cast of the quotient mass is bounded by t times the total normalized
gap mass. -/
theorem quotientList_cast_sum_le
    (t : ℝ) (gaps : List ℝ)
    (ht0 : 0 ≤ t)
    (hgaps0 : ∀ g ∈ gaps, 0 ≤ g) :
    ((quotientList t gaps).sum : ℝ) ≤
      t * gaps.sum := by
  induction gaps with
  | nil =>
      simp [quotientList]
  | cons g gs ih =>
      have hg0 : 0 ≤ g := hgaps0 g (by simp)
      have hfloor :
          ((Nat.floor (t * g) : ℕ) : ℝ) ≤ t * g :=
        Nat.floor_le (mul_nonneg ht0 hg0)
      have htail :
          ((quotientList t gs).sum : ℝ) ≤
            t * gs.sum := by
        apply ih
        intro x hx
        exact hgaps0 x (by simp [hx])
      simp only [quotientList, List.map_cons, List.sum_cons, Nat.cast_add]
      calc
        ((Nat.floor (t * g) : ℕ) : ℝ) +
              ((List.map (fun x => Nat.floor (t * x)) gs).sum : ℝ)
            ≤ t * g + t * gs.sum := add_le_add hfloor htail
        _ = t * (g + gs.sum) := by ring

/-- Actual centre-cycle quotient mass is at most n in the full delta<1
Sendov range. -/
theorem centreQuotient_sum_le_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    (quotientList t C.gaps).sum ≤ n := by
  have ht0 : 0 ≤ t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hreal :=
    quotientList_cast_sum_le
      t C.gaps ht0 C.gaps_nonneg
  rw [C.gaps_sum, mul_one] at hreal
  have htlt : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  by_contra hnot
  have hnat :
      n + 1 ≤ (quotientList t C.gaps).sum := by
    omega
  have hcast :
      ((n + 1 : ℕ) : ℝ) ≤
        ((quotientList t C.gaps).sum : ℕ) := by
    exact_mod_cast hnat
  push_cast at hcast
  linarith

/-- The concrete centre quotient list is aligned with its actual projective
gaps. -/
theorem centreQuotient_aligned
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht0 : 0 ≤ t) :
    QuotientGapAligned t (quotientList t C.gaps) C.gaps :=
  quotientList_aligned t C.gaps C.gaps_nonneg ht0

theorem centreQuotient_upper_aligned
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    QuotientGapUpperAligned t (quotientList t C.gaps) C.gaps :=
  quotientList_upper_aligned t C.gaps

#print axioms quotientList_aligned
#print axioms quotientList_upper_aligned
#print axioms quotientList_cast_sum_le
#print axioms centreQuotient_sum_le_n
#print axioms centreQuotient_aligned

end JSP000404Research
