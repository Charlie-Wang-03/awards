import JSP000404Research.StrictSupportAnglePacking
import JSP000404Research.ConcreteTransitionInterval
import JSP000404Research.LinearizedTransitionExposure
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Generic common-signed support interval certificates

Many geometric branches in JSP-000404 produce the same usable object: all
displacement rays from a centre lie, after canonical sign lifting, in one
common signed interval of width strictly below pi.

The dual strict-support arc then has physical angular length

  pi - width.

This file packages that object independently of how it was obtained.  In
particular every HighExponentTransitionIntervalCertificate forgets to one of
these certificates, with support-arc length exactly pi*ge.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

structure SupportIntervalCertificate
    {V : Type*} {p : V → Plane} (i : V) where
  a : ℝ
  width : ℝ
  sigma : Bool
  width_nonneg : 0 ≤ width
  width_lt_pi : width < Real.pi
  repr : ∀ j, j ≠ i →
    ∃ rho : ℝ, ∃ theta : ℝ,
      0 < rho ∧
      a ≤ theta ∧ theta ≤ a + width ∧
      p j - p i =
        rho • signedRayDirection sigma theta

namespace SupportIntervalCertificate

def turnLength
    {V : Type*} {p : V → Plane} {i : V}
    (C : SupportIntervalCertificate (p := p) i) : ℝ :=
  Real.pi - C.width

theorem turnLength_pos
    {V : Type*} {p : V → Plane} {i : V}
    (C : SupportIntervalCertificate (p := p) i) :
    0 < C.turnLength := by
  unfold turnLength
  linarith [C.width_lt_pi]

/-- Forget the quotient data from a high-exponent transition certificate. -/
def ofHighExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (H : HighExponentTransitionIntervalCertificate hp t i C) :
    SupportIntervalCertificate (p := p) i where
  a := H.a
  width := H.width
  sigma := H.sigma
  width_nonneg := H.width_nonneg
  width_lt_pi := H.width_lt_pi
  repr := H.repr

theorem turnLength_ofHighExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (H : HighExponentTransitionIntervalCertificate hp t i C) :
    (ofHighExponent H).turnLength = Real.pi * H.ge := by
  unfold turnLength ofHighExponent
  rw [H.width_eq]
  ring

/-- The high-exponent transition quotient supplies a quantitative lower bound
on the dual support-arc length. -/
theorem qe_mul_lam_le_turnLength_ofHighExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {t lam : ℝ}
    {C : CentreProjectiveCycle hp i}
    (H : HighExponentTransitionIntervalCertificate hp t i C)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t) :
    (H.qe : ℝ) * lam ≤ (ofHighExponent H).turnLength := by
  rw [turnLength_ofHighExponent H]
  exact quotient_mul_lam_le_pi_mul_gap ht H.qe_le hlam

/-- Any finite injective family of support-interval certificates has total
dual turn length at most the full direction circle. -/
theorem turnLength_sum_le_two_pi
    {V I : Type*} [Fintype I]
    {p : V → Plane}
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (cert : ∀ r : I,
      SupportIntervalCertificate (p := p) (centre r)) :
    (∑ r : I, (cert r).turnLength) ≤ 2 * Real.pi := by
  simpa [turnLength] using
    strict_support_arc_width_sum_le_two_pi
      (p := p)
      centre hcentre
      (fun r => (cert r).a)
      (fun r => (cert r).width)
      (fun r => (cert r).sigma)
      (fun r => (cert r).width_nonneg)
      (fun r => (cert r).width_lt_pi)
      (fun r => (cert r).repr)

/-- Four explicit pairwise-distinct support certificates pack into 2*pi. -/
theorem four_turnLength_sum_le_two_pi
    {V : Type*} {p : V → Plane}
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : SupportIntervalCertificate (p := p) s)
    (Ca : SupportIntervalCertificate (p := p) a)
    (Cb : SupportIntervalCertificate (p := p) b)
    (Cc : SupportIntervalCertificate (p := p) c) :
    Cs.turnLength + Ca.turnLength +
        Cb.turnLength + Cc.turnLength ≤ 2 * Real.pi := by
  let centre : Fin 4 → V := ![s,a,b,c]
  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢ <;>
      try { exact False.elim (hsa hxy) } <;>
      try { exact False.elim (hsb hxy) } <;>
      try { exact False.elim (hsc hxy) } <;>
      try { exact False.elim (hab hxy) } <;>
      try { exact False.elim (hac hxy) } <;>
      try { exact False.elim (hbc hxy) } <;>
      try { exact False.elim (hsa hxy.symm) } <;>
      try { exact False.elim (hsb hxy.symm) } <;>
      try { exact False.elim (hsc hxy.symm) } <;>
      try { exact False.elim (hab hxy.symm) } <;>
      try { exact False.elim (hac hxy.symm) } <;>
      try { exact False.elim (hbc hxy.symm) }
  let cert : ∀ r : Fin 4,
      SupportIntervalCertificate (p := p) (centre r) :=
    fun r => by
      fin_cases r
      · simpa [centre] using Cs
      · simpa [centre] using Ca
      · simpa [centre] using Cb
      · simpa [centre] using Cc
  have h :=
    turnLength_sum_le_two_pi centre hcentre cert
  simpa [cert, centre, Fin.sum_univ_succ] using h

#print axioms turnLength_sum_le_two_pi
#print axioms four_turnLength_sum_le_two_pi
#print axioms qe_mul_lam_le_turnLength_ofHighExponent

end SupportIntervalCertificate
end JSP000404Research
