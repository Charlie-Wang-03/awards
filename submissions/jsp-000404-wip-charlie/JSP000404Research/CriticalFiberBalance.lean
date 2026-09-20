import Mathlib.Tactic

/-!
# Critical duplicate-hole balance

For the retained n-bit projection of an (n+1)-colour canonical code, every
retained-code fibre has size at most two.  Write

* H for the number of empty retained codes (holes),
* S for the number of singleton retained-code fibres,
* D for the number of double fibres.

Then

  2^n = H + S + D,
  |V| = S + 2D.

At the critical cardinality |V| = 2^n + 1 these identities force

  D = H + 1.

Thus any injection (or Hall matching) from duplicate bases to holes is already
enough to rule out a critical counterexample.  This file isolates the exact
arithmetic statement; the finite-fibre counting bridge is kept separate.
-/

namespace JSP000404Research

/-- General excess identity for a 0/1/2 occupancy profile. -/
theorem double_sub_hole_eq_domain_sub_codomain
    {H S D U V : ℕ}
    (hcodomain : U = H + S + D)
    (hdomain : V = S + 2 * D)
    (hdomge : U ≤ V) :
    D - H = V - U := by
  omega

/-- Critical one-over-capacity profile: there is exactly one more duplicated
base than missing base. -/
theorem critical_double_eq_hole_add_one
    {H S D U V : ℕ}
    (hcodomain : U = H + S + D)
    (hdomain : V = S + 2 * D)
    (hcritical : V = U + 1) :
    D = H + 1 := by
  omega

/-- In particular, a critical profile cannot admit an injection from all
duplicate bases into the holes at the cardinality level. -/
theorem critical_not_double_le_hole
    {H S D U V : ℕ}
    (hcodomain : U = H + S + D)
    (hdomain : V = S + 2 * D)
    (hcritical : V = U + 1) :
    ¬ D ≤ H := by
  have h := critical_double_eq_hole_add_one
    hcodomain hdomain hcritical
  omega

/-- Conversely, any duplicate-to-hole cardinality bound closes the ordinary
capacity estimate for a 0/1/2 fibre profile. -/
theorem domain_le_codomain_of_double_le_hole
    {H S D U V : ℕ}
    (hcodomain : U = H + S + D)
    (hdomain : V = S + 2 * D)
    (hDH : D ≤ H) :
    V ≤ U := by
  omega

#print axioms double_sub_hole_eq_domain_sub_codomain
#print axioms critical_double_eq_hole_add_one
#print axioms critical_not_double_le_hole
#print axioms domain_le_codomain_of_double_le_hole

end JSP000404Research
