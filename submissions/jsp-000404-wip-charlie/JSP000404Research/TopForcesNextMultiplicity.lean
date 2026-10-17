import JSP000404Research.NoTopTwoNextMultiplicity
import Mathlib.Tactic

/-!
# Genuine planar dyadic spectrum: top forces at most one next layer

Given at least four distinct actual centres, the verified arbitrary-finite
top+two-next geometric contradiction entails the strict high-dyadic
multiplicity rule:

  one centre exponent n-1  ==>  at most one centre exponent n-2.

The restriction is for the original AngleCap planar cycles, not an
abstract Boolean hypercube model, and assumes no global hole payment.
The full JSP-000404 dyadic sum conjecture remains open.
-/

namespace JSP000404Research

theorem exists_fourth_of_card_ge_four
    {V : Type*} [Fintype V]
    (hcard : 4 ≤ Fintype.card V)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b) :
    ∃ c : V, s ≠ c ∧ a ≠ c ∧ b ≠ c := by
  classical
  by_contra hnone
  have hsub :
      (Finset.univ : Finset V) ⊆
        ({s, a, b} : Finset V) := by
    intro c _
    by_contra hc
    have hsc : s ≠ c := by
      intro h
      exact hc (by simp [h])
    have hac : a ≠ c := by
      intro h
      exact hc (by simp [h])
    have hbc : b ≠ c := by
      intro h
      exact hc (by simp [h])
    exact hnone ⟨c, hsc, hac, hbc⟩
  have hthree :
      ({s, a, b} : Finset V).card ≤ 3 := by
    simp [hsa, hsb, hab]
  have hupper : Fintype.card V ≤ 3 := by
    simpa using (Finset.card_le_card hsub).trans hthree
  omega

/-- In a four-or-more-vertex original planar configuration, if the
top dyadic exponent is achieved, the next-highest exponent can occur
at most once anywhere (not merely among a preselected triple). -/
theorem actual_next_exponent_card_le_one_of_top
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : 4 ≤ Fintype.card V)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1) :
    ((Finset.univ : Finset V).filter
      (fun i => centreExponent (C i) t = n - 2)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  have hsa : s ≠ a := by
    intro h
    have hh := congrArg
      (fun v : V => centreExponent (C v) t) h
    rw [hs, ha] at hh
    omega
  have hsb : s ≠ b := by
    intro h
    have hh := congrArg
      (fun v : V => centreExponent (C v) t) h
    rw [hs, hb] at hh
    omega
  obtain ⟨c, hsc, hac, hbc⟩ :=
    exists_fourth_of_card_ge_four hcard hsa hsb hab
  exact no_top_and_two_next_with_fourth
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc
    (C s) (C a) (C b) hs ha hb

#print axioms exists_fourth_of_card_ge_four
#print axioms actual_next_exponent_card_le_one_of_top

end JSP000404Research
