import JSP000404Research.QTTTThreeSupportSmallPairMatching
import Mathlib.Tactic

/-!
# Kernel-small finite terminal for the three-support branch

This module deliberately does not import the exact-two / whole-cube chain.
It records the part of the four-second-layer geometry that can be checked
independently:

if three distinct members of four distinct second-layer centres have quotient
support two, then the fourth member can be chosen and the configuration lies
in one of the eleven crossed small-angle states.

The exact-two support branch is left explicit elsewhere until its current
dependency chain is repaired.
-/

namespace JSP000404Research

theorem four_distinct_choose_fourth_of_three_members
    {V : Type*} [DecidableEq V]
    {s x y z a b c : V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : a ∈ ({s,x,y,z} : Finset V))
    (hb : b ∈ ({s,x,y,z} : Finset V))
    (hc : c ∈ ({s,x,y,z} : Finset V))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ d : V,
      d ∈ ({s,x,y,z} : Finset V) ∧
      a ≠ d ∧ b ≠ d ∧ c ≠ d := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;>
    simp_all
  all_goals
    first
    | exact ⟨s,by simp,by simp_all,by simp_all,by simp_all⟩
    | exact ⟨x,by simp,by simp_all,by simp_all,by simp_all⟩
    | exact ⟨y,by simp,by simp_all,by simp_all,by simp_all⟩
    | exact ⟨z,by simp,by simp_all,by simp_all,by simp_all⟩

theorem four_secondLayer_threeSupport_reduce_to_eleven
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ q : V, CentreProjectiveCycle hp q)
    {s x y z a b c : V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsSecond : centreExponent (C s) t = n - 2)
    (hxSecond : centreExponent (C x) t = n - 2)
    (hySecond : centreExponent (C y) t = n - 2)
    (hzSecond : centreExponent (C z) t = n - 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haMem : a ∈ ({s,x,y,z} : Finset V))
    (hbMem : b ∈ ({s,x,y,z} : Finset V))
    (hcMem : c ∈ ({s,x,y,z} : Finset V))
    (haSupport : positiveSupport (centreQuotient (C a) t) = 2)
    (hbSupport : positiveSupport (centreQuotient (C b) t) = 2)
    (hcSupport : positiveSupport (centreQuotient (C c) t) = 2) :
    ∃ d : V,
      a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      d ∈ ({s,x,y,z} : Finset V) ∧
      ThreeSupportTwoCrossedPattern11 p delta lam a b c d := by
  obtain ⟨d,hdMem,had,hbd,hcd⟩ :=
    four_distinct_choose_fourth_of_three_members
      hsx hsy hsz hxy hxz hyz
      haMem hbMem hcMem hab hac hbc

  have second_of_mem :
      ∀ {q : V},
        q ∈ ({s,x,y,z} : Finset V) →
        centreExponent (C q) t = n - 2 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hsSecond
    · exact hxSecond
    · exact hySecond
    · exact hzSecond

  have hpattern :=
    three_supportTwo_secondLayer_four_reduce_to_eleven
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab hac had hbc hbd hcd
      C
      (second_of_mem haMem)
      (second_of_mem hbMem)
      (second_of_mem hcMem)
      haSupport hbSupport hcSupport

  exact ⟨d,had,hbd,hcd,hdMem,hpattern⟩

#print axioms four_distinct_choose_fourth_of_three_members
#print axioms four_secondLayer_threeSupport_reduce_to_eleven

end JSP000404Research
