import JSP000404Research.SecondLayerFourSupportTerminal
import JSP000404Research.SecondLayerExactTwoSkinnyTerminal
import Mathlib.Tactic

/-!
# Geometric compression of the four-second-layer terminal

Replace the exact-two support branch's quotient bookkeeping by its geometric
consequence: both support-two centres force skinny triangles with a genuine
(n-1)*lambda angle.
-/

namespace JSP000404Research

def ThreeSupportTwoAmongFour
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (t : ℝ)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (a b c d : V) : Prop :=
  ∃ x y z : V,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    x ∈ ({a,b,c,d} : Finset V) ∧
    y ∈ ({a,b,c,d} : Finset V) ∧
    z ∈ ({a,b,c,d} : Finset V) ∧
    positiveSupport (centreQuotient (C x) t) = 2 ∧
    positiveSupport (centreQuotient (C y) t) = 2 ∧
    positiveSupport (centreQuotient (C z) t) = 2

def ExactTwoSupportSkinnyTerminal
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (t lam : ℝ) (n : ℕ)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (a b c d : V) : Prop :=
  ∃ s₁ s₂ o₁ o₂ : V,
    s₁ ≠ s₂ ∧ s₁ ≠ o₁ ∧ s₁ ≠ o₂ ∧
    s₂ ≠ o₁ ∧ s₂ ≠ o₂ ∧ o₁ ≠ o₂ ∧
    s₁ ∈ ({a,b,c,d} : Finset V) ∧
    s₂ ∈ ({a,b,c,d} : Finset V) ∧
    o₁ ∈ ({a,b,c,d} : Finset V) ∧
    o₂ ∈ ({a,b,c,d} : Finset V) ∧
    positiveSupport (centreQuotient (C s₁) t) = 2 ∧
    positiveSupport (centreQuotient (C s₂) t) = 2 ∧
    positiveSupport (centreQuotient (C o₁) t) = 1 ∧
    positiveSupport (centreQuotient (C o₂) t) = 1 ∧
    SupportTwoSkinnyTriangle p lam n s₁ ∧
    SupportTwoSkinnyTriangle p lam n s₂

theorem four_secondLayer_geometric_terminal
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haSecond : centreExponent (C a) t = n - 2)
    (hbSecond : centreExponent (C b) t = n - 2)
    (hcSecond : centreExponent (C c) t = n - 2)
    (hdSecond : centreExponent (C d) t = n - 2) :
    ThreeSupportTwoAmongFour hp t C a b c d ∨
    ExactTwoSupportSkinnyTerminal hp t lam n C a b c d := by
  have hterm :=
    four_secondLayer_support_terminal
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      hab hac had hbc hbd hcd
      haSecond hbSecond hcSecond hdSecond
  rcases hterm with hthree | hexact
  · exact Or.inl hthree
  · right
    obtain ⟨s₁,s₂,o₁,o₂,
      hs12,hs1o1,hs1o2,hs2o1,hs2o2,ho12,
      hs1Mem,hs2Mem,ho1Mem,ho2Mem,
      hs1Support,hs2Support,ho1Support,ho2Support,
      _cert1,_cert2,_hq1,_hq2,_hidden1,_hidden2⟩ := hexact

    have second_of_mem :
        ∀ {q : V},
          q ∈ ({a,b,c,d} : Finset V) →
          centreExponent (C q) t = n - 2 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact haSecond
      · exact hbSecond
      · exact hcSecond
      · exact hdSecond

    have hs1Second := second_of_mem hs1Mem
    have hs2Second := second_of_mem hs2Mem
    have ho1Second := second_of_mem ho1Mem
    have ho2Second := second_of_mem ho2Mem

    have hskinny :=
      twoSupportOne_twoSupportTwo_force_two_skinny_triangles
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        ho12 hs1o1.symm hs2o1.symm
        hs1o2.symm hs2o2.symm hs12
        (C o₁) (C o₂) (C s₁) (C s₂)
        ho1Second ho2Second hs1Second hs2Second
        ho1Support ho2Support hs1Support hs2Support

    exact ⟨s₁,s₂,o₁,o₂,
      hs12,hs1o1,hs1o2,hs2o1,hs2o2,ho12,
      hs1Mem,hs2Mem,ho1Mem,ho2Mem,
      hs1Support,hs2Support,ho1Support,ho2Support,
      hskinny.1,hskinny.2⟩

#print axioms four_secondLayer_geometric_terminal

end JSP000404Research
