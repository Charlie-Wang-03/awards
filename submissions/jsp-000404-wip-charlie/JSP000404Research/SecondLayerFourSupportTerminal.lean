import JSP000404Research.SecondLayerFourSupportReduction
import Mathlib.Tactic

/-!
# Four-second-layer support-pattern compression

Four distinct second-layer centres admit only two support terminals:

* at least three of the four centres are support-two; or
* exactly two are support-two and the other two are support-one.  In the
  exact-two case, four-centre transition packing forces both support-two
  transition quotients to equal one and exposes a hidden quotient n-1 at
  each support-two centre.
-/

namespace JSP000404Research

def FourSecondLayerSupportTerminal
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ) (n : ℕ)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (a b c d : V) : Prop :=
  (
    ∃ x y z : V,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      x ∈ ({a,b,c,d} : Finset V) ∧
      y ∈ ({a,b,c,d} : Finset V) ∧
      z ∈ ({a,b,c,d} : Finset V) ∧
      positiveSupport (centreQuotient (C x) t) = 2 ∧
      positiveSupport (centreQuotient (C y) t) = 2 ∧
      positiveSupport (centreQuotient (C z) t) = 2
  )
  ∨
  (
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
      ∃ cert₁ : HighExponentTransitionIntervalCertificate hp t s₁ (C s₁),
      ∃ cert₂ : HighExponentTransitionIntervalCertificate hp t s₂ (C s₂),
        cert₁.qe = 1 ∧ cert₂.qe = 1 ∧
        (n - 1 ∈ quotientList t (C s₁).gaps) ∧
        (n - 1 ∈ quotientList t (C s₂).gaps)
  )

theorem four_secondLayer_support_terminal
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
    FourSecondLayerSupportTerminal hp t n C a b c d := by
  have htwo :=
    four_secondLayer_has_two_supportTwo_of_three_le_n
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      hab hac had hbc hbd hcd
      haSecond hbSecond hcSecond hdSecond

  have exactTwo
      {o₁ o₂ s₁ s₂ : V}
      (ho12 : o₁ ≠ o₂)
      (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
      (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
      (hs12 : s₁ ≠ s₂)
      (ho1Mem : o₁ ∈ ({a,b,c,d} : Finset V))
      (ho2Mem : o₂ ∈ ({a,b,c,d} : Finset V))
      (hs1Mem : s₁ ∈ ({a,b,c,d} : Finset V))
      (hs2Mem : s₂ ∈ ({a,b,c,d} : Finset V))
      (ho1Second : centreExponent (C o₁) t = n - 2)
      (ho2Second : centreExponent (C o₂) t = n - 2)
      (hs1Second : centreExponent (C s₁) t = n - 2)
      (hs2Second : centreExponent (C s₂) t = n - 2)
      (ho1Support : positiveSupport (centreQuotient (C o₁) t) = 1)
      (ho2Support : positiveSupport (centreQuotient (C o₂) t) = 1)
      (hs1Support : positiveSupport (centreQuotient (C s₁) t) = 2)
      (hs2Support : positiveSupport (centreQuotient (C s₂) t) = 2) :
      FourSecondLayerSupportTerminal hp t n C a b c d := by
    obtain ⟨cert₁,cert₂,hq1,hq2,hhidden1,hhidden2⟩ :=
      twoSupportOne_twoSupportTwo_transition_qe_eq_one
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
        (C o₁) (C o₂) (C s₁) (C s₂)
        ho1Second ho2Second hs1Second hs2Second
        ho1Support ho2Support hs1Support hs2Support
    exact Or.inr
      ⟨s₁,s₂,o₁,o₂,
        hs12,ho1s1.symm,ho2s1.symm,
        ho1s2.symm,ho2s2.symm,ho12,
        hs1Mem,hs2Mem,ho1Mem,ho2Mem,
        hs1Support,hs2Support,ho1Support,ho2Support,
        cert₁,cert₂,hq1,hq2,hhidden1,hhidden2⟩

  have ha :=
    deficit_two_support_one_or_two_concrete
      (C a) hn3 hdelta0 hdeltaHalf ht haSecond
  have hb :=
    deficit_two_support_one_or_two_concrete
      (C b) hn3 hdelta0 hdeltaHalf ht hbSecond
  have hc :=
    deficit_two_support_one_or_two_concrete
      (C c) hn3 hdelta0 hdeltaHalf ht hcSecond
  have hd :=
    deficit_two_support_one_or_two_concrete
      (C d) hn3 hdelta0 hdeltaHalf ht hdSecond

  rcases ha with ha1 | ha2 <;>
    rcases hb with hb1 | hb2 <;>
    rcases hc with hc1 | hc2 <;>
    rcases hd with hd1 | hd2
  · exfalso
    rcases htwo with ⟨x,y,hxy,hxMem,hyMem,hx2,hy2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxMem hyMem
    rcases hxMem with rfl | rfl | rfl | rfl <;>
      rcases hyMem with rfl | rfl | rfl | rfl <;>
      simp_all
  · exfalso
    rcases htwo with ⟨x,y,hxy,hxMem,hyMem,hx2,hy2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxMem hyMem
    rcases hxMem with rfl | rfl | rfl | rfl <;>
      rcases hyMem with rfl | rfl | rfl | rfl <;>
      simp_all
  · exfalso
    rcases htwo with ⟨x,y,hxy,hxMem,hyMem,hx2,hy2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxMem hyMem
    rcases hxMem with rfl | rfl | rfl | rfl <;>
      rcases hyMem with rfl | rfl | rfl | rfl <;>
      simp_all
  · exact exactTwo
      hcd hac.symm hbc.symm had.symm hbd.symm hab
      (by simp) (by simp) (by simp) (by simp)
      hcSecond hdSecond haSecond hbSecond
      hc1 hd1 ha2 hb2
  · exfalso
    rcases htwo with ⟨x,y,hxy,hxMem,hyMem,hx2,hy2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxMem hyMem
    rcases hxMem with rfl | rfl | rfl | rfl <;>
      rcases hyMem with rfl | rfl | rfl | rfl <;>
      simp_all
  · exact exactTwo
      hbd hab.symm hbc had.symm hcd.symm hac
      (by simp) (by simp) (by simp) (by simp)
      hbSecond hdSecond haSecond hcSecond
      hb1 hd1 ha2 hc2
  · exact exactTwo
      hbc hab.symm hbd hac.symm hcd had
      (by simp) (by simp) (by simp) (by simp)
      hbSecond hcSecond haSecond hdSecond
      hb1 hc1 ha2 hd2
  · exact Or.inl
      ⟨b,c,d,hbc,hbd,hcd,by simp,by simp,by simp,hb2,hc2,hd2⟩
  · exfalso
    rcases htwo with ⟨x,y,hxy,hxMem,hyMem,hx2,hy2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxMem hyMem
    rcases hxMem with rfl | rfl | rfl | rfl <;>
      rcases hyMem with rfl | rfl | rfl | rfl <;>
      simp_all
  · exact exactTwo
      had hab hac hbd.symm hcd.symm hbc
      (by simp) (by simp) (by simp) (by simp)
      haSecond hdSecond hbSecond hcSecond
      ha1 hd1 hb2 hc2
  · exact exactTwo
      hac hab had hbc.symm hcd hbd
      (by simp) (by simp) (by simp) (by simp)
      haSecond hcSecond hbSecond hdSecond
      ha1 hc1 hb2 hd2
  · exact Or.inl
      ⟨b,c,d,hbc,hbd,hcd,by simp,by simp,by simp,hb2,hc2,hd2⟩
  · exact exactTwo
      hab hac had hbc hbd hcd
      (by simp) (by simp) (by simp) (by simp)
      haSecond hbSecond hcSecond hdSecond
      ha1 hb1 hc2 hd2
  · exact Or.inl
      ⟨a,c,d,hac,had,hcd,by simp,by simp,by simp,ha2,hc2,hd2⟩
  · exact Or.inl
      ⟨a,b,d,hab,had,hbd,by simp,by simp,by simp,ha2,hb2,hd2⟩
  · exact Or.inl
      ⟨a,b,c,hab,hac,hbc,by simp,by simp,by simp,ha2,hb2,hc2⟩

#print axioms four_secondLayer_support_terminal

end JSP000404Research
