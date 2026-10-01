import JSP000404Research.SecondLayerFourSupportTerminal
import JSP000404Research.SupportTwoActualNarrowClusters
import Mathlib.Tactic

/-!
# Narrow-angle data for the exact-two support terminal

If four second-layer centres split as two support-one and two support-two,
four-centre transition packing forces the support-two transition quotients to
equal one.  A transition-one support-two centre carries two all-zero quotient
blocks whose total actual-angle mass is at most delta*lambda.

This file packages that concrete angle data so the remaining Q/T/T/T geometry
can reason directly about narrow clusters rather than quotient bookkeeping.
-/

namespace JSP000404Research

def SupportTwoTransitionOneNarrowData
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t delta lam : ℝ} {n : ℕ}
    (i : V)
    (C : CentreProjectiveCycle hp i) : Prop :=
  ∃ first : OtherVertex i,
  ∃ rest : List (OtherVertex i),
    C.rays = first :: rest ∧
    ∃ pre post leftQ rightQ : List ℕ,
    ∃ Apre Apost : List ℝ, ∃ Ae : ℝ,
    ∃ leftA rightA : List ℝ, ∃ Ah : ℝ,
      quotientList t C.gaps = pre ++ 1 :: post ∧
      cyclicRayAngles (p := p) i first rest =
        Apre ++ Ae :: Apost ∧
      pre.length = Apre.length ∧
      post.length = Apost.length ∧
      post ++ pre = leftQ ++ (n - 1) :: rightQ ∧
      Apost ++ Apre = leftA ++ Ah :: rightA ∧
      leftQ.length = leftA.length ∧
      rightQ.length = rightA.length ∧
      (∀ q ∈ leftQ, q = 0) ∧
      (∀ q ∈ rightQ, q = 0) ∧
      leftA.sum + rightA.sum ≤ delta * lam

theorem supportTwo_transition_one_narrowData
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
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    (hqe : cert.qe = 1) :
    SupportTwoTransitionOneNarrowData
      (p := p) hp (t := t) (delta := delta) (lam := lam)
      (n := n) i C := by
  obtain ⟨first,rest,hrays⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases hR : C.rays with
    | nil =>
        exact False.elim (C.nonempty hR)
    | cons first rest =>
        exact ⟨first,rest,hR⟩
  obtain ⟨pre,post,leftQ,rightQ,
      Apre,Apost,Ae,leftA,rightA,Ah,
      hq,hAs,hpreA,hpostA,
      hhiddenQ,hhiddenA,hleftLen,hrightLen,
      hleftZero,hrightZero,hsmall⟩ :=
    supportTwo_transition_one_has_two_narrow_angle_blocks
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C hexp hsupport cert hqe
      first rest hrays
  exact ⟨first,rest,hrays,
    pre,post,leftQ,rightQ,
    Apre,Apost,Ae,leftA,rightA,Ah,
    hq,hAs,hpreA,hpostA,
    hhiddenQ,hhiddenA,hleftLen,hrightLen,
    hleftZero,hrightZero,hsmall⟩

/-- Exact-two support terminal with both unit-transition narrow-cluster
certificates exposed simultaneously. -/
theorem twoSupportOne_twoSupportTwo_have_narrowData
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
    {o₁ o₂ s₁ s₂ : V}
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (Co₁ : CentreProjectiveCycle hp o₁)
    (Co₂ : CentreProjectiveCycle hp o₂)
    (Cs₁ : CentreProjectiveCycle hp s₁)
    (Cs₂ : CentreProjectiveCycle hp s₂)
    (ho1Second : centreExponent Co₁ t = n - 2)
    (ho2Second : centreExponent Co₂ t = n - 2)
    (hs1Second : centreExponent Cs₁ t = n - 2)
    (hs2Second : centreExponent Cs₂ t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient Co₁ t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient Co₂ t) = 1)
    (hs1Support :
      positiveSupport (centreQuotient Cs₁ t) = 2)
    (hs2Support :
      positiveSupport (centreQuotient Cs₂ t) = 2) :
    ∃ cert₁ : HighExponentTransitionIntervalCertificate hp t s₁ Cs₁,
    ∃ cert₂ : HighExponentTransitionIntervalCertificate hp t s₂ Cs₂,
      cert₁.qe = 1 ∧ cert₂.qe = 1 ∧
      (n - 1 ∈ quotientList t Cs₁.gaps) ∧
      (n - 1 ∈ quotientList t Cs₂.gaps) ∧
      SupportTwoTransitionOneNarrowData
        (p := p) hp (t := t) (delta := delta) (lam := lam)
        (n := n) s₁ Cs₁ ∧
      SupportTwoTransitionOneNarrowData
        (p := p) hp (t := t) (delta := delta) (lam := lam)
        (n := n) s₂ Cs₂ := by
  obtain ⟨cert₁,cert₂,hq1,hq2,hhidden1,hhidden2⟩ :=
    twoSupportOne_twoSupportTwo_transition_qe_eq_one
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
      Co₁ Co₂ Cs₁ Cs₂
      ho1Second ho2Second hs1Second hs2Second
      ho1Support ho2Support hs1Support hs2Support
  have hdata1 :=
    supportTwo_transition_one_narrowData
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      Cs₁ hs1Second hs1Support cert₁ hq1
  have hdata2 :=
    supportTwo_transition_one_narrowData
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      Cs₂ hs2Second hs2Support cert₂ hq2
  exact ⟨cert₁,cert₂,hq1,hq2,hhidden1,hhidden2,hdata1,hdata2⟩

#print axioms supportTwo_transition_one_narrowData
#print axioms twoSupportOne_twoSupportTwo_have_narrowData

end JSP000404Research
