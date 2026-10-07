import JSP000404Research.ProjectionQTTTSupportOrWholeCube
import JSP000404Research.ProjectionThreeWholeCubeElevenTerminal
import JSP000404Research.ResidualQTTTWholeCubeRecursiveOutlet
import Mathlib.Tactic

/-!
# Q/T/T/T Hall-recursive terminal

This file consumes the current planar Q/T/T/T support-or-whole-cube terminal
inside an inclusion-minimal enlarged Hall obstruction.

There are only two genuine outcomes left.

* If at least three of the four second-layer centres are support-two, choose
  three such centres and the remaining fourth centre.  Their small-pair
  geometry reduces to the explicit eleven crossed patterns.
* If the exact-two branch has upgraded to a whole-cube Q/T pair, the
  minimal-core provenance routes that branch back into the standard recursive
  alphabet: a Boolean hole, a paid surplus blocker, or one of four
  cardinality-at-most-two recursive fibres.

Thus a saturated Q/T/T/T state is no longer a free-standing local terminal:
it is either a finite geometric state or a standard Hall-recursive outlet.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_QTTT_crossed11_or_hall_recursive
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ planarCentreExponent hp C q)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ planarCentreExponent hp C q)
          (planarEnlargedCandidateBlock
            hp hcap (by omega : 1 ≤ n)
            hdelta0 hdeltaHalf ht hlam C)
          U)
    {s x y z : ProjectionOrdered V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxCore : x ∈ T)
    (hyCore : y ∈ T)
    (hthirdCore : s ∈ T ∨ z ∈ T)
    (hsLoss :
      s ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hxLoss :
      x ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hyLoss :
      y ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hzLoss :
      z ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hsSecond : centreExponent (C s) t = n - 2)
    (hxSecond : centreExponent (C x) t = n - 2)
    (hySecond : centreExponent (C y) t = n - 2)
    (hzSecond : centreExponent (C z) t = n - 2)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcx :
      cx ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) x)
    (hcy :
      cy ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) y)
    (hcz :
      cz ∈ retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) z)
    (hcxy : cx ≠ cy) (hcxz : cx ≠ cz) (hcyz : cy ≠ cz)
    (hsActive :
      retainedActive
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) s
        = {cx,cy,cz})
    (hsQ :
      word ∈ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) s)
    (hxT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) x cx)
    (hyT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) y cy)
    (hzT :
      word ∈ translatedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) z cz) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ a b c d : ProjectionOrdered V,
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
        b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        a ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) ∧
        b ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) ∧
        c ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) ∧
        d ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) ∧
        positiveSupport (centreQuotient (C a) t) = 2 ∧
        positiveSupport (centreQuotient (C b) t) = 2 ∧
        positiveSupport (centreQuotient (C c) t) = 2 ∧
        ThreeSupportTwoCrossedPattern11
          (reindexedPoint p) delta lam a b c d
    )
    ∨
    (∃ hole : Fin n → Bool, hole ∉ coveredCompletionWords R)
    ∨
    (∃ blocker : ProjectionOrdered V,
      1 ≤ dyadicProfileSurplus exponent (projectedFree R) blocker)
    ∨
    QTTTWholeCubeRecursiveHardFibre R exponent x cx cy cz
    ∨
    QTTTWholeCubeRecursiveHardFibre R exponent y cy cx cz
    ∨
    QTTTWholeCubeRecursiveHardFibre R exponent z cz cx cy
    ∨
    QTTTWholeCubeRecursiveHardFibre R exponent s cz cx cy := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  have hexpLt :
      ∀ q : ProjectionOrdered V, exponent q < n :=
    planarCentreExponent_lt_n hp hn1 hdelta0 hdelta1 ht C
  have hexp : ∀ q : ProjectionOrdered V, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt (hexpLt q)
  have hone :
      ∀ q : ProjectionOrdered V,
        (active R q).card ≤ n - exponent q + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C

  have hdefR :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [R,exponent,hn1,hdelta1,planarEnlargedCandidateBlock,
      planarCentreExponent] using hdef
  have hminR :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock R exponent)
          U := by
    intro U hUT
    simpa [R,exponent,hn1,hdelta1,planarEnlargedCandidateBlock,
      planarCentreExponent] using hmin U hUT

  have hterm :=
    planar_QTTT_threeSupport_or_wholeCube
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      hsx hsy hsz hxy hxz hyz
      hsLoss hxLoss hyLoss hzLoss
      hsSecond hxSecond hySecond hzSecond
      hcx hcy hcz hcxy hcxz hcyz
      hsActive hsQ hxT hyT hzT

  rcases hterm with hthree | hwhole
  · obtain ⟨a,b,c,hab,hac,hbc,
      haMem,hbMem,hcMem,haSupport,hbSupport,hcSupport⟩ := hthree

    obtain ⟨d,hdMem,had,hbd,hcd⟩ :=
      four_insert_three_distinct_has_fourth
        hsx hsy hsz hxy hxz hyz
        haMem hbMem hcMem hab hac hbc

    have second_of_mem :
        ∀ {q : ProjectionOrdered V},
          q ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) →
          centreExponent (C q) t = n - 2 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hsSecond
      · exact hxSecond
      · exact hySecond
      · exact hzSecond

    have hcapR : AngleCap (reindexedPoint p) lam :=
      angleCap_reindexed hcap

    have hpattern :=
      three_supportTwo_secondLayer_four_reduce_to_eleven
        (reindexedPoint_injective hp)
        hcapR hn3 hdelta0 hdeltaHalf ht hlam
        hab hac had hbc hbd hcd
        C
        (second_of_mem haMem)
        (second_of_mem hbMem)
        (second_of_mem hcMem)
        haSupport hbSupport hcSupport

    exact Or.inl
      ⟨a,b,c,d,
        hab,hac,had,hbc,hbd,hcd,
        haMem,hbMem,hcMem,hdMem,
        haSupport,hbSupport,hcSupport,hpattern⟩

  · have hout :=
      QTTT_wholeCube_hole_or_paid_or_recursive_fibre
        R exponent hexp hone hn3
        hdefR hminR
        hsx hsy hsz
        hxCore hyCore hthirdCore
        (by simpa [R,exponent] using hsLoss)
        (by simpa [R,exponent] using hxLoss)
        (by simpa [R,exponent] using hyLoss)
        (by simpa [R,exponent] using hzLoss)
        (by simpa [exponent,planarCentreExponent] using hsSecond)
        (by simpa [exponent,planarCentreExponent] using hxSecond)
        (by simpa [exponent,planarCentreExponent] using hySecond)
        (by simpa [exponent,planarCentreExponent] using hzSecond)
        (by simpa [R] using hcx)
        (by simpa [R] using hcy)
        (by simpa [R] using hcz)
        (by simpa [R] using hsActive)
        (by simpa [R] using hwhole)

    rcases hout with hhole | hpaid | hxRec | hyRec | hzRec | hsRec
    · exact Or.inr (Or.inl hhole)
    · exact Or.inr (Or.inr (Or.inl hpaid))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hxRec)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hyRec))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hzRec)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hsRec)))))

#print axioms planar_QTTT_crossed11_or_hall_recursive

end ProjectionOrdered
end JSP000404Research
