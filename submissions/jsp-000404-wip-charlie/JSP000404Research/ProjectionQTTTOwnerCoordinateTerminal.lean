import JSP000404Research.SecondLayerFourSupportTerminal
import JSP000404Research.ProjectionExactTwoAllPalettesConsecutive
import Mathlib.Tactic

/-!
# Q/T/T/T support terminal with exact-two owner-palette rigidity

For a saturated Q/T/T/T configuration on four second-layer projected-loss
centres, the support-pattern terminal has two outcomes.

* At least three of the four centres are support-two.
* Exactly two are support-two.  Then all four retained palettes are
  consecutive triples.  Since the Q/T/T/T completion owner s has retained
  active set exactly {cx,cy,cz}, the three owner coordinates themselves are
  consecutive natural labels.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_QTTT_threeSupport_or_ownerCoordinates_consecutive
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
    {s x y z : ProjectionOrdered V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
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
    {cx cy cz : Fin n}
    (hsActive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R s = {cx,cy,cz}) :
    ThreeSupportTwoAmongFour
      (reindexedPoint_injective hp) t C s x y z
    ∨
    ∃ m : ℕ,
      ({cx.val,cy.val,cz.val} : Finset ℕ) =
        {m,m+1,m+2} := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  have hcapR :
      AngleCap (reindexedPoint p) lam :=
    angleCap_reindexed hcap

  have hterm :=
    four_secondLayer_support_terminal
      (p := reindexedPoint p)
      (reindexedPoint_injective hp)
      hcapR hn3 hdelta0 hdeltaHalf ht hlam C
      hsx hsy hsz hxy hxz hyz
      hsSecond hxSecond hySecond hzSecond

  rcases hterm with hthree | hexact
  · exact Or.inl hthree
  · right
    obtain ⟨s₁,s₂,o₁,o₂,
      hs12,hs1o1,hs1o2,hs2o1,hs2o2,ho12,
      hs1Mem,hs2Mem,ho1Mem,ho2Mem,
      hs1Support,hs2Support,ho1Support,ho2Support,
      cert₁,cert₂,hqe1,hqe2,_hidden1,_hidden2⟩ := hexact

    have loss_of_mem :
        ∀ {q : ProjectionOrdered V},
          q ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) →
          q ∈ projectedLossVertices R
            (planarCentreExponent hp C) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hsLoss
      · exact hxLoss
      · exact hyLoss
      · exact hzLoss

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

    obtain ⟨mo₁,mo₂,ms₁,ms₂,
      hpo1,hpo2,hps1,hps2⟩ :=
      exactTwo_support_four_projectedLoss_palettes_consecutive
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
        (loss_of_mem ho1Mem)
        (loss_of_mem ho2Mem)
        (loss_of_mem hs1Mem)
        (loss_of_mem hs2Mem)
        (second_of_mem ho1Mem)
        (second_of_mem ho2Mem)
        (second_of_mem hs1Mem)
        (second_of_mem hs2Mem)
        ho1Support ho2Support hs1Support hs2Support
        cert₁ cert₂ hqe1 hqe2

    have hnamedSub :
        ({s₁,s₂,o₁,o₂} :
          Finset (ProjectionOrdered V))
          ⊆
        ({s,x,y,z} :
          Finset (ProjectionOrdered V)) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hs1Mem
      · exact hs2Mem
      · exact ho1Mem
      · exact ho2Mem

    have hnamedCard :
        ({s₁,s₂,o₁,o₂} :
          Finset (ProjectionOrdered V)).card = 4 := by
      simp [hs12,hs1o1,hs1o2,hs2o1,hs2o2,ho12,
        Ne.symm hs12,Ne.symm hs1o1,Ne.symm hs1o2,
        Ne.symm hs2o1,Ne.symm hs2o2,Ne.symm ho12]

    have horigCard :
        ({s,x,y,z} :
          Finset (ProjectionOrdered V)).card = 4 := by
      simp [hsx,hsy,hsz,hxy,hxz,hyz,
        Ne.symm hsx,Ne.symm hsy,Ne.symm hsz,
        Ne.symm hxy,Ne.symm hxz,Ne.symm hyz]

    have hsets :
        ({s₁,s₂,o₁,o₂} :
          Finset (ProjectionOrdered V))
          =
        ({s,x,y,z} :
          Finset (ProjectionOrdered V)) := by
      apply Finset.eq_of_subset_of_card_le hnamedSub
      rw [hnamedCard,horigCard]

    have hsNamed :
        s ∈ ({s₁,s₂,o₁,o₂} :
          Finset (ProjectionOrdered V)) := by
      rw [hsets]
      simp

    have hsPalette :
        ∃ m : ℕ,
          (retainedActive R s).map Fin.valEmbedding =
            {m,m+1,m+2} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsNamed
      rcases hsNamed with hs1 | hs2 | ho1 | ho2
      · subst s₁
        exact ⟨ms₁,by simpa [R] using hps1⟩
      · subst s₂
        exact ⟨ms₂,by simpa [R] using hps2⟩
      · subst o₁
        exact ⟨mo₁,by simpa [R] using hpo1⟩
      · subst o₂
        exact ⟨mo₂,by simpa [R] using hpo2⟩

    obtain ⟨m,hm⟩ := hsPalette
    refine ⟨m,?_⟩
    have hsActive' :
        retainedActive R s = {cx,cy,cz} := by
      simpa [R] using hsActive
    rw [hsActive'] at hm
    simpa using hm

#print axioms planar_QTTT_threeSupport_or_ownerCoordinates_consecutive

end ProjectionOrdered
end JSP000404Research
