import JSP000404Research.ProjectionExactTwoAllPalettesConsecutive
import JSP000404Research.ResidualQTTTConsecutivePaletteTerminal
import Mathlib.Tactic

/-!
# Exact-two planar Q/T/T/T whole-cube terminal

The exact-two support branch names the four Q/T/T/T vertices by support role:
two support-one centres o1,o2 and two unit-transition support-two centres
u1,u2.  Because these are four distinct members of the four-element Q/T/T/T
set {s,x,y,z}, the two finite sets are equal.

Hence the consecutive-palette witnesses proved in support-role coordinates can
be transferred back to the Q/T/T/T coordinates s,x,y,z.  The generic
consecutive-palette Q/T/T/T theorem then forces a whole translated slice to
equal the completion owner's cube.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem four_distinct_members_eq_four_set
    {α : Type*} [DecidableEq α]
    {a b c d s x y z : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : a ∈ ({s,x,y,z} : Finset α))
    (hb : b ∈ ({s,x,y,z} : Finset α))
    (hc : c ∈ ({s,x,y,z} : Finset α))
    (hd : d ∈ ({s,x,y,z} : Finset α)) :
    ({a,b,c,d} : Finset α) = {s,x,y,z} := by
  have hsub :
      ({a,b,c,d} : Finset α) ⊆ {s,x,y,z} := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hleft : ({a,b,c,d} : Finset α).card = 4 := by
    simp [hab,hac,had,hbc,hbd,hcd,
      Ne.symm hab,Ne.symm hac,Ne.symm had,
      Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
  have hright : ({s,x,y,z} : Finset α).card = 4 := by
    simp [hsx,hsy,hsz,hxy,hxz,hyz,
      Ne.symm hsx,Ne.symm hsy,Ne.symm hsz,
      Ne.symm hxy,Ne.symm hxz,Ne.symm hyz]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem exactTwo_QTTT_palettes_consecutive_by_role_transfer
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
    {s x y z o₁ o₂ u₁ u₂ : ProjectionOrdered V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ho12 : o₁ ≠ o₂)
    (ho1u1 : o₁ ≠ u₁) (ho1u2 : o₁ ≠ u₂)
    (ho2u1 : o₂ ≠ u₁) (ho2u2 : o₂ ≠ u₂)
    (hu12 : u₁ ≠ u₂)
    (ho1Mem : o₁ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
    (ho2Mem : o₂ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
    (hu1Mem : u₁ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
    (hu2Mem : u₂ ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)))
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
    (ho1Support :
      positiveSupport (centreQuotient (C o₁) t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient (C o₂) t) = 1)
    (hu1Support :
      positiveSupport (centreQuotient (C u₁) t) = 2)
    (hu2Support :
      positiveSupport (centreQuotient (C u₂) t) = 2)
    (cert₁ :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t u₁ (C u₁))
    (cert₂ :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t u₂ (C u₂))
    (hqe1 : cert₁.qe = 1)
    (hqe2 : cert₂.qe = 1) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    ∃ ms mx my mz : ℕ,
      (retainedActive R s).map Fin.valEmbedding = threeNatInterval ms ∧
      (retainedActive R x).map Fin.valEmbedding = threeNatInterval mx ∧
      (retainedActive R y).map Fin.valEmbedding = threeNatInterval my ∧
      (retainedActive R z).map Fin.valEmbedding = threeNatInterval mz := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  have hset :
      ({o₁,o₂,u₁,u₂} : Finset (ProjectionOrdered V)) =
        {s,x,y,z} :=
    four_distinct_members_eq_four_set
      ho12 ho1u1 ho1u2 ho2u1 ho2u2 hu12
      hsx hsy hsz hxy hxz hyz
      ho1Mem ho2Mem hu1Mem hu2Mem

  have loss_of_mem :
      ∀ {q : ProjectionOrdered V},
        q ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) →
        q ∈ projectedLossVertices R (planarCentreExponent hp C) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simpa [R] using hsLoss
    · simpa [R] using hxLoss
    · simpa [R] using hyLoss
    · simpa [R] using hzLoss

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

  have ho1Loss := loss_of_mem ho1Mem
  have ho2Loss := loss_of_mem ho2Mem
  have hu1Loss := loss_of_mem hu1Mem
  have hu2Loss := loss_of_mem hu2Mem
  have ho1Second := second_of_mem ho1Mem
  have ho2Second := second_of_mem ho2Mem
  have hu1Second := second_of_mem hu1Mem
  have hu2Second := second_of_mem hu2Mem

  obtain ⟨mo₁,mo₂,mu₁,mu₂,hpo1,hpo2,hpu1,hpu2⟩ :=
    exactTwo_support_four_projectedLoss_palettes_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      (by simpa [R] using ho1Loss)
      (by simpa [R] using ho2Loss)
      (by simpa [R] using hu1Loss)
      (by simpa [R] using hu2Loss)
      ho1Second ho2Second hu1Second hu2Second
      ho1Support ho2Support hu1Support hu2Support
      cert₁ cert₂ hqe1 hqe2

  have palette_of_mem :
      ∀ {q : ProjectionOrdered V},
        q ∈ ({s,x,y,z} : Finset (ProjectionOrdered V)) →
        ∃ m : ℕ,
          (retainedActive R q).map Fin.valEmbedding =
            threeNatInterval m := by
    intro q hq
    have hq' :
        q ∈ ({o₁,o₂,u₁,u₂} : Finset (ProjectionOrdered V)) := by
      rw [hset]
      exact hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
    rcases hq' with rfl | rfl | rfl | rfl
    · exact ⟨mo₁,by simpa [threeNatInterval] using hpo1⟩
    · exact ⟨mo₂,by simpa [threeNatInterval] using hpo2⟩
    · exact ⟨mu₁,by simpa [threeNatInterval] using hpu1⟩
    · exact ⟨mu₂,by simpa [threeNatInterval] using hpu2⟩

  obtain ⟨ms,hps⟩ := palette_of_mem (by simp : s ∈ ({s,x,y,z} : Finset _))
  obtain ⟨mx,hpx⟩ := palette_of_mem (by simp : x ∈ ({s,x,y,z} : Finset _))
  obtain ⟨my,hpy⟩ := palette_of_mem (by simp : y ∈ ({s,x,y,z} : Finset _))
  obtain ⟨mz,hpz⟩ := palette_of_mem (by simp : z ∈ ({s,x,y,z} : Finset _))
  exact ⟨ms,mx,my,mz,hps,hpx,hpy,hpz⟩

#print axioms exactTwo_QTTT_palettes_consecutive_by_role_transfer

end ProjectionOrdered
end JSP000404Research
