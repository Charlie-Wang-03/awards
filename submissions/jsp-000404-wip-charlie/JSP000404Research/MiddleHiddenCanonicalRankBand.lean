import JSP000404Research.SupportThreeMiddleHiddenCanonicalSigns
import JSP000404Research.CanonicalRankMiddleTerminal
import Mathlib.Tactic

/-!
# Canonical-rank band for non-exposed middle-hidden centres

A non-exposed middle-hidden support-three centre has one of five canonical
wrap positions.  In every case there are two displayed non-top rays whose
canonical signs are opposite to the sign of the ray toward the distinguished
top centre.

This coarse fact is enough to force a rank band:

* if i < top in the canonical point order, then 2 <= rank(i) <= 4;
* if top < i, then 1 <= rank(i) <= 3.

Consequently two such centres cannot lie on opposite sides of the same top:
a chain b < top < c would require rank(b)+2 <= rank(c), incompatible with
rank(b)>=2 and rank(c)<=3.
-/

namespace JSP000404Research

theorem canonicalRank_le_card_sub_one
    {V : Type*} [Fintype V]
    (p : V → Plane) (i : V) :
    canonicalRank p i ≤ Fintype.card V - 1 := by
  classical
  unfold canonicalRank
  calc
    ((Finset.univ : Finset V).filter
        (fun v => CanonicalPointLt p v i)).card
        ≤ ((Finset.univ : Finset V).erase i).card := by
          apply Finset.card_le_card
          intro v hv
          have hvlt :
              CanonicalPointLt p v i :=
            (Finset.mem_filter.mp hv).2
          apply Finset.mem_erase.mpr
          constructor
          · intro hvi
            subst v
            exact canonicalPointLt_irrefl (p := p) i hvlt
          · exact Finset.mem_univ v
    _ = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp

theorem two_le_canonicalRank_of_two_predecessors
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {x y i : V}
    (hxy : x ≠ y)
    (hxi : CanonicalPointLt p x i)
    (hyi : CanonicalPointLt p y i) :
    2 ≤ canonicalRank p i := by
  rcases canonicalPointLt_total_of_ne hp hxy with hxylt | hyxlt
  · have h :=
      canonicalRank_add_two_le_of_chain
        (p := p) hxylt hyi
    omega
  · have h :=
      canonicalRank_add_two_le_of_chain
        (p := p) hyxlt hxi
    omega

theorem canonicalRank_le_three_of_two_successors_card_six
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcard : Fintype.card V = 6)
    {i x y : V}
    (hxy : x ≠ y)
    (hix : CanonicalPointLt p i x)
    (hiy : CanonicalPointLt p i y) :
    canonicalRank p i ≤ 3 := by
  rcases canonicalPointLt_total_of_ne hp hxy with hxylt | hyxlt
  · have hchain :=
      canonicalRank_add_two_le_of_chain
        (p := p) hix hxylt
    have hup :=
      canonicalRank_le_card_sub_one p y
    rw [hcard] at hup
    norm_num at hup
    omega
  · have hchain :=
      canonicalRank_add_two_le_of_chain
        (p := p) hiy hyxlt
    have hup :=
      canonicalRank_le_card_sub_one p x
    rw [hcard] at hup
    norm_num at hup
    omega

theorem canonicalRank_le_four_of_below_top_card_six
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hcard : Fintype.card V = 6)
    {i top : V}
    (hit : CanonicalPointLt p i top) :
    canonicalRank p i ≤ 4 := by
  have hlt :=
    canonicalRank_lt_of_lt (p := p) hit
  have hup :=
    canonicalRank_le_card_sub_one p top
  rw [hcard] at hup
  norm_num at hup
  omega

/-- Every non-exposed middle-hidden centre has two displayed rays whose
canonical signs are both opposite to the sign toward top. -/
theorem nonexposed_middle_hidden_opposite_sign_pair
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    {top i : V}
    (htopi : top ≠ i)
    (C : CentreProjectiveCycle hp i)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hnot : ¬ StrictlyExposedAt p i)
    (hmiddle :
      SupportThreePinnedMiddleShape (t := t) hp htopi C) :
    ∃ H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t,
      ∃ x y : OtherVertex i,
        x ≠ y ∧
        raySignAt hp i x =
          !raySignAt hp i
            (⟨top, htopi⟩ : OtherVertex i) ∧
        raySignAt hp i y =
          !raySignAt hp i
            (⟨top, htopi⟩ : OtherVertex i) := by
  obtain ⟨H, hcases⟩ :=
    nonexposed_middle_hidden_canonical_sign_cases
      hp hcap ht htone hlam hcard
      htopi C hsupport hnot hmiddle
  let topRay : OtherVertex i := ⟨top, htopi⟩
  have hnd :
      (topRay :: H.r :: H.b :: H.c :: H.d :: []).Nodup := by
    rw [← H.rays_rotate]
    simpa [topRay] using C.nodup
  have htail :
      (H.r :: H.b :: H.c :: H.d :: []).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hrb : H.r ≠ H.b :=
    (List.nodup_cons.mp htail).1 (by simp)
  have hrc : H.r ≠ H.c :=
    (List.nodup_cons.mp htail).1 (by simp)
  have hbcd :
      (H.b :: H.c :: H.d :: []).Nodup :=
    (List.nodup_cons.mp htail).2
  have hcdTail :
      (H.c :: H.d :: []).Nodup :=
    (List.nodup_cons.mp hbcd).2
  have hcd : H.c ≠ H.d :=
    (List.nodup_cons.mp hcdTail).1 (by simp)

  refine ⟨H, ?_⟩
  dsimp only at hcases
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨_,_,_,_,hc,hd⟩
    exact ⟨H.c,H.d,hcd,hc,hd⟩
  · rcases h1 with ⟨_,_,hr,_,hc,_⟩
    exact ⟨H.r,H.c,hrc,hr,hc⟩
  · rcases h2 with ⟨_,_,hr,hb,_,_⟩
    exact ⟨H.r,H.b,hrb,hr,hb⟩
  · rcases h3 with ⟨_,_,hr,hb,_,_⟩
    exact ⟨H.r,H.b,hrb,hr,hb⟩
  · rcases h4 with ⟨_,_,hr,hb,_,_⟩
    exact ⟨H.r,H.b,hrb,hr,hb⟩

def MiddleHiddenRankBand
    {V : Type*} [Fintype V]
    (p : V → Plane) (top i : V) : Prop :=
  (CanonicalPointLt p i top ∧
      2 ≤ canonicalRank p i ∧
      canonicalRank p i ≤ 4)
    ∨
  (CanonicalPointLt p top i ∧
      1 ≤ canonicalRank p i ∧
      canonicalRank p i ≤ 3)

theorem nonexposed_middle_hidden_rank_band
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    {top i : V}
    (htopi : top ≠ i)
    (C : CentreProjectiveCycle hp i)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hnot : ¬ StrictlyExposedAt p i)
    (hmiddle :
      SupportThreePinnedMiddleShape (t := t) hp htopi C) :
    MiddleHiddenRankBand p top i := by
  obtain ⟨H,x,y,hxy,hxOpp,hyOpp⟩ :=
    nonexposed_middle_hidden_opposite_sign_pair
      hp hcap ht htone hlam hcard
      htopi C hsupport hnot hmiddle
  let topRay : OtherVertex i := ⟨top, htopi⟩
  by_cases hTopTrue :
      raySignAt hp i topRay = true
  · left
    have hiTop :
        CanonicalPointLt p i top :=
      (raySign_true_iff_canonicalPointLt hp htopi).1
        (by simpa [topRay] using hTopTrue)
    have hxFalse :
        raySignAt hp i x = false := by
      rw [hxOpp]
      simpa [topRay, hTopTrue]
    have hyFalse :
        raySignAt hp i y = false := by
      rw [hyOpp]
      simpa [topRay, hTopTrue]
    have hxPred :
        CanonicalPointLt p x.1 i :=
      (raySign_false_iff_reverse_canonicalPointLt
        hp x.2.symm).1 hxFalse
    have hyPred :
        CanonicalPointLt p y.1 i :=
      (raySign_false_iff_reverse_canonicalPointLt
        hp y.2.symm).1 hyFalse
    have hxyVal : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    exact ⟨hiTop,
      two_le_canonicalRank_of_two_predecessors
        hp hxyVal hxPred hyPred,
      canonicalRank_le_four_of_below_top_card_six
        hcard hiTop⟩
  · right
    have hTopFalse :
        raySignAt hp i topRay = false := by
      cases h : raySignAt hp i topRay <;> simp_all
    have hTopI :
        CanonicalPointLt p top i :=
      (raySign_false_iff_reverse_canonicalPointLt
        hp htopi.symm).1
        (by simpa [topRay] using hTopFalse)
    have hxTrue :
        raySignAt hp i x = true := by
      rw [hxOpp]
      simpa [topRay, hTopFalse]
    have hyTrue :
        raySignAt hp i y = true := by
      rw [hyOpp]
      simpa [topRay, hTopFalse]
    have hiX :
        CanonicalPointLt p i x.1 :=
      (raySign_true_iff_canonicalPointLt
        hp x.2.symm).1 hxTrue
    have hiY :
        CanonicalPointLt p i y.1 :=
      (raySign_true_iff_canonicalPointLt
        hp y.2.symm).1 hyTrue
    have hxyVal : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    have hpos :
        1 ≤ canonicalRank p i := by
      have hlt :=
        canonicalRank_lt_of_lt (p := p) hTopI
      omega
    exact ⟨hTopI,hpos,
      canonicalRank_le_three_of_two_successors_card_six
        hp hcard hxyVal hiX hiY⟩

/-- Two rank-band centres cannot straddle top. -/
theorem middleHiddenRankBand_same_side
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {top b c : V}
    (hb : MiddleHiddenRankBand p top b)
    (hc : MiddleHiddenRankBand p top c) :
    (CanonicalPointLt p b top ∧ CanonicalPointLt p c top)
      ∨
    (CanonicalPointLt p top b ∧ CanonicalPointLt p top c) := by
  rcases hb with hb | hb
  · rcases hc with hc | hc
    · exact Or.inl ⟨hb.1,hc.1⟩
    · exfalso
      have hchain :=
        canonicalRank_add_two_le_of_chain
          (p := p) hb.1 hc.1
      omega
  · rcases hc with hc | hc
    · exfalso
      have hchain :=
        canonicalRank_add_two_le_of_chain
          (p := p) hc.1 hb.1
      omega
    · exact Or.inr ⟨hb.1,hc.1⟩

#print axioms canonicalRank_le_card_sub_one
#print axioms two_le_canonicalRank_of_two_predecessors
#print axioms canonicalRank_le_three_of_two_successors_card_six
#print axioms nonexposed_middle_hidden_opposite_sign_pair
#print axioms nonexposed_middle_hidden_rank_band
#print axioms middleHiddenRankBand_same_side

end JSP000404Research
