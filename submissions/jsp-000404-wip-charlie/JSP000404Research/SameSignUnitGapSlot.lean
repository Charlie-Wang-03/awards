import JSP000404Research.SixPointUnitGapSlots
import JSP000404Research.UnitSameSignOccurrence
import Mathlib.Tactic

/-!
# Positioning a same-sign unit occurrence at a concrete unit-gap slot

SameSignQuotientOccurs is value-level and recursive.  Phase-cover terminals,
however, use the concrete dependent slot type

  GlobalUnitGapSlot C t = Sigma centre, {gap-index // quotient=1}.

This file recovers the exact prefix index of a same-sign occurrence and turns
it into such a slot.  The resulting certificate records that the chosen slot
is aligned with a same-sign step of one displayed lifted centre sign path.
-/

namespace JSP000404Research

/-- Positional certificate for a concrete local unit-gap slot being carried by
a same-sign step. -/
def CentreUnitGapSameSign
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t) : Prop :=
  ∃ first : OtherVertex i,
    ∃ rest : List (OtherVertex i),
    ∃ signPre signPost : List Bool,
    ∃ qPre qPost : List ℕ,
    ∃ b : Bool,
      C.rays = first :: rest ∧
      liftedCentreSignPath hp i first rest =
        signPre ++ b :: signPost ∧
      quotientList t C.gaps =
        qPre ++ 1 :: qPost ∧
      signPre.length = qPre.length ∧
      qPre.length = u.1.val ∧
      boolLastFrom (raySignAt hp i first) signPre = b

/-- Global version for the sigma slot type. -/
def GlobalUnitGapSameSign
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) : Prop :=
  CentreUnitGapSameSign (C u.1) t u.2

/-- Recursive same-sign occurrence exposes an aligned list split. -/
theorem sameSignQuotientOccurs_split
    (q : ℕ)
    (a : Bool)
    (signs : List Bool)
    (qs : List ℕ)
    (hocc : SameSignQuotientOccurs q a signs qs) :
    ∃ signPre signPost : List Bool,
    ∃ qPre qPost : List ℕ,
    ∃ b : Bool,
      signs = signPre ++ b :: signPost ∧
      qs = qPre ++ q :: qPost ∧
      signPre.length = qPre.length ∧
      boolLastFrom a signPre = b := by
  induction signs generalizing a qs with
  | nil =>
      cases qs <;> simp [SameSignQuotientOccurs] at hocc
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [SameSignQuotientOccurs] at hocc
      | cons r rs =>
          simp only [SameSignQuotientOccurs] at hocc
          rcases hocc with hhead | htail
          · rcases hhead with ⟨hr, hab⟩
            subst r
            refine ⟨[], bs, [], rs, b, ?_, ?_, rfl, ?_⟩
            · simp
            · simp
            · simpa [boolLastFrom] using hab
          · obtain ⟨signPre, signPost, qPre, qPost, c,
                hsigns, hqs, hlen, hlast⟩ :=
              ih b rs htail
            refine ⟨b :: signPre, signPost,
              r :: qPre, qPost, c, ?_, ?_, ?_, ?_⟩
            · simp [hsigns, List.append_assoc]
            · simp [hqs, List.append_assoc]
            · simp [hlen]
            · simpa [boolLastFrom] using hlast

/-- Convert a same-sign unit occurrence on a displayed concrete centre path
into an actual CentreUnitGap slot with the same-sign positional certificate. -/
theorem exists_centreUnitGap_sameSign_of_occurs
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hocc :
      SameSignQuotientOccurs 1
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps)) :
    ∃ u : CentreUnitGap C t,
      CentreUnitGapSameSign C t u := by
  obtain ⟨signPre, signPost, qPre, qPost, b,
      hsigns, hqs, hlen, hlast⟩ :=
    sameSignQuotientOccurs_split
      1 (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps) hocc
  have hqLen :
      (quotientList t C.gaps).length =
        qPre.length + 1 + qPost.length := by
    rw [hqs]
    simp
  have hmGap :
      qPre.length < C.gaps.length := by
    rw [quotientList_length] at hqLen
    omega
  let rGap : Fin C.gaps.length :=
    ⟨qPre.length, hmGap⟩
  let rQ : Fin (quotientList t C.gaps).length :=
    ⟨qPre.length, by
      simpa [quotientList_length] using hmGap⟩
  have hqAt :
      (quotientList t C.gaps).get rQ = 1 := by
    dsimp [rQ]
    rw [hqs]
    simp
  have hbridge :
      centreQuotient C t rGap =
        (quotientList t C.gaps).get rQ := by
    simp [centreQuotient, quotientList, rGap, rQ]
  have hunit :
      centreQuotient C t rGap = 1 := by
    rw [hbridge, hqAt]
  let u : CentreUnitGap C t := ⟨rGap, hunit⟩
  refine ⟨u, first, rest,
    signPre, signPost, qPre, qPost, b,
    hrays, hsigns, hqs, hlen, ?_, hlast⟩
  rfl

/-- Global sigma-slot version. -/
theorem exists_globalUnitGap_sameSign_of_occurs
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : (C i).rays = first :: rest)
    (hocc :
      SameSignQuotientOccurs 1
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t (C i).gaps)) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧
      GlobalUnitGapSameSign C t u := by
  obtain ⟨u, hu⟩ :=
    exists_centreUnitGap_sameSign_of_occurs
      (C i) t first rest hrays hocc
  exact ⟨⟨i, u⟩, rfl, hu⟩

#print axioms sameSignQuotientOccurs_split
#print axioms exists_centreUnitGap_sameSign_of_occurs
#print axioms exists_globalUnitGap_sameSign_of_occurs

end JSP000404Research
