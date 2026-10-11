import JSP000404Research.ResidualIncomingUpperCubeDisjoint
import Mathlib.Tactic

/-!
# GLOBAL mass injection of entire hard overlap faces

Assume each truly overlapping hard residual carrier (a,v), a<v,
admits at least one outgoing-retained colour at a that is inactive
at v. Each hard overlap Boolean word has a UNIQUE hard carrier;
choose one safe colour for each carrier, independent of the word.

Flip this carrier's chosen colour. The whole face enters
Q_v \ Q_a and is either SINGLETON-COVERED or SOFT-OVERLAPPED.

The global map is injective:
* distinct hard carriers have distinct upper endpoints, because
  same-retained canonical codes cannot have three distinct vertices;
* the upper completion cubes of distinct residual edge upper
  endpoints are DISJOINT;
* within one carrier, the chosen coordinate flip is involutive.

Therefore, CONDITIONAL on the specified safe colour existing
FOR EVERY hard overlap carrier,

  card(hardOverlapCompletionWords)
    <= card(singletonCompletionWords) + card(softOverlapCompletionWords).

This is a true global full-dyadic-mass transport, not merely
an edge/colour injection. Its destinations remain covered words,
NOT Boolean holes. The existence of safe outgoing colours for
every hard carrier has NOT been proved in general.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The entire hard-to-soft mass transport requires an outward retained
coordinate at the lower endpoint, inactive at the upper endpoint,
for EVERY nonempty same-code overlap carrier. -/
def HasHardOverlapOutgoingTransport
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) : Prop :=
  ∀ p ∈ hardOverlapCarrierPairs C,
    ∃ c : Fin n,
      c ∈ outgoingRetained C p.1 ∧
      c ∉ retainedActive C p.2

/-- Each hard Boolean-overlap word has a chosen unique
same-code residual carrier, represented by its two endpoints. -/
noncomputable def hardWordCarrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {word : Fin n → Bool //
      word ∈ hardOverlapCompletionWords C}) :
    {p : V × V // p ∈ hardOverlapCarrierPairs C} := by
  classical
  have h : ∃ p ∈ hardOverlapCarrierPairs C,
      x.1 ∈ retainedCompletionWords C p.1 ∩
        retainedCompletionWords C p.2 :=
    Finset.mem_biUnion.mp x.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem hardWordCarrier_covers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {word : Fin n → Bool //
      word ∈ hardOverlapCompletionWords C}) :
    x.1 ∈ retainedCompletionWords C (hardWordCarrier C x).1.1 ∩
      retainedCompletionWords C (hardWordCarrier C x).1.2 := by
  classical
  exact (Classical.choose_spec
    (Finset.mem_biUnion.mp x.2)).2

theorem hardWordCarrier_residual
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {word : Fin n → Bool //
      word ∈ hardOverlapCompletionWords C}) :
    (hardWordCarrier C x).1.1 < (hardWordCarrier C x).1.2 ∧
    IsResidual C (hardWordCarrier C x).1.1
      (hardWordCarrier C x).1.2 := by
  have h := (mem_hardOverlapCarrierPairs C
    (hardWordCarrier C x).1).1 (hardWordCarrier C x).2
  exact (mem_residualCarrierPairs C _ _).1
    ((mem_overlapCarrierPairs C _).1 h.1).1

/-- A chosen source coordinate is fixed per hard carrier, not
per Boolean word. Consequently flipping is injective WITHIN
each full d-dimensional source overlap face. -/
noncomputable def hardPairTransportColor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hsafe : HasHardOverlapOutgoingTransport C)
    (p : {p : V × V // p ∈ hardOverlapCarrierPairs C}) :
    Fin n :=
  Classical.choose (hsafe p.1 p.2)

theorem hardPairTransportColor_spec
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hsafe : HasHardOverlapOutgoingTransport C)
    (p : {p : V × V // p ∈ hardOverlapCarrierPairs C}) :
    hardPairTransportColor C hsafe p ∈
        outgoingRetained C p.1.1 ∧
      hardPairTransportColor C hsafe p ∉
        retainedActive C p.1.2 :=
  Classical.choose_spec (hsafe p.1 p.2)

/-- The GLOBAL Boolean-word transport map, with carrier and
colour choices fixed consistently across each hard overlap face. -/
noncomputable def hardOverlapWordGlobalTransport
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hsafe : HasHardOverlapOutgoingTransport C) :
    {word : Fin n → Bool // word ∈ hardOverlapCompletionWords C} →
    {word : Fin n → Bool //
      word ∈ singletonCompletionWords C ∪
        softOverlapCompletionWords C} := by
  classical
  intro x
  let p := hardWordCarrier C x
  let c := hardPairTransportColor C hsafe p
  have hres := hardWordCarrier_residual C x
  have hsame := ((mem_hardOverlapCarrierPairs C p.1).1 p.2).2
  have hc := hardPairTransportColor_spec C hsafe p
  refine ⟨flipCompletionWord c x.1, ?_⟩
  exact hard_overlap_full_face_flip_singleton_or_soft
    C (ne_of_lt hres.1) hsame hc.1 hc.2
      (hardWordCarrier_covers C x)

/-- Each transported hard-overlap word stays in the completion
cube of its OWN residual carrier's upper endpoint. -/
theorem hardOverlapWordGlobalTransport_mem_upper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hsafe : HasHardOverlapOutgoingTransport C)
    (x : {word : Fin n → Bool //
      word ∈ hardOverlapCompletionWords C}) :
    (hardOverlapWordGlobalTransport C hsafe x).1 ∈
      retainedCompletionWords C (hardWordCarrier C x).1.2 := by
  change flipCompletionWord
      (hardPairTransportColor C hsafe (hardWordCarrier C x))
        x.1 ∈ retainedCompletionWords C (hardWordCarrier C x).1.2
  exact flipCompletionWord_mem_upper_of_inactive C
    (hardPairTransportColor_spec C hsafe
      (hardWordCarrier C x)).2
    (Finset.mem_inter.mp (hardWordCarrier_covers C x)).2

/-- Two globally transported hard words cannot collide:
distinct residual upper endpoints have disjoint completion cubes,
and equal upper endpoints force equal hard carriers, with the same
chosen flip coordinate, which is itself injective. -/
theorem hardOverlapWordGlobalTransport_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hsafe : HasHardOverlapOutgoingTransport C) :
    Function.Injective
      (hardOverlapWordGlobalTransport C hsafe) := by
  classical
  intro x y hxy
  let p := hardWordCarrier C x
  let q := hardWordCarrier C y
  have hpRes := hardWordCarrier_residual C x
  have hqRes := hardWordCarrier_residual C y
  have hwordEq :
      (hardOverlapWordGlobalTransport C hsafe x).1 =
      (hardOverlapWordGlobalTransport C hsafe y).1 :=
    congrArg Subtype.val hxy
  have hupper : p.1.2 = q.1.2 := by
    apply residual_upper_completion_word_unique
      C hpRes.1 hqRes.1 hpRes.2 hqRes.2
        (hardOverlapWordGlobalTransport_mem_upper C hsafe x)
    rw [hwordEq]
    exact hardOverlapWordGlobalTransport_mem_upper C hsafe y
  have hpSame := ((mem_hardOverlapCarrierPairs C p.1).1 p.2).2
  have hqSame := ((mem_hardOverlapCarrierPairs C q.1).1 q.2).2
  have hqLt : q.1.1 < p.1.2 := by
    simpa only [hupper] using hqRes.1
  have hqSame' : SameRetained C q.1.1 p.1.2 := by
    simpa only [hupper] using hqSame
  have hlower : p.1.1 = q.1.1 :=
    sameRetained_pairs_same_upper_unique_lower
      C hpRes.1 hqLt hpSame hqSame'
  have hpq : p = q := by
    apply Subtype.ext
    exact Prod.ext hlower hupper
  have hflips :
      flipCompletionWord (hardPairTransportColor C hsafe p) x.1 =
      flipCompletionWord (hardPairTransportColor C hsafe q) y.1 := by
    exact hwordEq
  rw [hpq] at hflips
  apply Subtype.ext
  exact flipCompletionWord_injective
    (hardPairTransportColor C hsafe q) hflips

/-- Main CONDITIONAL GLOBAL FULL-MASS TRANSPORT.
Unlike the earlier count of individual safe colours, this injects
EVERY hard-overlap Boolean word, and all source faces are handled
SIMULTANEOUSLY without collisions or a factor of two.

The safe-colour existence hypothesis is strictly weaker than the
original global payment inequality syntactically, but its universal
validity for geometric hard pairs is not known. -/
theorem hard_overlap_global_mass_le_singleton_add_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hsafe : HasHardOverlapOutgoingTransport C) :
    (hardOverlapCompletionWords C).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card := by
  classical
  have hbound := Fintype.card_le_of_injective
    (hardOverlapWordGlobalTransport C hsafe)
    (hardOverlapWordGlobalTransport_injective C hsafe)
  have hcard :
      (hardOverlapCompletionWords C).card ≤
        (singletonCompletionWords C ∪
          softOverlapCompletionWords C).card := by
    simpa only [Fintype.card_coe] using hbound
  have hunion := Finset.card_union_le
    (singletonCompletionWords C)
    (softOverlapCompletionWords C)
  omega

#print axioms hardWordCarrier_covers
#print axioms hardOverlapWordGlobalTransport_injective
#print axioms hard_overlap_global_mass_le_singleton_add_soft

end OrderedEdgeColoring
end JSP000404Research
