import JSP000404Research.ResidualLossBlockerEdgeColourRigidity
import JSP000404Research.ResidualLossBlockerTripleLocalCapacity
import Mathlib.Tactic

/-!
# Exact projected-loss covered mass on true same-colour retained edges

We remove false-positive blocker triples from the previous exact
chosen-coordinate carrier cover. A covered translated word is only
possible if its source and blocker are directly joined by a retained
edge of precisely the chosen flip coordinate.

This is an EXACT set equality, not merely a broader upper bound:
   covered-loss = union of actual-edge source/blocker intersections.

It implies a strictly more restrictive quantitative dyadic upper bound
indexed only by genuinely eligible coloured original edges. No
geometric AngleCap exclusion or global nonreuse allocation is assumed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def chosenLossActualEdgeBlockerTriples
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : Finset ((V × V) × Fin n) := by
  classical
  exact (chosenLossCoveredBlockerTriples C exponent choice).filter
    (fun z =>
      (∃ hvw : z.1.1 < z.1.2,
        ∃ hret : (C.color z.1.1 z.1.2).val < n,
          retainedColor C z.1.1 z.1.2 hret = z.2) ∨
      (∃ hwv : z.1.2 < z.1.1,
        ∃ hret : (C.color z.1.2 z.1.1).val < n,
          retainedColor C z.1.2 z.1.1 hret = z.2))

theorem translatedLossCovered_eq_actualEdgeTriple_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    translatedLossCoveredWords C exponent choice =
      (chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
        (lossCoveredBlockerTripleWords C) := by
  classical
  rw [translatedLossCovered_eq_chosenTriple_union
    C exponent hexp honeLoss choice hchoice]
  apply Finset.Subset.antisymm
  · intro word hword
    obtain ⟨⟨⟨v, w⟩, c⟩, hz, hinter⟩ :=
      Finset.mem_biUnion.mp hword
    have hdata :
        v ∈ projectedLossVertices C exponent ∧
        v ≠ w ∧ choice v = c ∧
        c ∈ retainedActive C v ∧
        c ∈ retainedActive C w ∧
        retainedBit C w c = !(retainedBit C v c) :=
      (Finset.mem_filter.mp hz).2
    have hvT :
        word ∈ translatedCompletionWords C v c :=
      (Finset.mem_inter.mp hinter).1
    have hw :
        word ∈ retainedCompletionWords C w :=
      (Finset.mem_inter.mp hinter).2
    have hed :=
      loss_translated_blocker_edge_colour_eq_flip
        C exponent hexp honeLoss hdata.1 hdata.2.1 hvT hw
    apply Finset.mem_biUnion.mpr
    refine ⟨((v, w), c), ?_, hinter⟩
    exact Finset.mem_filter.mpr ⟨hz, hed⟩
  · intro word hword
    obtain ⟨z, hz, hinter⟩ := Finset.mem_biUnion.mp hword
    exact Finset.mem_biUnion.mpr
      ⟨z, (Finset.mem_filter.mp hz).1, hinter⟩

/-- Exact edge rigidity permits a more restrictive local dyadic
bound than the broad all-opposite-bit triple sum. No carrier
disjointness is used. -/
theorem translatedLossCovered_card_le_actualEdgeTriple_dyadic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    (translatedLossCoveredWords C exponent choice).card ≤
      ∑ z ∈ chosenLossActualEdgeBlockerTriples C exponent choice,
        min (2 ^ projectedFree C z.1.1)
            (2 ^ projectedFree C z.1.2) := by
  classical
  rw [translatedLossCovered_eq_actualEdgeTriple_union
    C exponent hexp honeLoss choice hchoice]
  calc
    ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
      (lossCoveredBlockerTripleWords C)).card ≤
        ∑ z ∈ chosenLossActualEdgeBlockerTriples C exponent choice,
          (lossCoveredBlockerTripleWords C z).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ z ∈ chosenLossActualEdgeBlockerTriples C exponent choice,
          min (2 ^ projectedFree C z.1.1)
              (2 ^ projectedFree C z.1.2) := by
      apply Finset.sum_le_sum
      intro z hz
      exact lossCoveredBlockerTripleWords_card_le_min_dyadic C z

/-- An actual same-colour retained blocker of a projected-loss source
cannot occur on both sides of that source. This uses the ORIGINAL
ordered-colouring no-monochromatic-two-path axiom, not a false
proper-edge-colouring assumption. -/
theorem chosenLossActualEdgeBlockerTriples_no_straddle
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {a v b : V} (hav : a < v) (hvb : v < b)
    (ha : ((v, a), choice v) ∈
      chosenLossActualEdgeBlockerTriples C exponent choice)
    (hb : ((v, b), choice v) ∈
      chosenLossActualEdgeBlockerTriples C exponent choice) : False := by
  classical
  have hleft :
      ∃ hret : (C.color a v).val < n,
        retainedColor C a v hret = choice v := by
    rcases (Finset.mem_filter.mp ha).2 with
      ⟨hva, _, _⟩ | ⟨_, hret, hc⟩
    · exact False.elim (lt_asymm hav hva)
    · exact ⟨hret, hc⟩
  have hright :
      ∃ hret : (C.color v b).val < n,
        retainedColor C v b hret = choice v := by
    rcases (Finset.mem_filter.mp hb).2 with
      ⟨_, hret, hc⟩ | ⟨hbv, _, _⟩
    · exact ⟨hret, hc⟩
    · exact False.elim (lt_asymm hvb hbv)
  rcases hleft with ⟨hretA, hcA⟩
  rcases hright with ⟨hretB, hcB⟩
  have hvalA : (C.color a v).val = (choice v).val := by
    simpa [retainedColor] using congrArg Fin.val hcA
  have hvalB : (C.color v b).val = (choice v).val := by
    simpa [retainedColor] using congrArg Fin.val hcB
  have hcol : C.color a v = C.color v b :=
    Fin.ext (hvalA.trans hvalB.symm)
  exact C.noMonoTwoPath hav hvb hcol

/-- For each projected-loss source, all actual chosen-colour blocker
edges lie strictly on ONE side of the source (possibly none).
There is no assertion that blockers on the same side are unique. -/
theorem chosenLossActualEdgeBlockerTriples_one_side
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (v : V) :
    (∀ w, ((v, w), choice v) ∈
      chosenLossActualEdgeBlockerTriples C exponent choice → w < v) ∨
    (∀ w, ((v, w), choice v) ∈
      chosenLossActualEdgeBlockerTriples C exponent choice → v < w) := by
  classical
  by_cases hleft :
      ∃ a, a < v ∧
        ((v, a), choice v) ∈
          chosenLossActualEdgeBlockerTriples C exponent choice
  · left
    intro w hw
    by_contra hnot
    have hne : v ≠ w := by
      rcases (Finset.mem_filter.mp hw).2 with
        ⟨hvw, _, _⟩ | ⟨hwv, _, _⟩
      · exact ne_of_lt hvw
      · exact ne_of_gt hwv
    have hvw : v < w := lt_of_le_of_ne (le_of_not_gt hnot) hne
    rcases hleft with ⟨a, hav, ha⟩
    exact chosenLossActualEdgeBlockerTriples_no_straddle
      C exponent choice hav hvw ha hw
  · right
    intro w hw
    have hne : v ≠ w := by
      rcases (Finset.mem_filter.mp hw).2 with
        ⟨hvw, _, _⟩ | ⟨hwv, _, _⟩
      · exact ne_of_lt hvw
      · exact ne_of_gt hwv
    have hnleft : ¬ w < v := by
      intro hwv
      exact hleft ⟨w, hwv, hw⟩
    exact lt_of_le_of_ne (le_of_not_gt hnleft) hne

/-- The side of an ACTUAL chosen-colour blocker is not merely
consistent across a source: it is DETERMINED by that source's canonical
retained bit at its chosen coordinate. The proof uses the true
ordered-edge path axiom, not proper colouring of stars. -/
theorem chosenLossActualEdgeBlockerTriples_orientation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {v w : V}
    (h : ((v, w), choice v) ∈
      chosenLossActualEdgeBlockerTriples C exponent choice) :
    (retainedBit C v (choice v) = true ∧ w < v) ∨
    (retainedBit C v (choice v) = false ∧ v < w) := by
  classical
  rcases (Finset.mem_filter.mp h).2 with
    ⟨hvw, hret, hc⟩ | ⟨hwv, hret, hc⟩
  · right
    have hcol : C.color v w = (choice v).castSucc := by
      apply Fin.ext
      simpa [retainedColor] using (congrArg Fin.val hc)
    constructor
    · change bit C v (choice v).castSucc = false
      rw [← hcol]
      exact edgeColor_bit_lower_eq_false C hvw
    · exact hvw
  · left
    have hcol : C.color w v = (choice v).castSucc := by
      apply Fin.ext
      simpa [retainedColor] using (congrArg Fin.val hc)
    constructor
    · change bit C v (choice v).castSucc = true
      rw [← hcol]
      exact edgeColor_bit_upper_eq_true C hwv
    · exact hwv

/-- Bit-determined source orientation is a constructive refinement of
the one-side existential disjunction: true bits force incoming blockers,
while false bits force outgoing blockers. -/
theorem chosenLossActualEdgeBlockerTriples_side_of_bit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (v : V) :
    (retainedBit C v (choice v) = true →
      ∀ w, ((v, w), choice v) ∈
        chosenLossActualEdgeBlockerTriples C exponent choice → w < v) ∧
    (retainedBit C v (choice v) = false →
      ∀ w, ((v, w), choice v) ∈
        chosenLossActualEdgeBlockerTriples C exponent choice → v < w) := by
  constructor
  · intro htrue w hw
    rcases chosenLossActualEdgeBlockerTriples_orientation
      C exponent choice hw with ⟨_, hwv⟩ | ⟨hfalse, _⟩
    · exact hwv
    · simp [htrue] at hfalse
  · intro hfalse w hw
    rcases chosenLossActualEdgeBlockerTriples_orientation
      C exponent choice hw with ⟨htrue, _⟩ | ⟨_, hvw⟩
    · simp [hfalse] at htrue
    · exact hvw

#print axioms chosenLossActualEdgeBlockerTriples_orientation
#print axioms chosenLossActualEdgeBlockerTriples_side_of_bit

#print axioms chosenLossActualEdgeBlockerTriples_no_straddle
#print axioms chosenLossActualEdgeBlockerTriples_one_side

#print axioms translatedLossCovered_eq_actualEdgeTriple_union
#print axioms translatedLossCovered_card_le_actualEdgeTriple_dyadic

end OrderedEdgeColoring
end JSP000404Research
