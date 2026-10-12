import JSP000404Research.ResidualTerminalRigidReverseFlip
import Mathlib.Tactic

/-!
# Global injective reverse transport of ALL strict-descent terminal rigid faces

The previously certified reverse safe colour is chosen ONCE per
terminal strict-descent rigid hard carrier (a,v), a<v.
Its full overlap face Q_v is flipped into Q_a \ Q_v and thereby
into singleton-covered or SOFT-overlapped Boolean words.

The reverse map is globally injective, including ACROSS different
strict-descent carrier faces: its images remain in their source
carriers' LOWER completion cubes Q_a; lower residual completion
cubes of DISTINCT lower endpoints are disjoint, and hard carriers
cannot share a lower endpoint unless identical.

Thus the strict-descent rigid remainder admits the same sort of
collision-free, WHOLE-FACE covered transport as the previously
handled outward transportable hard carriers, but in the OPPOSITE
direction. It leaves only equal-exponent fully twin-incidence rigid
faces without either form of safe transport.

IMPORTANT: the destinations remain globally covered, not holes.
The forward/reverse maps are individually injective, but their
images have NOT been proved disjoint from each other. They cannot
be jointly charged as independent payments without further work.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def netStrictDescentRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (netRigidHardCarriers C exponent).filter
    (fun p => exponent p.2 < exponent p.1)

@[simp] theorem mem_netStrictDescentRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ netStrictDescentRigidCarriers C exponent ↔
      p ∈ netRigidHardCarriers C exponent ∧
      exponent p.2 < exponent p.1 := by
  classical
  simp [netStrictDescentRigidCarriers]

noncomputable def netStrictDescentRigidWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (netStrictDescentRigidCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- Select the unique strict-descending carrier of each overlap word. -/
noncomputable def strictDescentRigidWordCarrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (x : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent}) :
    {p : V × V // p ∈ netStrictDescentRigidCarriers C exponent} := by
  classical
  have h : ∃ p ∈ netStrictDescentRigidCarriers C exponent,
      x.1 ∈ carrierOverlapWords C p :=
    Finset.mem_biUnion.mp x.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem strictDescentRigidWordCarrier_covers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (x : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent}) :
    x.1 ∈ carrierOverlapWords C
      (strictDescentRigidWordCarrier C exponent x).1 := by
  exact (Classical.choose_spec
    (Finset.mem_biUnion.mp x.2)).2

theorem strictDescentRigidWordCarrier_residual
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (x : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent}) :
    (strictDescentRigidWordCarrier C exponent x).1.1 <
      (strictDescentRigidWordCarrier C exponent x).1.2 ∧
    IsResidual C
      (strictDescentRigidWordCarrier C exponent x).1.1
      (strictDescentRigidWordCarrier C exponent x).1.2 := by
  have pp := (mem_netStrictDescentRigidCarriers C exponent _).1
    (strictDescentRigidWordCarrier C exponent x).2
  have hp := ((mem_netUnpaidHardCarrierPairs C exponent _).1
    ((mem_netRigidHardCarriers C exponent _).1 pp.1).1).1
  exact (mem_residualCarrierPairs C _ _).1
    ((mem_overlapCarrierPairs C _).1
      ((mem_hardOverlapCarrierPairs C _).1 hp).1).1

/-- Pick a reverse safe colour ONCE per whole strict-rigid face. -/
noncomputable def strictDescentRigidPairColor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    (p : {p : V × V // p ∈ netStrictDescentRigidCarriers C exponent}) :
    Fin n :=
  Classical.choose
    (netRigidHardCarrier_strict_descent_has_reverse_safe_colour
      C exponent hexp honeLoss
      ((mem_netStrictDescentRigidCarriers C exponent p.1).1 p.2).1
      ((mem_netStrictDescentRigidCarriers C exponent p.1).1 p.2).2)

theorem strictDescentRigidPairColor_spec
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    (p : {p : V × V // p ∈ netStrictDescentRigidCarriers C exponent}) :
    strictDescentRigidPairColor C exponent hexp honeLoss p ∈
      outgoingRetained C p.1.2 ∧
    strictDescentRigidPairColor C exponent hexp honeLoss p ∉
      retainedActive C p.1.1 :=
  Classical.choose_spec
    (netRigidHardCarrier_strict_descent_has_reverse_safe_colour
      C exponent hexp honeLoss
      ((mem_netStrictDescentRigidCarriers C exponent p.1).1 p.2).1
      ((mem_netStrictDescentRigidCarriers C exponent p.1).1 p.2).2)

/-- The globally defined reverse full-face map lands in covered
singleton/soft overlap words, not genuine holes. -/
noncomputable def strictDescentRigidWordToSingletonOrSoft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent} →
    {word : Fin n → Bool //
      word ∈ singletonCompletionWords C ∪
        softOverlapCompletionWords C} := by
  classical
  intro x
  let pp := strictDescentRigidWordCarrier C exponent x
  let c := strictDescentRigidPairColor C exponent hexp honeLoss pp
  have hpdata := ((mem_netStrictDescentRigidCarriers C exponent
    pp.1).1 pp.2).1
  have hpHard := ((mem_netUnpaidHardCarrierPairs C exponent pp.1).1
    ((mem_netRigidHardCarriers C exponent pp.1).1 hpdata).1).1
  have hsame := ((mem_hardOverlapCarrierPairs C pp.1).1 hpHard).2
  have hres := strictDescentRigidWordCarrier_residual C exponent x
  have hc := strictDescentRigidPairColor_spec
    C exponent hexp honeLoss pp
  have hw := Finset.mem_inter.mp
    (strictDescentRigidWordCarrier_covers C exponent x)
  refine ⟨flipCompletionWord c x.1, ?_⟩
  exact hard_overlap_full_face_flip_singleton_or_soft C
    (ne_of_gt hres.1) (fun d => (hsame d).symm)
    hc.1 hc.2 (Finset.mem_inter.mpr ⟨hw.2,hw.1⟩)

/-- Every reverse-transport image remains in the LOWER cube Q_a
of the original strict-descending rigid hard carrier. -/
theorem strictDescentRigidWordToSingletonOrSoft_mem_lower
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    (x : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent}) :
    (strictDescentRigidWordToSingletonOrSoft
      C exponent hexp honeLoss x).1 ∈
      retainedCompletionWords C
        (strictDescentRigidWordCarrier C exponent x).1.1 := by
  change flipCompletionWord
    (strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent x)) x.1 ∈
    retainedCompletionWords C
      (strictDescentRigidWordCarrier C exponent x).1.1
  exact flipCompletionWord_mem_upper_of_inactive C
    (strictDescentRigidPairColor_spec C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent x)).2
    (Finset.mem_inter.mp
      (strictDescentRigidWordCarrier_covers C exponent x)).1

/-- Global injectivity across strict-descent rigid faces.
Different lower residual centres have disjoint LOWER cubes,
and carriers sharing a lower endpoint are identical. -/
theorem strictDescentRigidWordToSingletonOrSoft_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    Function.Injective
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss) := by
  classical
  intro x y hxy
  let p := strictDescentRigidWordCarrier C exponent x
  let q := strictDescentRigidWordCarrier C exponent y
  have hpRes := strictDescentRigidWordCarrier_residual C exponent x
  have hqRes := strictDescentRigidWordCarrier_residual C exponent y
  have hwordEq :
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1 :=
    congrArg Subtype.val hxy
  have hlower : p.1.1 = q.1.1 := by
    apply residual_lower_completion_word_unique
      C hpRes.1 hqRes.1 hpRes.2 hqRes.2
        (strictDescentRigidWordToSingletonOrSoft_mem_lower
          C exponent hexp honeLoss x)
    rw [hwordEq]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss y
  have hpData := (mem_netStrictDescentRigidCarriers
    C exponent p.1).1 p.2
  have hqData := (mem_netStrictDescentRigidCarriers
    C exponent q.1).1 q.2
  have hpHard := ((mem_netUnpaidHardCarrierPairs C exponent p.1).1
    ((mem_netRigidHardCarriers C exponent p.1).1 hpData.1).1).1
  have hqHard := ((mem_netUnpaidHardCarrierPairs C exponent q.1).1
    ((mem_netRigidHardCarriers C exponent q.1).1 hqData.1).1).1
  have hpq : p = q := by
    apply Subtype.ext
    exact hard_carrier_shared_endpoint_implies_same_pair
      C hpHard hqHard (Or.inl hlower)
  have hflips :
      flipCompletionWord
        (strictDescentRigidPairColor C exponent hexp honeLoss p) x.1 =
      flipCompletionWord
        (strictDescentRigidPairColor C exponent hexp honeLoss q) y.1 :=
    hwordEq
  rw [hpq] at hflips
  apply Subtype.ext
  exact flipCompletionWord_injective
    (strictDescentRigidPairColor C exponent hexp honeLoss q) hflips

/-- Exactly one globally injective covered destination for each
strict-descending rigid hard source word; no double count of sources. -/
theorem netStrictDescentRigidWords_card_le_singleton_add_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card := by
  classical
  have h :=
    Fintype.card_le_of_injective
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss)
      (strictDescentRigidWordToSingletonOrSoft_injective
        C exponent hexp honeLoss)
  have hcard :
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C ∪
          softOverlapCompletionWords C).card := by
    simpa only [Fintype.card_coe] using h
  have hunion := Finset.card_union_le
    (singletonCompletionWords C) (softOverlapCompletionWords C)
  omega

#print axioms strictDescentRigidWordToSingletonOrSoft_injective
#print axioms netStrictDescentRigidWords_card_le_singleton_add_soft

end OrderedEdgeColoring
end JSP000404Research
