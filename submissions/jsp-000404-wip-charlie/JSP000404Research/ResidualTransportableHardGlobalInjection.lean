import JSP000404Research.ResidualHardRigidMassAccounting
import Mathlib.Tactic

/-!
# UNCONDITIONAL global injection of ALL transportable hard-overlap words

The earlier full-face global injection assumed a colour was available
on EVERY hard residual carrier. That extra assumption is FALSE even for
a valid 3-point abstract DirectionData model.

Instead partition hard carriers canonically into transportable and
rigid. For a word whose unique hard carrier is TRANSPORTABLE, its
own carrier supplies a witness colour by definition. We can choose
that colour per carrier, consistently across the entire Boolean face.

The resulting map from ALL transportable hard-overlap words into
globally singleton or soft overlap words is injective, without ANY
global colour-availability hypothesis: different hard carriers have
different upper endpoints whose completion cubes are disjoint.

Consequently the only hard-overlap mass unhandled by this
unconditional face transport is the EXACT rigid sum
  ∑ rigid (a,v), 2 ^ projectedFree(v).
These rigid cubes are real and cannot generally be assumed empty.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A transportable hard-overlap word has a finite, nonempty
set of valid transportable hard carrier witnesses. -/
noncomputable def transportableWordCarrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C}) :
    {p : V × V // p ∈ transportableHardOverlapCarrierPairs C} := by
  classical
  have h : ∃ p ∈ transportableHardOverlapCarrierPairs C,
      x.1 ∈ carrierOverlapWords C p :=
    Finset.mem_biUnion.mp x.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem transportableWordCarrier_covers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C}) :
    x.1 ∈ retainedCompletionWords C (transportableWordCarrier C x).1.1 ∩
      retainedCompletionWords C (transportableWordCarrier C x).1.2 := by
  exact (Classical.choose_spec (Finset.mem_biUnion.mp x.2)).2

theorem transportableWordCarrier_residual
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C}) :
    (transportableWordCarrier C x).1.1 <
        (transportableWordCarrier C x).1.2 ∧
      IsResidual C (transportableWordCarrier C x).1.1
        (transportableWordCarrier C x).1.2 := by
  have hp := ((mem_transportableHardOverlapCarrierPairs C
    (transportableWordCarrier C x).1).1
      (transportableWordCarrier C x).2).1
  exact (mem_residualCarrierPairs C _ _).1
    ((mem_overlapCarrierPairs C _).1
      ((mem_hardOverlapCarrierPairs C _).1 hp).1).1

/-- Choose ONE outward/inactive coordinate PER transportable
hard carrier. All words in one source face use exactly this colour. -/
noncomputable def transportablePairColor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : {p : V × V // p ∈ transportableHardOverlapCarrierPairs C}) :
    Fin n :=
  Classical.choose
    ((mem_transportableHardOverlapCarrierPairs C p.1).1 p.2).2

theorem transportablePairColor_spec
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : {p : V × V // p ∈ transportableHardOverlapCarrierPairs C}) :
    transportablePairColor C p ∈ outgoingRetained C p.1.1 ∧
      transportablePairColor C p ∉ retainedActive C p.1.2 :=
  Classical.choose_spec
    ((mem_transportableHardOverlapCarrierPairs C p.1).1 p.2).2

/-- The unconditional WHOLE-FACE map, now restricted to the
precisely characterized transportable subset of hard words. -/
noncomputable def transportableHardWordToSingletonOrSoft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C} →
    {word : Fin n → Bool //
      word ∈ singletonCompletionWords C ∪
        softOverlapCompletionWords C} := by
  classical
  intro x
  let p := transportableWordCarrier C x
  let c := transportablePairColor C p
  have hres := transportableWordCarrier_residual C x
  have hsame := ((mem_hardOverlapCarrierPairs C p.1).1
    ((mem_transportableHardOverlapCarrierPairs C p.1).1 p.2).1).2
  have hc := transportablePairColor_spec C p
  refine ⟨flipCompletionWord c x.1, ?_⟩
  exact hard_overlap_full_face_flip_singleton_or_soft C
    (ne_of_lt hres.1) hsame hc.1 hc.2
      (transportableWordCarrier_covers C x)

/-- Every output remains in the particular upper completion cube
of its own hard residual carrier. -/
theorem transportableHardWordToSingletonOrSoft_mem_upper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C}) :
    (transportableHardWordToSingletonOrSoft C x).1 ∈
      retainedCompletionWords C (transportableWordCarrier C x).1.2 := by
  change flipCompletionWord
    (transportablePairColor C (transportableWordCarrier C x)) x.1 ∈
      retainedCompletionWords C (transportableWordCarrier C x).1.2
  exact flipCompletionWord_mem_upper_of_inactive C
    (transportablePairColor_spec C (transportableWordCarrier C x)).2
    (Finset.mem_inter.mp (transportableWordCarrier_covers C x)).2

/-- FULL GLOBAL INJECTIVITY, without assuming all hard carriers
have safe outward colours. Rigid carriers are merely not in the
domain. Their exact mass is separately tracked. -/
theorem transportableHardWordToSingletonOrSoft_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Function.Injective
      (transportableHardWordToSingletonOrSoft C) := by
  classical
  intro x y hxy
  let p := transportableWordCarrier C x
  let q := transportableWordCarrier C y
  have hpRes := transportableWordCarrier_residual C x
  have hqRes := transportableWordCarrier_residual C y
  have hwordEq :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (transportableHardWordToSingletonOrSoft C y).1 :=
    congrArg Subtype.val hxy
  have hupper : p.1.2 = q.1.2 := by
    apply residual_upper_completion_word_unique C
      hpRes.1 hqRes.1 hpRes.2 hqRes.2
        (transportableHardWordToSingletonOrSoft_mem_upper C x)
    rw [hwordEq]
    exact transportableHardWordToSingletonOrSoft_mem_upper C y
  have hpSame := ((mem_hardOverlapCarrierPairs C p.1).1
    ((mem_transportableHardOverlapCarrierPairs C p.1).1 p.2).1).2
  have hqSame := ((mem_hardOverlapCarrierPairs C q.1).1
    ((mem_transportableHardOverlapCarrierPairs C q.1).1 q.2).1).2
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
      flipCompletionWord (transportablePairColor C p) x.1 =
        flipCompletionWord (transportablePairColor C q) y.1 := hwordEq
  rw [hpq] at hflips
  apply Subtype.ext
  exact flipCompletionWord_injective
    (transportablePairColor C q) hflips

/-- UNCONDITIONAL injection bound for the movable hard-overlap
mass, with the rigid exceptional words excluded BY DEFINITION. -/
theorem transportable_hard_mass_le_singleton_add_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (transportableHardOverlapCompletionWords C).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card := by
  classical
  have h := Fintype.card_le_of_injective
    (transportableHardWordToSingletonOrSoft C)
    (transportableHardWordToSingletonOrSoft_injective C)
  have hcard :
      (transportableHardOverlapCompletionWords C).card ≤
        (singletonCompletionWords C ∪
          softOverlapCompletionWords C).card := by
    simpa only [Fintype.card_coe] using h
  have hunion := Finset.card_union_le
    (singletonCompletionWords C)
    (softOverlapCompletionWords C)
  omega

/-- All hard overlap mass is now bounded WITHOUT any global
colour-availability hypothesis, with its exact explicit
rigid remainder separated. -/
theorem hard_overlap_mass_le_singleton_add_soft_add_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (hardOverlapCompletionWords C).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
          (rigidHardOverlapCompletionWords C).card := by
  have hpartition := hard_overlap_card_eq_transportable_add_rigid C
  have htransport := transportable_hard_mass_le_singleton_add_soft C
  omega

/-- Same unconditional inequality in EXACT rigid dyadic mass:
no hidden transport hypothesis or unidentified local deficit. -/
theorem hard_overlap_mass_le_singleton_add_soft_add_rigid_dyadic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (hardOverlapCompletionWords C).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
          ∑ p ∈ rigidHardOverlapCarrierPairs C,
            2 ^ projectedFree C p.2 := by
  rw [← rigid_hard_overlap_card_eq_sum_upper_cubes]
  exact hard_overlap_mass_le_singleton_add_soft_add_rigid C

#print axioms transportableHardWordToSingletonOrSoft_injective
#print axioms transportable_hard_mass_le_singleton_add_soft
#print axioms hard_overlap_mass_le_singleton_add_soft_add_rigid_dyadic

end OrderedEdgeColoring
end JSP000404Research
