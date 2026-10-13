import JSP000404Research.ResidualTwoFlipTargetedTrueHoleLedger
import JSP000404Research.ResidualActualCollisionTwoBitDisagreement
import Mathlib.Tactic

/-!
# Source-endpoint blockers for the genuine opposite corner of a
# forward/reverse hard transport collision square.

If w = flip(cf,x) = flip(cr,y) is an actual common forward/reverse
sink word, then its diagonal d=flip(cf,flip(cr,w)) satisfies

  d = flip(cr,x) = flip(cf,y)

because cf != cr and each individual flip is involutive.

Consequently, there are TWO EXPLICIT, already-existing external
third-centre blockers:
* if cr is INACTIVE at the forward lower hard source a, then d in Q_a;
* if cf is INACTIVE at the reverse upper hard source z, then d in Q_z.

The matching theorem ensures a and z are different from the bridge
endpoints b and v. In particular, for d to be a GLOBAL TRUE HOLE,
cr MUST be active at a AND cf MUST be active at z.

This is a necessary condition for transforming one actual
cross-hard collision into a true Boolean hole. It does not assert
that the conditions hold for all planar AngleCap configurations,
and it does not solve the remaining six-source dyadic payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Flipping two different Boolean coordinates commutes, pointwise. -/
theorem flipCompletionWord_comm
    {n : ℕ} (c d : Fin n) (w : Fin n → Bool)
    (hcd : c ≠ d) :
    flipCompletionWord c (flipCompletionWord d w) =
      flipCompletionWord d (flipCompletionWord c w) := by
  funext e
  by_cases hc : e = c
  · subst e
    have hdc : c ≠ d := hcd
    simp [flipCompletionWord, hdc]
  · by_cases hd : e = d
    · subst e
      have hdc : d ≠ c := Ne.symm hcd
      simp [flipCompletionWord, hdc]
    · simp [flipCompletionWord, hc, hd]

/-- The opposite square diagonal equals the reverse-colour
single flip of the ORIGINAL forward HARD source word. -/
theorem actual_collision_diagonal_eq_reverse_flip_forward_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let w := (transportableHardWordToSingletonOrSoft C x).1
    flipCompletionWord cf (flipCompletionWord cr w) =
      flipCompletionWord cr x.1 := by
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  change flipCompletionWord cf (flipCompletionWord cr w) =
    flipCompletionWord cr x.1
  have hne := forward_reverse_actual_collision_distinct_flip_colors
    C exponent hexp honeLoss x y hcollision
  change cf ≠ cr at hne
  have hw : w = flipCompletionWord cf x.1 := rfl
  rw [flipCompletionWord_comm cf cr w hne, hw,
    flipCompletionWord_flip]

/-- The diagonal is also the forward-colour single flip of
the ORIGINAL reverse strict-rigid HARD source word. -/
theorem actual_collision_diagonal_eq_forward_flip_reverse_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let w := (transportableHardWordToSingletonOrSoft C x).1
    flipCompletionWord cf (flipCompletionWord cr w) =
      flipCompletionWord cf y.1 := by
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  change flipCompletionWord cf (flipCompletionWord cr w) =
    flipCompletionWord cf y.1
  have hw : w = flipCompletionWord cr y.1 := by
    change (transportableHardWordToSingletonOrSoft C x).1 =
      flipCompletionWord cr y.1
    exact hcollision
  rw [hw, flipCompletionWord_flip]

/-- INACTIVE reverse flip at the forward source a yields a
CONCRETE third-centre blocker for the opposite diagonal, not a hole. -/
theorem actual_collision_diagonal_covered_by_forward_lower_if_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1)
    (hcrInactiveA :
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent y) ∉
      retainedActive C (transportableWordCarrier C x).1.1) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let w := (transportableHardWordToSingletonOrSoft C x).1
    flipCompletionWord cf (flipCompletionWord cr w) ∈
      retainedCompletionWords C p.1.1 := by
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  change flipCompletionWord cf (flipCompletionWord cr w) ∈
    retainedCompletionWords C p.1.1
  have hsrc := (Finset.mem_inter.mp
    (transportableWordCarrier_covers C x)).1
  have hflip := flipCompletionWord_mem_upper_of_inactive
    C hcrInactiveA hsrc
  rwa [actual_collision_diagonal_eq_reverse_flip_forward_source
    C exponent hexp honeLoss x y hcollision]

/-- INACTIVE forward flip at the reverse upper hard source z
provides the OTHER explicit external source blocker. -/
theorem actual_collision_diagonal_covered_by_reverse_upper_if_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1)
    (hcfInactiveZ :
      transportablePairColor C (transportableWordCarrier C x) ∉
      retainedActive C
        (strictDescentRigidWordCarrier C exponent y).1.2) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let w := (transportableHardWordToSingletonOrSoft C x).1
    flipCompletionWord cf (flipCompletionWord cr w) ∈
      retainedCompletionWords C q.1.2 := by
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  change flipCompletionWord cf (flipCompletionWord cr w) ∈
    retainedCompletionWords C q.1.2
  have hsrc := (Finset.mem_inter.mp
    (strictDescentRigidWordCarrier_covers C exponent y)).2
  have hflip := flipCompletionWord_mem_upper_of_inactive
    C hcfInactiveZ hsrc
  rwa [actual_collision_diagonal_eq_forward_flip_reverse_source
    C exponent hexp honeLoss x y hcollision]

/-- A TRUE Boolean hole at the opposite corner NECESSARILY
requires cross-activity at BOTH original hard-source endpoints.
Failure of either condition has a concrete already-covered source
endpoint witness, not just an existential third centre. -/
theorem actual_collision_diagonal_true_hole_requires_source_cross_activity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1)
    (hhole :
      flipCompletionWord
        (transportablePairColor C (transportableWordCarrier C x))
        (flipCompletionWord
          (strictDescentRigidPairColor C exponent hexp honeLoss
            (strictDescentRigidWordCarrier C exponent y))
          (transportableHardWordToSingletonOrSoft C x).1)
        ∉ coveredCompletionWords C) :
    strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent y) ∈
      retainedActive C (transportableWordCarrier C x).1.1 ∧
    transportablePairColor C (transportableWordCarrier C x) ∈
      retainedActive C
        (strictDescentRigidWordCarrier C exponent y).1.2 := by
  classical
  constructor
  · by_contra hna
    have hcover :=
      actual_collision_diagonal_covered_by_forward_lower_if_inactive
        C exponent hexp honeLoss x y hcollision hna
    have hg : _ ∈ coveredCompletionWords C :=
      (mem_coveredCompletionWords C _).2
        ⟨(transportableWordCarrier C x).1.1,
          (mem_completionFibre C _ _).2 hcover⟩
    exact hhole hg
  · by_contra hnz
    have hcover :=
      actual_collision_diagonal_covered_by_reverse_upper_if_inactive
        C exponent hexp honeLoss x y hcollision hnz
    have hg : _ ∈ coveredCompletionWords C :=
      (mem_coveredCompletionWords C _).2
        ⟨(strictDescentRigidWordCarrier C exponent y).1.2,
          (mem_completionFibre C _ _).2 hcover⟩
    exact hhole hg

#print axioms flipCompletionWord_comm
#print axioms actual_collision_diagonal_eq_reverse_flip_forward_source
#print axioms actual_collision_diagonal_eq_forward_flip_reverse_source
#print axioms actual_collision_diagonal_covered_by_forward_lower_if_inactive
#print axioms actual_collision_diagonal_covered_by_reverse_upper_if_inactive
#print axioms actual_collision_diagonal_true_hole_requires_source_cross_activity

end OrderedEdgeColoring
end JSP000404Research
