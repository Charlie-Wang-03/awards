import JSP000404Research.ResidualTwoFlipSourceEndpointBlocker
import Mathlib.Tactic

/-!
# Exact obstruction characterization for actual hard transport collisions

This module adds NO planar or Hall hypotheses.  At a collision between the
already-proved globally injective forward and reverse transports, the opposite
two-flip diagonal is covered iff one of the two original hard source endpoints
blocks the flip, or some centre outside the four original hard endpoints
covers it.  This is a local IFF, not the missing global hole payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An actual collision diagonal is covered exactly by either source-side
cross-inactivity or by a fifth-or-later covering centre.  All alternatives
refer to the literal original hard transport data, without hypothetical
candidate bridge faces. -/
theorem actual_collision_diagonal_covered_iff_source_block_or_fifth
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
    let d := flipCompletionWord cf (flipCompletionWord cr w)
    d ∈ coveredCompletionWords C ↔
      (cr ∉ retainedActive C p.1.1 ∨
       cf ∉ retainedActive C q.1.2 ∨
       ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
         c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
         d ∈ retainedCompletionWords C c) := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  let d := flipCompletionWord cf (flipCompletionWord cr w)
  change d ∈ coveredCompletionWords C ↔
    (cr ∉ retainedActive C p.1.1 ∨
     cf ∉ retainedActive C q.1.2 ∨
     ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
       c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
       d ∈ retainedCompletionWords C c)
  constructor
  · intro hcovered
    by_cases ha : cr ∈ retainedActive C p.1.1
    · by_cases hz : cf ∈ retainedActive C q.1.2
      · right
        right
        exact actual_collision_covered_diagonal_has_fifth_centre
          C exponent hexp honeLoss x y hcollision ha hz hcovered
      · exact Or.inr (Or.inl hz)
    · exact Or.inl ha
  · intro h
    rcases h with ha | hz | ⟨c, _, _, _, _, hc⟩
    · have hlocal : d ∈ retainedCompletionWords C p.1.1 :=
        actual_collision_diagonal_covered_by_forward_lower_if_inactive
          C exponent hexp honeLoss x y hcollision ha
      exact (mem_coveredCompletionWords C d).2
        ⟨p.1.1, (mem_completionFibre C d p.1.1).2 hlocal⟩
    · have hlocal : d ∈ retainedCompletionWords C q.1.2 :=
        actual_collision_diagonal_covered_by_reverse_upper_if_inactive
          C exponent hexp honeLoss x y hcollision hz
      exact (mem_coveredCompletionWords C d).2
        ⟨q.1.2, (mem_completionFibre C d q.1.2).2 hlocal⟩
    · exact (mem_coveredCompletionWords C d).2
        ⟨c, (mem_completionFibre C d c).2 hc⟩

/-- Equivalently, a true global Boolean hole at an actual collision
diagonal requires BOTH source cross-activities and the absence of EVERY
fifth-or-later covering centre, and those conditions are sufficient.
This statement is local and does not assert a global injective allocation
of such holes across multiple collisions. -/
theorem actual_collision_diagonal_true_hole_iff_cross_active_no_fifth
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
    let d := flipCompletionWord cf (flipCompletionWord cr w)
    (d ∈ (Finset.univ : Finset (Fin n → Bool)) \
      coveredCompletionWords C) ↔
      (cr ∈ retainedActive C p.1.1 ∧
       cf ∈ retainedActive C q.1.2 ∧
       ∀ c : V, c ≠ p.1.1 → c ≠ p.1.2 →
         c ≠ q.1.1 → c ≠ q.1.2 →
         d ∉ retainedCompletionWords C c) := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  let d := flipCompletionWord cf (flipCompletionWord cr w)
  change (d ∈ (Finset.univ : Finset (Fin n → Bool)) \
    coveredCompletionWords C) ↔
    (cr ∈ retainedActive C p.1.1 ∧
     cf ∈ retainedActive C q.1.2 ∧
     ∀ c : V, c ≠ p.1.1 → c ≠ p.1.2 →
       c ≠ q.1.1 → c ≠ q.1.2 →
       d ∉ retainedCompletionWords C c)
  constructor
  · intro hhole
    have hcross :=
      actual_collision_diagonal_true_hole_requires_source_cross_activity
        C exponent hexp honeLoss x y hcollision
        (Finset.mem_sdiff.mp hhole).2
    have hiff :=
      actual_collision_diagonal_hole_iff_no_fifth_centre
        C exponent hexp honeLoss x y hcollision hcross.1 hcross.2
    exact ⟨hcross.1, hcross.2, hiff.mp hhole⟩
  · rintro ⟨ha, hz, hno⟩
    exact (actual_collision_diagonal_hole_iff_no_fifth_centre
      C exponent hexp honeLoss x y hcollision ha hz).2 hno

#print axioms actual_collision_diagonal_covered_iff_source_block_or_fifth
#print axioms actual_collision_diagonal_true_hole_iff_cross_active_no_fifth

end OrderedEdgeColoring
end JSP000404Research
