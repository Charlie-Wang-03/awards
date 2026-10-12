import JSP000404Research.ResidualActualCollisionTwoBitBridgePool
import Mathlib.Tactic

/-!
# Opposite corners of genuine forward/reverse transport collisions

The actual forward/reverse hard image intersection w is a SOFT
bridge completion word w in Q_b INTER Q_v. The two chosen hard
transport coordinates cf and cr satisfy:
  cf active at reverse lower b, inactive at forward upper v;
  cr inactive at reverse lower b, active at forward upper v.

The BOOLEAN SQUARE's opposite corner is
  d(w) = flip cf (flip cr w).
This square diagonal lies outside BOTH Q_b and Q_v.
This is a new, exact structural obstruction connecting actual
covered collision sink words to words EXTERIOR to their bridge cubes.

It is NOT claimed that d(w) is globally uncovered: there may be
an additional vertex c with d(w) in Q_c. We formalize the honest
dichotomy and the exact third-centre obstruction rather than
falsely invoking the two-cube exterior as genuine Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every ordered double flip is a global Boolean-word injection,
regardless of whether its two colours are distinct. -/
theorem double_flip_completion_word_injective
    {n : ℕ} (cf cr : Fin n) :
    Function.Injective
      (fun w : Fin n → Bool =>
        flipCompletionWord cf (flipCompletionWord cr w)) := by
  intro w z h
  exact (flipCompletionWord_injective cr)
    ((flipCompletionWord_injective cf) h)

/-- In the Boolean square with cross-active flip witnesses,
the corner opposite the SOFT bridge w is OUTSIDE BOTH bridge
endpoint completion cubes. Both exclusions are unconditional;
they do NOT imply that the corner is a global true hole. -/
theorem two_flip_diagonal_outside_bridge_endpoints
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n)
    (hcfActiveB : cf ∈ retainedActive C b)
    (hcrInactiveB : cr ∉ retainedActive C b)
    (hcrActiveV : cr ∈ retainedActive C v)
    (hwB : w ∈ retainedCompletionWords C b)
    (hwV : w ∈ retainedCompletionWords C v) :
    flipCompletionWord cf (flipCompletionWord cr w) ∉
        retainedCompletionWords C b ∧
      flipCompletionWord cf (flipCompletionWord cr w) ∉
        retainedCompletionWords C v := by
  have hne : cr ≠ cf := by
    intro h
    rw [h] at hcrInactiveB
    exact hcrInactiveB hcfActiveB
  constructor
  · have htemp : flipCompletionWord cr w ∈
        retainedCompletionWords C b :=
      flipCompletionWord_mem_upper_of_inactive
        C hcrInactiveB hwB
    exact flipCompletionWord_not_mem_lower_of_active
      C hcfActiveB htemp
  · intro hD
    have hbefore :=
      (mem_retainedCompletionWords C v w).1 hwV cr hcrActiveV
    have hafter :=
      (mem_retainedCompletionWords C v
        (flipCompletionWord cf (flipCompletionWord cr w))).1
        hD cr hcrActiveV
    rw [flipCompletionWord_off cf cr (flipCompletionWord cr w) hne,
      flipCompletionWord_at] at hafter
    have hbfalse : (! w cr) = w cr :=
      hafter.trans hbefore.symm
    cases w cr <;> simp at hbfalse

/-- The diagonal of a GENUINE collision of forward and reverse hard
transport images is outside the two (covered) SOFT bridge cubes.
Crucially, this statement refers to the actual chosen transport
colours and sources, rather than arbitrary candidate bridge faces. -/
theorem actual_forward_reverse_collision_two_flip_diagonal_outside_bridge
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
    flipCompletionWord cf (flipCompletionWord cr w) ∉
        retainedCompletionWords C q.1.1 ∧
      flipCompletionWord cf (flipCompletionWord cr w) ∉
        retainedCompletionWords C p.1.2 := by
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  change flipCompletionWord cf (flipCompletionWord cr w) ∉
      retainedCompletionWords C q.1.1 ∧
    flipCompletionWord cf (flipCompletionWord cr w) ∉
      retainedCompletionWords C p.1.2
  have hcross :=
    forward_reverse_collision_cross_active_flip_colors
      C exponent hexp honeLoss x y hcollision
  change cf ∈ retainedActive C q.1.1 ∧
    cr ∈ retainedActive C p.1.2 at hcross
  have hreverseInactive :=
    (strictDescentRigidPairColor_spec
      C exponent hexp honeLoss q).2
  have hB : w ∈ retainedCompletionWords C q.1.1 := by
    change (transportableHardWordToSingletonOrSoft C x).1 ∈ _
    rw [hcollision]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss y
  have hV : w ∈ retainedCompletionWords C p.1.2 :=
    transportableHardWordToSingletonOrSoft_mem_upper C x
  exact two_flip_diagonal_outside_bridge_endpoints
    C q.1.1 p.1.2 cf cr
      hcross.1 hreverseInactive hcross.2 hB hV

/-- Exact two-bit square obstruction to using a diagonal as a true
hole: if the diagonal is COVERED, there must be a third centre c
DIFFERENT from both bridge endpoints covering it. -/
theorem two_flip_diagonal_hole_or_external_centre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n)
    (hcfActiveB : cf ∈ retainedActive C b)
    (hcrInactiveB : cr ∉ retainedActive C b)
    (hcrActiveV : cr ∈ retainedActive C v)
    (hwB : w ∈ retainedCompletionWords C b)
    (hwV : w ∈ retainedCompletionWords C v) :
    let d := flipCompletionWord cf (flipCompletionWord cr w)
    d ∈ (Finset.univ : Finset (Fin n → Bool)) \
          coveredCompletionWords C ∨
      ∃ c : V, c ≠ b ∧ c ≠ v ∧
        d ∈ retainedCompletionWords C c := by
  classical
  let d := flipCompletionWord cf (flipCompletionWord cr w)
  change d ∈ (Finset.univ : Finset (Fin n → Bool)) \
          coveredCompletionWords C ∨
      ∃ c : V, c ≠ b ∧ c ≠ v ∧
        d ∈ retainedCompletionWords C c
  have houtside :=
    two_flip_diagonal_outside_bridge_endpoints
      C b v cf cr hcfActiveB hcrInactiveB hcrActiveV hwB hwV
  change d ∉ retainedCompletionWords C b ∧
    d ∉ retainedCompletionWords C v at houtside
  by_cases hcovered : d ∈ coveredCompletionWords C
  · right
    rw [coveredCompletionWords_eq_biUnion] at hcovered
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hcovered
    refine ⟨c, ?_, ?_, hc⟩
    · intro hcb
      subst c
      exact houtside.1 hc
    · intro hcv
      subst c
      exact houtside.2 hc
  · left
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcovered⟩

#print axioms double_flip_completion_word_injective
#print axioms two_flip_diagonal_outside_bridge_endpoints
#print axioms actual_forward_reverse_collision_two_flip_diagonal_outside_bridge
#print axioms two_flip_diagonal_hole_or_external_centre

end OrderedEdgeColoring
end JSP000404Research
