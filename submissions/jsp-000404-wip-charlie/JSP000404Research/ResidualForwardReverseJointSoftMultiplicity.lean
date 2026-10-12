import JSP000404Research.ResidualForwardReverseSinkCollision
import Mathlib.Tactic

/-!
# Joint GLOBAL forward/reverse covered-word capacity, no double singleton use

Both previously certified maps are individually injective into
singletons UNION soft-overlapped Boolean words. Their cross-map
collisions all lie within the SOFT target class, NEVER in singleton
words. Inclusion-exclusion therefore gives the genuinely joint bound

  fullForwardHardMass + reverseStrictRigidHardMass
      <= singletonMass + 2 * softOverlapMass.

In contrast, naive addition of two independent bounds would give
TWO copies of the singleton mass. This is the first verified
cross-map joint-capacity inequality, independent of geometry.

This is a COVERED sink capacity estimate, NOT a payment by TRUE holes.
It does not prove the remaining planar defect inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def forwardHardTransportSinkWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.image
    (fun x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C} =>
        (transportableHardWordToSingletonOrSoft C x).1)

noncomputable def reverseStrictRigidSinkWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.image
    (fun y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent} =>
        (strictDescentRigidWordToSingletonOrSoft
          C exponent hexp honeLoss y).1)

theorem forwardHardTransportSinkWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (forwardHardTransportSinkWords C).card =
      (transportableHardOverlapCompletionWords C).card := by
  classical
  have hinj : Function.Injective
      (fun x : {word : Fin n → Bool //
        word ∈ transportableHardOverlapCompletionWords C} =>
          (transportableHardWordToSingletonOrSoft C x).1) := by
    intro x y h
    apply transportableHardWordToSingletonOrSoft_injective C
    apply Subtype.ext
    exact h
  unfold forwardHardTransportSinkWords
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_coe]

theorem reverseStrictRigidSinkWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (reverseStrictRigidSinkWords C exponent hexp honeLoss).card =
      (netStrictDescentRigidWords C exponent).card := by
  classical
  have hinj : Function.Injective
      (fun y : {word : Fin n → Bool //
        word ∈ netStrictDescentRigidWords C exponent} =>
          (strictDescentRigidWordToSingletonOrSoft
            C exponent hexp honeLoss y).1) := by
    intro x y h
    apply strictDescentRigidWordToSingletonOrSoft_injective
      C exponent hexp honeLoss
    apply Subtype.ext
    exact h
  unfold reverseStrictRigidSinkWords
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_coe]

theorem forward_reverse_sink_inter_subset_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    forwardHardTransportSinkWords C ∩
        reverseStrictRigidSinkWords C exponent hexp honeLoss ⊆
      softOverlapCompletionWords C := by
  classical
  intro word hw
  have hf := (Finset.mem_inter.mp hw).1
  have hr := (Finset.mem_inter.mp hw).2
  unfold forwardHardTransportSinkWords at hf
  unfold reverseStrictRigidSinkWords at hr
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hf
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hr
  have hcoll :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1 := hx.trans hy.symm
  have hsoft :=
    forward_reverse_sink_collision_is_soft
      C exponent hexp honeLoss x y hcoll
  simpa only [hx] using hsoft

theorem forward_reverse_sink_union_subset_singleton_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    forwardHardTransportSinkWords C ∪
        reverseStrictRigidSinkWords C exponent hexp honeLoss ⊆
      singletonCompletionWords C ∪ softOverlapCompletionWords C := by
  classical
  intro word hw
  rcases Finset.mem_union.mp hw with hf | hr
  · unfold forwardHardTransportSinkWords at hf
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hf
    simpa only [hx] using
      (transportableHardWordToSingletonOrSoft C x).2
  · unfold reverseStrictRigidSinkWords at hr
    obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hr
    simpa only [hy] using
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).2

/-- JOINT global capacity bound, charging singleton sinks ONCE and
soft sinks at most TWICE across opposite hard-flip directions. -/
theorem forward_reverse_hard_mass_le_singleton_add_two_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C).card +
          2 * (softOverlapCompletionWords C).card := by
  let F := forwardHardTransportSinkWords C
  let R := reverseStrictRigidSinkWords C exponent hexp honeLoss
  let S := singletonCompletionWords C
  let T := softOverlapCompletionWords C
  have hf : F.card =
      (transportableHardOverlapCompletionWords C).card :=
    forwardHardTransportSinkWords_card C
  have hr : R.card =
      (netStrictDescentRigidWords C exponent).card :=
    reverseStrictRigidSinkWords_card C exponent hexp honeLoss
  have hsubset : F ∪ R ⊆ S ∪ T :=
    forward_reverse_sink_union_subset_singleton_soft
      C exponent hexp honeLoss
  have hcross : F ∩ R ⊆ T :=
    forward_reverse_sink_inter_subset_soft
      C exponent hexp honeLoss
  have hunion : (F ∪ R).card ≤ (S ∪ T).card :=
    Finset.card_le_card hsubset
  have hintersection : (F ∩ R).card ≤ T.card :=
    Finset.card_le_card hcross
  have htotal : (S ∪ T).card ≤ S.card + T.card :=
    Finset.card_union_le S T
  have hinclusion := Finset.card_union_add_card_inter F R
  omega

/-- Same joint bound on the ACTUALLY UNRESERVED forward hard
mass, avoiding irrelevant previously-paid source words. -/
theorem net_forward_reverse_hard_mass_le_singleton_add_two_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C).card +
          2 * (softOverlapCompletionWords C).card := by
  have hsub := Finset.card_le_card
    (netTransportableHardWords_subset_transportable C exponent)
  have hbound :=
    forward_reverse_hard_mass_le_singleton_add_two_soft
      C exponent hexp honeLoss
  omega

/-- Three-way exact hard remainder now has the verified total
covered sink capacity, leaving only equal-incidence TWIN dyadic debt. -/
theorem remaining_hard_mass_le_singleton_add_two_soft_add_twin
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (remainingUnpaidHardAfterMixedRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
        2 * (softOverlapCompletionWords C).card +
          (∑ p ∈ netTwinRigidCarriers C exponent,
            2 ^ exponent p.2) := by
  have hsplit := remainingUnpaidHard_card_eq_transport_strict_twin
    C exponent hexp honeLoss
  have htwin := netTwinRigidWords_card_eq_dyadic_target_sum
    C exponent hexp honeLoss
  have hmobile :=
    net_forward_reverse_hard_mass_le_singleton_add_two_soft
      C exponent hexp honeLoss
  omega

#print axioms forward_reverse_sink_inter_subset_soft
#print axioms forward_reverse_hard_mass_le_singleton_add_two_soft
#print axioms net_forward_reverse_hard_mass_le_singleton_add_two_soft
#print axioms remaining_hard_mass_le_singleton_add_two_soft_add_twin

end OrderedEdgeColoring
end JSP000404Research
