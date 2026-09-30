import JSP000404Research.ResidualLossTwoExitAvoidance
import JSP000404Research.ResidualLossBlockerEdge
import JSP000404Research.RetainedOrientation
import Mathlib.Data.Finset.Order
import Mathlib.Tactic

/-!
# Extreme projected-loss vertices push two-exit displacement inward

At a global minimum vertex there are no incoming retained colours. Hence every
retained-active coordinate is outgoing. At a global maximum every retained-
active coordinate is incoming.

Suppose an extreme loss vertex has two distinct active coordinates c,d.
For each loss word, blocker-specific two-exit avoidance lets us choose one of
the two flips that avoids the opposite extreme. Since blocker geometry is
one-sided, any remaining blocker must then lie strictly in the interior.

This converts the two-extreme-loss obstruction into an inward displacement
problem rather than an endpoint cycle.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_subset_outgoing_of_global_min
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V}
    (hmin : ∀ w : V, v ≤ w) :
    retainedActive C v ⊆ outgoingRetained C v := by
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C v] at hc
  rcases Finset.mem_union.mp hc with hcIn | hcOut
  · obtain ⟨u,huv,_hcol⟩ :=
      (mem_incomingRetained_iff C v c).1 hcIn
    exact False.elim ((not_lt_of_ge (hmin u)) huv)
  · exact hcOut

theorem retainedActive_subset_incoming_of_global_max
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V}
    (hmax : ∀ w : V, w ≤ v) :
    retainedActive C v ⊆ incomingRetained C v := by
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C v] at hc
  rcases Finset.mem_union.mp hc with hcIn | hcOut
  · exact hcIn
  · obtain ⟨w,hvw,_hcol⟩ :=
      (mem_outgoingRetained_iff C v c).1 hcOut
    exact False.elim ((not_lt_of_ge (hmax w)) hvw)

theorem minimum_loss_two_exit_avoids_max_and_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {bottom top : V}
    (hmin : ∀ w : V, bottom ≤ w)
    (hmax : ∀ w : V, w ≤ top)
    (hbt : bottom ≠ top)
    (hbottomLoss : bottom ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C bottom)
    {c d : Fin n}
    (hc : c ∈ retainedActive C bottom)
    (hd : d ∈ retainedActive C bottom)
    (hcd : c ≠ d) :
    ∃ e : Fin n,
      (e = c ∨ e = d) ∧
      e ∈ outgoingRetained C bottom ∧
      flipBoolWordAt word e ∉ retainedCompletionWords C bottom ∧
      flipBoolWordAt word e ∉ retainedCompletionWords C top ∧
      ∀ w : V,
        flipBoolWordAt word e ∈ retainedCompletionWords C w →
        bottom < w ∧ w < top := by
  obtain ⟨e,hecd,heOwner,heTop⟩ :=
    projectedLoss_two_flips_one_avoids_owner_and_fixed_blocker
      C exponent hexp honeLoss hbottomLoss hword
      hc hd hcd top
  have heActive : e ∈ retainedActive C bottom := by
    rcases hecd with rfl | rfl
    · exact hc
    · exact hd
  have heOut :
      e ∈ outgoingRetained C bottom :=
    retainedActive_subset_outgoing_of_global_min
      C hmin heActive
  refine ⟨e,hecd,heOut,heOwner,heTop,?_⟩
  intro w hw
  have hbw : bottom ≠ w := by
    intro h
    subst w
    exact heOwner hw
  have htw : w ≠ top := by
    intro h
    subst w
    exact heTop hw
  have hright :=
    loss_translated_blocker_right_of_outgoing
      C exponent hexp honeLoss
      hbottomLoss hbw heActive heOut hword hw
  have hwtop : w ≤ top := hmax w
  have hwlt : w < top := lt_of_le_of_ne hwtop htw
  exact ⟨hright,hwlt⟩

theorem maximum_loss_two_exit_avoids_min_and_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {bottom top : V}
    (hmin : ∀ w : V, bottom ≤ w)
    (hmax : ∀ w : V, w ≤ top)
    (hbt : bottom ≠ top)
    (htopLoss : top ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C top)
    {c d : Fin n}
    (hc : c ∈ retainedActive C top)
    (hd : d ∈ retainedActive C top)
    (hcd : c ≠ d) :
    ∃ e : Fin n,
      (e = c ∨ e = d) ∧
      e ∈ incomingRetained C top ∧
      flipBoolWordAt word e ∉ retainedCompletionWords C top ∧
      flipBoolWordAt word e ∉ retainedCompletionWords C bottom ∧
      ∀ w : V,
        flipBoolWordAt word e ∈ retainedCompletionWords C w →
        bottom < w ∧ w < top := by
  obtain ⟨e,hecd,heOwner,heBottom⟩ :=
    projectedLoss_two_flips_one_avoids_owner_and_fixed_blocker
      C exponent hexp honeLoss htopLoss hword
      hc hd hcd bottom
  have heActive : e ∈ retainedActive C top := by
    rcases hecd with rfl | rfl
    · exact hc
    · exact hd
  have heIn :
      e ∈ incomingRetained C top :=
    retainedActive_subset_incoming_of_global_max
      C hmax heActive
  refine ⟨e,hecd,heIn,heOwner,heBottom,?_⟩
  intro w hw
  have htw : top ≠ w := by
    intro h
    subst w
    exact heOwner hw
  have hbw : w ≠ bottom := by
    intro h
    subst w
    exact heBottom hw
  have hleft :=
    loss_translated_blocker_left_of_incoming
      C exponent hexp honeLoss
      htopLoss htw heActive heIn hword hw
  have hbottomw : bottom ≤ w := hmin w
  have hblt : bottom < w := lt_of_le_of_ne hbottomw (Ne.symm hbw)
  exact ⟨hblt,hleft⟩

#print axioms retainedActive_subset_outgoing_of_global_min
#print axioms retainedActive_subset_incoming_of_global_max
#print axioms minimum_loss_two_exit_avoids_max_and_owner
#print axioms maximum_loss_two_exit_avoids_min_and_owner

end OrderedEdgeColoring
end JSP000404Research
