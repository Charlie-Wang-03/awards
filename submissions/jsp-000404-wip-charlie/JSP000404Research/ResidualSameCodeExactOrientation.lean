
import JSP000404Research.ResidualHardPairSafe
import JSP000404Research.ResidualExactBudget
import JSP000404Research.ResidualLightFibreDyadic
import Mathlib.Tactic

/-!
# Exact orientation algebra of a same-retained pair with no common inactive coordinate

Let u,v have the same retained canonical code.  Their incoming retained sets
are therefore equal; call this common set I.  Write O_u and O_v for their
outgoing retained sets.

Assume there is no retained coordinate inactive at both endpoints.

Because each retained active set is the disjoint union I union O, every
retained coordinate belongs to

  I union O_u union O_v.

The free coordinates are exactly the asymmetric outgoing differences:

  inactive(u) = O_v \ O_u,
  inactive(v) = O_u \ O_v.

In particular the canonical safe-target set for the ordered pair u,v is

  complement (incoming(u) union outgoing(v))
    = inactive(v)
    = O_u \ O_v.

Counting the disjoint pieces

  I,
  O_u inter O_v,
  O_u \ O_v,
  O_v \ O_u

gives the exact identity

  projectedFree(u) + projectedFree(v)
    + card I + card(O_u inter O_v) = n.

If both endpoints saturate their projected budgets, the same identity holds
with the two projectedFree terms replaced by target exponents.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- No common inactive coordinate makes the lower free set exactly the
upper-only outgoing set. -/
theorem retainedInactive_left_eq_outgoingRight_sdiff_outgoingLeft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    retainedInactive C u =
      outgoingRetained C v \ outgoingRetained C u := by
  classical
  ext c
  rw [mem_retainedInactive, Finset.mem_sdiff]
  constructor
  · intro hcu
    have hcvActive : c ∈ retainedActive C v := by
      by_contra hcv
      exact hno ⟨c, hcu, hcv⟩
    rw [retainedActive_eq_incoming_union_outgoing C v] at hcvActive
    rcases Finset.mem_union.mp hcvActive with hInV | hOutV
    · have hInU :
          c ∈ incomingRetained C u := by
        rw [incomingRetained_eq_of_sameRetained C hsame]
        exact hInV
      have hActiveU :
          c ∈ retainedActive C u := by
        rw [retainedActive_eq_incoming_union_outgoing C u]
        exact Finset.mem_union_left _ hInU
      exact False.elim (hcu hActiveU)
    · refine ⟨hOutV, ?_⟩
      intro hOutU
      have hActiveU :
          c ∈ retainedActive C u := by
        rw [retainedActive_eq_incoming_union_outgoing C u]
        exact Finset.mem_union_right _ hOutU
      exact hcu hActiveU
  · rintro ⟨hOutV, hNotOutU⟩ hActiveU
    rw [retainedActive_eq_incoming_union_outgoing C u] at hActiveU
    rcases Finset.mem_union.mp hActiveU with hInU | hOutU
    · have hInV :
          c ∈ incomingRetained C v := by
        rw [← incomingRetained_eq_of_sameRetained C hsame]
        exact hInU
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hInV hOutV
    · exact hNotOutU hOutU

/-- Symmetric exact formula for the upper free set. -/
theorem retainedInactive_right_eq_outgoingLeft_sdiff_outgoingRight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    retainedInactive C v =
      outgoingRetained C u \ outgoingRetained C v := by
  exact retainedInactive_left_eq_outgoingRight_sdiff_outgoingLeft
    C (sameRetained_symm hsame)
    (by
      intro h
      obtain ⟨c, hcv, hcu⟩ := h
      exact hno ⟨c, hcu, hcv⟩)

/-- On a same-retained pair the local safe-target set is exactly the upper
inactive set. -/
theorem safeTargetSet_eq_retainedInactive_upper_of_sameRetained
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v) :
    (Finset.univ \ residualForbidden C u v) =
      retainedInactive C v := by
  classical
  ext c
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    residualForbidden, Finset.mem_union]
  rw [mem_retainedInactive]
  constructor
  · intro hsafe hActiveV
    rw [retainedActive_eq_incoming_union_outgoing C v] at hActiveV
    rcases Finset.mem_union.mp hActiveV with hInV | hOutV
    · have hInU :
          c ∈ incomingRetained C u := by
        rw [incomingRetained_eq_of_sameRetained C hsame]
        exact hInV
      exact hsafe (Or.inl hInU)
    · exact hsafe (Or.inr hOutV)
  · intro hInactiveV hforbid
    rcases hforbid with hInU | hOutV
    · have hInV :
          c ∈ incomingRetained C v := by
        rw [← incomingRetained_eq_of_sameRetained C hsame]
        exact hInU
      apply hInactiveV
      rw [retainedActive_eq_incoming_union_outgoing C v]
      exact Finset.mem_union_left _ hInV
    · apply hInactiveV
      rw [retainedActive_eq_incoming_union_outgoing C v]
      exact Finset.mem_union_right _ hOutV

/-- Exact four-piece cardinal partition of the retained palette. -/
theorem sameRetained_noCommonInactive_card_identity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    projectedFree C u + projectedFree C v +
        (incomingRetained C u).card +
        (outgoingRetained C u ∩ outgoingRetained C v).card
      =
    n := by
  classical
  have hIeq :
      incomingRetained C u = incomingRetained C v :=
    incomingRetained_eq_of_sameRetained C hsame
  have hdisjIU :
      Disjoint (incomingRetained C u) (outgoingRetained C u) :=
    incomingRetained_disjoint_outgoingRetained C u
  have hdisjIV :
      Disjoint (incomingRetained C u) (outgoingRetained C v) := by
    rw [hIeq]
    exact incomingRetained_disjoint_outgoingRetained C v
  have hcover :
      incomingRetained C u ∪
          (outgoingRetained C u ∪ outgoingRetained C v)
        =
      (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_forall
    intro c
    by_contra hc
    have hcNotI : c ∉ incomingRetained C u := by
      intro h
      exact hc (Finset.mem_union_left _ h)
    have hcNotOu : c ∉ outgoingRetained C u := by
      intro h
      exact hc (Finset.mem_union_right _
        (Finset.mem_union_left _ h))
    have hcNotOv : c ∉ outgoingRetained C v := by
      intro h
      exact hc (Finset.mem_union_right _
        (Finset.mem_union_right _ h))
    have hInactiveU :
        c ∉ retainedActive C u := by
      rw [retainedActive_eq_incoming_union_outgoing C u]
      simpa [hcNotI, hcNotOu]
    have hInactiveV :
        c ∉ retainedActive C v := by
      rw [retainedActive_eq_incoming_union_outgoing C v,
          ← hIeq]
      simpa [hcNotI, hcNotOv]
    exact hno ⟨c, hInactiveU, hInactiveV⟩
  have hOut :
      (outgoingRetained C u ∪ outgoingRetained C v).card +
          (outgoingRetained C u ∩ outgoingRetained C v).card
        =
      (outgoingRetained C u).card +
        (outgoingRetained C v).card :=
    Finset.card_union_add_card_inter _ _
  have hIOutDisj :
      Disjoint (incomingRetained C u)
        (outgoingRetained C u ∪ outgoingRetained C v) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hdisjIU, hdisjIV⟩
  have hcoverCard :
      (incomingRetained C u).card +
          (outgoingRetained C u ∪ outgoingRetained C v).card
        = n := by
    rw [← Finset.card_union_of_disjoint hIOutDisj,
        hcover]
    simp
  have hfreeU :
      projectedFree C u =
        (outgoingRetained C v \ outgoingRetained C u).card := by
    unfold projectedFree
    rw [← retainedInactive_card C u,
        retainedInactive_left_eq_outgoingRight_sdiff_outgoingLeft
          C hsame hno]
  have hfreeV :
      projectedFree C v =
        (outgoingRetained C u \ outgoingRetained C v).card := by
    unfold projectedFree
    rw [← retainedInactive_card C v,
        retainedInactive_right_eq_outgoingLeft_sdiff_outgoingRight
          C hsame hno]
  have hOuDecomp :
      (outgoingRetained C u).card =
        (outgoingRetained C u \ outgoingRetained C v).card +
          (outgoingRetained C u ∩ outgoingRetained C v).card := by
    exact Finset.card_sdiff_add_card_inter_of_subset
      (Finset.inter_subset_left :
        outgoingRetained C u ∩ outgoingRetained C v ⊆
          outgoingRetained C u)
  have hOvDecomp :
      (outgoingRetained C v).card =
        (outgoingRetained C v \ outgoingRetained C u).card +
          (outgoingRetained C u ∩ outgoingRetained C v).card := by
    have h :=
      Finset.card_sdiff_add_card_inter_of_subset
        (Finset.inter_subset_left :
          outgoingRetained C v ∩ outgoingRetained C u ⊆
            outgoingRetained C v)
    simpa [Finset.inter_comm, Nat.add_comm] using h
  omega

/-- Saturated same-code endpoints satisfy the exact exponent identity. -/
theorem sameRetained_saturated_exponent_identity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent u + exponent v +
        (incomingRetained C u).card +
        (outgoingRetained C u ∩ outgoingRetained C v).card
      =
    n := by
  have h :=
    sameRetained_noCommonInactive_card_identity
      C hsame hno
  rw [← huSat, ← hvSat] at h
  exact h

/-- Positive saturated hard pairs occupy a dyadic block reduced by their common
orientation credit. -/
theorem sameRetained_saturated_pair_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huPos : 1 ≤ exponent u)
    (hvPos : 1 ≤ exponent v) :
    2 ^ exponent u + 2 ^ exponent v
      ≤
    2 ^ (n -
      ((incomingRetained C u).card +
       (outgoingRetained C u ∩ outgoingRetained C v).card)) := by
  have hid :=
    sameRetained_saturated_exponent_identity
      C exponent hsame hno huSat hvSat
  have hsum :
      exponent u + exponent v ≤
        n -
          ((incomingRetained C u).card +
           (outgoingRetained C u ∩ outgoingRetained C v).card) := by
    omega
  exact two_pow_add_le_two_pow_of_pos_sum_le
    huPos hvPos hsum

#print axioms retainedInactive_left_eq_outgoingRight_sdiff_outgoingLeft
#print axioms retainedInactive_right_eq_outgoingLeft_sdiff_outgoingRight
#print axioms safeTargetSet_eq_retainedInactive_upper_of_sameRetained
#print axioms sameRetained_noCommonInactive_card_identity
#print axioms sameRetained_saturated_exponent_identity
#print axioms sameRetained_saturated_pair_dyadic_capacity

end OrderedEdgeColoring
end JSP000404Research
