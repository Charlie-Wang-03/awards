import JSP000404Research.ResidualNetCollisionElevenCentreTwinCap
import Mathlib.Tactic

/-!
# Global NET / TWIN original-vertex capacity

An actual doubled NET target forces four different hard carriers, and
none is a terminal equal-exponent TWIN carrier. Since ALL hard carriers
are an original-vertex matching, without ANY upper bound on |V|:

   E_D > 0  =>  8 + 2 * |TWIN hard carriers| <= |V|.

This is a global numerical carrier-capacity inequality. It does NOT
claim these carriers provide Boolean holes or independent dyadic surplus,
nor does it combine witnesses over distinct targets.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem net_collision_positive_duplicate_twin_global_vertex_budget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    8 + 2 * (netTwinRigidCarriers C exponent).card ≤ Fintype.card V := by
  classical
  obtain ⟨s, t, hne, hdiag⟩ :=
    net_collision_positive_duplicate_has_distinct_source_pair
      C exponent hexp honeLoss hpositive
  let ps := netCollisionForwardHardPair C exponent hexp honeLoss s
  let pt := netCollisionForwardHardPair C exponent hexp honeLoss t
  let qs := netCollisionReverseHardPair C exponent hexp honeLoss s
  let qt := netCollisionReverseHardPair C exponent hexp honeLoss t
  let A : Finset (V × V) := {ps, pt, qs, qt}
  let T := netTwinRigidCarriers C exponent
  have hpst : ps ≠ pt :=
    net_collision_distinct_same_target_forward_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hqst : qs ≠ qt :=
    net_collision_distinct_same_target_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hpsqs : ps ≠ qs :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s s
  have hpsqt : ps ≠ qt :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t
  have hptqs : pt ≠ qs :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss t s
  have hptqt : pt ≠ qt :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss t t
  have hAcard : A.card = 4 := by
    change ({ps, pt, qs, qt} : Finset (V × V)).card = 4
    simp [hpst, hpsqs, hpsqt, hptqs, hptqt, hqst]
  have hAsub : A ⊆ hardOverlapCarrierPairs C := by
    intro pair hp
    change pair ∈ ({ps, pt, qs, qt} : Finset (V × V)) at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss s).1
    · exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss t).1
    · exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss s).1
    · exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss t).1
  have hTsub : T ⊆ hardOverlapCarrierPairs C := by
    intro pair hp
    have hrigid : pair ∈ netRigidHardCarriers C exponent :=
      ((mem_netTwinRigidCarriers C exponent pair).mp hp).1
    exact ((mem_netUnpaidHardCarrierPairs C exponent pair).mp
      ((mem_netRigidHardCarriers C exponent pair).mp hrigid).1).1
  have hdisj : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro pair hp ht
    change pair ∈ ({ps, pt, qs, qt} : Finset (V × V)) at hp
    have htw := (mem_netTwinRigidCarriers C exponent pair).mp ht
    have hno : ¬ HasOutgoingHardTransport C pair.1 pair.2 :=
      ((mem_netRigidHardCarriers C exponent pair).mp htw.1).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hps | hpt | hqs | hqt
    · have hyes : HasOutgoingHardTransport C pair.1 pair.2 := by
        rw [hps]
        exact (net_collision_forward_hard_pair_safe
          C exponent hexp honeLoss s).2
      exact hno hyes
    · have hyes : HasOutgoingHardTransport C pair.1 pair.2 := by
        rw [hpt]
        exact (net_collision_forward_hard_pair_safe
          C exponent hexp honeLoss t).2
      exact hno hyes
    · have heq : exponent qs.1 = exponent qs.2 := by
        simpa only [hqs] using htw.2
      have hlt : exponent qs.2 < exponent qs.1 :=
        (mem_netStrictDescentRigidCarriers C exponent qs).mp
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource
              C exponent hexp honeLoss s)).2 |>.2
      omega
    · have heq : exponent qt.1 = exponent qt.2 := by
        simpa only [hqt] using htw.2
      have hlt : exponent qt.2 < exponent qt.1 :=
        (mem_netStrictDescentRigidCarriers C exponent qt).mp
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource
              C exponent hexp honeLoss t)).2 |>.2
      omega
  have hsub : A ∪ T ⊆ hardOverlapCarrierPairs C := by
    intro pair hp
    rcases Finset.mem_union.mp hp with ha | ht
    · exact hAsub ha
    · exact hTsub ht
  have hcard : A.card + T.card ≤ (hardOverlapCarrierPairs C).card := by
    calc
      A.card + T.card = (A ∪ T).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (hardOverlapCarrierPairs C).card := Finset.card_le_card hsub
  have hmatching := hardOverlapCarrierPairs_two_mul_card_le_vertices C
  dsimp only [T] at *
  omega


/-- Each extra TWIN hard pair consumes two additional original centres,
on top of the eight already required by one actual double-hit target. -/
theorem net_collision_positive_duplicate_twin_card_plus_four_le_half
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    (netTwinRigidCarriers C exponent).card + 4 ≤ Fintype.card V / 2 := by
  have h := net_collision_positive_duplicate_twin_global_vertex_budget
    C exponent hexp honeLoss hpositive
  omega

#print axioms net_collision_positive_duplicate_twin_global_vertex_budget
#print axioms net_collision_positive_duplicate_twin_card_plus_four_le_half

end OrderedEdgeColoring
end JSP000404Research
