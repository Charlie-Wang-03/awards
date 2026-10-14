import JSP000404Research.ResidualNetCollisionTwinGlobalVertexBudget
import JSP000404Research.ResidualNetCollisionVertexBudgetFibre
import Mathlib.Tactic

/-!
# Joint ACTUAL NET target fibre + terminal twin original-vertex budget

Every source in a fixed true NET diagonal fibre occupies TWO ORIGINAL
hard carriers (one safe forward, one strict-descending reverse). All of
these are mutually different within the fibre and disjoint from every
terminal equal-exponent TWIN rigid carrier. All original hard carriers
form one original-vertex matching.

Hence for every target, including an empty target:

  4 * |F_d| + 2 * |TWIN carriers| <= |V|.

This strengthens the old independent four-vertices-per-source estimate
and yields a TWIN-aware exact duplicate-fibre cap, valid in arbitrary
Boolean dimension. It is a vertex-ownership restriction, not a new
true-hole or unreserved profile-surplus credit.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem net_collision_fibre_twin_joint_vertex_budget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    4 * (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card +
      2 * (netTwinRigidCarriers C exponent).card ≤ Fintype.card V := by
  classical
  let F := netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let E := {s : S // s ∈ F}
  let f : E → V × V :=
    fun s => netCollisionForwardHardPair C exponent hexp honeLoss s.1
  let g : E → V × V :=
    fun s => netCollisionReverseHardPair C exponent hexp honeLoss s.1
  have hfinj : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    by_contra hne
    have hs : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        s.1 = d := (Finset.mem_filter.mp s.2).2
    have ht : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        t.1 = d := (Finset.mem_filter.mp t.2).2
    exact (net_collision_distinct_same_target_forward_hard_pairs_ne
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hne) h
  have hginj : Function.Injective g := by
    intro s t h
    apply Subtype.ext
    by_contra hne
    have hs : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        s.1 = d := (Finset.mem_filter.mp s.2).2
    have ht : netCollisionCertifiedDiagonal C exponent hexp honeLoss
        t.1 = d := (Finset.mem_filter.mp t.2).2
    exact (net_collision_distinct_same_target_reverse_hard_pairs_ne
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hne) h
  let A := (Finset.univ : Finset E).image f
  let B := (Finset.univ : Finset E).image g
  let T := netTwinRigidCarriers C exponent
  have hcardA : A.card = F.card := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ hfinj]
    simp [E]
  have hcardB : B.card = F.card := by
    dsimp [B]
    rw [Finset.card_image_of_injective _ hginj]
    simp [E]
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro pair ha hb
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp ha
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hb
    exact (net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s.1 t.1) (hs.trans ht.symm)
  have hsub : A ∪ B ⊆ hardOverlapCarrierPairs C := by
    intro pair hpair
    rcases Finset.mem_union.mp hpair with hA | hB
    · obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hA
      rw [← hs]
      exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss s.1).1
    · obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hB
      rw [← hs]
      exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss s.1).1
  have hunion : (A ∪ B).card = 2 * F.card := by
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB]
    omega
  have hTsub : T ⊆ hardOverlapCarrierPairs C := by
    intro pair hp
    have hrigid : pair ∈ netRigidHardCarriers C exponent :=
      ((mem_netTwinRigidCarriers C exponent pair).mp hp).1
    exact ((mem_netUnpaidHardCarrierPairs C exponent pair).mp
      ((mem_netRigidHardCarriers C exponent pair).mp hrigid).1).1
  have hAT : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro pair ha ht
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp ha
    have hrigid : pair ∈ netRigidHardCarriers C exponent :=
      ((mem_netTwinRigidCarriers C exponent pair).mp ht).1
    have hno : ¬ HasOutgoingHardTransport C pair.1 pair.2 :=
      ((mem_netRigidHardCarriers C exponent pair).mp hrigid).2
    have hyes := (net_collision_forward_hard_pair_safe
      C exponent hexp honeLoss s.1).2
    change HasOutgoingHardTransport C (f s).1 (f s).2 at hyes
    rw [hs] at hyes
    exact hno hyes
  have hBT : Disjoint B T := by
    apply Finset.disjoint_left.mpr
    intro pair hb ht
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hb
    have heq : exponent pair.1 = exponent pair.2 :=
      ((mem_netTwinRigidCarriers C exponent pair).mp ht).2
    have hstrict :=
      (mem_netStrictDescentRigidCarriers C exponent
        (netCollisionReverseHardPair C exponent hexp honeLoss s.1)).mp
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource
              C exponent hexp honeLoss s.1)).2 |>.2
    change exponent (g s).2 < exponent (g s).1 at hstrict
    rw [hs] at hstrict
    omega
  have hABT : Disjoint (A ∪ B) T := by
    apply Finset.disjoint_left.mpr
    intro pair hab ht
    rcases Finset.mem_union.mp hab with ha | hb
    · exact (Finset.disjoint_left.mp hAT) ha ht
    · exact (Finset.disjoint_left.mp hBT) hb ht
  have hfullsub : A ∪ B ∪ T ⊆ hardOverlapCarrierPairs C := by
    intro pair hmem
    rcases Finset.mem_union.mp hmem with hab | ht
    · exact hsub hab
    · exact hTsub ht
  have hfullcard : (A ∪ B ∪ T).card = 2 * F.card + T.card := by
    rw [Finset.card_union_of_disjoint hABT, hunion]
  have hle : 2 * F.card + T.card ≤ (hardOverlapCarrierPairs C).card := by
    calc
      2 * F.card + T.card = (A ∪ B ∪ T).card := hfullcard.symm
      _ ≤ (hardOverlapCarrierPairs C).card := Finset.card_le_card hfullsub
  have hsize := hardOverlapCarrierPairs_two_mul_card_le_vertices C
  change 4 * F.card + 2 * T.card ≤ Fintype.card V
  omega



/-- Effective per-target source capacity after accounting for all
terminal TWIN hard carriers, with ordinary Nat subtraction. -/
theorem net_collision_fibre_card_le_twin_adjusted_quarter
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      (Fintype.card V -
        2 * (netTwinRigidCarriers C exponent).card) / 4 := by
  have h := net_collision_fibre_twin_joint_vertex_budget
    C exponent hexp honeLoss d
  omega

/-- Global duplicate debt upper bound refined by the TWIN-adjusted
original-vertex capacity. This sum runs only over ACTUAL distinct
NET targets. It is not a new global geometry payment theorem. -/
theorem net_collision_duplicate_debt_le_twin_adjusted_quarter_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        ((Fintype.card V -
          2 * (netTwinRigidCarriers C exponent).card) / 4 - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have h := net_collision_fibre_card_le_twin_adjusted_quarter
    C exponent hexp honeLoss d
  omega

#print axioms net_collision_fibre_twin_joint_vertex_budget
#print axioms net_collision_fibre_card_le_twin_adjusted_quarter
#print axioms net_collision_duplicate_debt_le_twin_adjusted_quarter_excess

end OrderedEdgeColoring
end JSP000404Research
