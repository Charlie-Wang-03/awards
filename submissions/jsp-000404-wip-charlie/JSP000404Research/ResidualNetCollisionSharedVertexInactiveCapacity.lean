import JSP000404Research.ResidualNetCollisionSharedVertexTwoBitClassification
import Mathlib.Tactic

/-!
# Shared-vertex duplicate diagonals require at least TWO inactive bits there

For two genuine NET collision sink sources w,z both belonging to the
same retained-completion cube at vertex c, every disagreement between
w and z is necessarily at a coordinate INACTIVE at c.

Combine this with the proved classification that distinct NET
sources sharing a canonical diagonal and any original soft-bridge
vertex have exactly TWO disagreement bits. The COMMON vertex must
therefore have AT LEAST TWO inactive completion coordinates.

This eliminates any shared-vertex duplication involving a centre
with zero- or one-dimensional completion cube. It does not exclude
all such configurations for higher-dimensional cubes or solve the
global six-source payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Distinct completion words in one vertex cube can differ ONLY at
its retained-inactive coordinates. -/
theorem two_words_in_one_retained_cube_difference_subset_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (c : V) (w z : Fin n → Bool)
    (hw : w ∈ retainedCompletionWords C c)
    (hz : z ∈ retainedCompletionWords C c) :
    (Finset.univ.filter (fun e : Fin n => w e ≠ z e)) ⊆
      ((Finset.univ : Finset (Fin n)) \ retainedActive C c) := by
  classical
  intro e he
  have hdiff : w e ≠ z e := (Finset.mem_filter.mp he).2
  have hnot : e ∉ retainedActive C c := by
    intro heactive
    have hwe := (mem_retainedCompletionWords C c w).1 hw e heactive
    have hze := (mem_retainedCompletionWords C c z).1 hz e heactive
    exact hdiff (hwe.trans hze.symm)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hnot⟩

/-- Every certified NET collision source lies simultaneously in
BOTH retained completion cubes of its source-native soft bridge. -/
theorem net_collision_source_in_both_original_soft_bridge_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    let bs := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s
    s.1 ∈ retainedCompletionWords C bs.1 ∧
      s.1 ∈ retainedCompletionWords C bs.2 := by
  classical
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  change s.1 ∈ retainedCompletionWords C q.1.1 ∧
      s.1 ∈ retainedCompletionWords C p.1.2
  have hsrc := net_collision_certified_sources_same_sink
    C exponent hexp honeLoss s
  constructor
  · rw [← hsrc.2]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss y
  · rw [← hsrc.1]
    exact transportableHardWordToSingletonOrSoft_mem_upper C x

/-- If two distinct genuine NET collisions have the SAME canonical
diagonal AND their source-native original bridges share vertex c
(IN ANY endpoint role), then c's retained cube has dimension AT
LEAST TWO. This is an unconditional source-native obstruction. -/
theorem net_collision_shared_bridge_vertex_duplicate_requires_two_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hne : s ≠ t)
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (c : V)
    (hcs : c =
        (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 ∨
      c = (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2)
    (hct : c =
        (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1 ∨
      c = (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2) :
    2 ≤ ((Finset.univ : Finset (Fin n)) \ retainedActive C c).card := by
  classical
  let bs := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s
  let bt := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t
  change c = bs.1 ∨ c = bs.2 at hcs
  change c = bt.1 ∨ c = bt.2 at hct
  have hshare : netCollisionBridgeOwnersShareVertex
      C exponent hexp honeLoss s t := by
    change bs.1 = bt.1 ∨ bs.2 = bt.2 ∨
      bs.1 = bt.2 ∨ bs.2 = bt.1
    rcases hcs with hcS | hcS
    · rcases hct with hcT | hcT
      · exact Or.inl (hcS.symm.trans hcT)
      · exact Or.inr (Or.inr (Or.inl (hcS.symm.trans hcT)))
    · rcases hct with hcT | hcT
      · exact Or.inr (Or.inr (Or.inr (hcS.symm.trans hcT)))
      · exact Or.inr (Or.inl (hcS.symm.trans hcT))
  have htwo :=
    (net_collision_shared_bridge_vertex_same_diagonal_distinct_sources_two_bit
      C exponent hexp honeLoss s t hne hdiag hshare).1
  have hsourceS :=
    net_collision_source_in_both_original_soft_bridge_cubes
      C exponent hexp honeLoss s
  have hsourceT :=
    net_collision_source_in_both_original_soft_bridge_cubes
      C exponent hexp honeLoss t
  change s.1 ∈ retainedCompletionWords C bs.1 ∧
    s.1 ∈ retainedCompletionWords C bs.2 at hsourceS
  change t.1 ∈ retainedCompletionWords C bt.1 ∧
    t.1 ∈ retainedCompletionWords C bt.2 at hsourceT
  have hs : s.1 ∈ retainedCompletionWords C c := by
    rcases hcs with h | h
    · rw [h]; exact hsourceS.1
    · rw [h]; exact hsourceS.2
  have ht : t.1 ∈ retainedCompletionWords C c := by
    rcases hct with h | h
    · rw [h]; exact hsourceT.1
    · rw [h]; exact hsourceT.2
  have hsub := two_words_in_one_retained_cube_difference_subset_inactive
    C c s.1 t.1 hs ht
  have hcap := Finset.card_le_card hsub
  rw [htwo] at hcap
  exact hcap

#print axioms two_words_in_one_retained_cube_difference_subset_inactive
#print axioms net_collision_source_in_both_original_soft_bridge_cubes
#print axioms net_collision_shared_bridge_vertex_duplicate_requires_two_inactive

end OrderedEdgeColoring
end JSP000404Research
