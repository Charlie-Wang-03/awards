import JSP000404Research.ResidualNetCollisionOriginalBridgeVertexMatching
import Mathlib.Tactic

/-!
# Original-centre matching is ALWAYS no larger than slot matching

A target-exact eligible candidate SLOT matching can reuse the SAME
original centre with distinct flip-colour coordinates, even when
each of its slot endpoints is different.

Conversely, any original-centre VERTEX-DISJOINT matching of eligible
SOFT bridges can lift each original bridge to one of its eligible
(coloured) edges: the lifts form a genuine slot matching.

Thus for every target diagonal d,

  nu_original_vertex(d) <= nu_slot(d).

The new vertex matching capacity is kernel-proven to be AT LEAST
as strong as the old slot matching capacity, not just a
syntactically different bound. An example of STRICT inequality
is not claimed.

The original hard-source four-vertices-per-source budget remains
independent. Combining it with the original bridge matching gives
a jointly certified real NET fibre capacity

  |F_d| <= min(nu_original_vertex(d), floor(|V| / 4))

and a corresponding exact duplicate-image excess bound.
No Boolean hole payment or complete JSP-000404 proof is asserted.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Pick one actual eligible coloured edge over an ORIGINAL
soft bridge in the exact-shell projected candidate graph. -/
noncomputable def targetExactShellOriginalBridgeSlotLift
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (b : {r : V × V //
      r ∈ targetExactShellOriginalBridgeEdges C exponent d}) :
    ((V × Fin n) × (V × Fin n)) :=
  Classical.choose (Finset.mem_image.mp b.2)

/-- The chosen coloured edge is genuinely target-exact eligible,
and its two ORIGINAL endpoint vertices are the bridge. -/
theorem target_exact_shell_original_bridge_slot_lift_spec
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (b : {r : V × V //
      r ∈ targetExactShellOriginalBridgeEdges C exponent d}) :
    targetExactShellOriginalBridgeSlotLift C exponent d b ∈
      targetExactShellSlotEdges C exponent d ∧
    ((targetExactShellOriginalBridgeSlotLift C exponent d b).1.1,
     (targetExactShellOriginalBridgeSlotLift C exponent d b).2.1) =
      b.1 := by
  unfold targetExactShellOriginalBridgeSlotLift
  exact Classical.choose_spec (Finset.mem_image.mp b.2)

/-- Every eligible matching on ORIGINAL vertex-disjoint bridges
lifts to a target-exact (vertex,colour)-slot matching of the SAME
cardinality. The implication is one-way: slot matchings need not
be original-vertex-disjoint. -/
theorem target_original_vertex_matching_lifts_to_slot_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (M : Finset (V × V))
    (hM : targetExactShellOriginalVertexMatching C exponent d M) :
    ∃ N : Finset ((V × Fin n) × (V × Fin n)),
      N ⊆ targetExactShellSlotEdges C exponent d ∧
      N.card = M.card ∧
      (∀ e ∈ N, ∀ f ∈ N, e.1 = f.1 → e = f) ∧
      (∀ e ∈ N, ∀ f ∈ N, e.2 = f.2 → e = f) := by
  classical
  let E := {r : V × V // r ∈ M}
  let g : E → ((V × Fin n) × (V × Fin n)) :=
    fun r => targetExactShellOriginalBridgeSlotLift
      C exponent d ⟨r.1, hM.1 r.2⟩
  let N := (Finset.univ : Finset E).image g
  have hproj (r : E) : ((g r).1.1, (g r).2.1) = r.1 :=
    (target_exact_shell_original_bridge_slot_lift_spec
      C exponent d ⟨r.1, hM.1 r.2⟩).2
  have hleft : Function.Injective (fun r : E => (g r).1) := by
    intro r s h
    have hr := congrArg Prod.fst (hproj r)
    have hs := congrArg Prod.fst (hproj s)
    have hvertex : r.1.1 = s.1.1 := by
      calc
        r.1.1 = (g r).1.1 := hr.symm
        _ = (g s).1.1 := congrArg Prod.fst h
        _ = s.1.1 := hs
    exact Subtype.ext (hM.2 r.1 r.2 s.1 s.2 (Or.inl hvertex))
  have hright : Function.Injective (fun r : E => (g r).2) := by
    intro r s h
    have hr := congrArg Prod.snd (hproj r)
    have hs := congrArg Prod.snd (hproj s)
    have hvertex : r.1.2 = s.1.2 := by
      calc
        r.1.2 = (g r).2.1 := hr.symm
        _ = (g s).2.1 := congrArg Prod.fst h
        _ = s.1.2 := hs
    exact Subtype.ext
      (hM.2 r.1 r.2 s.1 s.2
        (Or.inr (Or.inr (Or.inr hvertex))))
  have hinj : Function.Injective g := by
    intro r s h
    exact hleft (congrArg Prod.fst h)
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
    exact (target_exact_shell_original_bridge_slot_lift_spec
      C exponent d ⟨r.1, hM.1 r.2⟩).1
  · change ((Finset.univ : Finset E).image g).card = M.card
    calc
      ((Finset.univ : Finset E).image g).card =
          (Finset.univ : Finset E).card :=
        Finset.card_image_of_injective _ hinj
      _ = M.card := by simp [E]
  · intro e he f hf h
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hf
    have hrs : r = s := hleft h
    rw [hrs]
  · intro e he f hf h
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hf
    have hrs : r = s := hright h
    rw [hrs]

/-- Formal dominance audit: ORIGINAL vertex matching capacity
is ALWAYS ≤ ordinary coloured slot matching capacity for the
same exact-shell eligible candidate graph. There is no
unjustified claim that the inequality is STRICT in all cases. -/
theorem target_exact_shell_original_vertex_number_le_slot_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    targetExactShellOriginalVertexMatchingNumber C exponent d ≤
      targetExactShellSlotMatchingNumber C exponent d := by
  classical
  unfold targetExactShellOriginalVertexMatchingNumber
  apply Finset.sup_le
  intro M hM
  obtain ⟨N, hsub, hcard, hl, hr⟩ :=
    target_original_vertex_matching_lifts_to_slot_matching
      C exponent d M (Finset.mem_filter.mp hM).2
  rw [← hcard]
  exact exact_shell_slot_matching_card_le_matching_number
    C exponent d N hsub hl hr

/-- The source-native ORIGINAL bridge matching number, combined
with the independent original hard-carrier quarter-vertex budget,
is an upper bound on each ACTUAL NET target fibre. -/
theorem net_collision_fibre_card_le_original_matching_vertex_quarter_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      min (targetExactShellOriginalVertexMatchingNumber C exponent d)
        (Fintype.card V / 4) := by
  exact le_min
    (net_collision_fibre_card_le_original_vertex_matching_number
      C exponent hexp honeLoss d)
    (net_collision_fibre_card_le_vertex_quarter
      C exponent hexp honeLoss d)

/-- Provably no weaker than the previous slot+vertex-quarter
MINIMUM capacity, as original-centre matching is a subconstraint
of ordinary slot matching. -/
theorem original_matching_vertex_quarter_min_le_prior_slot_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    min (targetExactShellOriginalVertexMatchingNumber C exponent d)
        (Fintype.card V / 4) ≤
      min (targetExactShellSlotMatchingNumber C exponent d)
        (Fintype.card V / 4) := by
  exact min_le_min_right _
    (target_exact_shell_original_vertex_number_le_slot_number
      C exponent d)

/-- Certified new duplicate-image excess upper bound from the
strictly SOURCE-COMPATIBLE original-vertex graph and independent
hard-carrier packing. All Boolean targets remain separately
counted, with NO assumed globally non-reused hole payment. -/
theorem net_collision_duplicate_debt_le_original_matching_vertex_min_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (min (targetExactShellOriginalVertexMatchingNumber C exponent d)
          (Fintype.card V / 4) - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hbound :=
    net_collision_fibre_card_le_original_matching_vertex_quarter_min
      C exponent hexp honeLoss d
  omega

#print axioms target_original_vertex_matching_lifts_to_slot_matching
#print axioms target_exact_shell_original_vertex_number_le_slot_number
#print axioms net_collision_fibre_card_le_original_matching_vertex_quarter_min
#print axioms original_matching_vertex_quarter_min_le_prior_slot_min
#print axioms net_collision_duplicate_debt_le_original_matching_vertex_min_excess

end OrderedEdgeColoring
end JSP000404Research
