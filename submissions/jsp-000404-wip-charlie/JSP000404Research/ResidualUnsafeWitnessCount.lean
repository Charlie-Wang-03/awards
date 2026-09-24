
import JSP000404Research.ResidualUnsafeEdgeBudget
import JSP000404Research.ResidualBlockerDensity
import Mathlib.Tactic

/-!
# Unsafe residual edges consume ordered outer witnesses

For a residual edge u<v with no safe retained colour,

  incomingRetained(u) union outgoingRetained(v) = Fin n.

The overlap J of these two colour sets is counted twice, so

  n + card J
    = card incomingRetained(u) + card outgoingRetained(v).

Each incoming retained colour at u requires a distinct witness vertex a<u,
because one edge a--u has only one colour.  Likewise each outgoing retained
colour at v requires a distinct witness w>v.

Therefore

  n + card J
    <= card {a | a<u} + card {w | v<w}.

This turns the through-colour credit from ResidualUnsafeEdgeBudget into an
actual ordered-vertex resource.  It is suitable for minimal-counterexample or
deletion arguments and uses no geometric conjecture beyond the existing
ordered-colouring axioms.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def strictLeftVertices
    {V : Type*} [LinearOrder V] [Fintype V]
    (u : V) : Finset V := by
  classical
  exact Finset.univ.filter fun a => a < u

@[simp] theorem mem_strictLeftVertices
    {V : Type*} [LinearOrder V] [Fintype V]
    (u a : V) :
    a ∈ strictLeftVertices u ↔ a < u := by
  classical
  simp [strictLeftVertices]

/-- Incoming retained colours inject into strict-left witness vertices. -/
theorem incomingRetained_card_le_left
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) :
    (incomingRetained C u).card ≤
      (strictLeftVertices u).card := by
  classical
  let chooseLeft :
      {c : Fin n // c ∈ incomingRetained C u} → V :=
    fun c => Classical.choose
      ((mem_incomingRetained_iff C u c.1).1 c.2)
  have hchoose :
      ∀ c : {c : Fin n // c ∈ incomingRetained C u},
        chooseLeft c < u ∧
        C.color (chooseLeft c) u = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      ((mem_incomingRetained_iff C u c.1).1 c.2)
  let f :
      {c : Fin n // c ∈ incomingRetained C u} →
        {a : V // a ∈ strictLeftVertices u} :=
    fun c => ⟨chooseLeft c,
      (mem_strictLeftVertices u (chooseLeft c)).2
        (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    apply Fin.ext
    have hw :
        chooseLeft c = chooseLeft d :=
      congrArg Subtype.val hcd
    have hcCol := (hchoose c).2
    have hdCol := (hchoose d).2
    rw [hw] at hcCol
    have heq :
        c.1.castSucc = d.1.castSucc :=
      hcCol.symm.trans hdCol
    exact congrArg Fin.val heq
  have hcard :=
    Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- Outgoing retained colours inject into strict-right witness vertices. -/
theorem outgoingRetained_card_le_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (outgoingRetained C v).card ≤
      (strictRightVertices v).card := by
  classical
  let chooseRight :
      {c : Fin n // c ∈ outgoingRetained C v} → V :=
    fun c => Classical.choose
      ((mem_outgoingRetained_iff C v c.1).1 c.2)
  have hchoose :
      ∀ c : {c : Fin n // c ∈ outgoingRetained C v},
        v < chooseRight c ∧
        C.color v (chooseRight c) = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      ((mem_outgoingRetained_iff C v c.1).1 c.2)
  let f :
      {c : Fin n // c ∈ outgoingRetained C v} →
        {w : V // w ∈ strictRightVertices v} :=
    fun c => ⟨chooseRight c,
      (mem_strictRightVertices v (chooseRight c)).2
        (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    apply Fin.ext
    have hw :
        chooseRight c = chooseRight d :=
      congrArg Subtype.val hcd
    have hcCol := (hchoose c).2
    have hdCol := (hchoose d).2
    rw [hw] at hcCol
    have heq :
        c.1.castSucc = d.1.castSucc :=
      hcCol.symm.trans hdCol
    exact congrArg Fin.val heq
  have hcard :=
    Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard


/-- Through colours separately inject into the strict-left and strict-right
outside vertex sets. -/
theorem residualThroughColours_card_le_outer_sides
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (residualThroughColours C u v).card ≤
        (strictLeftVertices u).card ∧
      (residualThroughColours C u v).card ≤
        (strictRightVertices v).card := by
  constructor
  · exact
      (Finset.card_le_card Finset.inter_subset_left).trans
        (incomingRetained_card_le_left C u)
  · exact
      (Finset.card_le_card Finset.inter_subset_right).trans
        (outgoingRetained_card_le_right C v)

/-- Main ordered witness-count inequality for a completely unsafe edge. -/
theorem unsafe_residual_outer_witness_count
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    n + (residualThroughColours C u v).card ≤
      (strictLeftVertices u).card +
        (strictRightVertices v).card := by
  have hbal :=
    unsafe_residual_card_balance C hunsafe
  have hleft :=
    incomingRetained_card_le_left C u
  have hright :=
    outgoingRetained_card_le_right C v
  omega


/-- Combining the local exponent credit with the ordered outer-witness credit
shows that each through colour is paid twice in the outside population. -/
theorem unsafe_residual_exponent_plus_twice_through_le_outer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    exponent u + exponent v +
        2 * (residualThroughColours C u v).card ≤
      (strictLeftVertices u).card +
        (strictRightVertices v).card := by
  have hexpBudget :=
    unsafe_residual_exponent_sum_add_through_le
      C exponent hexp honeLoss huv hres hunsafe
  have houter :=
    unsafe_residual_outer_witness_count C hunsafe
  omega

/-- A completely unsafe residual edge has at least n outside witness vertices
in total. -/
theorem unsafe_residual_n_le_outer_count
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    n ≤
      (strictLeftVertices u).card +
        (strictRightVertices v).card := by
  have h := unsafe_residual_outer_witness_count C hunsafe
  omega

/-- If there are too few outer vertices, a safe retained target must exist. -/
theorem exists_safe_colour_of_outer_count_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsmall :
      (strictLeftVertices u).card +
        (strictRightVertices v).card < n) :
    ∃ c : Fin n, c ∉ residualForbidden C u v := by
  by_contra hsafe
  push_neg at hsafe
  have hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v := by
    push_neg
    exact hsafe
  have hcount :=
    unsafe_residual_outer_witness_count C hunsafe
  omega

#print axioms incomingRetained_card_le_left
#print axioms outgoingRetained_card_le_right
#print axioms residualThroughColours_card_le_outer_sides
#print axioms unsafe_residual_outer_witness_count
#print axioms unsafe_residual_exponent_plus_twice_through_le_outer
#print axioms unsafe_residual_n_le_outer_count
#print axioms exists_safe_colour_of_outer_count_lt

end OrderedEdgeColoring
end JSP000404Research
