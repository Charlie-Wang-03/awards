
import JSP000404Research.ResidualUnsafeWitnessCount
import Mathlib.Tactic

/-!
# Unsafe residual edges consume vertices on both sides

For c in the through-colour set

  J(u,v) = incomingRetained(u) inter outgoingRetained(v),

there is an edge a--u of colour c with a<u and an edge v--w of colour c with
v<w.

Distinct colours force distinct witnesses, since a fixed edge has only one
colour.  Therefore J(u,v) injects into the strict-left vertices of u and into
the strict-right vertices of v.

Combined with the strengthened unsafe-edge budget

  exponent(u)+exponent(v)+card J(u,v) <= n,

this ties the local dyadic weight of an unsafe residual edge to actual room on
both sides in the ambient linear order.

At an extreme endpoint this becomes rigid: if u has no vertices to its left,
then J is empty and unsafety forces every retained colour to be outgoing at v.
Because the residual colour is also active at v, v uses all n+1 colours; under
the standard one-layer active bound this forces exponent(v)=0.  The symmetric
statement holds at a rightmost endpoint.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Through colours inject into actual vertices strictly left of u. -/
theorem throughColours_card_le_strictLeft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (residualThroughColours C u v).card ≤
      (strictLeftVertices u).card := by
  classical
  let chooseLeft :
      {c : Fin n // c ∈ residualThroughColours C u v} → V :=
    fun c =>
      Classical.choose
        ((throughColour_has_outer_witnesses
          C c.2).1)
  have hchoose :
      ∀ c : {c : Fin n // c ∈ residualThroughColours C u v},
        chooseLeft c < u ∧
        C.color (chooseLeft c) u = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      ((throughColour_has_outer_witnesses C c.2).1)
  have hinj : Function.Injective chooseLeft := by
    intro c d hcd
    apply Subtype.ext
    have hc := (hchoose c).2
    have hd := (hchoose d).2
    rw [hcd] at hc
    have hcast : c.1.castSucc = d.1.castSucc := by
      exact hc.symm.trans hd
    exact Fin.ext (congrArg Fin.val hcast)
  let f :
      {c : Fin n // c ∈ residualThroughColours C u v} →
        {a : V // a ∈ strictLeftVertices u} :=
    fun c => ⟨chooseLeft c,
      (mem_strictLeftVertices u (chooseLeft c)).2 (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d h
    apply hinj
    exact congrArg Subtype.val h
  have hcard :=
    Fintype.card_le_of_injective f hf
  simpa [f] using hcard

/-- Through colours inject into actual vertices strictly right of v. -/
theorem throughColours_card_le_strictRight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (residualThroughColours C u v).card ≤
      (strictRightVertices v).card := by
  classical
  let chooseRight :
      {c : Fin n // c ∈ residualThroughColours C u v} → V :=
    fun c =>
      Classical.choose
        ((throughColour_has_outer_witnesses
          C c.2).2)
  have hchoose :
      ∀ c : {c : Fin n // c ∈ residualThroughColours C u v},
        v < chooseRight c ∧
        C.color v (chooseRight c) = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      ((throughColour_has_outer_witnesses C c.2).2)
  have hinj : Function.Injective chooseRight := by
    intro c d hcd
    apply Subtype.ext
    have hc := (hchoose c).2
    have hd := (hchoose d).2
    rw [hcd] at hc
    have hcast : c.1.castSucc = d.1.castSucc := by
      exact hc.symm.trans hd
    exact Fin.ext (congrArg Fin.val hcast)
  let f :
      {c : Fin n // c ∈ residualThroughColours C u v} →
        {w : V // w ∈ strictRightVertices v} :=
    fun c => ⟨chooseRight c,
      (mem_strictRightVertices v (chooseRight c)).2 (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d h
    apply hinj
    exact congrArg Subtype.val h
  have hcard :=
    Fintype.card_le_of_injective f hf
  simpa [f] using hcard

/-- Unsafe residual edge: exponent sum plus available left/right order room is
bounded through the same through-colour credit. -/
theorem unsafe_residual_exponent_sum_add_min_side_le
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
        (residualThroughColours C u v).card ≤ n ∧
    (residualThroughColours C u v).card ≤
        (strictLeftVertices u).card ∧
    (residualThroughColours C u v).card ≤
        (strictRightVertices v).card := by
  exact ⟨
    unsafe_residual_exponent_sum_add_through_le
      C exponent hexp honeLoss huv hres hunsafe,
    throughColours_card_le_strictLeft C u v,
    throughColours_card_le_strictRight C u v⟩

/-- If the lower endpoint has no vertex to its left, an unsafe residual edge
forces the upper endpoint to have exponent zero. -/
theorem unsafe_residual_from_leftmost_forces_upper_exponent_zero
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (hleft : (strictLeftVertices u).card = 0)
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    exponent v = 0 := by
  have hthrough0 :
      (residualThroughColours C u v).card = 0 := by
    have hle := throughColours_card_le_strictLeft C u v
    omega
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hIncomingEmpty :
      incomingRetained C u = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    have hthrough :
        c ∈ residualThroughColours C u v := by
      have hOut : c ∈ outgoingRetained C v := by
        have hall : c ∈ incomingRetained C u ∪ outgoingRetained C v := by
          rw [hunion]
          simp
        rcases Finset.mem_union.mp hall with hIn | hOut
        · exact False.elim ((by
            have hleftWitness :=
              (mem_incomingRetained_iff C u c).1 hIn
            obtain ⟨a, hau, _⟩ := hleftWitness
            have haMem :
                a ∈ strictLeftVertices u :=
              (mem_strictLeftVertices u a).2 hau
            have hpos :
                0 < (strictLeftVertices u).card :=
              Finset.card_pos.mpr ⟨a, haMem⟩
            omega) : False)
        · exact hOut
      exact (mem_residualThroughColours C u v c).2 ⟨hc, hOut⟩
    have hpos :
        0 < (residualThroughColours C u v).card :=
      Finset.card_pos.mpr ⟨c, hthrough⟩
    omega
  have hOutAll :
      outgoingRetained C v = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    have hcAll :
        c ∈ incomingRetained C u ∪ outgoingRetained C v := by
      rw [hunion]
      simp
    rw [hIncomingEmpty] at hcAll
    simpa using hcAll
  have hretCard :
      (retainedActive C v).card = n := by
    have hsub :
        outgoingRetained C v ⊆ retainedActive C v :=
      outgoingRetained_subset_retainedActive C v
    have hN :
        n ≤ (retainedActive C v).card := by
      rw [hOutAll] at hsub
      have h := Finset.card_le_card hsub
      simpa using h
    have hle :
        (retainedActive C v).card ≤ n := by
      simpa using Finset.card_le_univ (retainedActive C v)
    omega
  have hresActive :=
    residualCoord_mem_active_of_isResidual C huv hres
  have hactiveLower :=
    retainedActive_card_add_one_le_active_of_residual_mem
      C v hresActive.2
  have hbound := honeLoss v
  have hvN := hexp v
  rw [hretCard] at hactiveLower
  omega

/-- Symmetric rightmost form. -/
theorem unsafe_residual_to_rightmost_forces_lower_exponent_zero
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (hright : (strictRightVertices v).card = 0)
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    exponent u = 0 := by
  have hthrough0 :
      (residualThroughColours C u v).card = 0 := by
    have hle := throughColours_card_le_strictRight C u v
    omega
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hOutgoingEmpty :
      outgoingRetained C v = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    have hrightWitness :=
      (mem_outgoingRetained_iff C v c).1 hc
    obtain ⟨w, hvw, _⟩ := hrightWitness
    have hwMem :
        w ∈ strictRightVertices v :=
      (mem_strictRightVertices v w).2 hvw
    have hpos :
        0 < (strictRightVertices v).card :=
      Finset.card_pos.mpr ⟨w, hwMem⟩
    omega
  have hInAll :
      incomingRetained C u = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    have hcAll :
        c ∈ incomingRetained C u ∪ outgoingRetained C v := by
      rw [hunion]
      simp
    rw [hOutgoingEmpty] at hcAll
    simpa using hcAll
  have hretCard :
      (retainedActive C u).card = n := by
    have hsub :
        incomingRetained C u ⊆ retainedActive C u :=
      incomingRetained_subset_retainedActive C u
    have hN :
        n ≤ (retainedActive C u).card := by
      rw [hInAll] at hsub
      have h := Finset.card_le_card hsub
      simpa using h
    have hle :
        (retainedActive C u).card ≤ n := by
      simpa using Finset.card_le_univ (retainedActive C u)
    omega
  have hresActive :=
    residualCoord_mem_active_of_isResidual C huv hres
  have hactiveLower :=
    retainedActive_card_add_one_le_active_of_residual_mem
      C u hresActive.1
  have hbound := honeLoss u
  have huN := hexp u
  rw [hretCard] at hactiveLower
  omega

#print axioms throughColours_card_le_strictLeft
#print axioms throughColours_card_le_strictRight
#print axioms unsafe_residual_exponent_sum_add_min_side_le
#print axioms unsafe_residual_from_leftmost_forces_upper_exponent_zero
#print axioms unsafe_residual_to_rightmost_forces_lower_exponent_zero

end OrderedEdgeColoring
end JSP000404Research
