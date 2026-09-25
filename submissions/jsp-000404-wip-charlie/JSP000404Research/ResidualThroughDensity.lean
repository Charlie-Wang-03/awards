
import JSP000404Research.ResidualUnsafeEdgeBudget
import JSP000404Research.ResidualUnsafeWitnessCount
import JSP000404Research.ResidualBlockerDensity
import JSP000404Research.ResidualActiveDrop
import Mathlib.Tactic

/-!
# Through-colour density around an unsafe residual edge

For an unsafe residual edge u<v, every colour in

  J(u,v) = incomingRetained(u) inter outgoingRetained(v)

has an entering witness a<u and a leaving witness w>v.

Because one edge has only one colour, distinct through colours require
distinct left witnesses and distinct right witnesses.  Hence

  card J(u,v) <= #{a | a<u},
  card J(u,v) <= #{w | v<w}.

At the boundary this becomes rigid.  If u has no earlier vertex, then
incomingRetained(u)=empty; unsafe means outgoingRetained(v)=all retained
colours.  Since uv is residual, v uses all n retained colours plus the
residual colour.  Under the one-layer Sendov active bound this forces
exponent(v)=0.  The right-boundary statement is symmetric.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Through colours inject into vertices strictly to the left of the lower
endpoint. -/
theorem residualThroughColours_card_le_left
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
        (throughColour_has_outer_witnesses C c.2).1
  have hchoose :
      ∀ c : {c : Fin n // c ∈ residualThroughColours C u v},
        chooseLeft c < u ∧
          C.color (chooseLeft c) u = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      (throughColour_has_outer_witnesses C c.2).1
  let f :
      {c : Fin n // c ∈ residualThroughColours C u v} →
        {a : V // a ∈ strictLeftVertices u} :=
    fun c => ⟨chooseLeft c, by
      exact (mem_strictLeftVertices u (chooseLeft c)).2
        (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    have had :
        chooseLeft c = chooseLeft d :=
      congrArg Subtype.val hcd
    have hcol :
        c.1.castSucc = d.1.castSucc := by
      calc
        c.1.castSucc
            = C.color (chooseLeft c) u := (hchoose c).2.symm
        _ = C.color (chooseLeft d) u := by rw [had]
        _ = d.1.castSucc := (hchoose d).2
    exact Fin.ext (congrArg Fin.val hcol)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- Through colours inject into vertices strictly to the right of the upper
endpoint. -/
theorem residualThroughColours_card_le_right
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
        (throughColour_has_outer_witnesses C c.2).2
  have hchoose :
      ∀ c : {c : Fin n // c ∈ residualThroughColours C u v},
        v < chooseRight c ∧
          C.color v (chooseRight c) = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      (throughColour_has_outer_witnesses C c.2).2
  let f :
      {c : Fin n // c ∈ residualThroughColours C u v} →
        {w : V // w ∈ strictRightVertices v} :=
    fun c => ⟨chooseRight c, by
      exact (mem_strictRightVertices v (chooseRight c)).2
        (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    have hwd :
        chooseRight c = chooseRight d :=
      congrArg Subtype.val hcd
    have hcol :
        c.1.castSucc = d.1.castSucc := by
      calc
        c.1.castSucc
            = C.color v (chooseRight c) := (hchoose c).2.symm
        _ = C.color v (chooseRight d) := by rw [hwd]
        _ = d.1.castSucc := (hchoose d).2
    exact Fin.ext (congrArg Fin.val hcol)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

theorem incomingRetained_eq_empty_of_no_left
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V)
    (hleft : ∀ a : V, ¬ a < u) :
    incomingRetained C u = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  obtain ⟨a, hau, _⟩ :=
    (mem_incomingRetained_iff C u c).1 hc
  exact hleft a hau

theorem outgoingRetained_eq_empty_of_no_right
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V)
    (hright : ∀ w : V, ¬ v < w) :
    outgoingRetained C v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  obtain ⟨w, hvw, _⟩ :=
    (mem_outgoingRetained_iff C v c).1 hc
  exact hright w hvw

/-- Unsafe residual edge from the global left boundary forces zero exponent at
the upper endpoint. -/
theorem exponent_upper_eq_zero_of_unsafe_residual_from_no_left
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hleft : ∀ a : V, ¬ a < u) :
    exponent v = 0 := by
  have hinc :
      incomingRetained C u = ∅ :=
    incomingRetained_eq_empty_of_no_left C u hleft
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hout :
      outgoingRetained C v =
        (Finset.univ : Finset (Fin n)) := by
    rw [hinc] at hunion
    simpa using hunion
  have hretAll :
      retainedActive C v =
        (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_forall
    intro c
    apply outgoingRetained_subset_retainedActive C v
    rw [hout]
    simp
  have hretCard :
      (retainedActive C v).card = n := by
    rw [hretAll]
    simp
  have hresActive :=
    residualCoord_mem_active_of_isResidual C huv hres
  have hdrop :=
    retainedActive_card_add_one_le_active_of_residual_mem
      C v hresActive.2
  rw [hretCard] at hdrop
  have hvN := hexp v
  have hact := honeLoss v
  omega

/-- Symmetric right-boundary form. -/
theorem exponent_lower_eq_zero_of_unsafe_residual_to_no_right
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hright : ∀ w : V, ¬ v < w) :
    exponent u = 0 := by
  have hout :
      outgoingRetained C v = ∅ :=
    outgoingRetained_eq_empty_of_no_right C v hright
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hinc :
      incomingRetained C u =
        (Finset.univ : Finset (Fin n)) := by
    rw [hout] at hunion
    simpa using hunion
  have hretAll :
      retainedActive C u =
        (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_forall
    intro c
    apply incomingRetained_subset_retainedActive C u
    rw [hinc]
    simp
  have hretCard :
      (retainedActive C u).card = n := by
    rw [hretAll]
    simp
  have hresActive :=
    residualCoord_mem_active_of_isResidual C huv hres
  have hdrop :=
    retainedActive_card_add_one_le_active_of_residual_mem
      C u hresActive.1
  rw [hretCard] at hdrop
  have huN := hexp u
  have hact := honeLoss u
  omega

#print axioms residualThroughColours_card_le_left
#print axioms residualThroughColours_card_le_right
#print axioms exponent_upper_eq_zero_of_unsafe_residual_from_no_left
#print axioms exponent_lower_eq_zero_of_unsafe_residual_to_no_right

end OrderedEdgeColoring
end JSP000404Research
