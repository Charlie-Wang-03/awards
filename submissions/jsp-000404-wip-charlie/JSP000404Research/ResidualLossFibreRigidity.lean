import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Monotone bit structure inside one translated-loss fibre

Fix a Boolean word y.  Suppose two distinct projected-loss vertices v,w carry
y in translated blocks obtained by flipping active retained coordinates c,d.

The translated-loss conflict theorem says the retained edge colour between
v and w is c or d.  If v<w, canonical endpoint bits sharpen this:

* if the edge colour is c (the lower vertex's flip coordinate), then y(c)=true;
* if the edge colour is d (the upper vertex's flip coordinate), then y(d)=false.

Consequently, for v<w it is impossible that y(c)=false and y(d)=true.

Thus in any fixed translated-loss fibre, after ordering vertices increasingly,
the Boolean values of y at their owner flip coordinates are monotone:
all true-labelled carriers precede all false-labelled carriers.  The fibre has
at most one true-to-false transition.

This is substantially stronger than a mere multiplicity bound and is the
starting point for a global fibre classification.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translated_loss_conflict_lower_colour_forces_word_true
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V} (hvw : v < w)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C w)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v c)
    (hwT : word ∈ translatedCompletionWords C w d)
    (hret : (C.color v w).val < n)
    (hcolour : retainedColor C v w hret = c) :
    word c = true := by
  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  have hvComp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word c)).1 hvOrig
  have hvAt := hvComp c hc
  have hbitLower :=
    retainedBit_false_of_outgoingRetained C
      (by
        apply (mem_outgoingRetained_iff C v c).2
        refine ⟨w,hvw,?_⟩
        apply Fin.ext
        simpa [retainedColor, hcolour])
  rw [flipBoolWordAt_at, hbitLower] at hvAt
  cases h : word c <;> simp [h] at hvAt ⊢

theorem translated_loss_conflict_upper_colour_forces_word_false
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V} (hvw : v < w)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C w)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v c)
    (hwT : word ∈ translatedCompletionWords C w d)
    (hret : (C.color v w).val < n)
    (hcolour : retainedColor C v w hret = d) :
    word d = false := by
  have hwOrig :
      flipBoolWordAt word d ∈ retainedCompletionWords C w :=
    (mem_translatedCompletionWords C w d word).1 hwT
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt word d)).1 hwOrig
  have hwAt := hwComp d hd
  have hbitUpper :
      retainedBit C w d = true := by
    apply (mem_incomingRetained_iff_retainedBit_true C w d).1
    apply (mem_incomingRetained_iff C w d).2
    refine ⟨v,hvw,?_⟩
    apply Fin.ext
    simpa [retainedColor, hcolour]
  rw [flipBoolWordAt_at, hbitUpper] at hwAt
  cases h : word d <;> simp [h] at hwAt ⊢

theorem translated_loss_fibre_no_false_before_true
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V} (hvw : v < w)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C w)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v c)
    (hwT : word ∈ translatedCompletionWords C w d) :
    word c = true ∨ word d = false := by
  have hedge :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hvLoss hwLoss (ne_of_lt hvw) hvT hwT
  rcases hedge with hforward | hbackward
  · obtain ⟨hvw',hret,hcolour⟩ := hforward
    rcases hcolour with hcEdge | hdEdge
    · exact Or.inl
        (translated_loss_conflict_lower_colour_forces_word_true
          C exponent hexp honeLoss hvw
          hvLoss hwLoss hc hd hvT hwT hret hcEdge)
    · exact Or.inr
        (translated_loss_conflict_upper_colour_forces_word_false
          C exponent hexp honeLoss hvw
          hvLoss hwLoss hc hd hvT hwT hret hdEdge)
  · obtain ⟨hwv,_hret,_hcolour⟩ := hbackward
    exact False.elim ((not_lt_of_ge hvw.le) hwv)

theorem translated_loss_fibre_monotone_bits
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {word : Fin n → Bool}
    {v w : V} {c d : Fin n}
    (hvw : v < w)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C w)
    (hvT : word ∈ translatedCompletionWords C v c)
    (hwT : word ∈ translatedCompletionWords C w d)
    (hvFalse : word c = false) :
    word d = false := by
  rcases translated_loss_fibre_no_false_before_true
      C exponent hexp honeLoss hvw
      hvLoss hwLoss hc hd hvT hwT
    with htrue | hfalse
  · rw [hvFalse] at htrue
    contradiction
  · exact hfalse

#print axioms translated_loss_conflict_lower_colour_forces_word_true
#print axioms translated_loss_conflict_upper_colour_forces_word_false
#print axioms translated_loss_fibre_no_false_before_true
#print axioms translated_loss_fibre_monotone_bits

end OrderedEdgeColoring
end JSP000404Research
