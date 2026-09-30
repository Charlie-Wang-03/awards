import JSP000404Research.ResidualLossFibreGlobal
import Mathlib.Tactic

/-!
# Edge-colour classification inside a translated-loss fibre

Fix a Boolean word y and chosen active flip coordinates.

For two fibre vertices v<w, the connecting retained edge colour is one of the
two owner coordinates.  Fibre monotonicity sharpens this:

* if both owner bits y(choice v), y(choice w) are true, the edge colour must be
  choice v, the lower owner's coordinate;
* if both owner bits are false, the edge colour must be choice w, the upper
  owner's coordinate.

Only an edge crossing the unique true-to-false cut may choose either endpoint
coordinate.

Thus each fixed translated-loss fibre is the concatenation of a lower-owner
coloured clique and an upper-owner coloured clique, with one mixed cut between
them.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translated_loss_fibre_true_true_edge_colour_lower
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x,
        x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {v w : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hvw : v < w)
    (hvTrue : word (choice v) = true)
    (hwTrue : word (choice w) = true) :
    ∃ hret : (C.color v w).val < n,
      retainedColor C v w hret = choice v := by
  have hvData :=
    (mem_translatedLossFibre
      C exponent choice word v).1 hv
  have hwData :=
    (mem_translatedLossFibre
      C exponent choice word w).1 hw
  have hedge :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hvData.1 hwData.1 (ne_of_lt hvw)
      hvData.2 hwData.2
  rcases hedge with hforward | hbackward
  · obtain ⟨hvw',hret,hcolour⟩ := hforward
    rcases hcolour with hlower | hupper
    · exact ⟨hret,hlower⟩
    · have hfalse :=
        translated_loss_conflict_upper_colour_forces_word_false
          C exponent hexp honeLoss hvw
          hvData.1 hwData.1
          (hactive v hv) (hactive w hw)
          hvData.2 hwData.2 hret hupper
      rw [hwTrue] at hfalse
      contradiction
  · obtain ⟨hwv,_hret,_hcolour⟩ := hbackward
    exact False.elim ((not_lt_of_ge hvw.le) hwv)

theorem translated_loss_fibre_false_false_edge_colour_upper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x,
        x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {v w : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hvw : v < w)
    (hvFalse : word (choice v) = false)
    (hwFalse : word (choice w) = false) :
    ∃ hret : (C.color v w).val < n,
      retainedColor C v w hret = choice w := by
  have hvData :=
    (mem_translatedLossFibre
      C exponent choice word v).1 hv
  have hwData :=
    (mem_translatedLossFibre
      C exponent choice word w).1 hw
  have hedge :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hvData.1 hwData.1 (ne_of_lt hvw)
      hvData.2 hwData.2
  rcases hedge with hforward | hbackward
  · obtain ⟨hvw',hret,hcolour⟩ := hforward
    rcases hcolour with hlower | hupper
    · have htrue :=
        translated_loss_conflict_lower_colour_forces_word_true
          C exponent hexp honeLoss hvw
          hvData.1 hwData.1
          (hactive v hv) (hactive w hw)
          hvData.2 hwData.2 hret hlower
      rw [hvFalse] at htrue
      contradiction
    · exact ⟨hret,hupper⟩
  · obtain ⟨hwv,_hret,_hcolour⟩ := hbackward
    exact False.elim ((not_lt_of_ge hvw.le) hwv)

#print axioms translated_loss_fibre_true_true_edge_colour_lower
#print axioms translated_loss_fibre_false_false_edge_colour_upper

end OrderedEdgeColoring
end JSP000404Research
