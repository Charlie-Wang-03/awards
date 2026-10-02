import JSP000404Research.ResidualWholeCubePartnerDistinct
import JSP000404Research.ResidualSecondLayerTripleCanonical
import JSP000404Research.ResidualQTTTCommonColourBitCut
import Mathlib.Tactic

/-!
# Order side of a whole-cube partner from the owner bit

For a projected-loss WholeCubeQTPair (s,v,c), the c-translated slice at v is
exactly Q_s.  Hence any common word gives a Q/T edge of colour c.

At that edge:
* v < s iff c is outgoing at v iff retainedBit(v,c)=false;
* s < v iff c is incoming at v iff retainedBit(v,c)=true.

Thus the retained code of v determines on which side every whole-cube partner
lies.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeQTPair_lt_iff_owner_bit_false
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s v : V} {c : Fin n}
    (hsv : s ≠ v)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    v < s ↔ retainedBit C v c = false := by
  have hnonempty :
      (retainedCompletionWords C s).Nonempty := by
    rw [retainedCompletionWords_nonempty_iff]
  obtain ⟨word,hsQ⟩ := hnonempty
  have hvT :
      word ∈ translatedCompletionWords C v c := by
    rcases hwhole with ⟨_,hEq⟩
    rw [hEq]
    exact hsQ
  have howner :=
    translated_word_owner_bit_ne_retainedBit
      C hcV hvT
  have hsem :=
    QTT_owner_edge_semantics
      C exponent hexp honeLoss
      hsv hvLoss hcV hsQ hvT
  constructor
  · intro hvs
    rcases hsem with hleft | hright
    · have hw : word c = true := hleft.2.2.2
      rw [hw] at howner
      cases hb : retainedBit C v c <;> simp_all
    · exact False.elim
        (lt_asymm hvs hright.1)
  · intro hfalse
    rcases hsem with hleft | hright
    · exact hleft.1
    · have hw : word c = false := hright.2.2.2
      rw [hw,hfalse] at howner
      simp at howner

theorem wholeCubeQTPair_gt_iff_owner_bit_true
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s v : V} {c : Fin n}
    (hsv : s ≠ v)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    s < v ↔ retainedBit C v c = true := by
  have hlt :=
    wholeCubeQTPair_lt_iff_owner_bit_false
      C exponent hexp honeLoss hsv hvLoss hcV hwhole
  constructor
  · intro hsvlt
    cases hb : retainedBit C v c
    · have hvs : v < s := hlt.mpr hb
      exact False.elim (lt_asymm hsvlt hvs)
    · rfl
  · intro htrue
    rcases lt_or_gt_of_ne hsv.symm with hvs | hsvlt
    · have hfalse : retainedBit C v c = false :=
        hlt.mp hvs
      rw [htrue] at hfalse
      simp at hfalse
    · exact hsvlt

theorem threeWholeCubePartners_side_profile
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s₁ s₂ s₃ : V} {c₁ c₂ c₃ : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hc1V : c₁ ∈ retainedActive C v)
    (hc2V : c₂ ∈ retainedActive C v)
    (hc3V : c₃ ∈ retainedActive C v)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    (v < s₁ ↔ retainedBit C v c₁ = false) ∧
    (v < s₂ ↔ retainedBit C v c₂ = false) ∧
    (v < s₃ ↔ retainedBit C v c₃ = false) := by
  have hs1v : s₁ ≠ v :=
    wholeCubeQTPair_ne_of_active C hc1V h₁
  have hs2v : s₂ ≠ v :=
    wholeCubeQTPair_ne_of_active C hc2V h₂
  have hs3v : s₃ ≠ v :=
    wholeCubeQTPair_ne_of_active C hc3V h₃
  exact ⟨
    wholeCubeQTPair_lt_iff_owner_bit_false
      C exponent hexp honeLoss hs1v hvLoss hc1V h₁,
    wholeCubeQTPair_lt_iff_owner_bit_false
      C exponent hexp honeLoss hs2v hvLoss hc2V h₂,
    wholeCubeQTPair_lt_iff_owner_bit_false
      C exponent hexp honeLoss hs3v hvLoss hc3V h₃
  ⟩

#print axioms wholeCubeQTPair_lt_iff_owner_bit_false
#print axioms wholeCubeQTPair_gt_iff_owner_bit_true
#print axioms threeWholeCubePartners_side_profile

end OrderedEdgeColoring
end JSP000404Research
