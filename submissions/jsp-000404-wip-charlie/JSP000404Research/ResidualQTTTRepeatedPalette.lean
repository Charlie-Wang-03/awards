import JSP000404Research.ResidualQTTTCommonColourBitCut
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Q/T/T/T common colour forces a repeated three-colour palette

In a saturated Q/T/T/T state the completion owner has retained palette
{cx,cy,cz}.  Suppose one common retained colour is cx and is active at all
four vertices.

Then y already has cx and its own coordinate cy; z already has cx and its own
coordinate cz.  The translated-loss overlap on y,z forces their connecting
edge colour to be either cy or cz.  Hence either cz is active at y or cy is
active at z.  Since y and z are second-layer loss vertices with retained
palette cardinality three, the corresponding palette must equal
{cx,cy,cz}=retainedActive(s).

The analogous statements hold when the common colour is cy or cz.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem three_distinct_members_card_three_eq
    {α : Type*} [DecidableEq α]
    {S : Finset α}
    {a b c : α}
    (hcard : S.card = 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    S = {a,b,c} := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    by_contra hnot
    have hsub :
        ({a,b,c,x} : Finset α) ⊆ S := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hx
    have hfour :
        ({a,b,c,x} : Finset α).card = 4 := by
      simp [hab,hac,hbc,hnot]
    have hle := Finset.card_le_card hsub
    rw [hfour,hcard] at hle
    omega
  · simp [hab,hac,hbc,hcard]

theorem QTTT_common_cx_forces_y_or_z_palette_eq_s
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y z : V}
    (hyz : y ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hySecond : exponent y = n - 2)
    (hzSecond : exponent z = n - 2)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hcxY : cx ∈ retainedActive C y)
    (hcxZ : cx ∈ retainedActive C z)
    (hcyY : cy ∈ retainedActive C y)
    (hczZ : cz ∈ retainedActive C z)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    retainedActive C y = retainedActive C s ∨
    retainedActive C z = retainedActive C s := by
  have hedge :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hyLoss hzLoss hyz hyT hzT
  have hyCard :=
    secondLayerLoss_retainedActive_card_eq_three
      C exponent hyLoss hySecond
  have hzCard :=
    secondLayerLoss_retainedActive_card_eq_three
      C exponent hzLoss hzSecond
  rcases hedge with hforward | hbackward
  · obtain ⟨hyzlt,hret,hcol⟩ := hforward
    rcases hcol with hcyEdge | hczEdge
    · right
      have hcyZ :
          cy ∈ retainedActive C z := by
        have hm :=
          retainedColor_mem_retainedActive_right
            C hyzlt hret
        simpa [hcyEdge] using hm
      have hzEq :
          retainedActive C z = {cx,cy,cz} :=
        three_distinct_members_card_three_eq
          hzCard hcxy hcxz hcyz
          hcxZ hcyZ hczZ
      simpa [hsActive] using hzEq
    · left
      have hczY :
          cz ∈ retainedActive C y := by
        have hm :=
          retainedColor_mem_retainedActive_left
            C hyzlt hret
        simpa [hczEdge] using hm
      have hyEq :
          retainedActive C y = {cx,cy,cz} :=
        three_distinct_members_card_three_eq
          hyCard hcxy hcxz hcyz
          hcxY hcyY hczY
      simpa [hsActive] using hyEq
  · obtain ⟨hzylt,hret,hcol⟩ := hbackward
    rcases hcol with hczEdge | hcyEdge
    · left
      have hczY :
          cz ∈ retainedActive C y := by
        have hm :=
          retainedColor_mem_retainedActive_right
            C hzylt hret
        simpa [hczEdge] using hm
      have hyEq :
          retainedActive C y = {cx,cy,cz} :=
        three_distinct_members_card_three_eq
          hyCard hcxy hcxz hcyz
          hcxY hcyY hczY
      simpa [hsActive] using hyEq
    · right
      have hcyZ :
          cy ∈ retainedActive C z := by
        have hm :=
          retainedColor_mem_retainedActive_left
            C hzylt hret
        simpa [hcyEdge] using hm
      have hzEq :
          retainedActive C z = {cx,cy,cz} :=
        three_distinct_members_card_three_eq
          hzCard hcxy hcxz hcyz
          hcxZ hcyZ hczZ
      simpa [hsActive] using hzEq

#print axioms three_distinct_members_card_three_eq
#print axioms QTTT_common_cx_forces_y_or_z_palette_eq_s

end OrderedEdgeColoring
end JSP000404Research
