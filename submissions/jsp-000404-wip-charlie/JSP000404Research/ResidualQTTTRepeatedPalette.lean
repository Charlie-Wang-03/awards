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


/-- Symmetric common-colour version: if cy is active at all four Q/T/T/T
vertices, then one of x,z has the same retained palette as the completion
owner s. -/
theorem QTTT_common_cy_forces_x_or_z_palette_eq_s
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y z : V}
    (hxz : x ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hxSecond : exponent x = n - 2)
    (hzSecond : exponent z = n - 2)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hcyX : cy ∈ retainedActive C x)
    (hcyZ : cy ∈ retainedActive C z)
    (hcxX : cx ∈ retainedActive C x)
    (hczZ : cz ∈ retainedActive C z)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    retainedActive C x = retainedActive C s ∨
    retainedActive C z = retainedActive C s := by
  -- Relabel common coordinate cy as the first coordinate of the generic lemma.
  have h :=
    QTTT_common_cx_forces_y_or_z_palette_eq_s
      C exponent hexp honeLoss
      hxz hsLoss hxLoss hzLoss
      hsSecond hxSecond hzSecond
      (word := word)
      (cx := cy) (cy := cx) (cz := cz)
      hcxy.symm hcyz hcxz
      (by
        simpa [Finset.pair_comm, Finset.insert_comm, Finset.insert_left_comm]
          using hsActive)
      hcyX hcyZ hcxX hczZ hxT hzT
  exact h

/-- Symmetric common-colour version for cz. -/
theorem QTTT_common_cz_forces_x_or_y_palette_eq_s
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y z : V}
    (hxy : x ≠ y)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hxSecond : exponent x = n - 2)
    (hySecond : exponent y = n - 2)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hczX : cz ∈ retainedActive C x)
    (hczY : cz ∈ retainedActive C y)
    (hcxX : cx ∈ retainedActive C x)
    (hcyY : cy ∈ retainedActive C y)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    retainedActive C x = retainedActive C s ∨
    retainedActive C y = retainedActive C s := by
  have h :=
    QTTT_common_cx_forces_y_or_z_palette_eq_s
      C exponent hexp honeLoss
      hxy hsLoss hxLoss hyLoss
      hsSecond hxSecond hySecond
      (word := word)
      (cx := cz) (cy := cx) (cz := cy)
      hcxz.symm hcyz.symm hcxy
      (by
        simpa [Finset.pair_comm, Finset.insert_comm, Finset.insert_left_comm]
          using hsActive)
      hczX hczY hcxX hcyY hxT hyT
  exact h

/-- If a retained colour is common to all four saturated Q/T/T/T vertices,
then some translated owner has exactly the same three-coordinate retained
palette as the completion owner. -/
theorem QTTT_common_colour_forces_some_translated_palette_eq_s
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hxSecond : exponent x = n - 2)
    (hySecond : exponent y = n - 2)
    (hzSecond : exponent z = n - 2)
    {word : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hcommonS : d ∈ retainedActive C s)
    (hcommonX : d ∈ retainedActive C x)
    (hcommonY : d ∈ retainedActive C y)
    (hcommonZ : d ∈ retainedActive C z)
    (hcxX : cx ∈ retainedActive C x)
    (hcyY : cy ∈ retainedActive C y)
    (hczZ : cz ∈ retainedActive C z)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    (retainedActive C x = retainedActive C s) ∨
    (retainedActive C y = retainedActive C s) ∨
    (retainedActive C z = retainedActive C s) := by
  have hd :
      d = cx ∨ d = cy ∨ d = cz := by
    rw [hsActive] at hcommonS
    simpa using hcommonS
  rcases hd with rfl | rfl | rfl
  · rcases
      QTTT_common_cx_forces_y_or_z_palette_eq_s
        C exponent hexp honeLoss
        hyz hsLoss hyLoss hzLoss
        hsSecond hySecond hzSecond
        hcxy hcxz hcyz hsActive
        hcommonY hcommonZ hcyY hczZ hyT hzT
      with hyEq | hzEq
    · exact Or.inr (Or.inl hyEq)
    · exact Or.inr (Or.inr hzEq)
  · rcases
      QTTT_common_cy_forces_x_or_z_palette_eq_s
        C exponent hexp honeLoss
        hxz hsLoss hxLoss hzLoss
        hsSecond hxSecond hzSecond
        hcxy hcxz hcyz hsActive
        hcommonX hcommonZ hcxX hczZ hxT hzT
      with hxEq | hzEq
    · exact Or.inl hxEq
    · exact Or.inr (Or.inr hzEq)
  · rcases
      QTTT_common_cz_forces_x_or_y_palette_eq_s
        C exponent hexp honeLoss
        hxy hsLoss hxLoss hyLoss
        hsSecond hxSecond hySecond
        hcxy hcxz hcyz hsActive
        hcommonX hcommonY hcxX hcyY hxT hyT
      with hxEq | hyEq
    · exact Or.inl hxEq
    · exact Or.inr (Or.inl hyEq)

#print axioms QTTT_common_cy_forces_x_or_z_palette_eq_s
#print axioms QTTT_common_cz_forces_x_or_y_palette_eq_s
#print axioms QTTT_common_colour_forces_some_translated_palette_eq_s

end OrderedEdgeColoring
end JSP000404Research
