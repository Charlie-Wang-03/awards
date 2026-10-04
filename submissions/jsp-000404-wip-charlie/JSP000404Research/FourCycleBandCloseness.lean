import Mathlib.Tactic

/-!
# Four-cycle one-step closeness forces a consecutive three-label palette

Suppose four natural labels x00,x01,x10,x11 sit on the edges of a K2,2 cycle
and every pair sharing a vertex differs by at most one.  If their value set has
cardinality three, then those three values are exactly {m,m+1,m+2}.

This is the finite arithmetic core needed after the ordered-adjacent
four-support-two reduction.
-/

namespace JSP000404Research

def NatOneStepClose (x y : ℕ) : Prop :=
  x ≤ y + 1 ∧ y ≤ x + 1

theorem four_cycle_oneStep_card_three_consecutive
    (x00 x01 x10 x11 : ℕ)
    (h0 : NatOneStepClose x00 x01)
    (h1 : NatOneStepClose x00 x10)
    (h2 : NatOneStepClose x11 x01)
    (h3 : NatOneStepClose x11 x10)
    (hcard : ({x00,x01,x10,x11} : Finset ℕ).card = 3) :
    ∃ m : ℕ,
      ({x00,x01,x10,x11} : Finset ℕ) = {m,m+1,m+2} := by
  let S : Finset ℕ := {x00,x01,x10,x11}
  let m := S.min' (by
    dsimp [S]
    simp)
  have hmMem : m ∈ S := Finset.min'_mem S _
  have hmLe : ∀ x ∈ S, m ≤ x := by
    intro x hx
    exact Finset.min'_le _ _ hx

  have hdiam2 :
      ∀ x ∈ S, x ≤ m + 2 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hmMem hx
    rcases hmMem with hm00 | hm01 | hm10 | hm11 <;>
      rcases hx with hx00 | hx01 | hx10 | hx11 <;>
      subst_vars <;>
      unfold NatOneStepClose at h0 h1 h2 h3 <;>
      omega

  have hsub :
      S ⊆ {m,m+1,m+2} := by
    intro x hx
    have hlo := hmLe x hx
    have hhi := hdiam2 x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

  have htargetCard :
      ({m,m+1,m+2} : Finset ℕ).card = 3 := by
    simp

  have hcardS : S.card = 3 := by
    simpa [S] using hcard
  have heq :
      S = {m,m+1,m+2} :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [hcardS, htargetCard])
  exact ⟨m, by simpa [S] using heq⟩

#print axioms four_cycle_oneStep_card_three_consecutive

end JSP000404Research
