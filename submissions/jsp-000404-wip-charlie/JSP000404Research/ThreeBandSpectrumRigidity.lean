import JSP000404Research.SaturatedBandJumpMismatch
import JSP000404Research.CyclicBandGapDomination
import Mathlib.Tactic

/-!
# Three-band spectrum rigidity

Two pure list lemmas used by the exact-two Q/T/T/T terminal.

1. Under pointwise quotient <= band-jump domination and equality of
   listExponent, a quotient spectrum {0,1,N} transfers to the band-jump
   spectrum {0,1,N}.

2. A sorted three-band profile contained in bands 0,...,n-1 whose cyclic
   band jumps all lie in {0,1,n-1} must occupy three consecutive bands.
   Indeed the wrap jump is at least two, hence equals n-1, forcing total
   ordinary span two.
-/

namespace JSP000404Research

theorem bandJump_spectrum_of_quotient_spectrum
    {qs bs : List ℕ} {N : ℕ}
    (hN : 2 ≤ N)
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hexp : listExponent qs = listExponent bs)
    (hspec : ∀ q ∈ qs, q = 0 ∨ q = 1 ∨ q = N) :
    ∀ b ∈ bs, b = 0 ∨ b = 1 ∨ b = N := by
  induction hle generalizing hexp with
  | nil =>
      simp
  | @cons q b qs bs hqb htail ih =>
      have hheadExp : excess q = excess b := by
        have hrel :=
          forall₂_excess_eq_of_forall₂_le_of_listExponent_eq
            (List.Forall₂.cons hqb htail) hexp
        exact (List.forall₂_cons.mp hrel).1
      have htailExp :
          listExponent qs = listExponent bs := by
        simp only [listExponent, List.map_cons, List.sum_cons] at hexp
        have htailLe :=
          listExponent_le_of_forall₂_le htail
        have hheadLe := excess_mono_nat hqb
        omega
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hqSpec := hspec q (by simp)
        rcases hqSpec with rfl | rfl | hqN
        · unfold excess at hheadExp
          omega
        · unfold excess at hheadExp
          omega
        · subst q
          unfold excess at hheadExp
          omega
      · exact ih htailExp
          (fun q hq => hspec q (by simp [hq]))
          x hx

theorem mem_between_head_last_of_pairwise_nat
    (a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    ∀ x ∈ a :: xs,
      a ≤ x ∧ x ≤ xs.getLastD a := by
  intro x hx
  have hax : a ≤ x := by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_rfl
    · exact (List.pairwise_cons.mp hsorted).1 x hx
  have hxlast : x ≤ xs.getLastD a := by
    induction xs generalizing a x with
    | nil =>
        simp at hx ⊢
        exact hx.le
    | cons b bs ih =>
        have hp := List.pairwise_cons.mp hsorted
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact
            (by
              have hablast :
                  a ≤ (b :: bs).getLastD a :=
                hp.1 _ (List.getLastD_mem_cons b bs)
              simpa using hablast)
        · have htail :
              (b :: bs).Pairwise (· ≤ ·) := hp.2
          have hxTail : x ∈ b :: bs := hx
          have h :=
            ih b x htail hxTail
          simpa [List.getLastD_cons] using h.2
  exact ⟨hax,hxlast⟩

theorem three_occupied_bands_consecutive_of_cyclic_spectrum
    {n a : ℕ} {xs : List ℕ}
    (hn3 : 3 ≤ n)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hcard : (a :: xs).toFinset.card = 3)
    (hbelowTop : ∀ x ∈ a :: xs, x ≤ n - 1)
    (hspec :
      ∀ b ∈ cyclicBandJumps n (a :: xs),
        b = 0 ∨ b = 1 ∨ b = n - 1) :
    ∃ m : ℕ,
      (a :: xs).toFinset = {m, m + 1, m + 2} := by
  classical
  let last := xs.getLastD a
  have hlastMem : last ∈ a :: xs :=
    List.getLastD_mem_cons a xs
  have hlastTop : last ≤ n - 1 :=
    hbelowTop last hlastMem
  have hwrapPos :
      1 ≤ (n + 1 - last) + a :=
    bandWrapJump_pos (n := n) (a := a)
      (by omega : last ≤ n)
  have hwrapMem :
      (n + 1 - last) + a ∈
        cyclicBandJumps n (a :: xs) := by
    unfold cyclicBandJumps
    exact List.mem_append_right _
      (by simp)
  have hwrapSpec := hspec _ hwrapMem
  have hwrapNeZero :
      (n + 1 - last) + a ≠ 0 := by omega
  have hwrapNeOne :
      (n + 1 - last) + a ≠ 1 := by
    have : 2 ≤ n + 1 - last := by omega
    omega
  have hwrapEq :
      (n + 1 - last) + a = n - 1 := by
    rcases hwrapSpec with h0 | h1 | hN
    · exact False.elim (hwrapNeZero h0)
    · exact False.elim (hwrapNeOne h1)
    · exact hN

  have halast :
      a ≤ last :=
    (mem_between_head_last_of_pairwise_nat
      a xs hsorted last hlastMem).1
  have hlastEq : last = a + 2 := by
    omega

  let S := (a :: xs).toFinset
  have haS : a ∈ S := by
    dsimp [S]
    simp
  have hlastS : a + 2 ∈ S := by
    dsimp [S]
    rw [← hlastEq]
    simpa using hlastMem

  have hmiddleS : a + 1 ∈ S := by
    by_contra hnot
    have hsub :
        S ⊆ ({a, a + 2} : Finset ℕ) := by
      intro x hx
      have hxList : x ∈ a :: xs := by
        simpa [S] using hx
      have hbounds :=
        mem_between_head_last_of_pairwise_nat
          a xs hsorted x hxList
      rw [hlastEq] at hbounds
      have hxCases :
          x = a ∨ x = a + 1 ∨ x = a + 2 := by
        omega
      rcases hxCases with rfl | hmid | htop
      · simp
      · exfalso
        apply hnot
        simpa [S, hmid]
      · subst x
        simp
    have hle := Finset.card_le_card hsub
    have hpairCard :
        ({a, a + 2} : Finset ℕ).card = 2 := by
      simp
    change S.card = 3 at hcard
    rw [hcard, hpairCard] at hle
    omega

  refine ⟨a,?_⟩
  apply Finset.Subset.antisymm
  · intro x hx
    have hxList : x ∈ a :: xs := by
      simpa [S] using hx
    have hbounds :=
      mem_between_head_last_of_pairwise_nat
        a xs hsorted x hxList
    rw [hlastEq] at hbounds
    have hxCases :
        x = a ∨ x = a + 1 ∨ x = a + 2 := by
      omega
    rcases hxCases with rfl | rfl | rfl <;> simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haS
    · exact hmiddleS
    · exact hlastS

#print axioms bandJump_spectrum_of_quotient_spectrum
#print axioms mem_between_head_last_of_pairwise_nat
#print axioms three_occupied_bands_consecutive_of_cyclic_spectrum

end JSP000404Research
