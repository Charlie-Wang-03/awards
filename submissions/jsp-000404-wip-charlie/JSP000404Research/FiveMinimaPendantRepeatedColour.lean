import JSP000404Research.FiveMinimaC4Pendant
import Mathlib.Tactic

/-!
# Finite repetition behind the pendant-C4 branch

This file records only the finite pigeonhole statement needed later.

Among four incident minimum-edges, suppose exactly one uses a distinguished
C4 colour and the total number of colours used is three.  Then two of the
three remaining edges use the same non-C4 colour.

The graph-specific application is deliberately kept separate until all
endpoint-incidence hypotheses are available; this module contains no
placeholder proofs.
-/

namespace JSP000404Research

/-- Four values use exactly three colours.  If one index is the unique
preimage of a distinguished colour, two of the other three indices have the
same colour. -/
theorem fin4_exists_repeated_nonroot_of_image_card_three
    {κ : Type*} [DecidableEq κ]
    (f : Fin 4 → κ)
    (root : κ)
    (r : Fin 4)
    (hroot : ∀ i : Fin 4, f i = root ↔ i = r)
    (hcard : (Finset.univ.image f).card = 3) :
    ∃ i j : Fin 4,
      i ≠ j ∧ i ≠ r ∧ j ≠ r ∧
      f i = f j ∧ f i ≠ root := by
  classical
  fin_cases r
  · by_contra hnone
    push_neg at hnone
    have h01 : f 1 ≠ f 2 := by
      intro h
      exact (hnone 1 2 (by decide) (by decide) (by decide)).1 h
    have h02 : f 1 ≠ f 3 := by
      intro h
      exact (hnone 1 3 (by decide) (by decide) (by decide)).1 h
    have h12 : f 2 ≠ f 3 := by
      intro h
      exact (hnone 2 3 (by decide) (by decide) (by decide)).1 h
    have h0r : f 0 = root := (hroot 0).2 rfl
    have h1r : f 1 ≠ root := by
      intro h
      have := (hroot 1).1 h
      decide at this
    have h2r : f 2 ≠ root := by
      intro h
      have := (hroot 2).1 h
      decide at this
    have h3r : f 3 ≠ root := by
      intro h
      have := (hroot 3).1 h
      decide at this
    have hfour :
        ({f 0,f 1,f 2,f 3} : Finset κ).card = 4 := by
      simp [h0r, h1r, h2r, h3r, h01, h02, h12,
        Ne.symm h01, Ne.symm h02, Ne.symm h12]
    have himage :
        Finset.univ.image f = {f 0,f 1,f 2,f 3} := by
      ext x
      simp
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        <;> exact Finset.mem_image.mpr ⟨by simp, rfl⟩
    rw [himage, hfour] at hcard
    omega
  · by_contra hnone
    push_neg at hnone
    have h02 : f 0 ≠ f 2 := by
      intro h
      exact (hnone 0 2 (by decide) (by decide) (by decide)).1 h
    have h03 : f 0 ≠ f 3 := by
      intro h
      exact (hnone 0 3 (by decide) (by decide) (by decide)).1 h
    have h23 : f 2 ≠ f 3 := by
      intro h
      exact (hnone 2 3 (by decide) (by decide) (by decide)).1 h
    have h1r : f 1 = root := (hroot 1).2 rfl
    have h0r : f 0 ≠ root := by
      intro h
      have := (hroot 0).1 h
      decide at this
    have h2r : f 2 ≠ root := by
      intro h
      have := (hroot 2).1 h
      decide at this
    have h3r : f 3 ≠ root := by
      intro h
      have := (hroot 3).1 h
      decide at this
    have hfour :
        ({f 0,f 1,f 2,f 3} : Finset κ).card = 4 := by
      simp [h1r, h0r, h2r, h3r, h02, h03, h23,
        Ne.symm h02, Ne.symm h03, Ne.symm h23]
    have himage :
        Finset.univ.image f = {f 0,f 1,f 2,f 3} := by
      ext x
      simp
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        <;> exact Finset.mem_image.mpr ⟨by simp, rfl⟩
    rw [himage, hfour] at hcard
    omega
  · by_contra hnone
    push_neg at hnone
    have h01 : f 0 ≠ f 1 := by
      intro h
      exact (hnone 0 1 (by decide) (by decide) (by decide)).1 h
    have h03 : f 0 ≠ f 3 := by
      intro h
      exact (hnone 0 3 (by decide) (by decide) (by decide)).1 h
    have h13 : f 1 ≠ f 3 := by
      intro h
      exact (hnone 1 3 (by decide) (by decide) (by decide)).1 h
    have h2r : f 2 = root := (hroot 2).2 rfl
    have h0r : f 0 ≠ root := by
      intro h
      have := (hroot 0).1 h
      decide at this
    have h1r : f 1 ≠ root := by
      intro h
      have := (hroot 1).1 h
      decide at this
    have h3r : f 3 ≠ root := by
      intro h
      have := (hroot 3).1 h
      decide at this
    have hfour :
        ({f 0,f 1,f 2,f 3} : Finset κ).card = 4 := by
      simp [h2r, h0r, h1r, h3r, h01, h03, h13,
        Ne.symm h01, Ne.symm h03, Ne.symm h13]
    have himage :
        Finset.univ.image f = {f 0,f 1,f 2,f 3} := by
      ext x
      simp
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        <;> exact Finset.mem_image.mpr ⟨by simp, rfl⟩
    rw [himage, hfour] at hcard
    omega
  · by_contra hnone
    push_neg at hnone
    have h01 : f 0 ≠ f 1 := by
      intro h
      exact (hnone 0 1 (by decide) (by decide) (by decide)).1 h
    have h02 : f 0 ≠ f 2 := by
      intro h
      exact (hnone 0 2 (by decide) (by decide) (by decide)).1 h
    have h12 : f 1 ≠ f 2 := by
      intro h
      exact (hnone 1 2 (by decide) (by decide) (by decide)).1 h
    have h3r : f 3 = root := (hroot 3).2 rfl
    have h0r : f 0 ≠ root := by
      intro h
      have := (hroot 0).1 h
      decide at this
    have h1r : f 1 ≠ root := by
      intro h
      have := (hroot 1).1 h
      decide at this
    have h2r : f 2 ≠ root := by
      intro h
      have := (hroot 2).1 h
      decide at this
    have hfour :
        ({f 0,f 1,f 2,f 3} : Finset κ).card = 4 := by
      simp [h3r, h0r, h1r, h2r, h01, h02, h12,
        Ne.symm h01, Ne.symm h02, Ne.symm h12]
    have himage :
        Finset.univ.image f = {f 0,f 1,f 2,f 3} := by
      ext x
      simp
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        <;> exact Finset.mem_image.mpr ⟨by simp, rfl⟩
    rw [himage, hfour] at hcard
    omega

#print axioms fin4_exists_repeated_nonroot_of_image_card_three

end JSP000404Research
