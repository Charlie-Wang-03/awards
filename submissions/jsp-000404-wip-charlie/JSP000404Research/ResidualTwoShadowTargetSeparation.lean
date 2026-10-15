import Mathlib.Tactic

/-!
# Shared distance-two SOFT shadows force close distinct NET targets

This is a pure Boolean-cube gate, independent of any allocation claim.
If one candidate SOFT shadow s lies at Hamming distance two from two
diagonal targets d and e, then d and e differ in at most four bits.
Consequently a target family separated by five or more coordinates has
no cross-target distance-two shadow reuse.

A planar AngleCap hypothesis is NOT known to imply this separation.
In particular this module makes no true-hole or unreserved-surplus
payment claim, and the global six-source sorry remains open.
-/

namespace JSP000404Research

/-- The two radius-two Hamming neighbourhoods around the same word
can meet only if their target centres differ on at most four bits. -/
theorem two_shared_two_flip_shadows_target_hamming_le_four
    {n : ℕ}
    (s d e : Fin n → Bool)
    (hsd :
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
    (hse :
      (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2) :
    (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≤ 4 := by
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ d i)
  let B : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ e i)
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => d i ≠ e i)
  have hA : A.card = 2 := hsd
  have hB : B.card = 2 := hse
  have hsubset : T ⊆ A ∪ B := by
    intro i hi
    have hde : d i ≠ e i := (Finset.mem_filter.mp hi).2
    by_cases hdiff : s i ≠ d i
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩)
    · have heq : s i = d i := of_not_not hdiff
      have hdiff' : s i ≠ e i := by
        intro h
        exact hde (heq.symm.trans h)
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff'⟩)
  have hcard : T.card ≤ (A ∪ B).card :=
    Finset.card_le_card hsubset
  have hunion : (A ∪ B).card ≤ A.card + B.card :=
    Finset.card_union_le A B
  change T.card ≤ 4
  omega

/-- Targets more than four bits apart cannot share a Hamming-two
shadow. This is a strict nonreuse criterion, not a derived planar fact. -/
theorem distant_targets_have_no_shared_two_flip_shadow
    {n : ℕ} (s d e : Fin n → Bool)
    (hfar :
      4 < (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card) :
    ¬ ((Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2 ∧
       (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2) := by
  rintro ⟨hsd, hse⟩
  have hle := two_shared_two_flip_shadows_target_hamming_le_four
    s d e hsd hse
  omega

#print axioms two_shared_two_flip_shadows_target_hamming_le_four
#print axioms distant_targets_have_no_shared_two_flip_shadow

end JSP000404Research
