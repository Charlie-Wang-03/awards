import JSP000404Research.ResidualTwoShadowParityGate
import Mathlib.Tactic

/-!
# Exact four-coordinate geometry of a shared Hamming-two SOFT shadow

The previous verified parity gate restricts shared shadows to target
distance 2 or 4. For distance FOUR, the two size-two flip supports
(relative to the same actual SOFT word s) are completely disjoint.
Thus all four target-difference coordinates are exhausted by these
two flips. In particular, a four-bit NET target conflict cannot hide
a shared shadow flip on any coordinate outside its target difference.

This is a pure, sorry-free finite Boolean-cube statement. No independent
TRUE hole, matching payment, or planar AngleCap implication is inferred.
-/

namespace JSP000404Research

/-- At the four-bit endpoint of the parity-sharp obstruction, the
two separate Hamming-two flip supports of the shared word are disjoint. -/
theorem shared_two_shadow_four_bit_flips_disjoint
    {n : ℕ} (s d e : Fin n → Bool)
    (hsd : (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
    (hse : (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2)
    (hde : (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 4) :
    Disjoint
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i))
      (Finset.univ.filter (fun i : Fin n => s i ≠ e i)) := by
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ d i)
  let B : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ e i)
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => d i ≠ e i)
  have hsubset : T ⊆ A ∪ B := by
    intro i hi
    have hdiff : d i ≠ e i := (Finset.mem_filter.mp hi).2
    by_cases hsd' : s i ≠ d i
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsd'⟩)
    · have heq : s i = d i := of_not_not hsd'
      have hse' : s i ≠ e i := by
        intro h
        exact hdiff (heq.symm.trans h)
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hse'⟩)
  have hbound : T.card ≤ (A ∪ B).card :=
    Finset.card_le_card hsubset
  have hsum := Finset.card_union_add_card_inter A B
  have hAc : A.card = 2 := hsd
  have hBc : B.card = 2 := hse
  have hTc : T.card = 4 := hde
  have hzero : (A ∩ B).card = 0 := by omega
  have hempty : A ∩ B = ∅ := Finset.card_eq_zero.mp hzero
  apply Finset.disjoint_left.mpr
  intro i hAi hBi
  have hi : i ∈ A ∩ B := Finset.mem_inter.mpr ⟨hAi, hBi⟩
  rw [hempty] at hi
  simpa using hi

/-- In the four-coordinate obstruction, the shared SOFT shadow may
differ from the first NET target ONLY on coordinates where the TWO
NET targets themselves differ. -/
theorem shared_two_shadow_four_bit_flip_subset_target_difference
    {n : ℕ} (s d e : Fin n → Bool)
    (hsd : (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
    (hse : (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2)
    (hde : (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 4) :
    (Finset.univ.filter (fun i : Fin n => s i ≠ d i)) ⊆
      (Finset.univ.filter (fun i : Fin n => d i ≠ e i)) := by
  classical
  have hdis := shared_two_shadow_four_bit_flips_disjoint
    s d e hsd hse hde
  intro i hi
  by_contra hnot
  have heq : d i = e i := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  have hsdi : s i ≠ d i := (Finset.mem_filter.mp hi).2
  have hsei : s i ≠ e i := by
    intro h
    exact hsdi (h.trans heq.symm)
  have hb : i ∈ Finset.univ.filter (fun i : Fin n => s i ≠ e i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsei⟩
  exact (Finset.disjoint_left.mp hdis) hi hb

#print axioms shared_two_shadow_four_bit_flips_disjoint
#print axioms shared_two_shadow_four_bit_flip_subset_target_difference

end JSP000404Research
