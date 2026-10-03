import Mathlib.Tactic

/-!
# Abstract four-choice derangement core

This file isolates the finite combinatorial kernel behind the saturated
four-support-two terminal.

There are four vertices A,B,C,D.  Each vertex chooses one of the three
triangles containing it:

* A chooses ABC, ABD, or ACD;
* B chooses ABC, ABD, or BCD;
* C chooses ABC, ACD, or BCD;
* D chooses ABD, ACD, or BCD.

Assume no triangle is chosen by two of its incident vertices.  Then the four
choices use the four triangles exactly once.  Equivalently the incidence
assignment is a derangement.  There are exactly nine possibilities.

No geometry and no JSP-000404 infrastructure is imported here.
-/

namespace JSP000404Research

def FourChoiceDerangement9
    (Aabc Aabd Aacd
     Babc Babd Bbcd
     Cabc Cacd Cbcd
     Dabd Dacd Dbcd : Prop) : Prop :=
  (Aabc ∧ Babd ∧ Cacd ∧ Dbcd) ∨
  (Aabc ∧ Babd ∧ Cbcd ∧ Dacd) ∨
  (Aabc ∧ Bbcd ∧ Cacd ∧ Dabd) ∨
  (Aabd ∧ Babc ∧ Cacd ∧ Dbcd) ∨
  (Aabd ∧ Babc ∧ Cbcd ∧ Dacd) ∨
  (Aabd ∧ Bbcd ∧ Cabc ∧ Dacd) ∨
  (Aacd ∧ Babc ∧ Cbcd ∧ Dabd) ∨
  (Aacd ∧ Babd ∧ Cabc ∧ Dbcd) ∨
  (Aacd ∧ Bbcd ∧ Cabc ∧ Dabd)

/-- Four three-way choices with at-most-one incidence per triangle reduce
exactly to the nine derangements of four objects. -/
theorem four_three_choices_pairwise_collision_reduce_to_nine
    {Aabc Aabd Aacd
     Babc Babd Bbcd
     Cabc Cacd Cbcd
     Dabd Dacd Dbcd : Prop}
    (hA : Aabc ∨ Aabd ∨ Aacd)
    (hB : Babc ∨ Babd ∨ Bbcd)
    (hC : Cabc ∨ Cacd ∨ Cbcd)
    (hD : Dabd ∨ Dacd ∨ Dbcd)
    (hABC_AB : ¬ (Aabc ∧ Babc))
    (hABC_AC : ¬ (Aabc ∧ Cabc))
    (hABC_BC : ¬ (Babc ∧ Cabc))
    (hABD_AB : ¬ (Aabd ∧ Babd))
    (hABD_AD : ¬ (Aabd ∧ Dabd))
    (hABD_BD : ¬ (Babd ∧ Dabd))
    (hACD_AC : ¬ (Aacd ∧ Cacd))
    (hACD_AD : ¬ (Aacd ∧ Dacd))
    (hACD_CD : ¬ (Cacd ∧ Dacd))
    (hBCD_BC : ¬ (Bbcd ∧ Cbcd))
    (hBCD_BD : ¬ (Bbcd ∧ Dbcd))
    (hBCD_CD : ¬ (Cbcd ∧ Dbcd)) :
    FourChoiceDerangement9
      Aabc Aabd Aacd
      Babc Babd Bbcd
      Cabc Cacd Cbcd
      Dabd Dacd Dbcd := by
  unfold FourChoiceDerangement9
  aesop

#print axioms four_three_choices_pairwise_collision_reduce_to_nine

end JSP000404Research
