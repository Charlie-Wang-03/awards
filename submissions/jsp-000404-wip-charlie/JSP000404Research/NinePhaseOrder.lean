import JSP000404Research.SmallOddWireCapacity

/-!
# Triple order after reduction to nine phases

Reducing a coherent integer triangle modulo nine changes the pair comparisons by the
parity of the period quotient. Its middle-pair phase still lies between the outer phases
in the resulting order. This retains information absent from separated rows alone.
-/

namespace JSP000404Research.NinePhase

def Between (middle left right : ℤ) : Prop :=
  (left ≤ middle ∧ middle ≤ right) ∨ (right ≤ middle ∧ middle ≤ left)

def OrderedPhases (a b c : ℤ) (ab ac bc : Bool) : Prop :=
  (ab = ac ∧ ac = bc ∧ Between b a c) ∨
  (ab = ac ∧ ac ≠ bc ∧ Between a b c) ∨
  (ab ≠ ac ∧ ac = bc ∧ Between c a b)

def phaseBefore (time : ℤ) : Bool := decide ((time / 9) % 2 = 0)

instance (middle left right : ℤ) : Decidable (Between middle left right) :=
  inferInstanceAs (Decidable
    ((left ≤ middle ∧ middle ≤ right) ∨ (right ≤ middle ∧ middle ≤ left)))

instance (a b c : ℤ) (ab ac bc : Bool) : Decidable (OrderedPhases a b c ab ac bc) :=
  inferInstanceAs (Decidable
    ((ab = ac ∧ ac = bc ∧ Between b a c) ∨
      (ab = ac ∧ ac ≠ bc ∧ Between a b c) ∨
      (ab ≠ ac ∧ ac = bc ∧ Between c a b)))

theorem ordered_phases_swap_first (a b c : ℤ) (ab ac bc : Bool) :
    OrderedPhases a b c ab ac bc ↔ OrderedPhases a c b (!ab) bc ac := by
  cases ab <;> cases ac <;> cases bc <;> simp [OrderedPhases, Between] <;> omega

theorem ordered_phases_swap_last (a b c : ℤ) (ab ac bc : Bool) :
    OrderedPhases a b c ab ac bc ↔ OrderedPhases b a c ac ab (!bc) := by
  cases ab <;> cases ac <;> cases bc <;> simp [OrderedPhases, Between] <;> omega

theorem ordered_phases_flip (a b c : ℤ) (ab ac bc : Bool) :
    OrderedPhases a b c ab ac bc ↔ OrderedPhases a b c (!ab) (!ac) (!bc) := by
  cases ab <;> cases ac <;> cases bc <;> simp [OrderedPhases]

set_option maxHeartbeats 1000000 in
theorem ordered_phases_of_integer_triangle {a b c : ℤ}
    (hbetween : Between b a c) (hspan : |c - a| ≤ 9)
    (hseparated : 2 ≤ |c - a|) (hleft : |b - a| ≤ 7) (hright : |c - b| ≤ 7) :
    OrderedPhases (a % 9) (b % 9) (c % 9)
      (phaseBefore a) (phaseBefore b) (phaseBefore c) := by
  rcases hbetween with ⟨hab, hbc⟩ | ⟨hcb, hba⟩
  all_goals first
    | simp only [abs_of_nonneg (sub_nonneg.mpr (hab.trans hbc)),
        abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg (sub_nonneg.mpr hbc)]
        at hspan hseparated hleft hright
    | simp only [abs_of_nonpos (sub_nonpos.mpr (hcb.trans hba)),
        abs_of_nonpos (sub_nonpos.mpr hba), abs_of_nonpos (sub_nonpos.mpr hcb)]
        at hspan hseparated hleft hright
  all_goals by_cases ha : (a / 9) % 2 = 0 <;>
    by_cases hb : (b / 9) % 2 = 0 <;> by_cases hc : (c / 9) % 2 = 0 <;>
    simp only [OrderedPhases, phaseBefore, ha, hb, hc, decide_true, decide_false, ne_eq,
      Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false, not_false_eq_true,
      and_false, true_and, false_and, false_or, or_false, Between] <;> omega

theorem event_bit_before (time : ℤ) :
    (OddWire.eventBit time true == decide ((time % 9) % 2 = 0)) = phaseBefore time := by
  by_cases ha : time % 2 = 0 <;> by_cases hb : (time % 9) % 2 = 0 <;>
    by_cases hc : (time / 9) % 2 = 0 <;>
    simp [OddWire.eventBit, phaseBefore, ha, hb, hc] <;> omega

theorem event_bit_before_false (time : ℤ) :
    (OddWire.eventBit time false == decide ((time % 9) % 2 = 0)) = !phaseBefore time := by
  by_cases ha : time % 2 = 0 <;> by_cases hb : (time % 9) % 2 = 0 <;>
    by_cases hc : (time / 9) % 2 = 0 <;>
    simp [OddWire.eventBit, phaseBefore, ha, hb, hc] <;> omega

#print axioms ordered_phases_of_integer_triangle
#print axioms event_bit_before
#print axioms event_bit_before_false

end JSP000404Research.NinePhase
