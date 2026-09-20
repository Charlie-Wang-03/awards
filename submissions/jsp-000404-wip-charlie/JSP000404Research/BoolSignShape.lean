import JSP000404Research.BoolSignPath
import Mathlib.Tactic

/-!
# Shape of a Boolean path with one transition

An antiperiodic Boolean path with exactly one sign change has a rigid form:
some initial block keeps the starting sign and the remaining nonempty block
has the opposite sign.

This is the finite combinatorial cut statement needed by the geometric
support<=2 exposure route.  Once the unique transition is identified with a
positive projective gap, cutting at that gap leaves a lifted ray chain with a
common sign.
-/

namespace JSP000404Research

/-- Two unequal Boolean values are complements. -/
theorem bool_eq_not_of_ne
    {a b : Bool} (h : a ≠ b) :
    b = !a := by
  cases a <;> cases b <;> simp_all

/-- Zero transitions means every read sign equals the starting sign. -/
theorem boolTransitionCountFrom_eq_zero_iff
    (a : Bool) (xs : List Bool) :
    boolTransitionCountFrom a xs = 0 ↔
      ∀ b ∈ xs, b = a := by
  induction xs generalizing a with
  | nil =>
      simp [boolTransitionCountFrom]
  | cons b bs ih =>
      constructor
      · intro h
        simp only [boolTransitionCountFrom] at h
        by_cases hab : a = b
        · subst b
          simp only [if_pos rfl, zero_add] at h
          have hrest := (ih a).1 h
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · rfl
          · exact hrest x hx
        · simp [hab] at h
      · intro hall
        have hb : b = a := hall b (by simp)
        subst b
        have hrest : ∀ x ∈ bs, x = a := by
          intro x hx
          exact hall x (by simp [hx])
        simp [boolTransitionCountFrom, (ih a).2 hrest]

/-- A list all of whose entries equal a is exactly the corresponding
replicate list. -/
theorem list_eq_replicate_length_of_forall_eq
    {α : Type*} (a : α) (xs : List α)
    (h : ∀ x ∈ xs, x = a) :
    xs = List.replicate xs.length a := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
      have hb : b = a := h b (by simp)
      subst b
      have hbs : ∀ x ∈ bs, x = a := by
        intro x hx
        exact h x (by simp [hx])
      rw [ih hbs]
      simp

/-- Exactly one transition, together with antiperiodic endpoint, gives the
canonical two-block form.  The opposite-sign block is nonempty. -/
theorem one_transition_antiperiodic_shape
    (a : Bool) (xs : List Bool)
    (htrans : boolTransitionCountFrom a xs = 1)
    (hlast : boolLastFrom a xs = !a) :
    ∃ m n : ℕ,
      xs =
        List.replicate m a ++
          List.replicate (n + 1) (!a) := by
  induction xs generalizing a with
  | nil =>
      simp [boolTransitionCountFrom] at htrans
  | cons b bs ih =>
      by_cases hab : a = b
      · subst b
        simp only [boolTransitionCountFrom, if_pos rfl, zero_add] at htrans
        have hlast' : boolLastFrom a bs = !a := by
          simpa [boolLastFrom] using hlast
        obtain ⟨m, n, hshape⟩ := ih a htrans hlast'
        refine ⟨m + 1, n, ?_⟩
        simp [hshape, List.replicate_succ, List.cons_append,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · have hb : b = !a := bool_eq_not_of_ne hab
        subst b
        have hrestZero :
            boolTransitionCountFrom (!a) bs = 0 := by
          simp only [boolTransitionCountFrom, hab, if_false] at htrans
          omega
        have hall :
            ∀ x ∈ bs, x = !a :=
          (boolTransitionCountFrom_eq_zero_iff (!a) bs).1 hrestZero
        have hrep :
            bs = List.replicate bs.length (!a) :=
          list_eq_replicate_length_of_forall_eq (!a) bs hall
        refine ⟨0, bs.length, ?_⟩
        simp [hrep, List.replicate_succ]

/-- Support at most two plus antiperiodicity therefore gives the same rigid
two-block sign shape. -/
theorem antiperiodic_shape_of_changes_only_on_support_le_two
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hlast : boolLastFrom a signs = !a)
    (hsupport : listPositiveCount qs ≤ 2) :
    ∃ m n : ℕ,
      signs =
        List.replicate m a ++
          List.replicate (n + 1) (!a) := by
  have htrans :=
    one_sign_transition_of_support_le_two
      a signs qs hchanges hlast hsupport
  exact one_transition_antiperiodic_shape a signs htrans hlast

#print axioms boolTransitionCountFrom_eq_zero_iff
#print axioms list_eq_replicate_length_of_forall_eq
#print axioms one_transition_antiperiodic_shape
#print axioms antiperiodic_shape_of_changes_only_on_support_le_two

end JSP000404Research
