import JSP000404Research.CanonicalMarkedSideSemantics
import Mathlib.Tactic

/-!
# Four-point canonical side table

For four distinct points a<b<c<d in the strict canonical planar order:

* at the extreme centres a and d, all three other points lie on one side;
* at the middle centre b, the unique same-side pair among {a,c,d} is {c,d};
* at the middle centre c, the unique same-side pair among {a,b,d} is {a,b}.

This finite table is the order-theoretic consumer for sign-aware zero-block
small-pair witnesses.
-/

namespace JSP000404Research

theorem canonical_four_order_distinct
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
    b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hac := canonicalPointLt_trans hab hbc
  have hbd := canonicalPointLt_trans hbc hcd
  have had := canonicalPointLt_trans hac hcd
  exact ⟨
    fun h => by subst b; exact canonicalPointLt_irrefl a hab,
    fun h => by subst c; exact canonicalPointLt_irrefl a hac,
    fun h => by subst d; exact canonicalPointLt_irrefl a had,
    fun h => by subst c; exact canonicalPointLt_irrefl b hbc,
    fun h => by subst d; exact canonicalPointLt_irrefl b hbd,
    fun h => by subst d; exact canonicalPointLt_irrefl c hcd
  ⟩

theorem canonical_extreme_left_all_sameSide
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d) :
    CanonicalSameSide p a b c ∧
    CanonicalSameSide p a b d ∧
    CanonicalSameSide p a c d := by
  have hac := canonicalPointLt_trans hab hbc
  have hbd := canonicalPointLt_trans hbc hcd
  have had := canonicalPointLt_trans hac hcd
  exact ⟨
    Or.inl ⟨hab,hac⟩,
    Or.inl ⟨hab,had⟩,
    Or.inl ⟨hac,had⟩
  ⟩

theorem canonical_extreme_right_all_sameSide
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d) :
    CanonicalSameSide p d a b ∧
    CanonicalSameSide p d a c ∧
    CanonicalSameSide p d b c := by
  have hac := canonicalPointLt_trans hab hbc
  have hbd := canonicalPointLt_trans hbc hcd
  have had := canonicalPointLt_trans hac hcd
  exact ⟨
    Or.inr ⟨had,hbd⟩,
    Or.inr ⟨had,hcd⟩,
    Or.inr ⟨hbd,hcd⟩
  ⟩

theorem canonical_middle_b_side_table
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d) :
    CanonicalOppositeSides p b a c ∧
    CanonicalOppositeSides p b a d ∧
    CanonicalSameSide p b c d := by
  have hbd := canonicalPointLt_trans hbc hcd
  exact ⟨
    Or.inl ⟨hab,hbc⟩,
    Or.inl ⟨hab,hbd⟩,
    Or.inl ⟨hbc,hbd⟩
  ⟩

theorem canonical_middle_c_side_table
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d) :
    CanonicalSameSide p c a b ∧
    CanonicalOppositeSides p c a d ∧
    CanonicalOppositeSides p c b d := by
  have hac := canonicalPointLt_trans hab hbc
  exact ⟨
    Or.inr ⟨hac,hbc⟩,
    Or.inl ⟨hac,hcd⟩,
    Or.inl ⟨hbc,hcd⟩
  ⟩

/-- At the first middle point b, same-side among the three marked vertices is
equivalent to choosing the upper pair {c,d}. -/
theorem canonical_middle_b_sameSide_unique
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d) :
    ¬ CanonicalSameSide p b a c ∧
    ¬ CanonicalSameSide p b a d ∧
    CanonicalSameSide p b c d := by
  have htab := canonical_middle_b_side_table hab hbc hcd
  refine ⟨?_,?_,htab.2.2⟩
  · intro hsame
    have hop := htab.1
    rcases hop with ⟨hab',hbc'⟩ | ⟨hcb',hba'⟩ <;>
      rcases hsame with ⟨hba,hbc⟩ | ⟨hab2,hcb2⟩
    · exact canonicalPointLt_asymm hab' hba
    · exact canonicalPointLt_asymm hbc' hcb2
    · exact canonicalPointLt_asymm hcb' hbc
    · exact canonicalPointLt_asymm hba' hab2
  · intro hsame
    have hop := htab.2.1
    rcases hop with ⟨hab',hbd'⟩ | ⟨hdb',hba'⟩ <;>
      rcases hsame with ⟨hba,hbd⟩ | ⟨hab2,hdb2⟩
    · exact canonicalPointLt_asymm hab' hba
    · exact canonicalPointLt_asymm hbd' hdb2
    · exact canonicalPointLt_asymm hdb' hbd
    · exact canonicalPointLt_asymm hba' hab2

/-- At the second middle point c, same-side among the three marked vertices is
equivalent to choosing the lower pair {a,b}. -/
theorem canonical_middle_c_sameSide_unique
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d) :
    CanonicalSameSide p c a b ∧
    ¬ CanonicalSameSide p c a d ∧
    ¬ CanonicalSameSide p c b d := by
  have htab := canonical_middle_c_side_table hab hbc hcd
  refine ⟨htab.1,?_,?_⟩
  · intro hsame
    have hop := htab.2.1
    rcases hop with ⟨hac,hcd'⟩ | ⟨hdc,hca⟩ <;>
      rcases hsame with ⟨hca',hcd⟩ | ⟨hac',hdc'⟩
    · exact canonicalPointLt_asymm hac hca'
    · exact canonicalPointLt_asymm hcd' hdc'
    · exact canonicalPointLt_asymm hdc hcd
    · exact canonicalPointLt_asymm hca hac'
  · intro hsame
    have hop := htab.2.2
    rcases hop with ⟨hbc',hcd'⟩ | ⟨hdc,hcb⟩ <;>
      rcases hsame with ⟨hcb',hcd⟩ | ⟨hbc2,hdc'⟩
    · exact canonicalPointLt_asymm hbc' hcb'
    · exact canonicalPointLt_asymm hcd' hdc'
    · exact canonicalPointLt_asymm hdc hcd
    · exact canonicalPointLt_asymm hcb hbc2

#print axioms canonical_middle_b_sameSide_unique
#print axioms canonical_middle_c_sameSide_unique

end JSP000404Research
