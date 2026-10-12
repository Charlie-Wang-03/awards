import JSP000404Research.ResidualIncomparableBridgeExteriorCapacity
import Mathlib.Tactic

/-!
# Exact obstruction to turning the two-flip exterior into TRUE Boolean holes

For two bridge endpoint completion cubes Q_b,Q_v with incomparable
active palettes, every intersection word admits an injective
double-flip image outside Q_b UNION Q_v. This does not make the
image a genuine hole: a THIRD centre may cover that image.

We now retain that external-cover mass explicitly in the global
hole ledger:

  card(Q_b INTER Q_v)
    <= card(global TRUE holes)
       + card((univ \ (Q_b UNION Q_v)) INTER global covered words).

The second summand is NOT unreserved profile surplus. It counts
words still covered by some other centre, and cannot be dropped.
The theorem is a rigorous necessary budget condition and an
explicit mathematical frontier to replace the admitted payment.

No artificial geometric or Hall payment axiom is introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If a Boolean word is outside both bridge cubes, GLOBAL coverage
is equivalent to coverage by some vertex different from BOTH
bridge endpoints. No assumption of an actual collision is needed. -/
theorem two_cube_exterior_covered_iff_external_centre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (word : Fin n → Bool)
    (hb : word ∉ retainedCompletionWords C b)
    (hv : word ∉ retainedCompletionWords C v) :
    word ∈ coveredCompletionWords C ↔
      ∃ c : V, c ≠ b ∧ c ≠ v ∧
        word ∈ retainedCompletionWords C c := by
  classical
  constructor
  · intro hcover
    rw [coveredCompletionWords_eq_biUnion] at hcover
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hcover
    refine ⟨c, ?_, ?_, hc⟩
    · intro hcb
      subst c
      exact hb hc
    · intro hcv
      subst c
      exact hv hc
  · rintro ⟨c, _, _, hc⟩
    apply (mem_coveredCompletionWords C word).2
    exact ⟨c, (mem_completionFibre C word c).2 hc⟩

/-- This is the exact LOCAL obstruction to upgrading the certified
two-flip injection to an injection into GLOBAL Boolean holes.
Any externally covered diagonal must be charged separately. -/
theorem incomparable_overlap_le_true_holes_plus_external_cover
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V)
    (hinc : ¬ retainedActive C b ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C b) :
    (retainedCompletionWords C b ∩
      retainedCompletionWords C v).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      ((((Finset.univ : Finset (Fin n → Bool)) \
          (retainedCompletionWords C b ∪
            retainedCompletionWords C v)) ∩
          coveredCompletionWords C).card) := by
  classical
  let E : Finset (Fin n → Bool) :=
    (Finset.univ : Finset (Fin n → Bool)) \
      (retainedCompletionWords C b ∪ retainedCompletionWords C v)
  let K : Finset (Fin n → Bool) := coveredCompletionWords C
  let H : Finset (Fin n → Bool) :=
    (Finset.univ : Finset (Fin n → Bool)) \ K
  have hbase :=
    incomparable_completion_overlap_le_two_cube_exterior C b v hinc
  change (retainedCompletionWords C b ∩
    retainedCompletionWords C v).card ≤ E.card at hbase
  have hpart : E = (E \ K) ∪ (E ∩ K) := by
    ext word
    by_cases hw : word ∈ K <;> simp [hw]
  have hdisjoint : Disjoint (E \ K) (E ∩ K) := by
    apply Finset.disjoint_left.mpr
    intro word hwOutside hwInside
    exact (Finset.mem_sdiff.mp hwOutside).2
      (Finset.mem_inter.mp hwInside).2
  have heq : E.card = (E \ K).card + (E ∩ K).card := by
    calc
      E.card = ((E \ K) ∪ (E ∩ K)).card := by rw [← hpart]
      _ = (E \ K).card + (E ∩ K).card :=
        Finset.card_union_of_disjoint hdisjoint
  have hholes : (E \ K).card ≤ H.card := by
    apply Finset.card_le_card
    intro word hw
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hw).2⟩
  change (retainedCompletionWords C b ∩
      retainedCompletionWords C v).card ≤ H.card +
      (E ∩ K).card
  omega

/-- A precise CONDITIONAL true-hole payment: if the two-cube
exterior contains NO globally covered words, the two-flip
injection really lands in genuine global holes. This extra
condition is NOT proved by AngleCap and must not be silently
assumed in JSP-000404. -/
theorem incomparable_overlap_le_true_holes_of_no_external_cover
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V)
    (hinc : ¬ retainedActive C b ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C b)
    (hzero :
      Disjoint
        ((Finset.univ : Finset (Fin n → Bool)) \
          (retainedCompletionWords C b ∪
            retainedCompletionWords C v))
        (coveredCompletionWords C)) :
    (retainedCompletionWords C b ∩
      retainedCompletionWords C v).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card := by
  have hbound :=
    incomparable_overlap_le_true_holes_plus_external_cover
      C b v hinc
  have hzeroCard :
      ((((Finset.univ : Finset (Fin n → Bool)) \
          (retainedCompletionWords C b ∪
            retainedCompletionWords C v)) ∩
          coveredCompletionWords C).card) = 0 := by
    apply Finset.card_eq_zero.mpr
    ext word
    constructor
    · intro hw
      exact False.elim ((Finset.disjoint_left.mp hzero)
        (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2)
    · intro hw
      simpa using hw
  omega

#print axioms two_cube_exterior_covered_iff_external_centre
#print axioms incomparable_overlap_le_true_holes_plus_external_cover
#print axioms incomparable_overlap_le_true_holes_of_no_external_cover

end OrderedEdgeColoring
end JSP000404Research
