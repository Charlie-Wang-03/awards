import JSP000404Research.ResidualBridgeDiagonalTrueHoleLedger
import JSP000404Research.ResidualPairFlipBlocker
import Mathlib.Tactic

/-!
# Two-flip third-centre obstruction: a genuinely OPPOSITE retained bit

The certified double-flip maps any overlap word w in the bridge cubes
Q_b and Q_v to a word d outside both Q_b and Q_v.

A central question in the sole admitted JSP-000404 payment is whether
d is a global Boolean hole or is covered by some OTHER vertex c.

Here we prove that any such external blocker MUST simultaneously:
  * activate at least ONE of the two cross-active flip coordinates;
  * have the OPPOSITE canonical retained bit to the corresponding
    bridge endpoint at that activated coordinate.

This is strictly stronger than just asserting a third centre exists.
It is an explicit finite colour/bit obstruction, amenable to
additional genuine planar AngleCap arguments.

We also derive an honest CONDITIONAL true-hole injection: it suffices
to rule out the two specific opposite-bit blocker orientations, not
to assume ALL local exterior words are globally uncovered. This
conditional is not established for all AngleCap configurations,
and no admitted proof is discharged.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If the opposite corner of a cross-active Boolean square is
covered by any centre c, that centre must exhibit an activated
cross-coordinate with the OPPOSITE retained bit of the source
bridge endpoint. Order is reverse flip cr then forward flip cf. -/
theorem two_flip_diagonal_external_blocker_opposite_bit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v c : V) (cf cr : Fin n) (w : Fin n → Bool)
    (hbv : b ≠ v)
    (hcfB : cf ∈ retainedActive C b)
    (hcrB : cr ∉ retainedActive C b)
    (hcrV : cr ∈ retainedActive C v)
    (hwB : w ∈ retainedCompletionWords C b)
    (hwV : w ∈ retainedCompletionWords C v)
    (hdiag : flipCompletionWord cf (flipCompletionWord cr w) ∈
      retainedCompletionWords C c) :
    (cr ∈ retainedActive C c ∧
      retainedBit C c cr = !(retainedBit C v cr)) ∨
    (cf ∈ retainedActive C c ∧
      retainedBit C c cf = !(retainedBit C b cf)) := by
  have hne : cr ≠ cf := by
    intro h
    subst cr
    exact hcrB hcfB
  have hflip :
      flipBoolWordAt (flipBoolWordAt w cr) cf ∈
        retainedCompletionWords C c := by
    change flipCompletionWord cf (flipCompletionWord cr w) ∈
      retainedCompletionWords C c
    exact hdiag
  have hactive :=
    two_flip_blocker_active_one C hbv.symm hne
      hwV hwB hcrV hcfB hflip
  rcases hactive with hcrC | hcfC
  · exact Or.inl ⟨hcrC,
      two_flip_blocker_bit_at_first
        C hne hwV hcrV hcrC hflip⟩
  · exact Or.inr ⟨hcfC,
      two_flip_blocker_bit_at_second
        C hne hwB hcfB hcfC hflip⟩

/-- A diagonal is a genuine GLOBAL Boolean hole if EVERY OTHER
centre is forbidden from having the required opposite retained-bit
orientation at either of the two flipped coordinates.

This is a genuine improvement over assuming that the entire
two-cube exterior has no covered word. -/
theorem two_flip_diagonal_true_hole_of_no_opposite_bit_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n) (w : Fin n → Bool)
    (hbv : b ≠ v)
    (hcfB : cf ∈ retainedActive C b)
    (hcrB : cr ∉ retainedActive C b)
    (hcrV : cr ∈ retainedActive C v)
    (hwB : w ∈ retainedCompletionWords C b)
    (hwV : w ∈ retainedCompletionWords C v)
    (hnoOpposite :
      ∀ c : V, c ≠ b → c ≠ v →
        (cr ∈ retainedActive C c →
          retainedBit C c cr = retainedBit C v cr) ∧
        (cf ∈ retainedActive C c →
          retainedBit C c cf = retainedBit C b cf)) :
    flipCompletionWord cf (flipCompletionWord cr w) ∈
      (Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C := by
  classical
  rcases two_flip_diagonal_hole_or_external_centre
      C b v cf cr w hcfB hcrB hcrV hwB hwV with hhole | ⟨c,hcb,hcv,hcover⟩
  · exact hhole
  have hblock :=
    two_flip_diagonal_external_blocker_opposite_bit
      C b v c cf cr w hbv hcfB hcrB hcrV hwB hwV hcover
  have hguard := hnoOpposite c hcb hcv
  rcases hblock with ⟨hc,hbit⟩ | ⟨hc,hbit⟩
  · have heq := hguard.1 hc
    rw [heq] at hbit
    cases retainedBit C v cr <;> simp at hbit
  · have heq := hguard.2 hc
    rw [heq] at hbit
    cases retainedBit C b cf <;> simp at hbit

/-- The whole bridge overlap cube injects into GLOBAL true holes
when the two chosen cross-active coordinates admit no external
OPPOSITE-bit blockers. This is only an explicit sufficient condition:
its hypothesis is NOT derived from AngleCap in the present file. -/
theorem two_flip_bridge_full_face_le_true_holes_of_no_opposite_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n)
    (hbv : b ≠ v)
    (hcfB : cf ∈ retainedActive C b)
    (hcrB : cr ∉ retainedActive C b)
    (hcrV : cr ∈ retainedActive C v)
    (hnoOpposite :
      ∀ c : V, c ≠ b → c ≠ v →
        (cr ∈ retainedActive C c →
          retainedBit C c cr = retainedBit C v cr) ∧
        (cf ∈ retainedActive C c →
          retainedBit C c cf = retainedBit C b cf)) :
    (retainedCompletionWords C b ∩
      retainedCompletionWords C v).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card := by
  classical
  let f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C b ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ (Finset.univ : Finset (Fin n → Bool)) \
          coveredCompletionWords C} :=
    fun x => ⟨flipCompletionWord cf (flipCompletionWord cr x.1),
      two_flip_diagonal_true_hole_of_no_opposite_bit_blocker
        C b v cf cr x.1 hbv hcfB hcrB hcrV
          (Finset.mem_inter.mp x.2).1
          (Finset.mem_inter.mp x.2).2 hnoOpposite⟩
  have hinj : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    exact double_flip_completion_word_injective cf cr
      (congrArg Subtype.val heq)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hcard

#print axioms two_flip_diagonal_external_blocker_opposite_bit
#print axioms two_flip_diagonal_true_hole_of_no_opposite_bit_blocker
#print axioms two_flip_bridge_full_face_le_true_holes_of_no_opposite_blocker

end OrderedEdgeColoring
end JSP000404Research
