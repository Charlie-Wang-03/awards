import JSP000404Research.ResidualHardSoftOverlapPartition
import Mathlib.Tactic

/-!
# Whole-cube transport across a hard residual pair

The earlier safe-flip results flipped only the canonical retained
code of a same-retained residual pair. This file proves a stronger
fact about EVERY point in the whole intersection cube.

For an oriented pair a<v with SameRetained(a,v), let c be any outgoing
retained coordinate at a that is inactive at v. Flipping coordinate c
maps the ENTIRE Boolean cube Q_a inter Q_v injectively into Q_v minus
Q_a. The source and destination sets are completely disjoint.

This quantitative full-face transport is only valid when the given
outward/inactive colour exists. It does not assert that all hard pairs
possess such a colour, or that any transported word is a Boolean hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Flip an arbitrary Boolean completion word at one retained coordinate. -/
def flipCompletionWord {n : ℕ}
    (c : Fin n) (word : Fin n → Bool) : Fin n → Bool :=
  fun d => if d = c then !word d else word d

@[simp] theorem flipCompletionWord_at
    {n : ℕ} (c : Fin n) (word : Fin n → Bool) :
    flipCompletionWord c word c = !word c := by
  simp [flipCompletionWord]

theorem flipCompletionWord_off
    {n : ℕ} (c d : Fin n) (word : Fin n → Bool)
    (hdc : d ≠ c) :
    flipCompletionWord c word d = word d := by
  simp [flipCompletionWord, hdc]

/-- Flipping twice is the identity on ALL words, not just retained codes. -/
@[simp] theorem flipCompletionWord_flip
    {n : ℕ} (c : Fin n) (word : Fin n → Bool) :
    flipCompletionWord c (flipCompletionWord c word) = word := by
  funext d
  by_cases hdc : d = c
  · subst d
    simp [flipCompletionWord]
  · simp [flipCompletionWord, hdc]

theorem flipCompletionWord_injective
    {n : ℕ} (c : Fin n) :
    Function.Injective (flipCompletionWord c) := by
  intro w z hwz
  have h := congrArg (flipCompletionWord c) hwz
  simpa only [flipCompletionWord_flip] using h

/-- A flip along a coordinate inactive at v stays in the whole Q_v,
without requiring a canonical initial retained code. -/
theorem flipCompletionWord_mem_upper_of_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c : Fin n} {word : Fin n → Bool}
    (hcInactive : c ∉ retainedActive C v)
    (hword : word ∈ retainedCompletionWords C v) :
    flipCompletionWord c word ∈ retainedCompletionWords C v := by
  apply (mem_retainedCompletionWords C v _).2
  intro d hd
  have hdc : d ≠ c := by
    intro h
    subst d
    exact hcInactive hd
  rw [flipCompletionWord_off _ _ _ hdc]
  exact (mem_retainedCompletionWords C v _).1 hword d hd

/-- Flipping an active lower coordinate LEAVES Q_a, for every
word in Q_a and not merely for its canonical retained code. -/
theorem flipCompletionWord_not_mem_lower_of_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a : V} {c : Fin n} {word : Fin n → Bool}
    (hcActive : c ∈ retainedActive C a)
    (hword : word ∈ retainedCompletionWords C a) :
    flipCompletionWord c word ∉ retainedCompletionWords C a := by
  intro hflipped
  have hbefore :=
    (mem_retainedCompletionWords C a word).1 hword c hcActive
  have hafter :=
    (mem_retainedCompletionWords C a
      (flipCompletionWord c word)).1 hflipped c hcActive
  rw [flipCompletionWord_at] at hafter
  have hfalse : (!word c) = word c :=
    hafter.trans hbefore.symm
  cases word c <;> simp at hfalse

/-- One orientation's safe colour transports each point of the
ENTIRE hard-overlap cube to an upper-only completion word. -/
theorem hard_overlap_cube_flip_mem_upper_only
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} {c : Fin n} {word : Fin n → Bool}
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v)
    (hword : word ∈ retainedCompletionWords C a ∩
      retainedCompletionWords C v) :
    flipCompletionWord c word ∈
      retainedCompletionWords C v \
        retainedCompletionWords C a := by
  have hcActive : c ∈ retainedActive C a := by
    rw [retainedActive_eq_incoming_union_outgoing C a]
    exact Finset.mem_union_right _ hcOutgoing
  have hw := Finset.mem_inter.mp hword
  exact Finset.mem_sdiff.mpr
    ⟨flipCompletionWord_mem_upper_of_inactive C hcInactive hw.2,
     flipCompletionWord_not_mem_lower_of_active C hcActive hw.1⟩

/-- The full overlap cube is no bigger than the upper-only part:
it has a certified injective flip, independently of its dimension. -/
theorem hard_overlap_cube_card_le_upper_only
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} {c : Fin n}
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v) :
    (retainedCompletionWords C a ∩
      retainedCompletionWords C v).card ≤
        (retainedCompletionWords C v \
          retainedCompletionWords C a).card := by
  classical
  let f :
      {word : Fin n → Bool // word ∈
        retainedCompletionWords C a ∩ retainedCompletionWords C v} →
      {word : Fin n → Bool // word ∈
        retainedCompletionWords C v \
          retainedCompletionWords C a} :=
    fun x => ⟨flipCompletionWord c x.1,
      hard_overlap_cube_flip_mem_upper_only C
        hcOutgoing hcInactive x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact flipCompletionWord_injective c
      (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hcard

/-- In particular, if a hard pair's overlap is a d-dimensional
Boolean cube, the upper-only region contains at least 2^d words. -/
theorem hard_overlap_full_dyadic_face_transport
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} {c : Fin n}
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v)
    (hbase : (retainedCompletionWords C a ∩
      retainedCompletionWords C v).Nonempty) :
    2 ^ (commonRetainedInactive C a v).card ≤
      (retainedCompletionWords C v \
        retainedCompletionWords C a).card := by
  obtain ⟨word,hword⟩ := hbase
  have heq := retainedCompletionWords_inter_card C
    (Finset.mem_inter.mp hword).1
    (Finset.mem_inter.mp hword).2
  rw [← heq]
  exact hard_overlap_cube_card_le_upper_only C
    hcOutgoing hcInactive

#print axioms flipCompletionWord_injective
#print axioms hard_overlap_cube_flip_mem_upper_only
#print axioms hard_overlap_cube_card_le_upper_only
#print axioms hard_overlap_full_dyadic_face_transport

end OrderedEdgeColoring
end JSP000404Research
