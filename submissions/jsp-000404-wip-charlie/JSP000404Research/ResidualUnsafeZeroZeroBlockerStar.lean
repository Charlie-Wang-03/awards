import JSP000404Research.ResidualUnsafeZeroZeroRigidity
import JSP000404Research.ResidualPairFlipBlocker
import Mathlib.Tactic

/-!
# Hypercube-star blockers of a zero--zero unsafe duplicate code

A zero--zero unsafe saturated carrier u<v has one common complete retained
code base and both endpoint cubes are the singleton {base}.

For every retained coordinate c, the one-bit neighbour flip_c(base) leaves
both endpoint cubes.  If that neighbour is nevertheless covered, any blocker
vertex must activate c and constrain it to the opposite endpoint bit.

Two distinct coordinates cannot have the same blocker.  Indeed, if one vertex
covered both flip_c(base) and flip_d(base), blocker rigidity for the second
neighbour would force its d-bit to be the opposite base bit, while membership
of the first neighbour (which is unchanged at d when c != d) forces the d-bit
to equal the base bit.

Hence, unless one Hamming neighbour is a global Boolean hole, the n one-bit
neighbours force n distinct blocker vertices outside the carrier.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A blocker of a one-bit neighbour of a zero--zero carrier is distinct from
both carrier endpoints. -/
theorem zero_zero_oneFlip_blocker_ne_endpoints
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {base : Fin n → Bool} {c : Fin n}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hw :
      flipBoolWordAt base c ∈ retainedCompletionWords C w) :
    w ≠ u ∧ w ≠ v := by
  constructor
  · intro hwu
    subst w
    exact (flip_active_not_mem_completion C huBase hcu) hw
  · intro hwv
    subst w
    exact (flip_active_not_mem_completion C hvBase hcv) hw

/-- One vertex cannot block two distinct one-bit neighbours of the same
duplicated complete code. -/
theorem zero_zero_oneFlip_blocker_coordinate_unique
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {base : Fin n → Bool}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huFull :
      retainedActive C u = (Finset.univ : Finset (Fin n)))
    (hvFull :
      retainedActive C v = (Finset.univ : Finset (Fin n)))
    {c d : Fin n}
    (hwc :
      flipBoolWordAt base c ∈ retainedCompletionWords C w)
    (hwd :
      flipBoolWordAt base d ∈ retainedCompletionWords C w) :
    c = d := by
  by_contra hcd
  have hcu : c ∈ retainedActive C u := by
    rw [huFull]
    simp
  have hcv : c ∈ retainedActive C v := by
    rw [hvFull]
    simp
  have hdu : d ∈ retainedActive C u := by
    rw [huFull]
    simp
  have hdv : d ∈ retainedActive C v := by
    rw [hvFull]
    simp

  have hcW :
      c ∈ retainedActive C w :=
    one_flip_blocker_active
      C huv huBase hvBase hcu hcv hwc
  have hdW :
      d ∈ retainedActive C w :=
    one_flip_blocker_active
      C huv huBase hvBase hdu hdv hwd

  have hdBit :
      retainedBit C w d = !(retainedBit C u d) :=
    one_flip_blocker_bit_eq_not
      C huv huBase hvBase hdu hdv hwd

  have hwcComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt base c)).1 hwc
  have huComp :=
    (mem_retainedCompletionWords C u base).1 huBase
  have hbaseD :
      base d = retainedBit C u d :=
    huComp d hdu
  have hwcD :
      flipBoolWordAt base c d = retainedBit C w d :=
    hwcComp d hdW
  have hflipOff :
      flipBoolWordAt base c d = base d :=
    flipBoolWordAt_off base (Ne.symm hcd)
  rw [hflipOff, hbaseD, hdBit] at hwcD
  cases h : retainedBit C u d <;> simp [h] at hwcD

/-- If every one-bit neighbour is covered, choose one blocker for each
coordinate.  The chosen blocker map is injective and avoids both endpoints. -/
theorem exists_injective_zero_zero_oneFlip_blockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huFull :
      retainedActive C u = (Finset.univ : Finset (Fin n)))
    (hvFull :
      retainedActive C v = (Finset.univ : Finset (Fin n)))
    (hcovered :
      ∀ c : Fin n,
        ∃ w : V,
          flipBoolWordAt base c ∈ retainedCompletionWords C w) :
    ∃ blocker : Fin n → V,
      Function.Injective blocker ∧
      (∀ c, blocker c ≠ u) ∧
      (∀ c, blocker c ≠ v) ∧
      ∀ c,
        flipBoolWordAt base c ∈
          retainedCompletionWords C (blocker c) := by
  classical
  let blocker : Fin n → V :=
    fun c => Classical.choose (hcovered c)
  have hblock :
      ∀ c,
        flipBoolWordAt base c ∈
          retainedCompletionWords C (blocker c) := by
    intro c
    exact Classical.choose_spec (hcovered c)
  have hinj : Function.Injective blocker := by
    intro c d hcd
    apply zero_zero_oneFlip_blocker_coordinate_unique
      C huv huBase hvBase huFull hvFull
      (w := blocker c)
      (hblock c)
    simpa [hcd] using hblock d
  have hneU : ∀ c, blocker c ≠ u := by
    intro c
    have hcu : c ∈ retainedActive C u := by
      rw [huFull]
      simp
    have hcv : c ∈ retainedActive C v := by
      rw [hvFull]
      simp
    exact
      (zero_zero_oneFlip_blocker_ne_endpoints
        C huv huBase hvBase hcu hcv (hblock c)).1
  have hneV : ∀ c, blocker c ≠ v := by
    intro c
    have hcu : c ∈ retainedActive C u := by
      rw [huFull]
      simp
    have hcv : c ∈ retainedActive C v := by
      rw [hvFull]
      simp
    exact
      (zero_zero_oneFlip_blocker_ne_endpoints
        C huv huBase hvBase hcu hcv (hblock c)).2
  exact ⟨blocker, hinj, hneU, hneV, hblock⟩

/-- Cardinal consequence: if none of the n one-bit neighbours is a global
hole, a zero--zero carrier forces at least n additional vertices besides its
two endpoints. -/
theorem zero_zero_carrier_card_ge_n_add_two_of_no_oneFlip_hole
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huFull :
      retainedActive C u = (Finset.univ : Finset (Fin n)))
    (hvFull :
      retainedActive C v = (Finset.univ : Finset (Fin n)))
    (hnoHole :
      ∀ c : Fin n,
        flipBoolWordAt base c ∈ coveredCompletionWords C) :
    n + 2 ≤ Fintype.card V := by
  have hcovered :
      ∀ c : Fin n,
        ∃ w : V,
          flipBoolWordAt base c ∈ retainedCompletionWords C w := by
    intro c
    have hnonempty :=
      (mem_coveredCompletionWords C
        (flipBoolWordAt base c)).1 (hnoHole c)
    obtain ⟨w, hw⟩ := hnonempty
    exact ⟨w, (mem_completionFibre C _ w).1 hw⟩

  obtain ⟨blocker, hinj, hneU, hneV, hblock⟩ :=
    exists_injective_zero_zero_oneFlip_blockers
      C huv huBase hvBase huFull hvFull hcovered

  let f : Sum (Fin n) (Fin 2) → V
    | Sum.inl c => blocker c
    | Sum.inr i => if i.val = 0 then u else v

  have hf : Function.Injective f := by
    intro x y hxy
    rcases x with c | i <;> rcases y with d | j
    · exact congrArg Sum.inl (hinj hxy)
    · exfalso
      fin_cases i
      · exact hneU c (by simpa [f] using hxy)
      · exact hneV c (by simpa [f] using hxy)
    · exfalso
      fin_cases j
      · exact hneU d (by simpa [f] using hxy.symm)
      · exact hneV d (by simpa [f] using hxy.symm)
    · fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        exact huv (by simpa [f] using hxy)
      · exfalso
        exact huv (by simpa [f] using hxy.symm)
      · rfl

  have hcard :=
    Fintype.card_le_of_injective f hf
  simpa [Fintype.card_sum, Fintype.card_fin] using hcard

#print axioms zero_zero_oneFlip_blocker_coordinate_unique
#print axioms exists_injective_zero_zero_oneFlip_blockers
#print axioms zero_zero_carrier_card_ge_n_add_two_of_no_oneFlip_hole

end OrderedEdgeColoring
end JSP000404Research
