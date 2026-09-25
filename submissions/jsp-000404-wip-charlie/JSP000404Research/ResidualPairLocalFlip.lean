
import JSP000404Research.ResidualPairLocalHall
import Mathlib.Tactic

/-!
# Explicit one- or two-bit displacement for saturated overlap cubes

The pair-local Hall theorem only asserts the existence of an injection from a
saturated overlap cube into the complement of the two endpoint cubes.

For later augmenting-path arguments we need more structure.  In fact the
injection can be chosen at Hamming distance at most two.

* If the two retained-active sets have a common coordinate c, flip c.
  Every overlap word satisfies both endpoint constraints at c, so the flip
  leaves both completion cubes at once.

* If the retained-active sets are disjoint, exact projected saturation and
  exponent < n imply that each active set is nonempty.  Choose
  c_u in active(u), c_v in active(v).  They are distinct.  Flip both.
  The c_u flip leaves Q_u and the c_v flip leaves Q_v.

Both maps are involutive Boolean translations, hence injective.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def flipBoolWordAt
    {n : ℕ}
    (word : Fin n → Bool) (c : Fin n) :
    Fin n → Bool :=
  fun d => if d = c then !(word d) else word d

@[simp] theorem flipBoolWordAt_at
    {n : ℕ}
    (word : Fin n → Bool) (c : Fin n) :
    flipBoolWordAt word c c = !(word c) := by
  simp [flipBoolWordAt]

theorem flipBoolWordAt_off
    {n : ℕ}
    (word : Fin n → Bool) {c d : Fin n}
    (hdc : d ≠ c) :
    flipBoolWordAt word c d = word d := by
  simp [flipBoolWordAt, hdc]

theorem flipBoolWordAt_involutive
    {n : ℕ} (c : Fin n)
    (word : Fin n → Bool) :
    flipBoolWordAt (flipBoolWordAt word c) c = word := by
  funext d
  by_cases hdc : d = c
  · subst d
    cases h : word c <;> simp [flipBoolWordAt, h]
  · simp [flipBoolWordAt, hdc]

theorem flipBoolWordAt_injective
    {n : ℕ} (c : Fin n) :
    Function.Injective
      (fun word : Fin n → Bool =>
        flipBoolWordAt word c) := by
  intro x y hxy
  have h :=
    congrArg (fun z => flipBoolWordAt z c) hxy
  simpa [flipBoolWordAt_involutive] using h

/-- Flipping an active coordinate exits that vertex's completion cube. -/
theorem flip_active_not_mem_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool} {c : Fin n}
    (hword : word ∈ retainedCompletionWords C v)
    (hc : c ∈ retainedActive C v) :
    flipBoolWordAt word c ∉
      retainedCompletionWords C v := by
  intro hflip
  have hcomp :=
    (mem_retainedCompletionWords
      C v (flipBoolWordAt word c)).1 hflip
  have horig :=
    (mem_retainedCompletionWords C v word).1 hword
  have hfixFlip :=
    hcomp c hc
  have hfixOrig :=
    horig c hc
  rw [flipBoolWordAt_at, hfixOrig] at hfixFlip
  cases h : retainedBit C v c <;> simp [h] at hfixFlip

/-- A second flip at another coordinate preserves the first coordinate. -/
theorem flipBoolWordAt_two_off_first
    {n : ℕ}
    (word : Fin n → Bool)
    {c d : Fin n} (hcd : c ≠ d) :
    flipBoolWordAt (flipBoolWordAt word c) d c =
      !(word c) := by
  rw [flipBoolWordAt_off _ hcd]
  simp [flipBoolWordAt]

/-- Two distinct fixed-coordinate flips are jointly injective. -/
theorem two_flip_injective
    {n : ℕ} (c d : Fin n) :
    Function.Injective
      (fun word : Fin n → Bool =>
        flipBoolWordAt (flipBoolWordAt word c) d) := by
  exact (flipBoolWordAt_injective d).comp
    (flipBoolWordAt_injective c)

/-- If c is active at v and d is distinct, flipping c and then d still exits
Q_v. -/
theorem two_flip_first_active_not_mem_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {c d : Fin n}
    (hword : word ∈ retainedCompletionWords C v)
    (hc : c ∈ retainedActive C v)
    (hcd : c ≠ d) :
    flipBoolWordAt (flipBoolWordAt word c) d ∉
      retainedCompletionWords C v := by
  intro hflip
  have hcomp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt (flipBoolWordAt word c) d)).1 hflip
  have horig :=
    (mem_retainedCompletionWords C v word).1 hword
  have hfix := hcomp c hc
  have hfixOrig := horig c hc
  rw [flipBoolWordAt_two_off_first word hcd,
      hfixOrig] at hfix
  cases h : retainedBit C v c <;> simp [h] at hfix

/-- The second active coordinate is also violated by the two-flip map. -/
theorem two_flip_second_active_not_mem_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {c d : Fin n}
    (hword : word ∈ retainedCompletionWords C v)
    (hd : d ∈ retainedActive C v) :
    flipBoolWordAt (flipBoolWordAt word c) d ∉
      retainedCompletionWords C v := by
  intro hflip
  have hcomp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt (flipBoolWordAt word c) d)).1 hflip
  have horig :=
    (mem_retainedCompletionWords C v word).1 hword
  have hfix := hcomp d hd
  have hfixOrig := horig d hd
  rw [flipBoolWordAt_at, hfixOrig] at hfix
  cases h : retainedBit C v d <;> simp [h] at hfix

/-- Saturated pair overlap has an explicit displacement into pair-local holes,
using either one common active coordinate or two endpoint-specific active
coordinates. -/
theorem exists_saturated_pair_explicit_flip_to_local_holes
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huLt : exponent u < n)
    (hvLt : exponent v < n) :
    ∃ f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ pairLocalHoles C u v},
      Function.Injective f ∧
      (
        (∃ c : Fin n,
          ∀ word,
            (f word).1 =
              flipBoolWordAt word.1 c)
        ∨
        (∃ c d : Fin n, c ≠ d ∧
          ∀ word,
            (f word).1 =
              flipBoolWordAt
                (flipBoolWordAt word.1 c) d)
      ) := by
  classical
  let Au := retainedActive C u
  let Av := retainedActive C v
  by_cases hcommon : (Au ∩ Av).Nonempty
  · obtain ⟨c, hc⟩ := hcommon
    have hcu : c ∈ retainedActive C u := by
      exact (Finset.mem_inter.mp hc).1
    have hcv : c ∈ retainedActive C v := by
      exact (Finset.mem_inter.mp hc).2
    let f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v} :=
      fun word => ⟨flipBoolWordAt word.1 c, by
        have hparts := Finset.mem_inter.mp word.2
        simp only [pairLocalHoles, Finset.mem_sdiff,
          Finset.mem_univ, true_and]
        rw [Finset.mem_union]
        push_neg
        constructor
        · exact flip_active_not_mem_completion
            C hparts.1 hcu
        · exact flip_active_not_mem_completion
            C hparts.2 hcv⟩
    refine ⟨f, ?_, Or.inl ?_⟩
    · intro x y hxy
      apply Subtype.ext
      apply flipBoolWordAt_injective c
      exact congrArg Subtype.val hxy
    · exact ⟨c, fun word => rfl⟩
  · have hAuPos : Au.Nonempty := by
      have hcard :
          0 < (retainedActive C u).card := by
        unfold ExactProjectedBudget projectedFree at huSat
        have hle :
            (retainedActive C u).card ≤ n := by
          simpa using Finset.card_le_univ (retainedActive C u)
        omega
      exact Finset.card_pos.mp hcard
    have hAvPos : Av.Nonempty := by
      have hcard :
          0 < (retainedActive C v).card := by
        unfold ExactProjectedBudget projectedFree at hvSat
        have hle :
            (retainedActive C v).card ≤ n := by
          simpa using Finset.card_le_univ (retainedActive C v)
        omega
      exact Finset.card_pos.mp hcard
    obtain ⟨c, hcu⟩ := hAuPos
    obtain ⟨d, hdv⟩ := hAvPos
    have hcd : c ≠ d := by
      intro h
      subst d
      exact hcommon ⟨c, Finset.mem_inter.mpr ⟨hcu, hdv⟩⟩
    let f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v} :=
      fun word => ⟨
        flipBoolWordAt
          (flipBoolWordAt word.1 c) d,
        by
          have hparts := Finset.mem_inter.mp word.2
          simp only [pairLocalHoles, Finset.mem_sdiff,
            Finset.mem_univ, true_and]
          rw [Finset.mem_union]
          push_neg
          constructor
          · exact two_flip_first_active_not_mem_completion
              C hparts.1 hcu hcd
          · exact two_flip_second_active_not_mem_completion
              C hparts.2 hdv⟩
    refine ⟨f, ?_, Or.inr ?_⟩
    · intro x y hxy
      apply Subtype.ext
      apply two_flip_injective c d
      exact congrArg Subtype.val hxy
    · exact ⟨c, d, hcd, fun word => rfl⟩

#print axioms flipBoolWordAt_injective
#print axioms flip_active_not_mem_completion
#print axioms two_flip_injective
#print axioms exists_saturated_pair_explicit_flip_to_local_holes

end OrderedEdgeColoring
end JSP000404Research
