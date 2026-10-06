import JSP000404Research.RetainedCompletionCore
import Mathlib.Tactic

/-!
# Lightweight Boolean coordinate flips

Single-coordinate Boolean flips and their interaction with one retained
completion cube.  Kept independent of pair-local Hall / residual-hole repair.
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
  calc
    x = flipBoolWordAt (flipBoolWordAt x c) c :=
      (flipBoolWordAt_involutive c x).symm
    _ = flipBoolWordAt (flipBoolWordAt y c) c := by
      rw [hxy]
    _ = y := flipBoolWordAt_involutive c y

/-- Flipping an active retained coordinate exits that completion cube. -/
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
  have hfixFlip := hcomp c hc
  have hfixOrig := horig c hc
  rw [flipBoolWordAt_at, hfixOrig] at hfixFlip
  cases h : retainedBit C v c <;> simp [h] at hfixFlip

#print axioms flipBoolWordAt_involutive
#print axioms flipBoolWordAt_injective
#print axioms flip_active_not_mem_completion

end OrderedEdgeColoring
end JSP000404Research
