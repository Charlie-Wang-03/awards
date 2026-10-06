import JSP000404Research.ResidualLossTranslatedBlock
import Mathlib.Tactic

/-!
# Lightweight whole-cube Q/T pair and retained-code core

This module isolates the small Boolean cube facts needed by the geometric
three-whole-cube branch from the heavier residual recursion machinery.

A WholeCubeQTPair C s v c means that the retained palettes of v and s
agree and the c-translated completion cube at v is exactly the retained
completion cube at s.

From this equality alone:

* the owner bit c is flipped;
* every other active retained bit is unchanged.

No Hall, recursive-outlet, two-flip, or Q/T/T/T terminal dependency is needed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def WholeCubeQTPair
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (s v : V) (c : Fin n) : Prop :=
  retainedActive C v = retainedActive C s ∧
  translatedCompletionWords C v c =
    retainedCompletionWords C s

theorem wholeCube_off_owner_retainedBit_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c d : Fin n}
    (hwhole : WholeCubeQTPair C s v c)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c) :
    retainedBit C s d = retainedBit C v d := by
  rcases hwhole with ⟨hactiveEq,htransEq⟩
  have hdS : d ∈ retainedActive C s := by
    rw [← hactiveEq]
    exact hdV

  let base : Fin n → Bool := fun e => retainedBit C v e
  have hbaseV :
      base ∈ retainedCompletionWords C v := by
    apply (mem_retainedCompletionWords C v base).2
    intro e he
    rfl

  have htrans :
      flipBoolWordAt base c ∈ translatedCompletionWords C v c := by
    apply (mem_translatedCompletionWords C v c _).2
    simpa [flipBoolWordAt_involutive] using hbaseV

  have hsQ :
      flipBoolWordAt base c ∈ retainedCompletionWords C s := by
    rw [← htransEq]
    exact htrans

  have hvComp :=
    (mem_retainedCompletionWords C v base).1 hbaseV
  have hsComp :=
    (mem_retainedCompletionWords C s
      (flipBoolWordAt base c)).1 hsQ
  have hvAt := hvComp d hdV
  have hsAt := hsComp d hdS
  rw [flipBoolWordAt_off base hdc] at hsAt
  exact hsAt.symm.trans hvAt

theorem wholeCube_owner_retainedBit_flip
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    retainedBit C s c = !(retainedBit C v c) := by
  rcases hwhole with ⟨hactiveEq,htransEq⟩
  have hcS : c ∈ retainedActive C s := by
    rw [← hactiveEq]
    exact hcV

  let word : Fin n → Bool := fun e => retainedBit C s e
  have hsQ :
      word ∈ retainedCompletionWords C s := by
    apply (mem_retainedCompletionWords C s word).2
    intro e he
    rfl
  have hvT :
      word ∈ translatedCompletionWords C v c := by
    rw [htransEq]
    exact hsQ
  have hvBase :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  have hsComp :=
    (mem_retainedCompletionWords C s word).1 hsQ
  have hvComp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word c)).1 hvBase
  have hsAt := hsComp c hcS
  have hvAt := hvComp c hcV
  rw [flipBoolWordAt_at, hsAt] at hvAt
  cases hs : retainedBit C s c <;>
    cases hv : retainedBit C v c <;>
    simp_all

theorem wholeCube_retainedCode_single_flip
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    retainedActive C s = retainedActive C v ∧
    retainedBit C s c = !(retainedBit C v c) ∧
    ∀ d : Fin n,
      d ∈ retainedActive C v →
      d ≠ c →
      retainedBit C s d = retainedBit C v d := by
  exact ⟨
    hwhole.1.symm,
    wholeCube_owner_retainedBit_flip C hcV hwhole,
    fun d hd hdc =>
      wholeCube_off_owner_retainedBit_eq C hwhole hd hdc
  ⟩

#print axioms wholeCube_off_owner_retainedBit_eq
#print axioms wholeCube_owner_retainedBit_flip
#print axioms wholeCube_retainedCode_single_flip

end OrderedEdgeColoring
end JSP000404Research
