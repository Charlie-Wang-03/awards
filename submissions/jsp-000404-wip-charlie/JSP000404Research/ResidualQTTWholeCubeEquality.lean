import JSP000404Research.ResidualQTTTRepeatedPalette
import JSP000404Research.ResidualPairLocalFlip
import Mathlib.Tactic

/-!
# Whole-cube equality from a one-bit retained-code difference

If two vertices have the same retained-active coordinate set and their
retained Boolean codes differ exactly at one active coordinate c, then
flipping c identifies their entire retained completion cubes.

Applied to a Q/T pair with equal retained palettes, the common Q/T word itself
proves exactly this one-bit code relation.  Thus a single Q/T overlap upgrades
to equality of the whole translated slice and the completion cube.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translatedCompletionWords_eq_completion_of_oneBit_code
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    (hactive :
      retainedActive C u = retainedActive C v)
    (hc : c ∈ retainedActive C u)
    (hbitC :
      retainedBit C v c = !(retainedBit C u c))
    (hbits :
      ∀ d : Fin n,
        d ∈ retainedActive C u →
        d ≠ c →
        retainedBit C v d = retainedBit C u d) :
    translatedCompletionWords C v c =
      retainedCompletionWords C u := by
  classical
  ext q
  rw [mem_translatedCompletionWords,
      mem_retainedCompletionWords,
      mem_retainedCompletionWords]
  constructor
  · intro hv d hdu
    have hdv : d ∈ retainedActive C v := by
      rw [← hactive]
      exact hdu
    have hvd := hv d hdv
    by_cases hdc : d = c
    · subst d
      rw [flipBoolWordAt_at, hbitC] at hvd
      cases hu : retainedBit C u c <;>
        cases hq : q c <;>
        simp_all
    · rw [flipBoolWordAt_off q hdc] at hvd
      rw [hbits d hdu hdc] at hvd
      exact hvd
  · intro hu d hdv
    have hdu : d ∈ retainedActive C u := by
      rw [hactive]
      exact hdv
    have hud := hu d hdu
    by_cases hdc : d = c
    · subst d
      rw [flipBoolWordAt_at, hbitC]
      cases huc : retainedBit C u c <;>
        cases hq : q c <;>
        simp_all
    · rw [flipBoolWordAt_off q hdc]
      rw [hbits d hdu hdc]
      exact hud

/-- A Q/T common word plus equality of active palettes forces the retained
codes to differ exactly at the translated owner coordinate. -/
theorem QTT_equal_palette_oneBit_code
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s y : V}
    {word : Fin n → Bool}
    {cy : Fin n}
    (hactive :
      retainedActive C y = retainedActive C s)
    (hcyY : cy ∈ retainedActive C y)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    retainedBit C y cy = !(retainedBit C s cy) ∧
    (∀ d : Fin n,
      d ∈ retainedActive C s →
      d ≠ cy →
      retainedBit C y d = retainedBit C s d) := by
  have hcyS : cy ∈ retainedActive C s := by
    rw [← hactive]
    exact hcyY
  have hsComp :=
    (mem_retainedCompletionWords C s word).1 hsQ
  have hyBase :
      flipBoolWordAt word cy ∈ retainedCompletionWords C y :=
    (mem_translatedCompletionWords C y cy word).1 hyT
  have hyComp :=
    (mem_retainedCompletionWords C y
      (flipBoolWordAt word cy)).1 hyBase
  have hsCy := hsComp cy hcyS
  have hyCy := hyComp cy hcyY
  constructor
  · rw [flipBoolWordAt_at, hsCy] at hyCy
    cases hsbit : retainedBit C s cy <;>
      cases hybit : retainedBit C y cy <;>
      simp_all
  · intro d hdS hdc
    have hdY : d ∈ retainedActive C y := by
      rw [hactive]
      exact hdS
    have hsD := hsComp d hdS
    have hyD := hyComp d hdY
    rw [flipBoolWordAt_off word hdc] at hyD
    exact hyD.symm.trans hsD

theorem QTT_equal_palette_translated_slice_eq_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s y : V}
    {word : Fin n → Bool}
    {cy : Fin n}
    (hactive :
      retainedActive C y = retainedActive C s)
    (hcyY : cy ∈ retainedActive C y)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    translatedCompletionWords C y cy =
      retainedCompletionWords C s := by
  have hcode :=
    QTT_equal_palette_oneBit_code
      C hactive hcyY hsQ hyT
  have hcyS : cy ∈ retainedActive C s := by
    rw [← hactive]
    exact hcyY
  exact translatedCompletionWords_eq_completion_of_oneBit_code
    C hactive.symm hcyS hcode.1 hcode.2

#print axioms translatedCompletionWords_eq_completion_of_oneBit_code
#print axioms QTT_equal_palette_oneBit_code
#print axioms QTT_equal_palette_translated_slice_eq_completion

end OrderedEdgeColoring
end JSP000404Research
