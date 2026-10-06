import JSP000404Research.TranslatedCompletionCore
import Mathlib.Tactic

/-!
# Lightweight translated-slice flip exclusion

If a word lies in a translated completion slice T_d(v), flipping a distinct
active coordinate c exits that same slice.  This local Boolean fact is used by
half-capture arguments and does not require whole-cube recursion machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem flip_other_active_not_mem_translated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcd : c ≠ d)
    (hword :
      word ∈ translatedCompletionWords C v d) :
    flipBoolWordAt word c ∉
      translatedCompletionWords C v d := by
  intro hflipT
  have hbase :
      flipBoolWordAt word d ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d word).1 hword
  have hflipBase :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d
      (flipBoolWordAt word c)).1 hflipT
  have hcomm :
      flipBoolWordAt (flipBoolWordAt word c) d =
        flipBoolWordAt (flipBoolWordAt word d) c := by
    exact flipBoolWordAt_commute word hcd
  rw [hcomm] at hflipBase
  exact flip_active_not_mem_completion C hbase hc hflipBase

#print axioms flip_other_active_not_mem_translated

end OrderedEdgeColoring
end JSP000404Research
