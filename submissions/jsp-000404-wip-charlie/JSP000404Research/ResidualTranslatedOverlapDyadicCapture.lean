import JSP000404Research.ResidualTranslatedOverlapCaptureDichotomy
import Mathlib.Tactic

/-!
# Dyadic form of translated-overlap capture decay

The overlap cube carried by u,v has cardinality exactly

  2 ^ card(commonInactiveRetained C u v).

Combining this identity with the full-free-or-half-capture dichotomy gives a
clean dyadic statement: if a blocker fails to inherit the full common-inactive
set and the overlap dimension d is positive, then its capture has size at most

  2 ^ (d - 1).

This is the quantitative branching unit needed by the global Kraft route.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_capture_le_half_pow_of_not_fullFree
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hdim :
      0 < (commonInactiveRetained C u v).card)
    (hnotFull :
      ¬ commonInactiveRetained C u v ⊆ retainedInactive C w) :
    (oneFlipCapturedSourceWords C u v w c).card ≤
      2 ^ ((commonInactiveRetained C u v).card - 1) := by
  have hhalf :=
    (oneFlip_blocker_fullFree_or_halfCapture C hc).resolve_left hnotFull
  rw [retainedCompletionWords_inter_card_eq_pow_commonInactive
      C hbaseU hbaseV] at hhalf
  have hpow :
      2 ^ (commonInactiveRetained C u v).card =
        2 * 2 ^ ((commonInactiveRetained C u v).card - 1) := by
    have hs :
        (commonInactiveRetained C u v).card - 1 + 1 =
          (commonInactiveRetained C u v).card := by
      omega
    calc
      2 ^ (commonInactiveRetained C u v).card
          =
        2 ^ ((commonInactiveRetained C u v).card - 1 + 1) := by
          rw [hs]
      _ =
        2 ^ ((commonInactiveRetained C u v).card - 1) * 2 := by
          rw [pow_succ]
      _ =
        2 * 2 ^ ((commonInactiveRetained C u v).card - 1) := by
          omega
  rw [hpow] at hhalf
  omega

theorem twoFlip_capture_le_half_pow_of_not_fullFree
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hdim :
      0 < (commonInactiveRetained C u v).card)
    (hnotFull :
      ¬ commonInactiveRetained C u v ⊆ retainedInactive C w) :
    (twoFlipCapturedSourceWords C u v w c d).card ≤
      2 ^ ((commonInactiveRetained C u v).card - 1) := by
  have hhalf :=
    (twoFlip_blocker_fullFree_or_halfCapture C hc hd).resolve_left hnotFull
  rw [retainedCompletionWords_inter_card_eq_pow_commonInactive
      C hbaseU hbaseV] at hhalf
  have hpow :
      2 ^ (commonInactiveRetained C u v).card =
        2 * 2 ^ ((commonInactiveRetained C u v).card - 1) := by
    have hs :
        (commonInactiveRetained C u v).card - 1 + 1 =
          (commonInactiveRetained C u v).card := by
      omega
    calc
      2 ^ (commonInactiveRetained C u v).card
          =
        2 ^ ((commonInactiveRetained C u v).card - 1 + 1) := by
          rw [hs]
      _ =
        2 ^ ((commonInactiveRetained C u v).card - 1) * 2 := by
          rw [pow_succ]
      _ =
        2 * 2 ^ ((commonInactiveRetained C u v).card - 1) := by
          omega
  rw [hpow] at hhalf
  omega

#print axioms oneFlip_capture_le_half_pow_of_not_fullFree
#print axioms twoFlip_capture_le_half_pow_of_not_fullFree

end OrderedEdgeColoring
end JSP000404Research
