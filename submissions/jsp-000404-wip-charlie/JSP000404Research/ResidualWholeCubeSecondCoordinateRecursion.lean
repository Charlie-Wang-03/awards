import JSP000404Research.ResidualWholeCubeTQRecursionStep
import JSP000404Research.ResidualSecondLayerTTCaptureDichotomy
import JSP000404Research.ResidualWholeCubeSecondCoordinateCollision
import JSP000404Research.ResidualWeightedRecursionRank
import Mathlib.Tactic

/-!
# Unified recursion step for the whole-cube second-coordinate terminal

The second-coordinate second-layer witness splits into T/Q and T/T.

T/Q:
* same-palette full rematch -> a new WholeCubeQTPair;
* otherwise positive capture of at most half one source cube.

T/T:
* same-palette full rematch -> equality of the two translated cubes;
* otherwise positive capture of at most half one source translated cube.

Thus no independent collision terminal remains.  Every branch is either a
lossless rematching state or has strictly smaller Boolean payload.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

inductive WholeCubeSecondCoordinateRecursionStep
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) (c : Fin n) : Prop
  | tqWholeCube
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hwhole : WholeCubeQTPair C w v d)
  | tqHalf
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hpos :
        0 < (translatedBaseCapture C v w d).card)
      (hhalf :
        2 * (translatedBaseCapture C v w d).card
          ≤ (retainedCompletionWords C v).card)
  | ttFull
      (w : V) (d e : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (heW : e ∈ retainedActive C w)
      (hed : e ≠ d)
      (hactiveEq :
        retainedActive C v = retainedActive C w)
      (hfull :
        translatedCompletionWords C v d =
          translatedCompletionWords C w e)
  | ttHalf
      (w : V) (d e : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (heW : e ∈ retainedActive C w)
      (hed : e ≠ d)
      (hpos :
        0 < (translatedTranslatedCapture C v w d e).card)
      (hhalf :
        2 * (translatedTranslatedCapture C v w d e).card
          ≤ (translatedCompletionWords C v d).card)

theorem wholeCubeSecondCoordinate_secondLayer_recursionStep
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hwit :
      WholeCubeSecondCoordinateSecondLayerWitness
        C exponent T s v c) :
    WholeCubeSecondCoordinateRecursionStep
      C exponent T s v c := by
  rcases wholeCubeSecondCoordinate_secondLayer_TQ_or_TT
      C exponent hexp honeLoss hvLoss hwit
    with hTQ | hTT
  · rcases wholeCubeSecondCoordinateTQ_rematch_or_halfCapture
        C exponent hn3 hvLoss hvSecond hTQ
      with hwhole | hhalf
    · obtain ⟨w,d,hwT,hwNeV,hwNeS,hdV,hdc,hrematch⟩ := hwhole
      exact WholeCubeSecondCoordinateRecursionStep.tqWholeCube
        w d hwT hwNeV hwNeS hdV hdc hrematch
    · obtain ⟨w,d,hwT,hwNeV,hwNeS,hdV,hdc,
        hpos,hbound⟩ := hhalf
      exact WholeCubeSecondCoordinateRecursionStep.tqHalf
        w d hwT hwNeV hwNeS hdV hdc hpos hbound
  · obtain ⟨word,w,d,e,
      hdV,hdc,heW,hed,
      hvT,hwTword,
      hwT,hwNeV,hwNeS,hwLoss,hwSecond,_hedge⟩ := hTT
    have hinter :
        (translatedCompletionWords C v d ∩
          translatedCompletionWords C w e).Nonempty :=
      ⟨word,Finset.mem_inter.mpr ⟨hvT,hwTword⟩⟩
    rcases secondLayer_TT_fullRematch_or_halfCapture
        C exponent
        hvLoss hwLoss hvSecond hwSecond
        hdV heW hinter
      with hfull | hhalf
    · exact WholeCubeSecondCoordinateRecursionStep.ttFull
        w d e hwT hwNeV hwNeS hdV hdc heW hed
        hfull.1 hfull.2
    · have hpos :
          0 < (translatedTranslatedCapture C v w d e).card := by
        apply Finset.card_pos.mpr
        exact ⟨word,Finset.mem_inter.mpr ⟨hvT,hwTword⟩⟩
      exact WholeCubeSecondCoordinateRecursionStep.ttHalf
        w d e hwT hwNeV hwNeS hdV hdc heW hed hpos hhalf

theorem wholeCubeSecondCoordinate_halfStep_payload_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e : Fin n}
    (hTQ :
      0 < (translatedBaseCapture C v w d).card ∧
      2 * (translatedBaseCapture C v w d).card
        ≤ (retainedCompletionWords C v).card) :
    (translatedBaseCapture C v w d).card <
      (retainedCompletionWords C v).card := by
  exact payload_strictly_decreases_of_half_capture
    (payload := (retainedCompletionWords C v).card)
    (captured := (translatedBaseCapture C v w d).card)
    (by
      rw [retainedCompletionWords_card]
      exact Nat.two_pow_pos _)
    hTQ.2 hTQ.1

theorem wholeCubeSecondCoordinate_TTHalf_payload_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e : Fin n}
    (hpos :
      0 < (translatedTranslatedCapture C v w d e).card)
    (hhalf :
      2 * (translatedTranslatedCapture C v w d e).card
        ≤ (translatedCompletionWords C v d).card) :
    (translatedTranslatedCapture C v w d e).card <
      (translatedCompletionWords C v d).card := by
  exact payload_strictly_decreases_of_half_capture
    (payload := (translatedCompletionWords C v d).card)
    (captured := (translatedTranslatedCapture C v w d e).card)
    (by
      rw [translatedCompletionWords_card,
          retainedCompletionWords_card]
      exact Nat.two_pow_pos _)
    hhalf hpos

#print axioms wholeCubeSecondCoordinate_secondLayer_recursionStep
#print axioms wholeCubeSecondCoordinate_TTHalf_payload_lt

end OrderedEdgeColoring
end JSP000404Research
