import JSP000404Research.ResidualWholeCubeProfiledProgress
import JSP000404Research.ResidualWholeCubeSecondCoordinateRecursion
import JSP000404Research.ResidualTranslatedCubeRematchQuotient
import Mathlib.Tactic

/-!
# Complete profiled second-coordinate recursion outcome

For a projected-loss second-layer source, a second-coordinate witness now has
five exhaustive outcomes:

1. T/Q whole-cube repeat at an already discovered coordinate;
2. T/Q whole-cube discovery at a new coordinate, strictly decreasing the
   unified whole-cube progress rank;
3. T/Q positive half-capture, strictly decreasing payload and hence rank;
4. T/T full rematch with equal retained palette and equal translated cube,
   hence contractible in the translated-cube quotient;
5. T/T positive half-capture, strictly decreasing payload and hence rank.

Thus every non-contractible second-coordinate continuation carries an explicit
natural-valued rank decrease.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

inductive WholeCubeSecondCoordinateProfiledOutcome
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) (c : Fin n)
    (coords : Finset (Fin n)) : Prop
  | tqRepeat
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hwhole : WholeCubeQTPair C w v d)
      (hdOld : d ∈ coords)
  | tqDiscovery
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hwhole : WholeCubeQTPair C w v d)
      (hdNew : d ∉ coords)
      (hrank :
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            (insert d coords)
          <
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            coords)
  | tqHalf
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hhalf : WholeCubeSecondCoordinateTQHalfCapture C v w d)
      (hrank :
        wholeCubeProgressRank
            (translatedBaseCapture C v w d).card
            coords
          <
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            coords)
  | ttEquivalent
      (w : V) (d e : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (heW : e ∈ retainedActive C w)
      (hed : e ≠ d)
      (hactiveEq : retainedActive C v = retainedActive C w)
      (hfull :
        translatedCompletionWords C v d =
          translatedCompletionWords C w e)
  | ttHalf
      (w : V) (d e : Fin n)
      (hwT : w ∈ T)
      (hwNeV : w ≠ v)
      (hwNeS : w ≠ s)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (heW : e ∈ retainedActive C w)
      (hed : e ≠ d)
      (hpos :
        0 < (translatedTranslatedCapture C v w d e).card)
      (hhalf :
        2 * (translatedTranslatedCapture C v w d e).card
          ≤ (translatedCompletionWords C v d).card)
      (hrank :
        wholeCubeProgressRank
            (translatedTranslatedCapture C v w d e).card
            coords
          <
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            coords)

theorem wholeCubeSecondCoordinate_profiled_outcome
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
        C exponent T s v c)
    (coords : Finset (Fin n))
    (hcoords : coords ⊆ retainedActive C v) :
    WholeCubeSecondCoordinateProfiledOutcome
      C exponent T s v c coords := by
  rcases wholeCubeSecondCoordinate_secondLayer_TQ_or_TT
      C exponent hexp honeLoss hvLoss hwit
    with hTQ | hTT
  · rcases wholeCubeSecondCoordinateTQ_profiled_repeat_or_rank_progress
        C exponent hn3 hvLoss hvSecond hTQ coords hcoords
      with hrep | hdisc | hhalf
    · obtain ⟨w,d,
        hwT,hwNeV,hwNeS,
        hwLoss,hwSecond,
        hdV,hdc,hwhole,hdOld⟩ := hrep
      exact WholeCubeSecondCoordinateProfiledOutcome.tqRepeat
        w d hwT hwNeV hwNeS hwLoss hwSecond
        hdV hdc hwhole hdOld
    · obtain ⟨w,d,
        hwT,hwNeV,hwNeS,
        hwLoss,hwSecond,
        hdV,hdc,hwhole,hdNew,hrank⟩ := hdisc
      exact WholeCubeSecondCoordinateProfiledOutcome.tqDiscovery
        w d hwT hwNeV hwNeS hwLoss hwSecond
        hdV hdc hwhole hdNew hrank
    · obtain ⟨w,d,
        hwT,hwNeV,hwNeS,
        hwLoss,hwSecond,
        hdV,hdc,hhalf,hrank⟩ := hhalf
      exact WholeCubeSecondCoordinateProfiledOutcome.tqHalf
        w d hwT hwNeV hwNeS hwLoss hwSecond
        hdV hdc hhalf hrank
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
    · exact WholeCubeSecondCoordinateProfiledOutcome.ttEquivalent
        w d e hwT hwNeV hwNeS hwLoss hwSecond
        hdV hdc heW hed hfull.1 hfull.2
    · have hpos :
          0 < (translatedTranslatedCapture C v w d e).card := by
        exact Finset.card_pos.mpr
          ⟨word,Finset.mem_inter.mpr ⟨hvT,hwTword⟩⟩
      have hpayload :
          (translatedTranslatedCapture C v w d e).card <
            (translatedCompletionWords C v d).card :=
        wholeCubeSecondCoordinate_TTHalf_payload_lt
          C hpos hhalf
      have hpayload' :
          (translatedTranslatedCapture C v w d e).card <
            (retainedCompletionWords C v).card := by
        simpa [translatedCompletionWords_card] using hpayload
      have hrank :
          wholeCubeProgressRank
              (translatedTranslatedCapture C v w d e).card
              coords
            <
          wholeCubeProgressRank
              (retainedCompletionWords C v).card
              coords :=
        wholeCubeProgressRank_lt_of_payload_lt hpayload'
      exact WholeCubeSecondCoordinateProfiledOutcome.ttHalf
        w d e hwT hwNeV hwNeS hwLoss hwSecond
        hdV hdc heW hed hpos hhalf hrank

/-- The T/T full constructor is genuinely stationary in the translated-cube
quotient. -/
theorem profiledOutcome_ttEquivalent_same_quotient
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e : Fin n}
    (hdV : d ∈ retainedActive C v)
    (heW : e ∈ retainedActive C w)
    (hactiveEq : retainedActive C v = retainedActive C w)
    (hfull :
      translatedCompletionWords C v d =
        translatedCompletionWords C w e) :
    Quotient.mk
        (translatedCubeStateSetoid C)
        (TranslatedCubeState.mk v d hdV)
      =
    Quotient.mk
        (translatedCubeStateSetoid C)
        (TranslatedCubeState.mk w e heW) :=
  ttFull_same_quotient_state
    C hdV heW hactiveEq hfull

#print axioms wholeCubeSecondCoordinate_profiled_outcome
#print axioms profiledOutcome_ttEquivalent_same_quotient

end OrderedEdgeColoring
end JSP000404Research
