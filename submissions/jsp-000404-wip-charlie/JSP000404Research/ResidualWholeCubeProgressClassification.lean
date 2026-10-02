import JSP000404Research.ResidualWholeCubeDiscoveryRank
import JSP000404Research.ResidualWholeCubeTQProfiledRecursion
import JSP000404Research.ResidualWholeCubeSecondCoordinateRecursion
import Mathlib.Tactic

/-!
# Progress classification for the second-coordinate whole-cube recursion

Relative to a finite set of already discovered whole-cube coordinates at the
fixed translated endpoint v, every second-coordinate second-layer continuation
is one of five types:

1. T/Q repeat at an already discovered coordinate -- contractible;
2. T/Q discovery of a new coordinate -- discovery rank strictly decreases;
3. T/Q half capture -- Boolean payload strictly decreases;
4. T/T full rematch -- exact translated-cube equality, contractible;
5. T/T half capture -- Boolean payload strictly decreases.

This is the explicit well-founded/quotiented recursion interface: every
non-contractible step decreases a natural-valued measure.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

inductive WholeCubeSecondCoordinateProgress
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) (c : Fin n)
    (coords : Finset (Fin n)) : Prop
  | tqRepeat
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hwhole : WholeCubeQTPair C w v d)
      (hrepeat : d ∈ coords)
  | tqDiscover
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hwhole : WholeCubeQTPair C w v d)
      (hnew : d ∉ coords)
      (hrank :
        wholeCubeDiscoveryRank (insert d coords) <
          wholeCubeDiscoveryRank coords)
  | tqHalf
      (w : V) (d : Fin n)
      (hwT : w ∈ T)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (hpos :
        0 < (translatedBaseCapture C v w d).card)
      (hpayload :
        (translatedBaseCapture C v w d).card <
          (retainedCompletionWords C v).card)
  | ttFull
      (w : V) (d e : Fin n)
      (hwT : w ∈ T)
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
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
      (hwLoss : w ∈ projectedLossVertices C exponent)
      (hwSecond : exponent w = n - 2)
      (hdV : d ∈ retainedActive C v)
      (hdc : d ≠ c)
      (heW : e ∈ retainedActive C w)
      (hed : e ≠ d)
      (hpos :
        0 < (translatedTranslatedCapture C v w d e).card)
      (hpayload :
        (translatedTranslatedCapture C v w d e).card <
          (translatedCompletionWords C v d).card)

theorem wholeCubeSecondCoordinate_progress
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
    WholeCubeSecondCoordinateProgress
      C exponent T s v c coords := by
  rcases wholeCubeSecondCoordinate_secondLayer_TQ_or_TT
      C exponent hexp honeLoss hvLoss hwit
    with hTQ | hTT

  · rcases wholeCubeSecondCoordinateTQ_rematch_or_halfCapture_profiled
        C exponent hn3 hvLoss hvSecond hTQ
      with hwhole | hhalf
    · obtain ⟨w,d,hwT,_hwNeV,_hwNeS,
          hwLoss,hwSecond,hdV,hdc,hrematch⟩ := hwhole
      rcases profiled_TQ_rematch_repeat_or_discovery_progress
          C exponent hvLoss hvSecond
          hdV hwLoss hrematch coords hcoords
        with hrepeat | hprogress
      · exact WholeCubeSecondCoordinateProgress.tqRepeat
          w d hwT hwLoss hwSecond hdV hdc hrematch hrepeat
      · exact WholeCubeSecondCoordinateProgress.tqDiscover
          w d hwT hwLoss hwSecond hdV hdc hrematch
          hprogress.1 hprogress.2

    · obtain ⟨w,d,hwT,_hwNeV,_hwNeS,
          hwLoss,hwSecond,hdV,hdc,hcapture⟩ := hhalf
      have hpayload :=
        wholeCubeSecondCoordinateTQ_halfCapture_payload_lt
          C hcapture
      exact WholeCubeSecondCoordinateProgress.tqHalf
        w d hwT hwLoss hwSecond hdV hdc
        hcapture.1 hpayload

  · obtain ⟨word,w,d,e,
        hdV,hdc,heW,hed,
        hvT,hwTword,
        hwT,_hwNeV,_hwNeS,hwLoss,hwSecond,_hedge⟩ := hTT
    have hinter :
        (translatedCompletionWords C v d ∩
          translatedCompletionWords C w e).Nonempty :=
      ⟨word,Finset.mem_inter.mpr ⟨hvT,hwTword⟩⟩
    rcases secondLayer_TT_fullRematch_or_halfCapture
        C exponent
        hvLoss hwLoss hvSecond hwSecond
        hdV heW hinter
      with hfull | hhalf
    · exact WholeCubeSecondCoordinateProgress.ttFull
        w d e hwT hwLoss hwSecond hdV hdc heW hed
        hfull.1 hfull.2
    · have hpos :
          0 < (translatedTranslatedCapture C v w d e).card := by
        apply Finset.card_pos.mpr
        exact ⟨word,Finset.mem_inter.mpr ⟨hvT,hwTword⟩⟩
      have hpayload :=
        wholeCubeSecondCoordinate_TTHalf_payload_lt
          C hpos hhalf
      exact WholeCubeSecondCoordinateProgress.ttHalf
        w d e hwT hwLoss hwSecond hdV hdc heW hed
        hpos hpayload

#print axioms wholeCubeSecondCoordinate_progress

end OrderedEdgeColoring
end JSP000404Research
