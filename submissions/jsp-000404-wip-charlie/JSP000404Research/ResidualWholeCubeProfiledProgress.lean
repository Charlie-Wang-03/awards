import JSP000404Research.ResidualWholeCubeTQProfiledRecursion
import JSP000404Research.ResidualWholeCubeUnifiedRank
import JSP000404Research.ResidualWholeCubePartnerUniqueness
import Mathlib.Tactic

/-!
# Profiled T/Q recursion as repeat or strict unified-rank progress

For a fixed second-layer projected-loss source v, combine:

* the profiled T/Q rematch-or-half-capture dichotomy;
* coordinate discovery progress;
* half-capture payload decrease;
* the unified whole-cube progress rank.

Every T/Q continuation is therefore exactly one of:

1. a whole-cube rematch at an already-discovered coordinate;
2. a whole-cube rematch at a new coordinate, strictly decreasing discovery rank;
3. a positive half-capture, strictly decreasing Boolean payload.

In the latter two cases the unified natural rank strictly decreases.  A
separate theorem identifies a repeat with the already-registered projected-loss
partner at that coordinate.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeSecondCoordinateTQ_profiled_repeat_or_rank_progress
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hwit : WholeCubeSecondCoordinateTQ C exponent T s v c)
    (coords : Finset (Fin n))
    (hcoords : coords ⊆ retainedActive C v) :
    (
      ∃ w d,
        w ∈ T ∧
        w ≠ v ∧
        w ≠ s ∧
        w ∈ projectedLossVertices C exponent ∧
        exponent w = n - 2 ∧
        d ∈ retainedActive C v ∧
        d ≠ c ∧
        WholeCubeQTPair C w v d ∧
        d ∈ coords
    )
    ∨
    (
      ∃ w d,
        w ∈ T ∧
        w ≠ v ∧
        w ≠ s ∧
        w ∈ projectedLossVertices C exponent ∧
        exponent w = n - 2 ∧
        d ∈ retainedActive C v ∧
        d ≠ c ∧
        WholeCubeQTPair C w v d ∧
        d ∉ coords ∧
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            (insert d coords)
          <
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            coords
    )
    ∨
    (
      ∃ w d,
        w ∈ T ∧
        w ≠ v ∧
        w ≠ s ∧
        w ∈ projectedLossVertices C exponent ∧
        exponent w = n - 2 ∧
        d ∈ retainedActive C v ∧
        d ≠ c ∧
        WholeCubeSecondCoordinateTQHalfCapture C v w d ∧
        wholeCubeProgressRank
            (translatedBaseCapture C v w d).card
            coords
          <
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            coords
    ) := by
  rcases wholeCubeSecondCoordinateTQ_rematch_or_halfCapture_profiled
      C exponent hn3 hvLoss hvSecond hwit
    with hwhole | hhalf
  · obtain ⟨w,d,
      hwT,hwNeV,hwNeS,
      hwLoss,hwSecond,
      hdV,hdc,hpair⟩ := hwhole
    rcases profiled_TQ_rematch_repeat_or_discovery_progress
        C exponent hvLoss hvSecond hdV
        hwLoss hpair coords hcoords
      with hdOld | ⟨hdNew,hdisc⟩
    · exact Or.inl
        ⟨w,d,
          hwT,hwNeV,hwNeS,
          hwLoss,hwSecond,
          hdV,hdc,hpair,hdOld⟩
    · right; left
      have hrank :
          wholeCubeProgressRank
              (retainedCompletionWords C v).card
              (insert d coords)
            <
          wholeCubeProgressRank
              (retainedCompletionWords C v).card
              coords :=
        wholeCubeProgressRank_lt_of_discovery hdisc
      exact ⟨w,d,
        hwT,hwNeV,hwNeS,
        hwLoss,hwSecond,
        hdV,hdc,hpair,hdNew,hrank⟩
  · right; right
    obtain ⟨w,d,
      hwT,hwNeV,hwNeS,
      hwLoss,hwSecond,
      hdV,hdc,hhalf⟩ := hhalf
    have hpayload :
        (translatedBaseCapture C v w d).card <
          (retainedCompletionWords C v).card :=
      wholeCubeSecondCoordinateTQ_halfCapture_payload_lt
        C hhalf
    have hrank :
        wholeCubeProgressRank
            (translatedBaseCapture C v w d).card
            coords
          <
        wholeCubeProgressRank
            (retainedCompletionWords C v).card
            coords :=
      wholeCubeProgressRank_lt_of_payload_lt hpayload
    exact ⟨w,d,
      hwT,hwNeV,hwNeS,
      hwLoss,hwSecond,
      hdV,hdc,hhalf,hrank⟩

/-- A whole-cube repeat at a registered coordinate is the exact same
projected-loss partner state, by fixed-coordinate partner uniqueness. -/
theorem profiled_TQ_repeat_eq_registered_partner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v w : V} {d : Fin n}
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hwhole : WholeCubeQTPair C w v d)
    (coords : Finset (Fin n))
    (hd : d ∈ coords)
    (hregistry :
      ∀ e,
        e ∈ coords →
        ∃ s₀ : V,
          s₀ ∈ projectedLossVertices C exponent ∧
          WholeCubeQTPair C s₀ v e) :
    ∃ s₀ : V,
      s₀ ∈ projectedLossVertices C exponent ∧
      WholeCubeQTPair C s₀ v d ∧
      w = s₀ := by
  obtain ⟨s₀,hs0Loss,hs0Whole⟩ :=
    hregistry d hd
  refine ⟨s₀,hs0Loss,hs0Whole,?_⟩
  exact projectedLoss_wholeCube_partner_unique_at_coordinate
    C exponent hexp honeLoss
    hwLoss hs0Loss hwhole hs0Whole

#print axioms wholeCubeSecondCoordinateTQ_profiled_repeat_or_rank_progress
#print axioms profiled_TQ_repeat_eq_registered_partner

end OrderedEdgeColoring
end JSP000404Research
