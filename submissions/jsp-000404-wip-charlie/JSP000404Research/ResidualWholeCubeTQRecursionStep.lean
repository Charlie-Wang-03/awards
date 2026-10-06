import JSP000404Research.ResidualWholeCubeSecondCoordinateCore
import JSP000404Research.ResidualSecondLayerTQCaptureDichotomy
import Mathlib.Tactic

/-!
# Consumption of the whole-cube second-coordinate T/Q terminal

A WholeCubeSecondCoordinateTQ witness already records:

* v and w are second-layer projected-loss vertices;
* d is active at v;
* a word lies in T_d(v) ∩ Q_w;
* the retained edge vw has colour d.

The edge-colour witness implies d is active at w as well.  Therefore the
general second-layer T/Q dichotomy applies immediately.

Consequently every T/Q second-coordinate continuation is either

* a new exact WholeCubeQTPair (w,v,d), or
* a non-full capture of at most half one source completion-cube mass.

This removes T/Q as an independent hard terminal.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def WholeCubeSecondCoordinateTQHalfCapture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v w : V) (d : Fin n) : Prop :=
  0 < (translatedBaseCapture C v w d).card ∧
  2 * (translatedBaseCapture C v w d).card
    ≤ (retainedCompletionWords C v).card

theorem wholeCubeSecondCoordinateTQ_rematch_or_halfCapture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hwit : WholeCubeSecondCoordinateTQ C exponent T s v c) :
    (
      ∃ w : V, ∃ d : Fin n,
        w ∈ T ∧
        w ≠ v ∧
        w ≠ s ∧
        d ∈ retainedActive C v ∧
        d ≠ c ∧
        WholeCubeQTPair C w v d
    )
    ∨
    (
      ∃ w : V, ∃ d : Fin n,
        w ∈ T ∧
        w ≠ v ∧
        w ≠ s ∧
        d ∈ retainedActive C v ∧
        d ≠ c ∧
        WholeCubeSecondCoordinateTQHalfCapture C v w d
    ) := by
  obtain ⟨word,w,d,
      hdV,hdc,hvT,hwQ,
      hwT,hwNeV,hwNeS,
      hwLoss,hwSecond,hedge⟩ := hwit

  have hdW : d ∈ retainedActive C w := by
    rcases hedge with hedge | hedge
    · obtain ⟨hvw,hret,hcol⟩ := hedge
      have hm :=
        retainedColor_mem_retainedActive_right C hvw hret
      simpa [hcol] using hm
    · obtain ⟨hwv,hret,hcol⟩ := hedge
      have hm :=
        retainedColor_mem_retainedActive_left C hwv hret
      simpa [hcol] using hm

  have hinter :
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty :=
    ⟨word,Finset.mem_inter.mpr ⟨hvT,hwQ⟩⟩

  rcases secondLayer_TQ_wholeCube_or_half_source_cube
      C exponent hn3
      hvLoss hwLoss hvSecond hwSecond
      hdV hdW hinter
    with hwhole | hhalf
  · exact Or.inl
      ⟨w,d,hwT,hwNeV,hwNeS,hdV,hdc,hwhole⟩
  · right
    have hpos :
        0 < (translatedBaseCapture C v w d).card := by
      apply Finset.card_pos.mpr
      exact ⟨word,Finset.mem_inter.mpr ⟨hvT,hwQ⟩⟩
    exact ⟨w,d,hwT,hwNeV,hwNeS,hdV,hdc,
      hpos,hhalf⟩

/-- A positive half-capture has strictly smaller payload than the source
completion cube. -/
theorem wholeCubeSecondCoordinateTQ_halfCapture_payload_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d : Fin n}
    (hhalf :
      WholeCubeSecondCoordinateTQHalfCapture C v w d) :
    (translatedBaseCapture C v w d).card <
      (retainedCompletionWords C v).card := by
  rcases hhalf with ⟨hpos,hbound⟩
  omega

#print axioms wholeCubeSecondCoordinateTQ_rematch_or_halfCapture
#print axioms wholeCubeSecondCoordinateTQ_halfCapture_payload_lt

end OrderedEdgeColoring
end JSP000404Research
