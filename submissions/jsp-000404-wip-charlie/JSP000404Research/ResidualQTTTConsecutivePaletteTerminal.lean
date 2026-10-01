import JSP000404Research.FourConsecutiveLossPaletteHelly
import JSP000404Research.ResidualQTTWholeCubeEquality
import Mathlib.Tactic

/-!
# Consecutive-palette Q/T/T/T whole-cube terminal

A saturated Q/T/T/T state on four second-layer projected-loss vertices whose
four retained palettes are consecutive triples necessarily contains a
whole-cube Q/T pair.

Reason:
1. every pair of loss palettes intersects through their retained edge colour;
2. four consecutive length-three palettes therefore share a common retained
   colour by the discrete Helly lemma;
3. because the completion-owner palette is exactly {cx,cy,cz}, that common
   colour is one owner coordinate;
4. Q/T/T/T translated-edge rigidity forces one translated owner to have the
   exact same retained palette as the completion owner;
5. their common Q/T word then upgrades this to equality of the whole
   translated slice with the completion cube.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTTT_consecutive_palettes_force_whole_cube_QT_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y z : V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hxSecond : exponent x = n - 2)
    (hySecond : exponent y = n - 2)
    (hzSecond : exponent z = n - 2)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcz : cz ∈ retainedActive C z)
    (hcxy : cx ≠ cy) (hcxz : cx ≠ cz) (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz)
    {ms mx my mz : ℕ}
    (hps :
      (retainedActive C s).map Fin.valEmbedding =
        threeNatInterval ms)
    (hpx :
      (retainedActive C x).map Fin.valEmbedding =
        threeNatInterval mx)
    (hpy :
      (retainedActive C y).map Fin.valEmbedding =
        threeNatInterval my)
    (hpz :
      (retainedActive C z).map Fin.valEmbedding =
        threeNatInterval mz) :
    (
      retainedActive C x = retainedActive C s ∧
      translatedCompletionWords C x cx =
        retainedCompletionWords C s
    )
    ∨
    (
      retainedActive C y = retainedActive C s ∧
      translatedCompletionWords C y cy =
        retainedCompletionWords C s
    )
    ∨
    (
      retainedActive C z = retainedActive C s ∧
      translatedCompletionWords C z cz =
        retainedCompletionWords C s
    ) := by
  obtain ⟨d,hds,hdx,hdy,hdz⟩ :=
    four_projectedLoss_consecutive_palettes_common_retained
      C exponent hexp honeLoss
      hsx hsy hsz hxy hxz hyz
      hsLoss hxLoss hyLoss hzLoss
      hps hpx hpy hpz
  exact QTTT_common_colour_forces_whole_cube_QT_pair
    C exponent hexp honeLoss
    hxy hxz hyz
    hsLoss hxLoss hyLoss hzLoss
    hsSecond hxSecond hySecond hzSecond
    hcxy hcxz hcyz hsActive
    hds hdx hdy hdz
    hcx hcy hcz
    hsQ hxT hyT hzT

#print axioms QTTT_consecutive_palettes_force_whole_cube_QT_pair

end OrderedEdgeColoring
end JSP000404Research
