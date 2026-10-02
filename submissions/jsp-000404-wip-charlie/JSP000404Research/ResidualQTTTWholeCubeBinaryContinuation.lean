import JSP000404Research.ResidualWholeCubeSecondCoordinateCollision
import JSP000404Research.ResidualWholeCubeTQCoordinateIdentification
import Mathlib.Tactic

/-!
# Binary owner-coordinate continuation from a Q/T/T/T whole-cube partner

In a saturated Q/T/T/T state the completion owner has exactly the three active
owner coordinates {cx,cy,cz}.  If x is a whole-cube Q/T partner of s along cx,
then x has the same retained-active palette.

Any augmenting second coordinate d at x is active at x and differs from cx.
Hence d is forced to be cy or cz.

If the third source is one of the already-known translated owners y or z and
the augmentation is T/Q, the coordinate is identified exactly:
  source y -> d=cy,
  source z -> d=cz.

Thus the whole-cube augmenting branch is intrinsically binary.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTTT_wholeCube_x_second_coordinate_cy_or_cz
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x : V}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hwhole : WholeCubeQTPair C s x cx)
    (hdX : d ∈ retainedActive C x)
    (hdcx : d ≠ cx) :
    d = cy ∨ d = cz := by
  rcases hwhole with ⟨hactiveEq,_⟩
  have hdS : d ∈ retainedActive C s := by
    rw [← hactiveEq]
    exact hdX
  rw [hsActive] at hdS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdS
  rcases hdS with hdx | hdy | hdz
  · exact False.elim (hdcx hdx)
  · exact Or.inl hdy
  · exact Or.inr hdz

theorem QTTT_wholeCube_x_TQ_known_source_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    {common extra : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hwhole : WholeCubeQTPair C s x cx)
    (hxCommon : common ∈ translatedCompletionWords C x cx)
    (hyCommon : common ∈ translatedCompletionWords C y cy)
    (hzCommon : common ∈ translatedCompletionWords C z cz)
    (hdX : d ∈ retainedActive C x)
    (hdcx : d ≠ cx)
    (hxExtra : extra ∈ translatedCompletionWords C x d) :
    (
      extra ∈ retainedCompletionWords C y → d = cy
    )
    ∧
    (
      extra ∈ retainedCompletionWords C z → d = cz
    )
    ∧
    (d = cy ∨ d = cz) := by
  refine ⟨?_,?_,?_⟩
  · intro hyExtra
    exact second_TQ_coordinate_eq_known_translated_owner
      C exponent hexp honeLoss
      hxy hxLoss hyLoss
      hcxy hdcx
      hxCommon hyCommon
      hdX hxExtra hyExtra
  · intro hzExtra
    exact second_TQ_coordinate_eq_known_translated_owner
      C exponent hexp honeLoss
      hxz hxLoss hzLoss
      hcxz hdcx
      hxCommon hzCommon
      hdX hxExtra hzExtra
  · exact QTTT_wholeCube_x_second_coordinate_cy_or_cz
      C hcxy hcxz hcyz hsActive hwhole hdX hdcx

#print axioms QTTT_wholeCube_x_second_coordinate_cy_or_cz
#print axioms QTTT_wholeCube_x_TQ_known_source_coordinate

end OrderedEdgeColoring
end JSP000404Research
