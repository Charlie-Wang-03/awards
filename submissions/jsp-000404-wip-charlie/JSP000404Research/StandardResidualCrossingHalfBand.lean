import JSP000404Research.StandardResidualHalfBandTriangle
import Mathlib.Tactic

/-!
# Two crossing residual carriers force two strict low-band outer flanks

Let u<a<v<b and suppose u--v and a--b are residual edges in
DirectionData at normalized width t=n+delta, delta<1/2.

The standard residual interval property forces the crossing edge a--v
to be residual. Apply the half-band triangle separation first to the
outer edge u--v with interior point a, and again to a--b with interior
point v. In BOTH triangles the inner cross edge a--v must be the
unique residual child. Consequently BOTH outer flank directions
u--a and v--b fall strictly below n-1/2 and each differs from the
residual cross-edge direction by at least one full normalized unit.

Unlike the single-edge terminal cone theorem, this is a two-triangle,
four-centre geometric constraint on crossing residual carriers. It
does not establish global Hall expansion or hard-word payment.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Four ordered vertices with crossing residual edges exhibit one
central residual edge and two strictly subhalf nonresidual flanks,
both separated by at least one from the central direction. -/
theorem standardResidual_crossing_forces_two_subhalf_flanks
    {V : Type*} [LinearOrder V]
    {t delta : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hwidth : t < (n + 1 : ℕ))
    {u a v b : V}
    (hua : u < a)
    (hav : a < v)
    (hvb : v < b)
    (hresUV : IsResidual (standardResidualColoring D n hwidth) u v)
    (hresAB : IsResidual (standardResidualColoring D n hwidth) a b) :
    let R := standardResidualColoring D n hwidth
    IsResidual R a v ∧
      ¬ IsResidual R u a ∧
      ¬ IsResidual R v b ∧
      D.value u a + 1 ≤ D.value a v ∧
      D.value v b + 1 ≤ D.value a v ∧
      D.value u a + (1 : ℝ) / 2 < (n : ℝ) ∧
      D.value v b + (1 : ℝ) / 2 < (n : ℝ) := by
  let R := standardResidualColoring D n hwidth
  have hsourceA : residualBit R a = true :=
    residualBit_eq_true_of_residual R (hav.trans hvb) hresAB
  have hcross : IsResidual R a v :=
    (standardResidual_right_child_iff_bit_true
      D hwidth hua hav hresUV).2 hsourceA
  have hfirst :
      ¬ IsResidual R u a ∧
        D.value u a + 1 ≤ D.value a v ∧
        D.value u a + (1 : ℝ) / 2 < (n : ℝ) := by
    rcases standardResidual_intermediate_forces_subhalf_opposite_child
      D hdeltaHalf ht hwidth hua hav hresUV with hbad | hgood
    · exact False.elim (hbad.2.1 hcross)
    · exact ⟨hgood.1, hgood.2.2.1, hgood.2.2.2⟩
  have hsecond :
      ¬ IsResidual R v b ∧
        D.value v b + 1 ≤ D.value a v ∧
        D.value v b + (1 : ℝ) / 2 < (n : ℝ) := by
    rcases standardResidual_intermediate_forces_subhalf_opposite_child
      D hdeltaHalf ht hwidth hav hvb hresAB with hgood | hbad
    · exact ⟨hgood.2.1, hgood.2.2.1, hgood.2.2.2⟩
    · exact False.elim (hbad.1 hcross)
  exact ⟨hcross, hfirst.1, hsecond.1, hfirst.2.1,
    hsecond.2.1, hfirst.2.2, hsecond.2.2⟩

#print axioms standardResidual_crossing_forces_two_subhalf_flanks

end DirectionData
end JSP000404Research
