import JSP000404Research.PlanarInteriorPhaseSlipAngle
import JSP000404Research.TriangleSignParity
import Mathlib.Tactic

/-!
# The phase-slip ray pair participates in cross-centre triangle parity

A genuine saturated residual-inactive planar centre has two distinct
neighbouring ray endpoints u,v with forward angular difference < lambda.

The canonical reversal-sign identity forces the triangle (i,u,v) to
have odd sign-transition parity. In particular, if the two short rays
at i have the same canonical sign, then exactly one of the OTHER
two centres u,v sees a sign transition between its two triangle rays.

This gives a checkable cross-centre geometric target for global
phase-slip accounting, but does not yet pay the weighted excess.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

theorem planar_phase_slip_triangle_other_transition
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (htwidth : t < (n : ℝ) + 1)
    (i : ProjectionOrdered V)
    (C : ProjectionCentreCycle hp i)
    (htight :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let L := projectionCutLocalCycle hp hcap htpos hlam i C
      L.exponent + (D.incidentBands (n + 1) i).card = n + 1)
    (hres :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      residualCoord n ∉
        active (standardResidualColoring D n
          (by exact_mod_cast htwidth)) i) :
    ∃ (u v : OtherVertex i) (huv : u.1 ≠ v.1),
      0 ≤ centreForwardLiftedAngle hp i v -
        centreForwardLiftedAngle hp i u ∧
      centreForwardLiftedAngle hp i v -
        centreForwardLiftedAngle hp i u < lam ∧
      (raySignAt (reindexedPoint_injective hp) i u =
         raySignAt (reindexedPoint_injective hp) i v →
        ((raySignAt (reindexedPoint_injective hp) u.1
              ⟨i, u.2.symm⟩ ≠
            raySignAt (reindexedPoint_injective hp) u.1
              ⟨v.1, huv.symm⟩) ∧
          ¬ (raySignAt (reindexedPoint_injective hp) v.1
                ⟨i, v.2.symm⟩ ≠
              raySignAt (reindexedPoint_injective hp) v.1
                ⟨u.1, huv⟩)) ∨
        (¬ (raySignAt (reindexedPoint_injective hp) u.1
                ⟨i, u.2.symm⟩ ≠
              raySignAt (reindexedPoint_injective hp) u.1
                ⟨v.1, huv.symm⟩) ∧
          (raySignAt (reindexedPoint_injective hp) v.1
                ⟨i, v.2.symm⟩ ≠
              raySignAt (reindexedPoint_injective hp) v.1
                ⟨u.1, huv⟩))) := by
  obtain ⟨u, v, hneq, hnonneg, hshort⟩ :=
    planar_tight_residual_inactive_has_short_angle_rays
      hp hcap htpos hlam htwidth i C htight hres
  have huv : u.1 ≠ v.1 := by
    intro heq
    exact hneq (Subtype.ext heq)
  refine ⟨u, v, huv, hnonneg, hshort, ?_⟩
  intro hsame
  exact triangle_exactly_one_other_sign_transition
    (reindexedPoint_injective hp)
    u.2.symm v.2.symm huv hsame

#print axioms planar_phase_slip_triangle_other_transition

end ProjectionOrdered
end JSP000404Research
