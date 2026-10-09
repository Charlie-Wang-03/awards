import JSP000404Research.StandardResidualCrossingRepair
import JSP000404Research.StandardResidualCrossingHalfBand
import Mathlib.Tactic

/-!
# Crossing hard overlap carriers: subhalf flanks plus safe-or-credit exit

For u<a<v<b, suppose the outer residual overlap carriers u--v and a--b
each carry an actual shared Boolean completion word, and are both unsafe
(no locally available retained flip coordinate).

Their forced middle edge a--v is residual. The NEW half-band geometry
makes both outer flanks u--a and v--b strictly lower than n-1/2 and a
full unit below the middle direction.

The OLD unsafe crossing repair, now combined with this structural
witness, says either a--v has a SAFE colour coordinate (a local
hole-flip outlet) OR, if it is also unsafe, then the exponent profile
has one full unit of extra joint saving:

    exponent(a) + exponent(v) + 1 <= n.

This is a precise two-carrier geometric+weighted structural statement,
not a proof the safe local target is globally uncovered. Nor does it
assume the refuted subset Hall G1.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem crossing_unsafe_hard_carriers_halfband_safe_or_exponent_credit
    {V : Type*} [LinearOrder V] [Fintype V]
    {t delta : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hwidth : t < (n + 1 : ℕ))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x,
        (active (standardResidualColoring D n hwidth) x).card
          ≤ n - exponent x + 1)
    {u a v b : V}
    (hua : u < a)
    (hav : a < v)
    (hvb : v < b)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden
        (standardResidualColoring D n hwidth) u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden
        (standardResidualColoring D n hwidth) a b)
    (huWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) u)
    (hvWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) v)
    (haWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) a)
    (hbWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) b) :
    let R := standardResidualColoring D n hwidth
    IsResidual R a v ∧
      ¬ IsResidual R u a ∧
      ¬ IsResidual R v b ∧
      D.value u a + 1 ≤ D.value a v ∧
      D.value v b + 1 ≤ D.value a v ∧
      D.value u a + (1 : ℝ) / 2 < (n : ℝ) ∧
      D.value v b + (1 : ℝ) / 2 < (n : ℝ) ∧
      ((∃ c : Fin n, c ∉ residualForbidden R a v) ∨
        exponent a + exponent v + 1 ≤ n) := by
  let R := standardResidualColoring D n hwidth
  have hresUV : IsResidual R u v :=
    isResidual_of_retainedCompletion_overlap_lt
      R (hua.trans hav) huWord hvWord
  have hresAB : IsResidual R a b :=
    isResidual_of_retainedCompletion_overlap_lt
      R (hav.trans hvb) haWord hbWord
  obtain ⟨hcross, hnotUA, hnotVB, hgapUA, hgapVB,
    hhalfUA, hhalfVB⟩ :=
    standardResidual_crossing_forces_two_subhalf_flanks
      D hdeltaHalf ht hwidth hua hav hvb hresUV hresAB
  have hcredit :
      (∃ c : Fin n, c ∉ residualForbidden R a v) ∨
        exponent a + exponent v + 1 ≤ n := by
    by_cases hsafe :
        ∃ c : Fin n, c ∉ residualForbidden R a v
    · exact Or.inl hsafe
    · right
      exact crossing_unsafe_overlap_cross_exponent_credit
        D hwidth exponent hexp honeLoss hua hav hvb
        hunsafeUV hunsafeAB
        huWord hvWord haWord hbWord hsafe
  exact ⟨hcross, hnotUA, hnotVB, hgapUA, hgapVB,
    hhalfUA, hhalfVB, hcredit⟩

/-- Large centre-exponent mass at the two middle endpoints precludes
an unsafe middle edge for crossing hard carriers: a safe flip must exist.
This is only LOCAL safety, not a globally uncovered completion word. -/
theorem crossing_unsafe_hard_carriers_high_mass_forces_safe_middle
    {V : Type*} [LinearOrder V] [Fintype V]
    {t delta : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hwidth : t < (n + 1 : ℕ))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x,
        (active (standardResidualColoring D n hwidth) x).card
          ≤ n - exponent x + 1)
    {u a v b : V}
    (hua : u < a) (hav : a < v) (hvb : v < b)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden
        (standardResidualColoring D n hwidth) u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden
        (standardResidualColoring D n hwidth) a b)
    (huWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) u)
    (hvWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) v)
    (haWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) a)
    (hbWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) b)
    (hmass : n ≤ exponent a + exponent v) :
    ∃ c : Fin n,
      c ∉ residualForbidden
        (standardResidualColoring D n hwidth) a v := by
  have hpackage :=
    crossing_unsafe_hard_carriers_halfband_safe_or_exponent_credit
      D hdeltaHalf ht hwidth exponent hexp honeLoss
      hua hav hvb hunsafeUV hunsafeAB
      huWord hvWord haWord hbWord
  rcases hpackage.2.2.2.2.2.2.2 with hsafe | hsave
  · exact hsafe
  · omega

#print axioms crossing_unsafe_hard_carriers_halfband_safe_or_exponent_credit
#print axioms crossing_unsafe_hard_carriers_high_mass_forces_safe_middle

end DirectionData
end JSP000404Research
