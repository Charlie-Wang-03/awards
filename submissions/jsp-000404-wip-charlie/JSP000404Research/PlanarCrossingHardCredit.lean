import JSP000404Research.StandardResidualCrossingHardCredit
import JSP000404Research.PlanarCrossingResidualAngleSeparation
import JSP000404Research.DirectionDataOneLayerProfileAnyWidth
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# Geometric crossing-hard compensation in genuine planar configurations

Under t=n+delta and 0<=delta<1/2, let four canonical projection ordered
planar vertices satisfy u<a<v<b. Suppose the outer pairs uv and ab
each carry an ACTUAL overlapping Boolean completion word, and both pairs
are unsafe (no retained one-flip source coordinate).

Their middle cross edge av is residual. Its forward physical direction
is at least lambda above BOTH outer flank directions ua and vb.
Furthermore, either:
  * the middle cross edge av has a safe local flip coordinate, OR
  * the true canonical centre exponents satisfy k(a)+k(v)+1<=n.

The exact centre exponents are supplied by the verified
projectionCutLocalCycle relation, not chosen abstractly.
The safe flip coordinate need not be a globally uncovered completion
word: the global hard payment remains an open theorem.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

theorem planar_crossing_unsafe_hard_words_angle_or_exponent_credit
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (u a v b : ProjectionOrdered V)
    (hua :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      u < a)
    (hav :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < v)
    (hvb :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      v < b)
    (hHard :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let hpos : 0 < t := by
        rw [ht]
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      let hwidth : t < ((n + 1 : ℕ) : ℝ) := by
        rw [ht]
        push_cast
        linarith
      let D := genericDirectionData_sendov hp hcap hpos hlam
      let B := standardResidualColoring D n hwidth
      ∃ wordUV wordAB : Fin n → Bool,
        (¬ ∃ c : Fin n, c ∉ residualForbidden B u v) ∧
        (¬ ∃ c : Fin n, c ∉ residualForbidden B a b) ∧
        wordUV ∈ retainedCompletionWords B u ∧
        wordUV ∈ retainedCompletionWords B v ∧
        wordAB ∈ retainedCompletionWords B a ∧
        wordAB ∈ retainedCompletionWords B b) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let hpos : 0 < t := by
      rw [ht]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < ((n + 1 : ℕ) : ℝ) := by
      rw [ht]
      push_cast
      linarith
    let D := genericDirectionData_sendov hp hcap hpos hlam
    let B := standardResidualColoring D n hwidth
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    let phiUA :=
      centreForwardLiftedAngle hp u ⟨a, ne_of_gt hua⟩
    let phiAV :=
      centreForwardLiftedAngle hp a ⟨v, ne_of_gt hav⟩
    let phiVB :=
      centreForwardLiftedAngle hp v ⟨b, ne_of_gt hvb⟩
    IsResidual B a v ∧
      phiUA + lam ≤ phiAV ∧
      phiVB + lam ≤ phiAV ∧
      ((∃ c : Fin n, c ∉ residualForbidden B a v) ∨
        k a + k v + 1 ≤ n) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < ((n + 1 : ℕ) : ℝ) := by
    rw [ht]
    push_cast
    linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap hpos hlam i (cycles i)
  let phiUA := centreForwardLiftedAngle hp u ⟨a, ne_of_gt hua⟩
  let phiAV := centreForwardLiftedAngle hp a ⟨v, ne_of_gt hav⟩
  let phiVB := centreForwardLiftedAngle hp v ⟨b, ne_of_gt hvb⟩
  change IsResidual B a v ∧
    phiUA + lam ≤ phiAV ∧
    phiVB + lam ≤ phiAV ∧
    ((∃ c : Fin n, c ∉ residualForbidden B a v) ∨
      k a + k v + 1 ≤ n)
  change ∃ wordUV wordAB : Fin n → Bool,
    (¬ ∃ c : Fin n, c ∉ residualForbidden B u v) ∧
    (¬ ∃ c : Fin n, c ∉ residualForbidden B a b) ∧
    wordUV ∈ retainedCompletionWords B u ∧
    wordUV ∈ retainedCompletionWords B v ∧
    wordAB ∈ retainedCompletionWords B a ∧
    wordAB ∈ retainedCompletionWords B b at hHard
  obtain ⟨wordUV, wordAB, hunsafeUV, hunsafeAB,
    huWord, hvWord, haWord, hbWord⟩ := hHard
  have hresUV : IsResidual B u v :=
    isResidual_of_retainedCompletion_overlap_lt
      B (hua.trans hav) huWord hvWord
  have hresAB : IsResidual B a b :=
    isResidual_of_retainedCompletion_overlap_lt
      B (hav.trans hvb) haWord hbWord
  have hgeom :=
    planar_crossing_residual_forces_two_full_lambda_angle_gaps
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      u a v b hua hav hvb ⟨hresUV, hresAB⟩
  change
    IsResidual B a v ∧
      ¬ IsResidual B u a ∧ ¬ IsResidual B v b ∧
      phiUA + lam ≤ phiAV ∧ phiVB + lam ≤ phiAV ∧
      lam < Real.pi - (phiUA -
        projectionAngleBase (genericProjectionSlope p)) ∧
      lam < Real.pi - (phiVB -
        projectionAngleBase (genericProjectionSlope p)) ∧
      D.value u a + (1 : ℝ) / 2 < (n : ℝ) ∧
      D.value v b + (1 : ℝ) / 2 < (n : ℝ) at hgeom
  obtain ⟨hcross, _, _, hgapUA, hgapVB, _, _, _, _⟩ := hgeom
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hprof :
      (∀ i : ProjectionOrdered V, (L i).exponent ≤ n) ∧
      (∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - (L i).exponent + 1) := by
    exact localCycles_standardResidual_oneLayer_profile
      (n := n) D hwidthR L
  have hExp : ∀ i : ProjectionOrdered V,
      (L i).exponent = k i := by
    intro i
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap hpos hlam i (cycles i)
  have hexp : ∀ i, k i ≤ n := by
    intro i
    rw [← hExp i]
    exact hprof.1 i
  have hone : ∀ i, (active B i).card ≤ n - k i + 1 := by
    intro i
    rw [← hExp i]
    exact hprof.2 i
  have hhard :=
    crossing_unsafe_hard_carriers_halfband_safe_or_exponent_credit
      D hdeltaHalf ht hwidth k hexp hone
      hua hav hvb hunsafeUV hunsafeAB
      huWord hvWord haWord hbWord
  have hcredit :
      (∃ c : Fin n, c ∉ residualForbidden B a v) ∨
        k a + k v + 1 ≤ n :=
    hhard.2.2.2.2.2.2.2
  exact ⟨hcross, hgapUA, hgapVB, hcredit⟩

#print axioms planar_crossing_unsafe_hard_words_angle_or_exponent_credit

end ProjectionOrdered
end JSP000404Research
