import JSP000404Research.PlanarCrossingHardCredit
import JSP000404Research.StandardResidualCrossingSafeFlipDescent
import Mathlib.Tactic

/-!
# True planar crossing hard-word carrier: a finite-ranking flip obstruction

For real AngleCap projected planar vertices u<a<v<b, suppose uv and ab
are unsafe common-word hard carriers. Assume high actual canonical
exponent mass n <= k(a)+k(v), plus SameRetained(a,v) and absence of
a common inactive retained coordinate.

The previously proven DirectionData descent theorem gives a *specific*
safe coordinate c at the crossing edge a<v. Either:
(1) no vertex has the exact flipped canonical retained code,
(2) an interior blocker creates a retained-separated residual child, or
(3) an exterior blocker lies right of v and its retained edge v--w has
colour strictly below c (a natural-number rank decrease).

These are the actual canonical projective-cycle exponents of the planar
configuration, rather than an arbitrary weighted DirectionData profile.

No case claims a hole in the union of retained COMPLETION CUBES.
Such a global hole / no-double-charge theorem is still missing.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

theorem planar_crossing_unsafe_high_mass_flip_hole_resolve_or_descend
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
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      (∃ wordUV wordAB : Fin n → Bool,
        (¬ ∃ c : Fin n, c ∉ residualForbidden B u v) ∧
        (¬ ∃ c : Fin n, c ∉ residualForbidden B a b) ∧
        wordUV ∈ retainedCompletionWords B u ∧
        wordUV ∈ retainedCompletionWords B v ∧
        wordAB ∈ retainedCompletionWords B a ∧
        wordAB ∈ retainedCompletionWords B b) ∧
      n ≤ k a + k v ∧
      SameRetained B a v ∧
      (¬ ∃ c : Fin n,
        c ∉ retainedActive B a ∧
        c ∉ retainedActive B v)) :
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
    ∃ c : Fin n,
      c ∉ residualForbidden B a v ∧
      c ∈ outgoingRetained B a ∧
      c ∉ retainedActive B v ∧
      ((¬ ∃ w : ProjectionOrdered V,
          (fun d => retainedBit B w d) =
            flippedRetainedCode B a c) ∨
        (∃ w : ProjectionOrdered V,
          a < w ∧ w < v ∧
          IsResidual B w v ∧ RetainedSeparated B w v) ∨
        (∃ w : ProjectionOrdered V,
          v < w ∧
          (fun d => retainedBit B w d) =
            flippedRetainedCode B a c ∧
          (B.color v w).val < c.val)) := by
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
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap hpos hlam i (cycles i)
  change
    (∃ wordUV wordAB : Fin n → Bool,
      (¬ ∃ c : Fin n, c ∉ residualForbidden B u v) ∧
      (¬ ∃ c : Fin n, c ∉ residualForbidden B a b) ∧
      wordUV ∈ retainedCompletionWords B u ∧
      wordUV ∈ retainedCompletionWords B v ∧
      wordAB ∈ retainedCompletionWords B a ∧
      wordAB ∈ retainedCompletionWords B b) ∧
    n ≤ k a + k v ∧
    SameRetained B a v ∧
    (¬ ∃ c : Fin n,
      c ∉ retainedActive B a ∧
      c ∉ retainedActive B v) at hHard
  obtain ⟨⟨wordUV, wordAB, hunsafeUV, hunsafeAB,
    huWord, hvWord, haWord, hbWord⟩,
    hmass, hsame, hnoCommon⟩ := hHard
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
  have hmain :=
    crossing_unsafe_hard_high_mass_middle_flip_hole_resolve_or_descend
      D n hn hdeltaHalf ht hwidth k hexp hone
      hua hav hvb hunsafeUV hunsafeAB huWord hvWord haWord hbWord
      hmass hsame hnoCommon
  exact hmain

#print axioms planar_crossing_unsafe_high_mass_flip_hole_resolve_or_descend

end ProjectionOrdered
end JSP000404Research
