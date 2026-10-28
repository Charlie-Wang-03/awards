import JSP000404Research.ActualExteriorBicolourFibrePacking
import JSP000404Research.PlanarOverweightCanonicalActiveShortfallWitness
import Mathlib.Tactic

/-!
# Original planar AngleCap: true exterior collision fibres pay bichromatic owners

This transports the certified source-native bicolour q-fibre packing
bound to the ACTUAL Sendov / JSP-000404 planar lower branch, using the
canonical projected centre order, genuine centre projective cycles,
the actual standard residual colouring, and the existing
projectedLossActiveFlipChoice construction.

No extra choice-existence hypothesis is required, and no fictitious
credit or original centre is introduced. The resulting estimate is a
necessary local geometry constraint and does NOT establish the
global AngleCap eight-debt payment or remove the original root sorry.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- In every ACTUAL lower-branch AngleCap configuration, there is a
canonical retained-active loss coordinate choice for which EACH
genuine exterior q-fibre consumes TWO distinct genuine bichromatic
projected-loss centres per earliest-prior source record. The bound
is independent of the number of original points and of n. -/
theorem planar_lower_branch_exterior_fibre_twice_le_bichromatic_loss_centres
    {V : Type*} [Fintype V]
    {p : V → Plane}
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∃ choice : ProjectionOrdered V → Fin n,
      (∀ v ∈ projectedLossVertices B k,
        choice v ∈ retainedActive B v) ∧
      (∀ q ∈ lossLedgerOutsideTranslatedTrueHoles B k choice,
        2 * (actualLossOppositeCandidateFibre B k choice q).card ≤
          ((projectedLossVertices B k).filter (fun v =>
            ∃ c d : Fin n, c ≠ d ∧
              c ∈ retainedActive B v ∧
              d ∈ retainedActive B v)).card) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  have hdelta1 : delta < 1 := by linarith
  have hexp : ∀ v : ProjectionOrdered V, k v ≤ n := by
    intro v
    exact Nat.le_of_lt
      (centreExponent_lt_n (cycles v) n delta t
        hn hdelta0 hdelta1 ht)
  let choice : ProjectionOrdered V → Fin n :=
    projectedLossActiveFlipChoice B k hexp hn
  have hactive : ∀ v ∈ projectedLossVertices B k,
      choice v ∈ retainedActive B v := by
    intro v hv
    exact projectedLossActiveFlipChoice_mem_retainedActive
      B k hexp hn hv
  change ∃ choice : ProjectionOrdered V → Fin n,
    (∀ v ∈ projectedLossVertices B k,
      choice v ∈ retainedActive B v) ∧
    (∀ q ∈ lossLedgerOutsideTranslatedTrueHoles B k choice,
      2 * (actualLossOppositeCandidateFibre B k choice q).card ≤
        ((projectedLossVertices B k).filter (fun v =>
          ∃ c d : Fin n, c ≠ d ∧
            c ∈ retainedActive B v ∧
            d ∈ retainedActive B v)).card)
  refine ⟨choice, hactive, ?_⟩
  intro q hq
  exact actual_any_width_true_exterior_opposite_fibre_twice_card_le_bichromatic_centres
    B k choice q hq hactive

#print axioms planar_lower_branch_exterior_fibre_twice_le_bichromatic_loss_centres

end ProjectionOrdered
end JSP000404Research
