import JSP000404Research.PlanarOverweightHardCarrierPhaseWitness
import JSP000404Research.DirectionDataGlobalOverweightRigidity
import Mathlib.Tactic

/-!
# Geometry-facing endgame dichotomy for an overweight planar configuration

Combining the kernel-checked genuine planar hard-carrier theorem with the
consecutive short-band-crossing ray witness for projected loss yields a
fully concrete disjunction:

1. one centre has a pair of adjacent cut-rotated rays with normalized
   separation in [0,1) whose integer floors cross one band; OR
2. a genuine residual top-band edge has a common retained Boolean word
   and one endpoint whose complete sorted local cyclic gap list is
   stepwise-tight, with exact wrap equality.

The first is an actual local phase slip; the second is an actual
saturated residual collision, not an isolated saturated centre.
No subset-Hall G1 exclusion or independent geometric payment is assumed.
The complete JSP-000404 dyadic upper bound remains open.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

theorem planar_overweight_has_concrete_phase_slip_or_rigid_hard_edge
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < ∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let hpos : 0 < t := by
      rw [ht]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap hpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
      fun i => projectionCutLocalCycle hp hcap hpos hlam i (cycles i)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    (
      ∃ (i : ProjectionOrdered V) (u v : OtherVertex i)
        (pre post : List (OtherVertex i)),
        (L i).rays = pre ++ u :: v :: post ∧
        0 ≤ D.localDirectionValue i v - D.localDirectionValue i u ∧
        D.localDirectionValue i v - D.localDirectionValue i u < 1 ∧
        Nat.floor (D.localDirectionValue i v) -
          Nat.floor (D.localDirectionValue i u) = 1
    ) ∨
    (
      ∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧ IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        Nat.floor (D.value u v) = n ∧
        ∃ i : ProjectionOrdered V,
          (i = u ∨ i = v) ∧
          k i = projectedFree B i ∧
          ∃ a : ℝ, ∃ xs : List ℝ,
            (L i).values = a :: xs ∧
            Nat.floor (xs.getLastD a) = n ∧
            InteriorBandGapTight a xs ∧
            excess (Nat.floor (a + t - xs.getLastD a)) =
              Nat.floor a
    ) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap hpos hlam i (cycles i)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  have hexp : (fun i : ProjectionOrdered V => (L i).exponent) = k := by
    funext i
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap hpos hlam i (cycles i)
  have hcase :=
    planar_overweight_loss_or_hard_carrier_stepwise_top_witness
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hover
  change
    (∃ i : ProjectionOrdered V, i ∈ projectedLossVertices B k) ∨
    (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧ IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        Nat.floor (D.value u v) = n ∧
        ∃ i : ProjectionOrdered V,
          (i = u ∨ i = v) ∧
          k i = projectedFree B i ∧
          ∃ a : ℝ, ∃ xs : List ℝ,
            (L i).values = a :: xs ∧
            Nat.floor (xs.getLastD a) = n ∧
            InteriorBandGapTight a xs ∧
            excess (Nat.floor (a + t - xs.getLastD a)) =
              Nat.floor a) at hcase
  rcases hcase with ⟨i, hiLoss⟩ | hcarrier
  · left
    have hiLossLocal :
        i ∈ projectedLossVertices B
          (fun j => (L j).exponent) := by
      simpa only [hexp] using hiLoss
    obtain ⟨u, v, pre, post, hwords, hnonneg, hshort, hband⟩ :=
      projected_loss_has_consecutive_short_band_crossing_rays
        D hwidth L i hiLossLocal
    exact ⟨i, u, v, pre, post, hwords, hnonneg, hshort, hband⟩
  · exact Or.inr hcarrier

#print axioms planar_overweight_has_concrete_phase_slip_or_rigid_hard_edge

end ProjectionOrdered
end JSP000404Research
