import JSP000404Research.PlanarNetNineCentreTwinTradeoff
import JSP000404Research.ResidualNetCollisionShadowFirstHitGlobalCharge
import Mathlib.Tactic

/-!
# Genuine planar AngleCap SOFT first-hit global NET reuse capacity

Using actual centre projection cycles and the real AngleCap one-layer
bound, all genuinely hit diagonal targets (one first source each)
AND actual duplicate excess NET debt are bounded by at most choose(n,2)
Hamming-two target uses of every ACTUAL covered SOFT shadow word.

The result does NOT declare that these SOFT words are TRUE Boolean
holes or unreserved dyadic payment; the unrestricted six-source
global inequality remains open.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_soft_first_hit_global_reuse_bound
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
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by
      rw [ht]
      linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss +
          (netCollisionCertifiedDiagonalWords B k hexp honeLoss).card ≤
          (softOverlapCompletionWords B).card * Nat.choose n 2 := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hdelta1 : delta < 1 := by linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss +
          (netCollisionCertifiedDiagonalWords B k hexp honeLoss).card ≤
          (softOverlapCompletionWords B).card * Nat.choose n 2
  have hstrict : ∀ i : ProjectionOrdered V, k i < n := by
    intro i
    exact centreExponent_lt_n (cycles i) n delta t
      hn hdelta0 hdelta1 ht
  have hexp : ∀ i : ProjectionOrdered V, k i ≤ n :=
    fun i => (hstrict i).le
  have honeLoss :
      ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1 := by
    intro i
    exact planarStandardResidual_active_card_le_oneLayer
      hp hcap hn hdelta0 hdelta1 ht hlam i (cycles i)
  exact ⟨hexp, honeLoss,
    net_duplicate_plus_distinct_hits_le_choose_soft_mass
      B k hexp honeLoss⟩


#print axioms planar_net_soft_first_hit_global_reuse_bound

end ProjectionOrdered
end JSP000404Research
