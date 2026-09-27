import JSP000404Research.ZeroUnitTwoBandRigidity
import JSP000404Research.CutSaturatedEndpointDichotomy
import Mathlib.Tactic

/-!
# Top-bad saturation forces exactly two adjacent cut bands

In the six-point terminal the top centre has exponent n-1.  If it is
saturation-bad for an arbitrary cut, exact one-layer saturation gives

  old active-card = (n+1) - (n-1) = 2.

The saturated-endpoint dichotomy supplies a zero-quotient unit-band crossing
in the cut-sorted normalized value list.  The generic two-band rigidity then
forces the two occupied natural floor bands to be consecutive.

Thus a top-bad cut is not an arbitrary local merge failure: all five top rays
occupy exactly a pair {m,m+1} of adjacent old projective bands.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem top_cutSaturationBad_has_adjacent_occupied_bands
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (top : V)
    (hTopExp :
      centreExponent (C top) t = n - 1)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi top) :
    ∃ R : CentreCutRayCycle hp (C top) c,
      ∃ a xs,
        R.normalizedValues t = a :: xs ∧
        HasZeroQuotientUnitStep a xs ∧
        ∃ m : ℕ,
          occupiedNatBands (R.normalizedValues t) =
            {m, m + 1} := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  have hbad' :
      SaturationCollisionFailure
        P (fun i => centreExponent (C i) t) top := by
    simpa [CutSaturationBadAt, P, htop] using hbad
  rcases hbad' with ⟨hsatCard, hfail⟩

  let R : CentreCutRayCycle hp (C top) c :=
    Classical.choice
      (exists_centreCutRayCycle hp (C top) c)

  have hsat :
      centreExponent (C top) t +
          (active P top).card =
        n + 1 := by
    rw [hsatCard, hTopExp]
    omega

  obtain ⟨a, xs, hvalues, hstep⟩ :=
    R.zeroUnitStep_of_saturated_boundary_collision_failure
      hp hcap (by omega : 1 ≤ n)
      htpos hlam ht hdeltaHalf hc0 hcpi
      hsat hfail

  have hactiveCard :
      (active P top).card = 2 := by
    rw [hsatCard, hTopExp]
    omega

  have hoccupiedCard :
      (occupiedNatBands (R.normalizedValues t)).card = 2 := by
    rw [R.occupiedNatBands_normalizedValues_card_eq_occupiedCut
        hp htpos hc0 hcpi n htop,
      ← cutProjectiveBandPartition_active_eq_occupied
        hp hcap htpos hlam hc0 hcpi n htop top]
    exact hactiveCard

  have hoccupiedCard' :
      (occupiedNatBands (a :: xs)).card = 2 := by
    rw [← hvalues]
    exact hoccupiedCard

  obtain ⟨m, hm⟩ :=
    occupiedNatBands_eq_adjacent_pair_of_card_two_zeroUnit
      hoccupiedCard' hstep

  refine ⟨R, a, xs, hvalues, hstep, m, ?_⟩
  rw [hvalues]
  exact hm

#print axioms top_cutSaturationBad_has_adjacent_occupied_bands

end JSP000404Research
