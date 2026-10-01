import Mathlib.Tactic

/-!
# Lexicographic rank for the weighted hard-state recursion

Track a recursive hard-state branch by two natural parameters:

* payload m: the amount of still-unpaid source mass carried by the branch;
* free dimension d: the inherited common-inactive dimension of the current
  exact residual pair.

The local recursion has two genuine progress modes.

1. Small-capture progress:
     m' < m.
   The free dimension may reset arbitrarily.

2. Full-pair progress:
     m' = m and d < d'.
   The same payload is rematched into a residual pair with strictly larger
   common-inactive dimension.

Equal-mass/equal-dimension full transitions are explicit bijective rematchings
and are contracted rather than counted as progress.

Because d,d' <= n, the single natural-valued rank

  R_n(m,d) = m * (n+1) + (n-d)

strictly decreases in either genuine progress mode.  This is the unified
well-founded measure behind the final weighted augmenting recursion.
-/

namespace JSP000404Research

def weightedHardStateRank
    (n payload freeDim : ℕ) : ℕ :=
  payload * (n + 1) + (n - freeDim)

theorem weightedHardStateRank_lt_of_payload_lt
    {n payload payload' freeDim freeDim' : ℕ}
    (hfree : freeDim ≤ n)
    (hfree' : freeDim' ≤ n)
    (hpayload : payload' < payload) :
    weightedHardStateRank n payload' freeDim' <
      weightedHardStateRank n payload freeDim := by
  unfold weightedHardStateRank
  have hgap :
      payload' * (n + 1) + n <
        payload * (n + 1) := by
    have hstep :
        payload' + 1 ≤ payload := by
      omega
    have hmul :
        (payload' + 1) * (n + 1) ≤
          payload * (n + 1) :=
      Nat.mul_le_mul_right (n + 1) hstep
    omega
  have hleft :
      payload' * (n + 1) + (n - freeDim') ≤
        payload' * (n + 1) + n := by
    omega
  have hright :
      payload * (n + 1) ≤
        payload * (n + 1) + (n - freeDim) := by
    omega
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hgap hright)

theorem weightedHardStateRank_lt_of_dimension_growth
    {n payload freeDim freeDim' : ℕ}
    (hfree : freeDim ≤ n)
    (hfree' : freeDim' ≤ n)
    (hdim : freeDim < freeDim') :
    weightedHardStateRank n payload freeDim' <
      weightedHardStateRank n payload freeDim := by
  unfold weightedHardStateRank
  have hsub :
      n - freeDim' < n - freeDim := by
    omega
  omega

theorem weightedHardStateRank_lt_of_progress
    {n payload payload' freeDim freeDim' : ℕ}
    (hfree : freeDim ≤ n)
    (hfree' : freeDim' ≤ n)
    (hprogress :
      payload' < payload
      ∨
      (payload' = payload ∧ freeDim < freeDim')) :
    weightedHardStateRank n payload' freeDim' <
      weightedHardStateRank n payload freeDim := by
  rcases hprogress with hpayload | hfull
  · exact weightedHardStateRank_lt_of_payload_lt
      hfree hfree' hpayload
  · subst payload'
    exact weightedHardStateRank_lt_of_dimension_growth
      hfree hfree' hfull.2

theorem payload_strictly_decreases_of_half_capture
    {payload captured : ℕ}
    (hpos : 0 < payload)
    (hhalf : 2 * captured ≤ payload)
    (hcaptured : 0 < captured) :
    captured < payload := by
  omega

#print axioms weightedHardStateRank_lt_of_payload_lt
#print axioms weightedHardStateRank_lt_of_dimension_growth
#print axioms weightedHardStateRank_lt_of_progress
#print axioms payload_strictly_decreases_of_half_capture


def lossLayerHardStateRank
    (n payload exponent : ℕ) : ℕ :=
  payload * (n + 1) + exponent

theorem lossLayerHardStateRank_lt_of_payload_lt
    {n payload payload' exponent exponent' : ℕ}
    (hexp : exponent ≤ n)
    (hexp' : exponent' ≤ n)
    (hpayload : payload' < payload) :
    lossLayerHardStateRank n payload' exponent' <
      lossLayerHardStateRank n payload exponent := by
  unfold lossLayerHardStateRank
  have hgap :
      payload' * (n + 1) + n <
        payload * (n + 1) := by
    have hstep : payload' + 1 ≤ payload := by omega
    have hmul :
        (payload' + 1) * (n + 1) ≤
          payload * (n + 1) :=
      Nat.mul_le_mul_right (n + 1) hstep
    omega
  have hleft :
      payload' * (n + 1) + exponent'
        ≤ payload' * (n + 1) + n := by
    omega
  have hright :
      payload * (n + 1) ≤
        payload * (n + 1) + exponent := by
    omega
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hgap hright)

theorem lossLayerHardStateRank_lt_of_exponent_lt
    {n payload exponent exponent' : ℕ}
    (hexp : exponent ≤ n)
    (hexp' : exponent' < exponent) :
    lossLayerHardStateRank n payload exponent' <
      lossLayerHardStateRank n payload exponent := by
  unfold lossLayerHardStateRank
  omega

theorem lossLayerHardStateRank_lt_of_progress
    {n payload payload' exponent exponent' : ℕ}
    (hexp : exponent ≤ n)
    (hexp' : exponent' ≤ n)
    (hprogress :
      payload' < payload
      ∨
      (payload' = payload ∧ exponent' < exponent)) :
    lossLayerHardStateRank n payload' exponent' <
      lossLayerHardStateRank n payload exponent := by
  rcases hprogress with hpayload | ⟨rfl,hexponent⟩
  · exact lossLayerHardStateRank_lt_of_payload_lt
      hexp hexp' hpayload
  · exact lossLayerHardStateRank_lt_of_exponent_lt
      hexp hexponent

#print axioms lossLayerHardStateRank_lt_of_progress

end JSP000404Research
