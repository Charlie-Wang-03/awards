import JSP000404Research.ElevenPhaseCut
import JSP000404Research.CutMergedTwoBadRigidity
import Mathlib.Tactic

/-!
# Final two-branch reduction on a critical-uncovered cut

The one-exception merged terminal implies a sharp contrapositive:

  on any critical-uncovered cut, if the top is safe,
  there must be at least two distinct bad minima.

Combining this with the eleven-phase cyclic counting theorem gives, for every
six-point terminal with n>=5, an actual canonical sampled cut at which exactly
one of the two hard mechanisms must remain:

* the top itself is saturation-bad; or
* two distinct non-top centres are saturation-bad.

No third branch remains.
-/

namespace JSP000404Research

theorem uncovered_cut_top_safe_forces_two_bad_minima
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
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTopExp :
      centreExponent (C top) t = n - 1)
    (hMinExp :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (hTopSafe :
      ¬ CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi top) :
    ∃ bad₁ bad₂ : V,
      bad₁ ≠ top ∧
      bad₂ ≠ top ∧
      bad₁ ≠ bad₂ ∧
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₁ ∧
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₂ := by
  by_contra htwo
  have hAtMostOne :
      ∀ {u v : V},
        u ≠ top →
        v ≠ top →
        CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi u →
        CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi v →
        u = v := by
    intro u v hut hvt hu hv
    by_contra huv
    apply htwo
    exact ⟨u, v, hut, hvt, huv, hu, hv⟩

  by_cases hex :
      ∃ bad : V,
        bad ≠ top ∧
        CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi bad
  · obtain ⟨bad, hbt, hbad⟩ := hex
    have hUnique :
        ∀ v : V, v ≠ top →
          CutSaturationBadAt
            hp hcap C htpos hlam ht hdelta0
            (by linarith : delta < 1)
            hc0 hcpi v →
          v = bad := by
      intro v hvt hv
      exact hAtMostOne hvt hbt hv hbad
    exact no_uncovered_cut_with_top_safe_and_atMostOne_bad_minimum
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcard top bad hbt.symm
      hTopExp hMinExp huncovered hTopSafe hUnique
  · have hcardGt : 1 < Fintype.card V := by
      rw [hcard]
      norm_num
    obtain ⟨bad, hbt⟩ :=
      Fintype.exists_ne_of_one_lt_card hcardGt top
    have hUnique :
        ∀ v : V, v ≠ top →
          CutSaturationBadAt
            hp hcap C htpos hlam ht hdelta0
            (by linarith : delta < 1)
            hc0 hcpi v →
          v = bad := by
      intro v hvt hv
      exfalso
      apply hex
      exact ⟨v, hvt, hv⟩
    exact no_uncovered_cut_with_top_safe_and_atMostOne_bad_minimum
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcard top bad hbt.symm
      hTopExp hMinExp huncovered hTopSafe hUnique

/-- Main n>=5 reduction: one canonical eleven-sample cut is critical-uncovered
and leaves only the top-bad or two-bad-minima branch. -/
theorem exists_eleven_cut_top_bad_or_two_bad_minima
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ∃ r : Fin 11,
      let c := projectiveCutOfPhase t (elevenPhase t r)
      0 ≤ c ∧
      c < Real.pi ∧
      (∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi)) ∧
      (
        CutSaturationBadAt
          hp hcap C
          (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
          hlam ht hdelta0
          (by linarith : delta < 1)
          (projectiveCutOfPhase_nonneg
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            (elevenPhase_nonneg
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le r))
          (projectiveCutOfPhase_lt_pi
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            (elevenPhase_lt_t
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht) r))
          top
        ∨
        ∃ bad₁ bad₂ : V,
          bad₁ ≠ top ∧
          bad₂ ≠ top ∧
          bad₁ ≠ bad₂ ∧
          CutSaturationBadAt
            hp hcap C
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            hlam ht hdelta0
            (by linarith : delta < 1)
            (projectiveCutOfPhase_nonneg
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
              (elevenPhase_nonneg
                (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le r))
            (projectiveCutOfPhase_lt_pi
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
              (elevenPhase_lt_t
                (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht) r))
            bad₁ ∧
          CutSaturationBadAt
            hp hcap C
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            hlam ht hdelta0
            (by linarith : delta < 1)
            (projectiveCutOfPhase_nonneg
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
              (elevenPhase_nonneg
                (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le r))
            (projectiveCutOfPhase_lt_pi
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
              (elevenPhase_lt_t
                (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht) r))
            bad₂
      ) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨r, hc0, hcpi, huncovered⟩ :=
    exists_critical_uncovered_eleven_cut
      C hn4 hn5 hdelta0 hdeltaHalf ht
      hcard top hTop hMin
  refine ⟨r, hc0, hcpi, huncovered, ?_⟩
  let c := projectiveCutOfPhase t (elevenPhase t r)
  by_cases hTopBad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi top
  · exact Or.inl hTopBad
  · right
    exact uncovered_cut_top_safe_forces_two_bad_minima
      hp hcap C hn4 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcard top hTop hMin
      huncovered hTopBad

#print axioms uncovered_cut_top_safe_forces_two_bad_minima
#print axioms exists_eleven_cut_top_bad_or_two_bad_minima

end JSP000404Research
