import JSP000404Research.SupportTwoTransitionClusterBridge
import JSP000404Research.ThreeBandSpectrumRigidity
import JSP000404Research.ZeroUnitStepQuotient
import Mathlib.Tactic

/-!
# Unit-transition support-two band rigidity

A second-layer support-two centre with transition quotient one has canonical
quotient spectrum exactly contained in {0,1,n-1}.  When its projection-cut
local profile uses exactly three non-top bands, saturation transfers this
spectrum to the cyclic band jumps.  ThreeBandSpectrumRigidity then forces the
three occupied bands to be consecutive.
-/

namespace JSP000404Research

theorem supportTwo_transition_one_quotient_spectrum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    (hqe : cert.qe = 1) :
    ∀ q ∈ quotientList t C.gaps,
      q = 0 ∨ q = 1 ∨ q = n - 1 := by
  obtain ⟨pre,post,_gpre,_gpost,_ge,
      leftQ,rightQ,_leftG,_rightG,_gh,
      hq,_hgaps,_hpreLen,_hpostLen,
      hhiddenQ,_hhiddenG,
      _hleftLen,_hrightLen,
      hleftZero,hrightZero,
      _hhiddenAlign,_hzeroWidth⟩ :=
    supportTwo_transition_one_has_two_narrow_zero_blocks
      hcap hn3 hdelta0 hdeltaHalf ht hlam
      C hexp hsupport cert hqe

  have hinternal :
      ∀ q ∈ post ++ pre,
        q = 0 ∨ q = n - 1 := by
    intro q hqmem
    rw [hhiddenQ] at hqmem
    simp only [List.mem_append, List.mem_cons] at hqmem
    rcases hqmem with hleft | hmid | hright
    · exact Or.inl (hleftZero q hleft)
    · exact Or.inr hmid
    · exact Or.inl (hrightZero q hright)

  intro q hqmem
  rw [hq] at hqmem
  simp only [List.mem_append, List.mem_cons] at hqmem
  rcases hqmem with hpre | hmid | hpost
  · have hi := hinternal q (by
      apply List.mem_append_right post
      exact hpre)
    rcases hi with h0 | hN
    · exact Or.inl h0
    · exact Or.inr (Or.inr hN)
  · exact Or.inr (Or.inl hmid)
  · have hi := hinternal q (by
      apply List.mem_append_left pre
      exact hpost)
    rcases hi with h0 | hN
    · exact Or.inl h0
    · exact Or.inr (Or.inr hN)

namespace ProjectionOrdered

theorem projectionCut_unitSupportTwo_threeBands_consecutive
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (cert :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t i C)
    (hqe : cert.qe = 1)
    (hcard :
      (occupiedNatBands
        (projectionCutLocalCycle
          hp hcap
          (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
          hlam i C).values).card = 3)
    (htop :
      n ∉ occupiedNatBands
        (projectionCutLocalCycle
          hp hcap
          (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
          hlam i C).values) :
    ∃ m : ℕ,
      occupiedNatBands
        (projectionCutLocalCycle
          hp hcap
          (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
          hlam i C).values
        =
      {m, m + 1, m + 2} := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let L :=
    projectionCutLocalCycle hp hcap htpos hlam i C

  obtain ⟨a,xs,hvalues⟩ :
      ∃ a xs, L.values = a :: xs := by
    cases hv : L.values with
    | nil =>
        exact False.elim (L.values_nonempty hv)
    | cons a xs =>
        exact ⟨a,xs,hv⟩

  have haMem : a ∈ L.values := by
    rw [hvalues]
    simp
  have ha0 : 0 ≤ a :=
    (L.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (L.value_mem_bounds
        (by simpa [hvalues] using hx)).2
  have hall0 :
      ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact
      (L.value_mem_bounds
        (by simpa [hvalues] using hx)).1

  let qs :=
    (cyclicRealGapsAt t (a :: xs)).map Nat.floor
  let bs :=
    cyclicBandJumps n
      ((a :: xs).map Nat.floor)

  have hle : List.Forall₂ (· ≤ ·) qs bs := by
    dsimp [qs,bs]
    exact cyclicFloorGaps_le_cyclicBandJumps
      a xs n ha0 hsorted hall hwidth

  have hqEq :
      qs = L.gapQuotients := by
    dsimp [qs,L]
    unfold LocalDirectionCycle.gapQuotients
    rw [hvalues]
    rfl

  have hqExp :
      listExponent qs = n - 2 := by
    rw [hqEq]
    have hlocal :=
      projectionCutLocalCycle_exponent_eq_centreExponent
        hp hcap htpos hlam i C
    simpa [L, LocalDirectionCycle.exponent, hexp] using hlocal

  have hfloorSorted :
      ((a :: xs).map Nat.floor).Pairwise (· ≤ ·) :=
    floorLabels_pairwise a xs hsorted

  have hfloorBound :
      ∀ c ∈ (a :: xs).map Nat.floor, c ≤ n := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    have hx0 := hall0 x hx
    exact floorLabel_le_n_of_lt_n_succ
      hx0 (hall x hx |>.trans hwidth)

  have hcardFloor :
      ((a :: xs).map Nat.floor).toFinset.card = 3 := by
    have hc := hcard
    change (occupiedNatBands L.values).card = 3 at hc
    rw [hvalues] at hc
    simpa [occupiedNatBands] using hc

  have hbExp :
      listExponent bs = n - 2 := by
    dsimp [bs]
    have h :=
      cyclicBandJumps_exponent_eq_total_sub_distinct
        n (Nat.floor a) (xs.map Nat.floor)
        (by simpa using hfloorSorted)
        (by
          intro c hc
          exact hfloorBound c (by simpa using hc))
    rw [hcardFloor] at h
    omega

  have hqSpec :
      ∀ q ∈ qs, q = 0 ∨ q = 1 ∨ q = n - 1 := by
    intro q hqmem
    have hqL : q ∈ L.gapQuotients := by
      rw [← hqEq]
      exact hqmem
    have hqCan :
        q ∈ quotientList t C.gaps :=
      mem_centreQuotients_of_mem_projectionCutLocalQuotients
        hp hcap htpos hlam i C hqL
    exact supportTwo_transition_one_quotient_spectrum
      (hp := reindexedPoint_injective hp)
      hcap hn3 hdelta0 hdeltaHalf ht hlam
      C hexp hsupport cert hqe q hqCan

  have hbSpec :
      ∀ b ∈ bs, b = 0 ∨ b = 1 ∨ b = n - 1 :=
    bandJump_spectrum_of_quotient_spectrum
      (N := n - 1) (by omega)
      hle (by rw [hqExp,hbExp]) hqSpec

  have hbelowTop :
      ∀ c ∈ (Nat.floor a :: xs.map Nat.floor),
        c ≤ n - 1 := by
    intro c hc
    have hcMap :
        c ∈ (a :: xs).map Nat.floor := by
      simpa using hc
    have hcn := hfloorBound c hcMap
    have hcNotTop : c ≠ n := by
      intro hcnEq
      apply htop
      change n ∈ occupiedNatBands L.values
      rw [hvalues]
      unfold occupiedNatBands
      rw [List.mem_toFinset]
      simpa [hcnEq] using hcMap
    omega

  obtain ⟨m,hm⟩ :=
    three_occupied_bands_consecutive_of_cyclic_spectrum
      (n := n) (a := Nat.floor a) (xs := xs.map Nat.floor)
      hn3
      (by simpa using hfloorSorted)
      (by simpa using hcardFloor)
      hbelowTop
      (by
        intro b hb
        exact hbSpec b (by
          dsimp [bs] at hb ⊢
          simpa using hb))

  refine ⟨m,?_⟩
  change occupiedNatBands L.values = {m,m+1,m+2}
  rw [hvalues]
  unfold occupiedNatBands
  simpa using hm

#print axioms supportTwo_transition_one_quotient_spectrum
#print axioms projectionCut_unitSupportTwo_threeBands_consecutive

end ProjectionOrdered
end JSP000404Research
