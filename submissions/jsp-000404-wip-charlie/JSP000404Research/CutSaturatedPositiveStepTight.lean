import JSP000404Research.CutSaturatedSupportMismatch
import JSP000404Research.CutBadOrdinaryMismatchShape
import Mathlib.Tactic

/-!
# Positive ordinary steps are exactly band-tight at saturation

Exact saturation gives pointwise equality of excess contributions between the
cyclic quotient gaps q and the cyclic occupied-band jumps b.

For a positive quotient q, excess(q)=q-1.  Since q<=b, b is positive as well
and excess(b)=b-1.  Therefore q=b.

After removing the wrap coordinate, every positive ordinary cut step is
exactly tight:

  q > 0  ==>  q = b.

Together with the existing q=0,b>0 ==> b=1 mismatch theorem, this gives a
complete local description of every positive ordinary band jump.
-/

namespace JSP000404Research

theorem eq_of_le_excess_eq_of_pos
    {q b : ℕ}
    (hqb : q ≤ b)
    (hex : excess q = excess b)
    (hq : q ≠ 0) :
    q = b := by
  have hb : b ≠ 0 := by
    intro hb0
    subst b
    omega
  unfold excess at hex
  omega

theorem forall₂_positive_eq_of_le_excess_eq
    {qs bs : List ℕ}
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hex :
      List.Forall₂
        (fun q b => excess q = excess b)
        qs bs) :
    List.Forall₂
      (fun q b => q ≠ 0 → q = b)
      qs bs := by
  induction hle generalizing hex with
  | nil =>
      exact List.Forall₂.nil
  | @cons q b qs bs hqb htail ih =>
      cases hex with
      | cons hexHead hexTail =>
          exact List.Forall₂.cons
            (fun hq =>
              eq_of_le_excess_eq_of_pos hqb hexHead hq)
            (ih hexTail)

/-- Full cyclic exact saturation gives q=b at every positive quotient
position. -/
theorem cutSaturationBadAt_positive_steps_band_tight
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n s : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hexp :
      centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = s)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        let qs := linearCyclicGapQuotients t (a :: xs)
        let bs :=
          cyclicBandJumps n ((a :: xs).map Nat.floor)
        List.Forall₂
          (fun q b => q ≠ 0 → q = b)
          qs bs := by
  obtain ⟨R,a,xs,hvalues,hdom,_hqs,_hbs,_hmis,_hunit⟩ :=
    cutSaturationBadAt_support_mismatch_data
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      i hexp hsupport hbad

  let qs := linearCyclicGapQuotients t (a :: xs)
  let bs := cyclicBandJumps n ((a :: xs).map Nat.floor)

  have hqExp :
      listExponent qs = n - 3 := by
    have h := R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    simpa [qs, CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using h

  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]; simp
  have ha0 :=
    (R.normalizedValues_mem_bounds htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise htpos.le
  have hall0 :
      ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact (R.normalizedValues_mem_bounds htpos hc0 hcpi
      (by simpa [hvalues] using hx)).1
  have hallT :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (R.normalizedValues_mem_bounds htpos hc0 hcpi
      (by simpa [hvalues] using hx)).2
  have htTop : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hfloorSorted :
      ((a :: xs).map Nat.floor).Pairwise (· ≤ ·) :=
    floorLabels_pairwise a xs hsorted
  have hfloorBound :
      ∀ q ∈ (a :: xs).map Nat.floor, q ≤ n := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx) ((hallT x hx).trans htTop)
  have hbExp :
      listExponent bs = n - 3 := by
    have h :=
      cyclicBandJumps_exponent_eq_total_sub_distinct
        n (Nat.floor a) (xs.map Nat.floor)
        (by simpa using hfloorSorted)
        (by
          intro q hq
          exact hfloorBound q (by simpa using hq))
    have hoccR :
        (occupiedNatBands (R.normalizedValues t)).card =
          (occupiedCutProjectiveBands hp t c n i).card :=
      R.occupiedNatBands_normalizedValues_card_eq_occupiedCut
        hp htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith)
    have htopFin : t < (n + 1 : ℕ) := by
      rw [ht]
      push_cast
      linarith
    let P :=
      cutProjectiveBandPartition
        hp hcap htpos hlam hc0 hcpi n htopFin
    let exponent : V → ℕ := fun v => centreExponent (C v) t
    have hbad' :
        SaturationCollisionFailure P exponent i := by
      simpa [CutSaturationBadAt, P, exponent, htopFin] using hbad
    have hactive4 :
        (BinaryEdgePartition.active P i).card = 4 := by
      rw [hbad'.1]
      dsimp [exponent]
      rw [hexp]
      omega
    have hactiveOcc :
        (BinaryEdgePartition.active P i).card =
          (occupiedCutProjectiveBands hp t c n i).card := by
      dsimp [P]
      rw [cutProjectiveBandPartition_active_eq_occupied
        hp hcap htpos hlam hc0 hcpi n htopFin i]
    have hocc4 :
        ((a :: xs).map Nat.floor).toFinset.card = 4 := by
      have hoccValues :
          (occupiedNatBands (a :: xs)).card = 4 := by
        rw [hvalues] at hoccR
        omega
      simpa [occupiedNatBands] using hoccValues
    dsimp [bs]
    rw [h, hocc4]
    omega

  have hexLists : listExponent qs = listExponent bs := by
    rw [hqExp,hbExp]
  have hexPoint :=
    forall₂_excess_eq_of_forall₂_le_of_listExponent_eq
      hdom hexLists

  exact ⟨R,a,xs,hvalues,
    forall₂_positive_eq_of_le_excess_eq hdom hexPoint⟩

/-- Ordinary-prefix version: every positive ordinary quotient equals the
corresponding old band jump. -/
theorem cutSaturationBadAt_positive_ordinary_steps_band_tight
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n s : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hexp : centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = s)
    (hbad :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi i) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        List.Forall₂
          (fun q b => q ≠ 0 → q = b)
          ((successiveDiffsFrom a xs).map Nat.floor)
          (successiveNatDiffsFrom (Nat.floor a)
            (xs.map Nat.floor)) := by
  obtain ⟨R,a,xs,hvalues,htight⟩ :=
    cutSaturationBadAt_positive_steps_band_tight
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hexp hsupport hbad

  have hqDecomp :=
    linearCyclicGapQuotients_cons_decompose t a xs
  have hbDecomp :=
    cyclicBandJumps_map_floor_cons_decompose n a xs
  rw [hqDecomp,hbDecomp] at htight

  let qOrd := (successiveDiffsFrom a xs).map Nat.floor
  let bOrd :=
    successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor)
  have hlen : qOrd.length = bOrd.length := by
    dsimp [qOrd,bOrd]
    rw [List.length_map,
      successiveDiffsFrom_length_for_bad_shape,
      successiveNatDiffsFrom_length,
      List.length_map]
  have hprefix :=
    forall₂_left_of_append_of_length
      qOrd
      [Nat.floor (a + t - xs.getLastD a)]
      bOrd
      [(n + 1 - Nat.floor (xs.getLastD a)) + Nat.floor a]
      hlen htight
  exact ⟨R,a,xs,hvalues,by simpa [qOrd,bOrd] using hprefix⟩

#print axioms eq_of_le_excess_eq_of_pos
#print axioms cutSaturationBadAt_positive_steps_band_tight
#print axioms cutSaturationBadAt_positive_ordinary_steps_band_tight

end JSP000404Research
