import JSP000404Research.ExplicitCutRayCycle
import JSP000404Research.CutSaturatedEndpointDichotomy
import JSP000404Research.CutNormalizedPhase
import JSP000404Research.TurnUnitGapBridge
import JSP000404Research.TurnUnitPhaseInterval
import Mathlib.Tactic

/-!
# Return a saturated cut seam to one canonical whole-unit turn slot

At a saturated centre whose 0/n merge does not collide, the cut-wrap gap has
quotient q>=2 and carries an offset j<q (SaturatedSeamPhaseArithmetic).

Choose the explicit cut cycle obtained from the canonical split

  C.rays = low ++ high,
  R.rays = high ++ low.

The wrap gap of R is then visibly one fixed canonical cyclic gap:

* if low and high are both nonempty, it is the ordinary canonical gap
  last(low) -> first(high);
* if one side is empty, it is the canonical wrap gap.

The cut phase belongs to the periodic delta bad interval of the corresponding
CentreTurnUnitSlot at offset j.  Thus the obstruction is cut-independent and
can be counted globally.
-/

namespace JSP000404Research

theorem get_cons_append_cons_at_tail_length
    {α : Type*}
    (a : α) (as : List α) (b : α) (bs : List α) :
    ((a :: as) ++ b :: bs).get
        ⟨as.length, by simp⟩
      =
    as.getLastD a := by
  induction as generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      simpa [List.getLastD_cons] using ih x

theorem get_cons_append_cons_at_next
    {α : Type*}
    (a : α) (as : List α) (b : α) (bs : List α) :
    ((a :: as) ++ b :: bs).get
        ⟨as.length + 1, by simp⟩
      =
    b := by
  induction as generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      simpa using ih x

theorem get_cons_at_tail_length
    {α : Type*}
    (a : α) (as : List α) :
    (a :: as).get ⟨as.length, by simp⟩ =
      as.getLastD a := by
  induction as generalizing a with
  | nil => simp
  | cons x xs ih =>
      simpa [List.getLastD_cons] using ih x

namespace CentreCutRayCycle

/-- Read the first and last normalized values from an explicit cons
presentation of the cut ray cycle. -/
theorem normalizedValues_head_last_of_rays_cons
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : R.rays = first :: rest)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs) :
    a = cutNormalizedRayTheta hp t c i first ∧
      xs.getLastD a =
        cutNormalizedRayTheta hp t c i
          (rest.getLastD first) := by
  unfold CentreCutRayCycle.normalizedValues at hvalues
  rw [hrays] at hvalues
  simp only [List.map_cons] at hvalues
  have hhead := (List.cons.inj hvalues).1
  have htail := (List.cons.inj hvalues).2
  constructor
  · exact hhead.symm
  · rw [hhead.symm, ← htail, map_getLastD]

end CentreCutRayCycle

/-- Main canonicalization theorem. -/
theorem exists_canonical_large_turnUnit_bad_of_cut_saturated_failure
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hsat :
      centreExponent C t +
        (BinaryEdgePartition.active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i).card
        =
      n + 1)
    (hfail :
      ¬ (
        (0 : Fin (n + 1)) ∈
          BinaryEdgePartition.active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
        ∧
        Fin.last n ∈
          BinaryEdgePartition.active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
      )) :
    ∃ u : CentreTurnUnitSlot C t,
      2 ≤ centreTurnUnitGapQuotient C t u ∧
      CentreCyclicTurnUnitBadAt
        C t delta u (t * c / Real.pi) := by
  obtain ⟨low, high, R, hdecomp, hlow, hhigh, hRays⟩ :=
    exists_centreCutRayCycle_with_split hp C c
  obtain ⟨a, xs, hvalues, hseam⟩ :=
    R.saturated_failure_has_wrap_unit_subslot_data
      hp hcap hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hsat hfail
  let z := xs.getLastD a
  let s := a + t - z
  let q := Nat.floor s
  let j := saturatedSeamIndex n z
  have hseam' :
      2 ≤ q ∧ j < q ∧
      ((j : ℝ) + s - (q : ℝ) < t - z) ∧
      (t - z ≤ (j : ℝ) + delta) := by
    simpa [z, s, q, j] using hseam

  cases low with
  | nil =>
      -- All rays lie on/above the cut.  The cut-wrap seam is the canonical
      -- wrap gap, but its universal-cover start is shifted back by one period.
      cases high with
      | nil =>
          have : C.rays = [] := by simpa using hdecomp
          exact False.elim (C.nonempty this)
      | cons first rest =>
          have hCRays : C.rays = first :: rest := by
            simpa using hdecomp
          have hRRays : R.rays = first :: rest := by
            simpa using hRays
          have hv :=
            R.normalizedValues_head_last_of_rays_cons
              first rest hRRays hvalues
          have haEq := hv.1
          have hzEq : z =
              cutNormalizedRayTheta hp t c i
                (rest.getLastD first) := by
            simpa [z] using hv.2
          have hfirstHigh :
              c ≤ rayThetaAt hp i first :=
            hhigh first (by simp)
          have hlastHigh :
              c ≤ rayThetaAt hp i (rest.getLastD first) :=
            hhigh _ (by
              exact List.getLastD_mem_cons first rest)
          have hsCanon :
              s =
                t * ((rayThetaAt hp i first + Real.pi -
                  rayThetaAt hp i (rest.getLastD first)) /
                    Real.pi) := by
            dsimp [s]
            rw [haEq, hzEq,
              cutNormalizedRayTheta_eq_normalized_sub_phase_of_ge
                hp t first hfirstHigh,
              cutNormalizedRayTheta_eq_normalized_sub_phase_of_ge
                hp t (rest.getLastD first) hlastHigh]
            unfold normalizedRayTheta
            field_simp [Real.pi_ne_zero]
            ring
          have hfloor :
              wrapRayQuotient hp i t first
                  (rest.getLastD first) = q := by
            unfold wrapRayQuotient
            dsimp [q]
            rw [← hsCanon]
          obtain ⟨u, huIdx, huOff, huQ⟩ :=
            exists_centreTurnUnitSlot_of_wrap_floor
              C t first rest hCRays q j hfloor hseam'.2.1
          have hlen :
              centreTurnUnitGapScaledLength C t u = s := by
            rw [centreTurnUnitGapScaledLength_eq_wrap
              C t u first rest hCRays huIdx]
            exact hsCanon.symm
          have hm : rest.length < C.rays.length := by
            rw [hCRays]
            simp
          have hget :
              C.rays.get ⟨rest.length, hm⟩ =
                rest.getLastD first := by
            rw [hCRays]
            exact get_cons_at_tail_length first rest
          have hstart :
              centreTurnUnitStart C t u =
                normalizedRayTheta hp t i
                    (rest.getLastD first) + j := by
            rw [centreTurnUnitStart_eq_adjacent_left
              C t u rest.length hm huIdx,
              hget, huOff]
          have hbeta :
              t - z =
                t * c / Real.pi + t -
                  normalizedRayTheta hp t i
                    (rest.getLastD first) := by
            rw [hzEq,
              cutNormalizedRayTheta_eq_normalized_sub_phase_of_ge
                hp t (rest.getLastD first) hlastHigh]
            ring
          refine ⟨u, ?_, ?_⟩
          · rw [huQ]
            exact hseam'.1
          · unfold CentreCyclicTurnUnitBadAt
          refine ⟨(-1 : ℤ), ?_, ?_⟩
          dsimp
          rw [hstart, hlen, huQ]
          unfold positiveGapBadLeft positiveGapBadRight
          norm_num
          constructor
          · have hlo := hseam'.2.2.1
            rw [hbeta] at hlo
            linarith
          · have hhi := hseam'.2.2.2
            rw [hbeta] at hhi
            linarith
  | cons lowFirst lowRest =>
      cases high with
      | nil =>
          -- All rays lie below the cut.  The seam is again the canonical
          -- wrap gap, now with no period correction.
          have hCRays : C.rays = lowFirst :: lowRest := by
            simpa using hdecomp
          have hRRays : R.rays = lowFirst :: lowRest := by
            simpa using hRays
          have hv :=
            R.normalizedValues_head_last_of_rays_cons
              lowFirst lowRest hRRays hvalues
          have haEq := hv.1
          have hzEq : z =
              cutNormalizedRayTheta hp t c i
                (lowRest.getLastD lowFirst) := by
            simpa [z] using hv.2
          have hfirstLow :
              rayThetaAt hp i lowFirst < c :=
            hlow lowFirst (by simp)
          have hlastLow :
              rayThetaAt hp i (lowRest.getLastD lowFirst) < c :=
            hlow _ (List.getLastD_mem_cons lowFirst lowRest)
          have hsCanon :
              s =
                t * ((rayThetaAt hp i lowFirst + Real.pi -
                  rayThetaAt hp i (lowRest.getLastD lowFirst)) /
                    Real.pi) := by
            dsimp [s]
            rw [haEq, hzEq,
              cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt
                hp t lowFirst hfirstLow,
              cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt
                hp t (lowRest.getLastD lowFirst) hlastLow]
            unfold normalizedRayTheta
            field_simp [Real.pi_ne_zero]
            ring
          have hfloor :
              wrapRayQuotient hp i t lowFirst
                  (lowRest.getLastD lowFirst) = q := by
            unfold wrapRayQuotient
            dsimp [q]
            rw [← hsCanon]
          obtain ⟨u, huIdx, huOff, huQ⟩ :=
            exists_centreTurnUnitSlot_of_wrap_floor
              C t lowFirst lowRest hCRays
              q j hfloor hseam'.2.1
          have hlen :
              centreTurnUnitGapScaledLength C t u = s := by
            rw [centreTurnUnitGapScaledLength_eq_wrap
              C t u lowFirst lowRest hCRays huIdx]
            exact hsCanon.symm
          have hm : lowRest.length < C.rays.length := by
            rw [hCRays]
            simp
          have hget :
              C.rays.get ⟨lowRest.length, hm⟩ =
                lowRest.getLastD lowFirst := by
            rw [hCRays]
            exact get_cons_at_tail_length lowFirst lowRest
          have hstart :
              centreTurnUnitStart C t u =
                normalizedRayTheta hp t i
                    (lowRest.getLastD lowFirst) + j := by
            rw [centreTurnUnitStart_eq_adjacent_left
              C t u lowRest.length hm huIdx,
              hget, huOff]
          have hbeta :
              t - z =
                t * c / Real.pi -
                  normalizedRayTheta hp t i
                    (lowRest.getLastD lowFirst) := by
            rw [hzEq,
              cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt
                hp t (lowRest.getLastD lowFirst) hlastLow]
            ring
          refine ⟨u, ?_, ?_⟩
          · rw [huQ]
            exact hseam'.1
          · unfold CentreCyclicTurnUnitBadAt
          refine ⟨(0 : ℤ), ?_, ?_⟩
          dsimp
          rw [hstart, hlen, huQ]
          unfold positiveGapBadLeft positiveGapBadRight
          norm_num
          constructor
          · have hlo := hseam'.2.2.1
            rw [hbeta] at hlo
            linarith
          · have hhi := hseam'.2.2.2
            rw [hbeta] at hhi
            linarith
      | cons highFirst highRest =>
          -- Genuine split: the seam is the ordinary canonical gap from the
          -- last low ray to the first high ray.
          have hCRays :
              C.rays =
                (lowFirst :: lowRest) ++
                  (highFirst :: highRest) := by
            simpa using hdecomp
          have hRRays :
              R.rays =
                highFirst ::
                  (highRest ++ (lowFirst :: lowRest)) := by
            simpa [List.append_assoc] using hRays
          have hv :=
            R.normalizedValues_head_last_of_rays_cons
              highFirst
              (highRest ++ (lowFirst :: lowRest))
              hRRays hvalues
          have haEq := hv.1
          have hlastAppend :
              (highRest ++ (lowFirst :: lowRest)).getLastD highFirst =
                lowRest.getLastD lowFirst := by
            exact getLastD_append_cons
              highRest lowFirst lowRest highFirst
          have hzEq : z =
              cutNormalizedRayTheta hp t c i
                (lowRest.getLastD lowFirst) := by
            have hz0 := hv.2
            rw [hlastAppend] at hz0
            simpa [z] using hz0
          have hfirstHigh :
              c ≤ rayThetaAt hp i highFirst :=
            hhigh highFirst (by simp)
          have hlastLow :
              rayThetaAt hp i (lowRest.getLastD lowFirst) < c :=
            hlow _ (List.getLastD_mem_cons lowFirst lowRest)
          have hsCanon :
              s =
                t * ((rayThetaAt hp i highFirst -
                  rayThetaAt hp i (lowRest.getLastD lowFirst)) /
                    Real.pi) := by
            dsimp [s]
            rw [haEq, hzEq,
              cutNormalizedRayTheta_eq_normalized_sub_phase_of_ge
                hp t highFirst hfirstHigh,
              cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt
                hp t (lowRest.getLastD lowFirst) hlastLow]
            unfold normalizedRayTheta
            ring
          let m := lowRest.length
          have hm :
              m + 1 < C.rays.length := by
            dsimp [m]
            rw [hCRays]
            simp
          have hleft :
              C.rays.get ⟨m, by omega⟩ =
                lowRest.getLastD lowFirst := by
            dsimp [m]
            rw [hCRays]
            exact get_cons_append_cons_at_tail_length
              lowFirst lowRest highFirst highRest
          have hright :
              C.rays.get ⟨m + 1, hm⟩ =
                highFirst := by
            dsimp [m]
            rw [hCRays]
            exact get_cons_append_cons_at_next
              lowFirst lowRest highFirst highRest
          have hfloor :
              Nat.floor
                (t * ((rayThetaAt hp i
                    (C.rays.get ⟨m + 1, hm⟩) -
                  rayThetaAt hp i
                    (C.rays.get ⟨m, by omega⟩)) /
                    Real.pi))
                =
              q := by
            rw [hright, hleft]
            dsimp [q]
            rw [← hsCanon]
          obtain ⟨u, huIdx, huOff, huQ⟩ :=
            exists_centreTurnUnitSlot_of_adjacent_floor
              C t m q j hm hfloor hseam'.2.1
          have hlen :
              centreTurnUnitGapScaledLength C t u = s := by
            rw [centreTurnUnitGapScaledLength_eq_adjacent
              C t u m hm huIdx, hright, hleft]
            exact hsCanon.symm
          have hstart :
              centreTurnUnitStart C t u =
                normalizedRayTheta hp t i
                    (lowRest.getLastD lowFirst) + j := by
            rw [centreTurnUnitStart_eq_adjacent_left
              C t u m (by omega) huIdx,
              hleft, huOff]
          have hbeta :
              t - z =
                t * c / Real.pi -
                  normalizedRayTheta hp t i
                    (lowRest.getLastD lowFirst) := by
            rw [hzEq,
              cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt
                hp t (lowRest.getLastD lowFirst) hlastLow]
            ring
          refine ⟨u, ?_, ?_⟩
          · rw [huQ]
            exact hseam'.1
          · unfold CentreCyclicTurnUnitBadAt
          refine ⟨(0 : ℤ), ?_, ?_⟩
          dsimp
          rw [hstart, hlen, huQ]
          unfold positiveGapBadLeft positiveGapBadRight
          norm_num
          constructor
          · have hlo := hseam'.2.2.1
            rw [hbeta] at hlo
            linarith
          · have hhi := hseam'.2.2.2
            rw [hbeta] at hhi
            linarith

/-- Backward-compatible form retaining only the periodic badness witness. -/
theorem exists_canonical_turnUnit_bad_of_cut_saturated_failure
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hsat :
      centreExponent C t +
        (BinaryEdgePartition.active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i).card
        =
      n + 1)
    (hfail :
      ¬ (
        (0 : Fin (n + 1)) ∈
          BinaryEdgePartition.active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
        ∧
        Fin.last n ∈
          BinaryEdgePartition.active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
      )) :
    ∃ u : CentreTurnUnitSlot C t,
      CentreCyclicTurnUnitBadAt
        C t delta u (t * c / Real.pi) := by
  obtain ⟨u, _huLarge, hubad⟩ :=
    exists_canonical_large_turnUnit_bad_of_cut_saturated_failure
      hp hcap hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi C hsat hfail
  exact ⟨u, hubad⟩

#print axioms exists_canonical_large_turnUnit_bad_of_cut_saturated_failure
#print axioms exists_canonical_turnUnit_bad_of_cut_saturated_failure

end JSP000404Research
