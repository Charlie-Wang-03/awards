import JSP000404Research.FullQuotientZeroAngleMass
import JSP000404Research.SharpOuterAngles
import JSP000404Research.CyclicEdgeRotation
import JSP000404Research.PinnedCycleRotation
import JSP000404Research.SixPointSeparatedSupportTwo
import Mathlib.Tactic

/-!
# Residual zero-angle budget for a separated support-two minimum

Pin the ray to the sharp top at the front of a deficit-three/support-two centre
and rotate the quotient and actual-angle cycles together.

The complete zero-angle mass is at most (1+delta)*lambda.  If the centre is
not positive-positive pinned at the top ray, at least one of the two end
quotients is zero.  The corresponding actual angle involves the sharp top, so
SharpOuterAngles gives a lower bound (1-delta)*lambda.

Subtracting this one top-adjacent zero angle leaves at most

  2*delta*lambda

for every other zero-quotient angle at that centre.

This is the quantitative geometry carried by the separated support-two witness
forced in SixPointSeparatedSupportTwo.
-/

namespace JSP000404Research

open Real

/-- Zero-quotient angle mass splits across aligned list concatenation. -/
private theorem listZeroAngleMass_append_aligned
    (qs₁ qs₂ : List ℕ) (As₁ As₂ : List ℝ)
    (hlen : qs₁.length = As₁.length) :
    listZeroAngleMass (qs₁ ++ qs₂) (As₁ ++ As₂) =
      listZeroAngleMass qs₁ As₁ + listZeroAngleMass qs₂ As₂ := by
  induction qs₁ generalizing As₁ with
  | nil =>
      have hnil : As₁ = [] :=
        List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst As₁
      simp [listZeroAngleMass]
  | cons q qs ih =>
      cases As₁ with
      | nil => simp at hlen
      | cons A As =>
          simp at hlen
          simp [listZeroAngleMass, ih As hlen, add_assoc]

/-- Rotate an exact deficit-three/support-two centre so the ray to the sharp
top is first, retaining aligned quotient and actual-angle data. -/
theorem exists_sharp_pinned_support_two_deficit_three_shape
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i : V}
    (hit : i ≠ top)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ first0 : OtherVertex i,
      ∃ rest0 : List (OtherVertex i),
      ∃ k : ℕ,
      ∃ pre post : List (OtherVertex i),
      ∃ r : OtherVertex i,
      ∃ rest : List (OtherVertex i),
      ∃ qFirst qLast : ℕ,
      ∃ qmid : List ℕ,
        C.rays = first0 :: rest0 ∧
        C.rays =
          pre ++ (⟨top, hit.symm⟩ : OtherVertex i) :: post ∧
        k = pre.length ∧
        C.rays.rotate k =
          (⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest ∧
        (quotientList t C.gaps).rotate k =
          qFirst :: qmid ++ [qLast] ∧
        listPositiveCount
          (qFirst :: qmid ++ [qLast]) = 2 ∧
        qmid.length =
          (consecutiveRayAngles (p := p) i r rest).length ∧
        listZeroAngleMass
            ((quotientList t C.gaps).rotate k)
            ((cyclicRayAngles (p := p) i first0 rest0).rotate k)
          ≤ (1 + delta) * lam ∧
        (cyclicRayAngles (p := p) i first0 rest0).rotate k =
          cyclicRayAngles (p := p) i
            (⟨top, hit.symm⟩ : OtherVertex i) (r :: rest) := by
  classical
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht

  obtain ⟨first0, rest0, hrays0⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases hR : C.rays with
    | nil => exact False.elim (C.nonempty hR)
    | cons first rest => exact ⟨first, rest, rfl⟩

  let qs : List ℕ := quotientList t C.gaps
  let As : List ℝ :=
    cyclicRayAngles (p := p) i first0 rest0

  have hqLen : qs.length = C.rays.length := by
    dsimp [qs]
    rw [quotientList_length, C.gaps_length]
  have hALen : As.length = C.rays.length := by
    dsimp [As]
    rw [cyclicRayAngles_length]
    simpa [hrays0]
  have hqA : qs.length = As.length := by omega

  have hsupportList :
      listPositiveCount qs = 2 := by
    dsimp [qs]
    rw [← centreQuotient_ofFn C t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport

  have hmass :
      listZeroAngleMass qs As ≤ (1 + delta) * lam := by
    dsimp [qs, As]
    exact
      centre_zeroAngleMass_le_one_add_delta_lam_of_deficit_three_support_two
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        i C hexp hsupport first0 rest0 hrays0

  let topRay : OtherVertex i := ⟨top, hit.symm⟩
  have htopMem : topRay ∈ C.rays := C.mem_rays_iff topRay
  obtain ⟨pre, post, hsplit⟩ :=
    exists_append_cons_of_mem htopMem
  let k : ℕ := pre.length
  let tailRays : List (OtherVertex i) := post ++ pre

  have hrotRays :
      C.rays.rotate k = topRay :: tailRays := by
    dsimp [k, tailRays]
    rw [hsplit, List.rotate_append_length_eq]
    simp [List.append_assoc]

  let qR : List ℕ := qs.rotate k
  let AR : List ℝ := As.rotate k

  have hqRLen0 :
      qR.length = (topRay :: tailRays).length := by
    dsimp [qR]
    rw [List.length_rotate, hqLen]
    rw [← List.length_rotate C.rays k, hrotRays]
    simp

  have hsupportR :
      listPositiveCount qR = 2 := by
    dsimp [qR]
    rw [listPositiveCount_rotate]
    exact hsupportList

  have htailNonempty : tailRays ≠ [] := by
    intro hnil
    have hlen1 : qR.length = 1 := by
      rw [hqRLen0, hnil]
      rfl
    have hcountLe := listPositiveCount_le_length qR
    rw [hsupportR, hlen1] at hcountLe
    omega

  obtain ⟨r, rest, htail⟩ :
      ∃ r rest, tailRays = r :: rest := by
    cases hT : tailRays with
    | nil => exact False.elim (htailNonempty hT)
    | cons r rest => exact ⟨r, rest, rfl⟩

  have hqRLen :
      qR.length = (topRay :: r :: rest).length := by
    rw [hqRLen0, htail]

  have hqAR : qR.length = AR.length := by
    dsimp [qR, AR]
    simpa using hqA

  have hmassR :
      listZeroAngleMass qR AR ≤ (1 + delta) * lam := by
    dsimp [qR, AR]
    rw [listZeroAngleMass_rotate qs As hqA k]
    exact hmass

  have hARpin :
      AR =
        cyclicRayAngles (p := p) i topRay (r :: rest) := by
    let w :=
      fun a b : OtherVertex i =>
        EuclideanGeometry.angle (p a.1) (p i) (p b.1)
    have hAedge :
        As = cyclicEdgeValues w C.rays := by
      dsimp [As, w]
      rw [hrays0]
      exact cyclicRayAngles_eq_cyclicEdgeValues
        (p := p) i first0 rest0
    calc
      AR = As.rotate k := rfl
      _ = (cyclicEdgeValues w C.rays).rotate k := by rw [hAedge]
      _ = cyclicEdgeValues w (C.rays.rotate k) := by
          symm
          exact cyclicEdgeValues_rotate w C.rays k
      _ = cyclicEdgeValues w (topRay :: r :: rest) := by
          rw [hrotRays, htail]
      _ = cyclicRayAngles (p := p) i topRay (r :: rest) := by
          symm
          exact cyclicRayAngles_eq_cyclicEdgeValues
            (p := p) i topRay (r :: rest)

  cases hqCase : qR with
  | nil =>
      have : qR.length = 0 := by simp [hqCase]
      rw [hqRLen] at this
      simp at this
  | cons qFirst qrest =>
      have hqrestLen :
          qrest.length =
            (consecutiveRayAngles (p := p) i r rest ++
              [EuclideanGeometry.angle
                (p ((r :: rest).getLastD r).1)
                (p i) (p top)]).length := by
        have h := hqAR
        rw [hqCase, hARpin] at h
        simpa [cyclicRayAngles, consecutiveRayAngles, topRay]
          using h
      have hqrestNonempty : qrest ≠ [] := by
        intro hnil
        rw [hnil] at hqrestLen
        simp at hqrestLen

      let qLast : ℕ := qrest.getLast hqrestNonempty
      let qmid : List ℕ := qrest.dropLast
      have hqrestShape :
          qrest = qmid ++ [qLast] := by
        dsimp [qmid, qLast]
        symm
        exact List.dropLast_append_getLast hqrestNonempty
      have hqShape :
          qR = qFirst :: qmid ++ [qLast] := by
        simp [hqCase, hqrestShape]

      let Amid := consecutiveRayAngles (p := p) i r rest
      let lastRay : OtherVertex i := (r :: rest).getLastD r
      let AFirst :=
        EuclideanGeometry.angle (p top) (p i) (p r.1)
      let ALast :=
        EuclideanGeometry.angle (p lastRay.1) (p i) (p top)

      have hARShape :
          AR = AFirst :: Amid ++ [ALast] := by
        rw [hARpin]
        simp [cyclicRayAngles, consecutiveRayAngles,
          topRay, AFirst, Amid, ALast, lastRay,
          List.getLastD_cons] <;> cases rest <;> rfl

      have hmidLen :
          qmid.length = Amid.length := by
        have h := hqAR
        rw [hqShape, hARShape] at h
        simp at h
        exact h

      refine ⟨first0, rest0, k, pre, post, r, rest,
        qFirst, qLast, qmid,
        hrays0, hsplit, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hrotRays, htail]
      · dsimp [qR, qs] at hqShape
        exact hqShape
      · rw [← hqShape]
        exact hsupportR
      · dsimp [Amid] at hmidLen
        exact hmidLen
      · dsimp [qR, AR, qs, As] at hmassR
        exact hmassR
      · dsimp [AR, As] at hARpin
        exact hARpin

/-- Separated top pin: one end quotient is zero, and deleting its sharp
outer-angle contribution leaves at most 2*delta*lambda of zero-angle mass. -/
theorem separated_support_two_residual_zero_budget
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hcard : Fintype.card V = 6)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hsep :
      ¬ TopPinnedPositivePair Cfam top i hit t) :
    ∃ first0 rest0 k pre post r rest qFirst qLast qmid,
      (Cfam i).rays = first0 :: rest0 ∧
      (Cfam i).rays =
        pre ++ (⟨top, hit.symm⟩ : OtherVertex i) :: post ∧
      k = pre.length ∧
      (Cfam i).rays.rotate k =
        (⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t (Cfam i).gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      listPositiveCount (qFirst :: qmid ++ [qLast]) = 2 ∧
      (
        (qFirst = 0 ∧
          (1 - delta) * lam ≤
            EuclideanGeometry.angle (p top) (p i) (p r.1))
        ∨
        (qLast = 0 ∧
          (1 - delta) * lam ≤
            EuclideanGeometry.angle
              (p ((r :: rest).getLastD r).1) (p i) (p top))
      ) ∧
      (
        qFirst = 0 →
          listZeroAngleMass
              (qmid ++ [qLast])
              (consecutiveRayAngles (p := p) i r rest ++
                [EuclideanGeometry.angle
                  (p ((r :: rest).getLastD r).1)
                  (p i) (p top)])
            ≤ 2 * delta * lam
      ) ∧
      (
        qLast = 0 →
          listZeroAngleMass
              (qFirst :: qmid)
              (EuclideanGeometry.angle (p top) (p i) (p r.1) ::
                consecutiveRayAngles (p := p) i r rest)
            ≤ 2 * delta * lam
      ) := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsharp :
      SharpAt p delta lam top :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      top (Cfam top) hTop

  obtain ⟨first0, rest0, k, pre, post, r, rest,
      qFirst, qLast, qmid,
      hrays0, hsplit, hk, hrotRays, hqrot,
      hsupportRot, hmidLen, hmass, hangleRot⟩ :=
    exists_sharp_pinned_support_two_deficit_three_shape
      hp hcap (by omega : 4 ≤ n) hdelta0 hdeltaHalf ht hlam
      hit (Cfam i) hI hsupport

  have hnotBoth :
      ¬ (1 ≤ qFirst ∧ 1 ≤ qLast) := by
    intro hboth
    apply hsep
    refine ⟨pre, post, qFirst, qLast, qmid, hsplit, ?_, hboth.1, hboth.2⟩
    rw [← hk]
    exact hqrot

  have hendZero : qFirst = 0 ∨ qLast = 0 := by
    by_cases hF : qFirst = 0
    · exact Or.inl hF
    · right
      by_contra hL
      apply hnotBoth
      exact ⟨by omega, by omega⟩

  let lastRay : OtherVertex i := (r :: rest).getLastD r
  let AFirst := EuclideanGeometry.angle (p top) (p i) (p r.1)
  let Amid := consecutiveRayAngles (p := p) i r rest
  let ALast := EuclideanGeometry.angle (p lastRay.1) (p i) (p top)

  have hrotNodup :
      ((⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest).Nodup := by
    rw [← hrotRays]
    simpa using (Cfam i).nodup
  have htopr : top ≠ r.1 := by
    intro h
    have hne :=
      (List.nodup_cons.mp hrotNodup).1
    apply hne
    simp only [List.mem_cons]
    exact Or.inl (Subtype.ext h)
  have hlastMem : lastRay ∈ r :: rest := by
    dsimp [lastRay]
    have hlastEq :
        (r :: rest).getLastD r = rest.getLastD r := by
      cases rest with
      | nil => rfl
      | cons x xs => rfl
    rw [hlastEq]
    exact List.getLastD_mem_cons
  have htopLast : top ≠ lastRay.1 := by
    intro h
    have hne :=
      (List.nodup_cons.mp hrotNodup).1
    apply hne
    have : (⟨top, hit.symm⟩ : OtherVertex i) = lastRay :=
      Subtype.ext h
    rw [this]
    exact hlastMem

  have hFirstLower :
      (1 - delta) * lam ≤ AFirst := by
    dsimp [AFirst]
    exact outer_angle_ge_one_sub_delta_mul_lam_of_sharp
      hp hcap hit.symm htopr (by
        intro h
        apply r.2
        exact h.symm) hsharp

  have hLastLower :
      (1 - delta) * lam ≤ ALast := by
    dsimp [ALast]
    have h :=
      outer_angle_ge_one_sub_delta_mul_lam_of_sharp
        hp hcap hit.symm htopLast
        (by
          intro h
          apply lastRay.2
          exact h.symm)
        hsharp
    have hcomm :
        EuclideanGeometry.angle (p top) (p i) (p lastRay.1) =
          EuclideanGeometry.angle (p lastRay.1) (p i) (p top) :=
      EuclideanGeometry.angle_comm _ _ _
    simpa [hcomm] using h

  have hARShape :
      (cyclicRayAngles (p := p) i first0 rest0).rotate k =
        AFirst :: Amid ++ [ALast] := by
    rw [hangleRot]
    simp [cyclicRayAngles, consecutiveRayAngles,
      AFirst, Amid, ALast, lastRay,
      List.getLastD_cons] <;> cases rest <;> rfl

  have hmassShape :
      listZeroAngleMass
          (qFirst :: qmid ++ [qLast])
          (AFirst :: Amid ++ [ALast])
        ≤ (1 + delta) * lam := by
    rw [← hqrot, ← hARShape]
    exact hmass

  have htailBudget :
      qFirst = 0 →
        listZeroAngleMass
            (qmid ++ [qLast])
            (Amid ++ [ALast])
          ≤ 2 * delta * lam := by
    intro hF
    have hEq :
        listZeroAngleMass
            (qFirst :: qmid ++ [qLast])
            (AFirst :: Amid ++ [ALast])
          =
        AFirst +
          listZeroAngleMass
            (qmid ++ [qLast]) (Amid ++ [ALast]) := by
      simp [listZeroAngleMass, hF]
    rw [hEq] at hmassShape
    nlinarith

  have hheadBudget :
      qLast = 0 →
        listZeroAngleMass
            (qFirst :: qmid)
            (AFirst :: Amid)
          ≤ 2 * delta * lam := by
    intro hL
    have hpreLen :
        (qFirst :: qmid).length =
          (AFirst :: Amid).length := by
      simp [Amid, hmidLen]
    have hEq :=
      listZeroAngleMass_append_aligned
        (qFirst :: qmid) [qLast]
        (AFirst :: Amid) [ALast] hpreLen
    have hsingle :
        listZeroAngleMass [qLast] [ALast] = ALast := by
      simp [listZeroAngleMass, hL]
    rw [hEq, hsingle] at hmassShape
    nlinarith

  refine ⟨first0, rest0, k, pre, post, r, rest,
    qFirst, qLast, qmid,
    hrays0, hsplit, hk, hrotRays, hqrot,
    hsupportRot, ?_, ?_, ?_⟩
  · rcases hendZero with hF | hL
    · exact Or.inl ⟨hF, hFirstLower⟩
    · exact Or.inr ⟨hL, hLastLower⟩
  · simpa [Amid, ALast, lastRay] using htailBudget
  · simpa [AFirst, Amid] using hheadBudget


/-- A separated genuine support-two, deficit-three centre adjacent to a sharp
top cannot have both of its top-adjacent quotient gaps zero when
\(\delta < 1/3\). The positive endpoint is an ACTUAL quotient-gap
certificate, not a candidate Boolean hole or an unpaid dyadic credit. -/
theorem separated_support_two_has_positive_top_endpoint_of_delta_lt_third
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hcard : Fintype.card V = 6)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaThird : delta < (1 : ℝ) / 3)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hsep : ¬ TopPinnedPositivePair Cfam top i hit t) :
    ∃ (k : ℕ) (r : OtherVertex i) (rest : List (OtherVertex i))
      (qFirst qLast : ℕ) (qmid : List ℕ),
      (Cfam i).rays.rotate k =
        (⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t (Cfam i).gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      ((qFirst = 0 ∧ 0 < qLast) ∨ (qLast = 0 ∧ 0 < qFirst)) := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsharp : SharpAt p delta lam top :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n) hdelta0
      (by linarith : delta < 1) ht hlam
      top (Cfam top) hTop
  obtain ⟨first0, rest0, k, pre, post, r, rest,
      qFirst, qLast, qmid,
      hrays0, hsplit, hk, hrotRays, hqrot,
      hsupportRot, hmidLen, hmass, hangleRot⟩ :=
    exists_sharp_pinned_support_two_deficit_three_shape
      hp hcap (by omega : 4 ≤ n) hdelta0 hdeltaHalf ht hlam
      hit (Cfam i) hI hsupport
  have hnotBothPositive : ¬ (0 < qFirst ∧ 0 < qLast) := by
    intro hboth
    apply hsep
    refine ⟨pre, post, qFirst, qLast, qmid, hsplit, ?_, hboth.1, hboth.2⟩
    rw [← hk]
    exact hqrot
  have hrotNodup :
      ((⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest).Nodup := by
    rw [← hrotRays]
    simpa using (Cfam i).nodup
  have htopr : top ≠ r.1 := by
    intro h
    have hne := (List.nodup_cons.mp hrotNodup).1
    apply hne
    exact List.mem_cons.mpr (Or.inl (Subtype.ext h))
  let lastRay : OtherVertex i := (r :: rest).getLastD r
  have hlastMem : lastRay ∈ r :: rest := by
    dsimp [lastRay]
    have hlastEq : (r :: rest).getLastD r = rest.getLastD r := by
      cases rest <;> rfl
    rw [hlastEq]
    exact List.getLastD_mem_cons
  have htopLast : top ≠ lastRay.1 := by
    intro h
    have hne := (List.nodup_cons.mp hrotNodup).1
    apply hne
    have : (⟨top, hit.symm⟩ : OtherVertex i) = lastRay :=
      Subtype.ext h
    rw [this]
    exact hlastMem
  let AFirst := EuclideanGeometry.angle (p top) (p i) (p r.1)
  let Amid := consecutiveRayAngles (p := p) i r rest
  let ALast := EuclideanGeometry.angle (p lastRay.1) (p i) (p top)
  have hFirstLower : (1 - delta) * lam ≤ AFirst := by
    dsimp [AFirst]
    exact outer_angle_ge_one_sub_delta_mul_lam_of_sharp
      hp hcap hit.symm htopr
      (by intro h; apply r.2; exact h.symm) hsharp
  have hLastLower : (1 - delta) * lam ≤ ALast := by
    dsimp [ALast]
    have h := outer_angle_ge_one_sub_delta_mul_lam_of_sharp
      hp hcap hit.symm htopLast
      (by intro h; apply lastRay.2; exact h.symm) hsharp
    have hcomm :
        EuclideanGeometry.angle (p top) (p i) (p lastRay.1) =
        EuclideanGeometry.angle (p lastRay.1) (p i) (p top) :=
      EuclideanGeometry.angle_comm _ _ _
    simpa [hcomm] using h
  have hARShape :
      (cyclicRayAngles (p := p) i first0 rest0).rotate k =
        AFirst :: Amid ++ [ALast] := by
    rw [hangleRot]
    simp [cyclicRayAngles, consecutiveRayAngles,
      AFirst, Amid, ALast, lastRay,
      List.getLastD_cons] <;> cases rest <;> rfl
  have hmassShape :
      listZeroAngleMass (qFirst :: qmid ++ [qLast])
        (AFirst :: Amid ++ [ALast]) ≤ (1 + delta) * lam := by
    rw [← hqrot, ← hARShape]
    exact hmass
  have hmidNonneg : 0 ≤ listZeroAngleMass qmid Amid :=
    listZeroAngleMass_nonneg qmid Amid
      (all_consecutiveRayAngles_nonneg (p := p) i r rest)
  have hnotBothZero : ¬(qFirst = 0 ∧ qLast = 0) := by
    rintro ⟨hF, hL⟩
    have hsplitMass :=
      listZeroAngleMass_append_aligned
        qmid [qLast] Amid [ALast] hmidLen
    have hsingle :
        listZeroAngleMass [qLast] [ALast] = ALast := by
      simp [listZeroAngleMass, hL]
    have hmassExact :
        listZeroAngleMass (qFirst :: qmid ++ [qLast])
            (AFirst :: Amid ++ [ALast]) =
          AFirst + listZeroAngleMass qmid Amid + ALast := by
      calc
        _ = AFirst + listZeroAngleMass (qmid ++ [qLast])
            (Amid ++ [ALast]) := by simp [listZeroAngleMass, hF]
        _ = AFirst + (listZeroAngleMass qmid Amid + ALast) := by
          rw [hsplitMass, hsingle]
        _ = _ := by ring
    rw [hmassExact] at hmassShape
    have hthree : 3 * delta < (1 : ℝ) := by linarith
    have hscaled : 3 * delta * lam < lam := by
      have h := mul_lt_mul_of_pos_right hthree hlampos
      nlinarith
    nlinarith [hmassShape, hmidNonneg, hFirstLower, hLastLower, hscaled]
  refine ⟨k, r, rest, qFirst, qLast, qmid, hrotRays, hqrot, ?_⟩
  by_cases hF : qFirst = 0
  · left
    constructor
    · exact hF
    · have hLastNe : qLast ≠ 0 := by
        intro hL
        exact hnotBothZero ⟨hF, hL⟩
      omega
  · right
    constructor
    · by_contra hLastNe
      apply hnotBothPositive
      constructor
      · omega
      · omega
    · omega

/-- Actual planar double-zero sharp-pinned budget.

If BOTH sharp-top-adjacent quotient gaps at a genuine deficit-three,
support-two centre vanish, then the sum of ALL remaining middle zero-gap
angles costs at most (3*delta-1)*lambda. In particular this geometry
forces delta >= 1/3.

This is an explicit quantitative geometric necessary condition. It is
NOT a payment of Boolean holes, covered sink words or dyadic debt. -/
theorem separated_support_two_double_zero_middle_angle_budget
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2) :
    ∃ (k : ℕ) (r : OtherVertex i) (rest : List (OtherVertex i))
      (qFirst qLast : ℕ) (qmid : List ℕ),
      (Cfam i).rays.rotate k =
        (⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t (Cfam i).gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      (qFirst = 0 ∧ qLast = 0 →
        listZeroAngleMass qmid
            (consecutiveRayAngles (p := p) i r rest)
          ≤ (3 * delta - 1) * lam ∧
        (1 : ℝ) / 3 ≤ delta) := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsharp : SharpAt p delta lam top :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n) hdelta0
      (by linarith : delta < 1) ht hlam
      top (Cfam top) hTop
  obtain ⟨first0, rest0, k, pre, post, r, rest,
      qFirst, qLast, qmid,
      hrays0, hsplit, hk, hrotRays, hqrot,
      hsupportRot, hmidLen, hmass, hangleRot⟩ :=
    exists_sharp_pinned_support_two_deficit_three_shape
      hp hcap (by omega : 4 ≤ n) hdelta0 hdeltaHalf ht hlam
      hit (Cfam i) hI hsupport
  let lastRay : OtherVertex i := (r :: rest).getLastD r
  let AFirst := EuclideanGeometry.angle (p top) (p i) (p r.1)
  let Amid := consecutiveRayAngles (p := p) i r rest
  let ALast := EuclideanGeometry.angle (p lastRay.1) (p i) (p top)
  have hrotNodup :
      ((⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest).Nodup := by
    rw [← hrotRays]
    simpa using (Cfam i).nodup
  have htopr : top ≠ r.1 := by
    intro h
    have hne := (List.nodup_cons.mp hrotNodup).1
    apply hne
    exact List.mem_cons.mpr (Or.inl (Subtype.ext h))
  have hlastMem : lastRay ∈ r :: rest := by
    dsimp [lastRay]
    have hlastEq : (r :: rest).getLastD r = rest.getLastD r := by
      cases rest <;> rfl
    rw [hlastEq]
    exact List.getLastD_mem_cons
  have htopLast : top ≠ lastRay.1 := by
    intro h
    have hne := (List.nodup_cons.mp hrotNodup).1
    apply hne
    have he : (⟨top, hit.symm⟩ : OtherVertex i) = lastRay :=
      Subtype.ext h
    rw [he]
    exact hlastMem
  have hFirstLower : (1 - delta) * lam ≤ AFirst := by
    dsimp [AFirst]
    exact outer_angle_ge_one_sub_delta_mul_lam_of_sharp
      hp hcap hit.symm htopr
      (by intro h; apply r.2; exact h.symm) hsharp
  have hLastLower : (1 - delta) * lam ≤ ALast := by
    dsimp [ALast]
    have h :=
      outer_angle_ge_one_sub_delta_mul_lam_of_sharp
        hp hcap hit.symm htopLast
        (by intro h; apply lastRay.2; exact h.symm) hsharp
    have hcomm :
        EuclideanGeometry.angle (p top) (p i) (p lastRay.1) =
        EuclideanGeometry.angle (p lastRay.1) (p i) (p top) :=
      EuclideanGeometry.angle_comm _ _ _
    simpa [hcomm] using h
  have hARShape :
      (cyclicRayAngles (p := p) i first0 rest0).rotate k =
        AFirst :: Amid ++ [ALast] := by
    rw [hangleRot]
    simp [cyclicRayAngles, consecutiveRayAngles,
      AFirst, Amid, ALast, lastRay,
      List.getLastD_cons] <;> cases rest <;> rfl
  have hmassShape :
      listZeroAngleMass (qFirst :: qmid ++ [qLast])
        (AFirst :: Amid ++ [ALast]) ≤ (1 + delta) * lam := by
    rw [← hqrot, ← hARShape]
    exact hmass
  have hmidNonneg : 0 ≤ listZeroAngleMass qmid Amid :=
    listZeroAngleMass_nonneg qmid Amid
      (all_consecutiveRayAngles_nonneg (p := p) i r rest)
  refine ⟨k, r, rest, qFirst, qLast, qmid, hrotRays, hqrot, ?_⟩
  rintro ⟨hF, hL⟩
  have hsplitMass :=
    listZeroAngleMass_append_aligned
      qmid [qLast] Amid [ALast] hmidLen
  have hsingle :
      listZeroAngleMass [qLast] [ALast] = ALast := by
    simp [listZeroAngleMass, hL]
  have hmassExact :
      listZeroAngleMass (qFirst :: qmid ++ [qLast])
          (AFirst :: Amid ++ [ALast]) =
        AFirst + listZeroAngleMass qmid Amid + ALast := by
    calc
      _ = AFirst + listZeroAngleMass (qmid ++ [qLast])
          (Amid ++ [ALast]) := by simp [listZeroAngleMass, hF]
      _ = AFirst + (listZeroAngleMass qmid Amid + ALast) := by
        rw [hsplitMass, hsingle]
      _ = _ := by ring
  rw [hmassExact] at hmassShape
  constructor
  · dsimp [Amid]
    nlinarith [hFirstLower, hLastLower, hmassShape]
  · by_contra hthird
    have hlt : delta < (1 : ℝ) / 3 := by push_neg at hthird; exact hthird
    have hgap : 0 < (1 - 3 * delta) * lam :=
      mul_pos (by linarith) hlampos
    nlinarith [hFirstLower, hLastLower, hmassShape, hmidNonneg, hgap]

#print axioms separated_support_two_has_positive_top_endpoint_of_delta_lt_third
#print axioms separated_support_two_double_zero_middle_angle_budget

#print axioms exists_sharp_pinned_support_two_deficit_three_shape
#print axioms separated_support_two_residual_zero_budget

end JSP000404Research
