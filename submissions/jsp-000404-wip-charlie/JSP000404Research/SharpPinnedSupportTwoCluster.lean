import JSP000404Research.GeneralSupportTwoMultiplicity
import JSP000404Research.CyclicEdgeRotation
import JSP000404Research.AnglePath
import JSP000404Research.SupportTwoPinnedCycle
import JSP000404Research.PinnedCycleRotation
import Mathlib.Tactic

/-!
# Arbitrary-cardinality support-two centre pinned by a sharp centre

Let s be a Sendov-sharp centre and i a distinct centre with

  exponent(i) = n-2,
  positiveSupport(i) = 2.

Pin the ray i->s at the head of the cyclic ray list by rotation.  Rotate the
quotient list and actual cyclic-angle list by the same amount.

The total actual angle mass carried by quotient-zero positions is at most

  delta*lambda.

If either quotient adjacent to the pinned sharp ray were zero, its actual
angle would itself be at most this total zero mass.  SharpOuterAngles gives the
strict opposite inequality for every ray involving s at centre i.  Therefore
both gaps adjacent to s are positive.

Since total positive support is exactly two, every middle quotient is zero.
The middle actual-angle list is precisely the consecutive angular path through
all rays other than s.  Its total length is at most delta*lambda, so angle
triangle inequality shows that every pair of non-s rays at i has mutual angle
at most delta*lambda.

This is the arbitrary-cardinality replacement for the Fin 4 theorem
support_two_outer_angle_le_delta_lam.
-/

namespace JSP000404Research

open Real

theorem supportTwo_outerSmallAwayFrom_sharp
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    OuterSmallAwayFrom p delta lam s i := by
  classical
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone : 1 ≤ t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  obtain ⟨first0, rest0, hrays0⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases hR : C.rays with
    | nil =>
        exact False.elim (C.nonempty hR)
    | cons first rest =>
        exact ⟨first, rest, hR⟩

  let qs : List ℕ := quotientList t C.gaps
  let As : List ℝ :=
    cyclicRayAngles (p := p) i first0 rest0

  have hqLen :
      qs.length = C.rays.length := by
    dsimp [qs]
    rw [quotientList_length, C.gaps_length]
  have hALen :
      As.length = C.rays.length := by
    dsimp [As]
    rw [cyclicRayAngles_length]
    simpa [hrays0]
  have hqA : qs.length = As.length := by
    rw [hqLen, hALen]

  have hsupportList :
      listPositiveCount qs = 2 := by
    dsimp [qs]
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport

  have hmass :
      listZeroAngleMass qs As ≤ delta * lam := by
    dsimp [qs, As]
    exact centre_zeroAngleMass_le_delta_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      i C hexp hsupport first0 rest0 hrays0

  let rs : OtherVertex i := ⟨s, hsi⟩
  have hrsMem : rs ∈ C.rays :=
    C.mem_rays_iff rs
  obtain ⟨pre, post, hsplit⟩ :=
    exists_append_cons_of_mem hrsMem
  let k : ℕ := pre.length
  let tailRays : List (OtherVertex i) := post ++ pre

  have hrotRays :
      C.rays.rotate k = rs :: tailRays := by
    dsimp [k, tailRays]
    rw [hsplit, List.rotate_append_length_eq]
    simp [List.append_assoc]

  let qR : List ℕ := qs.rotate k
  let AR : List ℝ := As.rotate k

  have hqRLen :
      qR.length = (rs :: tailRays).length := by
    dsimp [qR]
    rw [List.length_rotate, hqLen]
    rw [← List.length_rotate C.rays k, hrotRays]

  have hqAR :
      qR.length = AR.length := by
    dsimp [qR, AR]
    simpa using hqA

  have hsupportR :
      listPositiveCount qR = 2 := by
    dsimp [qR]
    rw [listPositiveCount_rotate]
    exact hsupportList

  have hmassR :
      listZeroAngleMass qR AR ≤ delta * lam := by
    dsimp [qR, AR]
    rw [listZeroAngleMass_rotate qs As hqA k]
    exact hmass

  have hARpin :
      AR =
        cyclicRayAngles (p := p) i rs tailRays := by
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
      _ = (cyclicEdgeValues w C.rays).rotate k := by
          rw [hAedge]
      _ = cyclicEdgeValues w (C.rays.rotate k) := by
          symm
          exact cyclicEdgeValues_rotate w C.rays k
      _ = cyclicEdgeValues w (rs :: tailRays) := by
          rw [hrotRays]
      _ = cyclicRayAngles (p := p) i rs tailRays := by
          symm
          exact cyclicRayAngles_eq_cyclicEdgeValues
            (p := p) i rs tailRays

  have htailNonempty : tailRays ≠ [] := by
    intro hnil
    have hlen1 : qR.length = 1 := by
      rw [hqRLen, hnil]
      rfl
    have hcountLe :=
      listPositiveCount_le_length qR
    rw [hsupportR, hlen1] at hcountLe
    omega

  obtain ⟨r, rest, htail⟩ :
      ∃ r rest, tailRays = r :: rest := by
    cases hT : tailRays with
    | nil =>
        exact False.elim (htailNonempty hT)
    | cons r rest =>
        exact ⟨r, rest, hT⟩

  let AFirst : ℝ :=
    EuclideanGeometry.angle (p s) (p i) (p r.1)
  let Amid : List ℝ :=
    consecutiveRayAngles (p := p) i r rest
  let lastRay : OtherVertex i :=
    (r :: rest).getLastD r
  let ALast : ℝ :=
    EuclideanGeometry.angle (p lastRay.1) (p i) (p s)

  have hARShape :
      AR = AFirst :: (Amid ++ [ALast]) := by
    rw [hARpin, htail]
    simp [cyclicRayAngles, consecutiveRayAngles,
      AFirst, Amid, ALast, lastRay, rs]

  have hrotNodup :
      (rs :: r :: rest).Nodup := by
    have hnd : (C.rays.rotate k).Nodup := by
      simpa using C.nodup
    rw [hrotRays, htail] at hnd
    exact hnd

  have hrsr : rs ≠ r := by
    exact (List.nodup_cons.mp hrotNodup).1 (by simp)
  have hsr : s ≠ r.1 := by
    intro h
    apply hrsr
    apply Subtype.ext
    exact h

  have hlastMem : lastRay ∈ r :: rest := by
    dsimp [lastRay]
    exact List.getLastD_mem (by simp)
  have hrsLast : rs ≠ lastRay := by
    intro h
    have htailNo := (List.nodup_cons.mp hrotNodup).1
    exact htailNo (by simpa [h] using hlastMem)
  have hsLast : s ≠ lastRay.1 := by
    intro h
    apply hrsLast
    apply Subtype.ext
    exact h

  cases hqR : qR with
  | nil =>
      have : qR.length = 0 := by rw [hqR]
      rw [hqRLen, htail] at this
      simp at this
  | cons qFirst qrest =>
      have hqrestLen :
          qrest.length = (Amid ++ [ALast]).length := by
        have h := hqAR
        rw [hqR, hARShape] at h
        simpa using h
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
          qR = qFirst :: (qmid ++ [qLast]) := by
        rw [hqR, hqrestShape]

      have hmidLen :
          qmid.length = Amid.length := by
        have h := hqAR
        rw [hqShape, hARShape] at h
        simp at h
        exact h

      have hAR0 : ∀ A ∈ AR, 0 ≤ A := by
        rw [hARpin, htail]
        exact all_cyclicRayAngles_nonneg
          (p := p) i rs (r :: rest)

      have hFirstNe : qFirst ≠ 0 := by
        intro hq0
        have hpostLen :
            (qmid ++ [qLast]).length =
              (Amid ++ [ALast]).length := by
          simp [hmidLen]
        have hAFirstLe :
            AFirst ≤ listZeroAngleMass qR AR := by
          rw [hqShape, hARShape, hq0]
          exact displayed_zero_angle_le_listZeroAngleMass
            [] (qmid ++ [qLast])
            [] (Amid ++ [ALast])
            AFirst rfl hpostLen
            (by simpa [hARShape] using hAR0)
        have hsmall : AFirst ≤ delta * lam :=
          hAFirstLe.trans hmassR
        have hlower :=
          delta_mul_lam_lt_outer_angle_of_sharp
            hp hcap hdeltaHalf hlampos
            hsi hsr (Ne.symm r.2) hs
        have hAeq :
            AFirst =
              EuclideanGeometry.angle (p s) (p i) (p r.1) := rfl
        rw [hAeq] at hsmall
        linarith

      have hLastNe : qLast ≠ 0 := by
        intro hq0
        have hpreLen :
            (qFirst :: qmid).length =
              (AFirst :: Amid).length := by
          simp [hmidLen]
        have hALastLe :
            ALast ≤ listZeroAngleMass qR AR := by
          have hqShape' :
              qR = (qFirst :: qmid) ++ 0 :: [] := by
            rw [hqShape, hq0]
            simp [List.append_assoc]
          have hAShape' :
              AR = (AFirst :: Amid) ++ ALast :: [] := by
            rw [hARShape]
            simp [List.append_assoc]
          rw [hqShape', hAShape']
          exact displayed_zero_angle_le_listZeroAngleMass
            (qFirst :: qmid) []
            (AFirst :: Amid) []
            ALast hpreLen rfl
            (by
              intro A hA
              apply hAR0 A
              rw [hARShape]
              simpa [List.append_assoc] using hA)
        have hsmall : ALast ≤ delta * lam :=
          hALastLe.trans hmassR
        have hlower :=
          delta_mul_lam_lt_outer_angle_of_sharp
            hp hcap hdeltaHalf hlampos
            hsi hsLast (Ne.symm lastRay.2) hs
        have hcomm :
            EuclideanGeometry.angle
                (p lastRay.1) (p i) (p s) =
              EuclideanGeometry.angle
                (p s) (p i) (p lastRay.1) :=
          EuclideanGeometry.angle_comm _ _ _
        dsimp [ALast] at hsmall
        rw [hcomm] at hsmall
        linarith

      have hsupportShape :
          listPositiveCount
              (qFirst :: qmid ++ [qLast]) = 2 := by
        rw [← hqShape]
        exact hsupportR

      have hshape :=
        pinned_support_two_shape_of_end_zero_impossible
          qFirst qLast qmid
          (fun h => hFirstNe h)
          (fun h => hLastNe h)
          hsupportShape
      have hmidZero : ∀ q ∈ qmid, q = 0 :=
        hshape.2.2

      have hmassEq :
          listZeroAngleMass qR AR = Amid.sum := by
        rw [hqShape, hARShape]
        exact listZeroAngleMass_pinned_eq_middle_sum
          qFirst qLast qmid
          AFirst ALast Amid
          hFirstNe hLastNe hmidLen hmidZero

      have hAmid :
          Amid.sum ≤ delta * lam := by
        rw [hmassEq] at hmassR
        exact hmassR

      have hcomplete :
          ∀ j : V, j ≠ i → j ≠ s →
            j ∈ (r :: rest).map Subtype.val := by
        intro j hji hjs
        let jo : OtherVertex i := ⟨j, hji⟩
        have hjC : jo ∈ C.rays := C.mem_rays_iff jo
        have hjRot : jo ∈ C.rays.rotate k := by
          simpa using hjC
        rw [hrotRays, htail] at hjRot
        simp only [List.mem_cons] at hjRot
        rcases hjRot with hjo | hjTail
        · have hval := congrArg Subtype.val hjo
          dsimp [jo, rs] at hval
          exact False.elim (hjs hval)
        · exact List.mem_map.mpr ⟨jo, hjTail, rfl⟩

      intro j k' hji hki hjs hks hjk
      have hj := hcomplete j hji hjs
      have hk := hcomplete k' hki hks
      have hpair :=
        angle_mem_otherVertex_path_le_consecutive_sum
          (p := p) i r rest hj hk
      dsimp [Amid] at hAmid
      exact hpair.trans hAmid

#print axioms supportTwo_outerSmallAwayFrom_sharp

end JSP000404Research
