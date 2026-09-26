import JSP000404Research.CutProjectiveBandOccupancy
import JSP000404Research.ProjectiveCutRotation
import JSP000404Research.ProjectiveGapScaling
import JSP000404Research.ScaledCyclicBandBudget
import Mathlib.Tactic

/-!
# Local one-layer budget at an arbitrary projective cut

For a cut c in [0,pi), split the canonical sorted angle list as

  low ++ high,

with low < c and c <= high.

The cut-angle list is

  (high-c) ++ (low+pi-c).

It is again sorted in [0,pi), its cyclic projective gap list is merely a
rotation of the canonical one, and therefore its Sendov exponent is identical.
ScaledCyclicBandBudget then pays that exponent by empty unit bands at the new
cut.

Combining with CutProjectiveBandOccupancy gives, for every centre i,

  active_cut(i).card <= (n+1) - centreExponent(i).

Thus moving the global projective cut does not weaken the local Hansel budget.
-/

namespace JSP000404Research

open Real
open BinaryEdgePartition

def cutProjectiveAngle (c theta : ℝ) : ℝ :=
  if theta < c then theta + Real.pi - c else theta - c

theorem cutRayTheta_eq_cutProjectiveAngle
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) (i : V) (j : OtherVertex i) :
    cutRayTheta hp c i j =
      cutProjectiveAngle c (rayThetaAt hp i j) := by
  rfl

/-- Every sorted real list admits the obvious lower/upper decomposition at c. -/
theorem exists_cut_decomposition_of_pairwise
    (xs : List ℝ)
    (hsorted : xs.Pairwise (· ≤ ·))
    (c : ℝ) :
    ∃ low high : List ℝ,
      xs = low ++ high ∧
      (∀ x ∈ low, x < c) ∧
      (∀ x ∈ high, c ≤ x) := by
  induction xs with
  | nil =>
      exact ⟨[], [], rfl, by simp, by simp⟩
  | cons a xs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      by_cases ha : a < c
      · obtain ⟨low, high, hsplit, hlow, hhigh⟩ :=
          ih hpair.2
        refine ⟨a :: low, high, ?_, ?_, hhigh⟩
        · simp [hsplit]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hlow x hx
      · have hca : c ≤ a := le_of_not_gt ha
        refine ⟨[], a :: xs, by simp, by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hca
        · exact hca.trans (hpair.1 x hx)

/-- Cut rotation preserves sortedness when the split occurs at the cut. -/
theorem anglesAfterProjectiveCut_pairwise
    (c : ℝ)
    (low high : List ℝ)
    (hsorted : (low ++ high).Pairwise (· ≤ ·))
    (hall0 : ∀ x ∈ low ++ high, 0 ≤ x)
    (hallpi : ∀ x ∈ low ++ high, x < Real.pi)
    (hlow : ∀ x ∈ low, x < c)
    (hhigh : ∀ x ∈ high, c ≤ x) :
    (anglesAfterProjectiveCut c low high).Pairwise (· ≤ ·) := by
  rw [anglesAfterProjectiveCut]
  have hpairs := List.pairwise_append.mp hsorted
  have hhighPair :
      (high.map (fun x => x - c)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hpairs.2.1.imp (by
      intro a b hab
      linarith)
  have hlowPair :
      (low.map (fun x => x + Real.pi - c)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hpairs.1.imp (by
      intro a b hab
      linarith)
  apply List.pairwise_append.mpr
  refine ⟨hhighPair, hlowPair, ?_⟩
  intro x hx y hy
  obtain ⟨xh, hxmem, rfl⟩ := List.mem_map.mp hx
  obtain ⟨yl, hymem, rfl⟩ := List.mem_map.mp hy
  have hxhPi : xh < Real.pi :=
    hallpi xh (by simp [hxmem])
  have hyl0 : 0 ≤ yl :=
    hall0 yl (by simp [hymem])
  linarith

theorem anglesAfterProjectiveCut_mem_nonneg
    (c : ℝ)
    (low high : List ℝ)
    (hcpi : c < Real.pi)
    (hall0 : ∀ x ∈ low ++ high, 0 ≤ x)
    (hlow : ∀ x ∈ low, x < c)
    (hhigh : ∀ x ∈ high, c ≤ x) :
    ∀ y ∈ anglesAfterProjectiveCut c low high, 0 ≤ y := by
  intro y hy
  rw [anglesAfterProjectiveCut, List.mem_append] at hy
  rcases hy with hy | hy
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    linarith [hhigh x hx]
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hx0 := hall0 x (by simp [hx])
    linarith

theorem anglesAfterProjectiveCut_mem_lt_pi
    (c : ℝ)
    (low high : List ℝ)
    (hc0 : 0 ≤ c)
    (hallpi : ∀ x ∈ low ++ high, x < Real.pi)
    (hlow : ∀ x ∈ low, x < c) :
    ∀ y ∈ anglesAfterProjectiveCut c low high, y < Real.pi := by
  intro y hy
  rw [anglesAfterProjectiveCut, List.mem_append] at hy
  rcases hy with hy | hy
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hxpi := hallpi x (by simp [hx])
    linarith
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    linarith [hlow x hx]

/-- The natural floor labels of the cut-angle list are a cyclic permutation of
the floor labels obtained directly from the original rays with cutRayTheta. -/
theorem floorBandList_cutAngles_toFinset_eq_cutFloor
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t c : ℝ)
    (low high : List ℝ)
    (hdecomp : C.angles = low ++ high)
    (hlow : ∀ x ∈ low, x < c)
    (hhigh : ∀ x ∈ high, c ≤ x) :
    (floorBandList
      ((anglesAfterProjectiveCut c low high).map
        (scaleProjectiveAngle t))).toFinset
      =
    (cutFloorBandList C t c).toFinset := by
  classical
  have hcutFloor :
      cutFloorBandList C t c =
        C.angles.map
          (fun theta =>
            Nat.floor
              (scaleProjectiveAngle t
                (cutProjectiveAngle c theta))) := by
    unfold cutFloorBandList CentreProjectiveCycle.angles
    simp only [List.map_map]
    apply List.map_congr_left
    intro j hj
    simp [cutNormalizedRayTheta,
      scaleProjectiveAngle,
      cutRayTheta_eq_cutProjectiveAngle]
  have hlowMap :
      low.map
          (fun theta =>
            Nat.floor
              (scaleProjectiveAngle t
                (cutProjectiveAngle c theta)))
        =
      low.map
          (fun theta =>
            Nat.floor
              (scaleProjectiveAngle t
                (theta + Real.pi - c))) := by
    apply List.map_congr_left
    intro theta htheta
    simp [cutProjectiveAngle, hlow theta htheta]
  have hhighMap :
      high.map
          (fun theta =>
            Nat.floor
              (scaleProjectiveAngle t
                (cutProjectiveAngle c theta)))
        =
      high.map
          (fun theta =>
            Nat.floor
              (scaleProjectiveAngle t
                (theta - c))) := by
    apply List.map_congr_left
    intro theta htheta
    have hnot : ¬ theta < c := not_lt.mpr (hhigh theta htheta)
    simp [cutProjectiveAngle, hnot]
  rw [hcutFloor, hdecomp, List.map_append,
      hlowMap, hhighMap]
  unfold anglesAfterProjectiveCut floorBandList
  simp only [List.map_append, List.map_map]
  ext m
  simp [or_comm]

/-- Main arbitrary-cut missing-band estimate at one centre. -/
theorem centreExponent_le_missing_cutProjectiveBands
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta c : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi) :
    centreExponent C t ≤
      (n + 1) -
        (occupiedCutProjectiveBands hp t c n i).card := by
  obtain ⟨low, high, hdecomp, hlow, hhigh⟩ :=
    exists_cut_decomposition_of_pairwise
      C.angles C.angles_pairwise c
  have hall0 :
      ∀ x ∈ low ++ high, 0 ≤ x := by
    intro x hx
    have hxC : x ∈ C.angles := by
      rw [hdecomp]
      exact hx
    exact (C.angle_mem_bounds hxC).1
  have hallpi :
      ∀ x ∈ low ++ high, x < Real.pi := by
    intro x hx
    have hxC : x ∈ C.angles := by
      rw [hdecomp]
      exact hx
    exact (C.angle_mem_bounds hxC).2
  let A := anglesAfterProjectiveCut c low high
  have hA_sorted :
      A.Pairwise (· ≤ ·) := by
    dsimp [A]
    exact anglesAfterProjectiveCut_pairwise
      c low high
      (by rw [← hdecomp]; exact C.angles_pairwise)
      hall0 hallpi hlow hhigh
  have hA0 :
      ∀ x ∈ A, 0 ≤ x := by
    dsimp [A]
    exact anglesAfterProjectiveCut_mem_nonneg
      c low high hcpi hall0 hlow hhigh
  have hApi :
      ∀ x ∈ A, x < Real.pi := by
    dsimp [A]
    exact anglesAfterProjectiveCut_mem_lt_pi
      c low high hc0 hallpi hlow
  have hAne : A ≠ [] := by
    intro hnil
    have hlen :
        A.length = C.angles.length := by
      dsimp [A, anglesAfterProjectiveCut]
      rw [hdecomp]
      simp [Nat.add_comm]
    have : C.angles.length = 0 := by
      rw [← hlen, hnil]
      rfl
    exact C.angles_nonempty (List.length_eq_zero.mp this)
  obtain ⟨a, xs, hAcons⟩ :
      ∃ a xs, A = a :: xs := by
    cases hAeq : A with
    | nil => exact False.elim (hAne hAeq)
    | cons a xs => exact ⟨a, xs, hAeq⟩
  let SA : List ℝ := A.map (scaleProjectiveAngle t)
  let aa := scaleProjectiveAngle t a
  let xxs := xs.map (scaleProjectiveAngle t)
  have hSAcons : SA = aa :: xxs := by
    simp [SA, aa, xxs, hAcons]
  have hSA_sorted :
      SA.Pairwise (· ≤ ·) := by
    dsimp [SA]
    rw [List.pairwise_map]
    exact hA_sorted.imp (by
      intro x y hxy
      unfold scaleProjectiveAngle
      have hpi := Real.pi_pos
      exact (div_le_div_iff_of_pos_right hpi).2
        (mul_le_mul_of_nonneg_left hxy htpos.le))
  have hSA0 :
      ∀ x ∈ SA, 0 ≤ x := by
    intro x hx
    dsimp [SA] at hx
    obtain ⟨theta, htheta, rfl⟩ := List.mem_map.mp hx
    have ht0 := hA0 theta htheta
    unfold scaleProjectiveAngle
    positivity
  have hSAt :
      ∀ x ∈ SA, x < t := by
    intro x hx
    dsimp [SA] at hx
    obtain ⟨theta, htheta, rfl⟩ := List.mem_map.mp hx
    have htpi := hApi theta htheta
    unfold scaleProjectiveAngle
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_pos]
  have haa0 : 0 ≤ aa := by
    apply hSA0 aa
    rw [hSAcons]
    simp
  have hscaledSorted :
      (aa :: xxs).Pairwise (· ≤ ·) := by
    rw [← hSAcons]
    exact hSA_sorted
  have hscaledLt :
      ∀ x ∈ aa :: xxs, x < t := by
    intro x hx
    apply hSAt x
    rw [hSAcons]
    exact hx
  have hcyc :=
    listExponent_floor_cyclicGaps_le_cyclicBandMissing
      aa xxs haa0 hscaledSorted hscaledLt
      ht hdelta0 hdelta1
  have hquot :
      (cyclicGapsAt t
        ((a :: xs).map (scaleProjectiveAngle t))).map Nat.floor
        =
      quotientList t
        (normalizedProjectiveGaps (a :: xs)) :=
    floor_scaled_cyclicGaps_eq_quotientList t a xs
  have hscaledEq :
      (a :: xs).map (scaleProjectiveAngle t) =
        aa :: xxs := by
    simp [aa, xxs]
  rw [← hscaledEq] at hcyc
  rw [hquot] at hcyc
  have hExpCut :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps (a :: xs)))
        =
      centreExponent C t := by
    have hcut :=
      listExponent_after_projective_cut_any
        t c low high
    have hleft :
        anglesAfterProjectiveCut c low high = a :: xs := by
      exact hAcons
    rw [hleft, ← hdecomp,
      CentreProjectiveCycle.gaps] at hcut
    exact hcut.trans
      (listExponent_quotientList_eq_centreExponent' C t)
  rw [hExpCut] at hcyc
  have hfloorSorted :
      (floorBandList (aa :: xxs)).Pairwise (· ≤ ·) :=
    floorBandList_pairwise aa xxs haa0 hscaledSorted
  have hbound :
      ∀ m ∈ floorBandList (aa :: xxs), m < n + 1 := by
    intro m hm
    change m ∈ (aa :: xxs).map Nat.floor at hm
    obtain ⟨x, hx, hxm⟩ := List.mem_map.mp hm
    subst m
    have hx0 : 0 ≤ x := by
      exact hSA0 x (by rw [hSAcons]; exact hx)
    have hxt : x < t :=
      hscaledLt x hx
    have htTop : t < (n : ℝ) + 1 := by
      rw [ht]
      linarith
    have hxTop : x < ((n + 1 : ℕ) : ℝ) := by
      exact hxt.trans (by simpa using htTop)
    exact (Nat.floor_lt hx0).2 (by simpa using hxTop)
  obtain ⟨b, bs, hfloorCons⟩ :
      ∃ b bs, floorBandList (aa :: xxs) = b :: bs := by
    simp [floorBandList]
  have hmissing :
      cyclicBandMissing (n + 1)
          (floorBandList (aa :: xxs))
        =
      (n + 1) -
        (floorBandList (aa :: xxs)).toFinset.card := by
    rw [hfloorCons] at hfloorSorted hbound ⊢
    exact cyclicBandMissing_eq_complement_card
      (n + 1) b bs hfloorSorted hbound
  rw [hmissing] at hcyc
  have hfloorSet :
      (floorBandList (aa :: xxs)).toFinset =
        (cutFloorBandList C t c).toFinset := by
    rw [← hscaledEq, ← hAcons]
    exact floorBandList_cutAngles_toFinset_eq_cutFloor
      C t c low high hdecomp hlow hhigh
  rw [hfloorSet,
      cutFloorBandList_toFinset_card_eq_occupied
        hp C htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith)] at hcyc
  exact hcyc

/-- Active-colour form used by the final one-band merge. -/
theorem cutProjectiveBandPartition_active_card_le_deficit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t delta lam c : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (i : V) :
    (active
      (cutProjectiveBandPartition
        hp hcap htpos hlam hc0 hcpi n
        (by rw [ht]; push_cast; linarith))
      i).card
      ≤
    (n + 1) - centreExponent (C i) t := by
  rw [cutProjectiveBandPartition_active_eq_occupied
    hp hcap htpos hlam hc0 hcpi n
    (by rw [ht]; push_cast; linarith) i]
  have hmissing :=
    centreExponent_le_missing_cutProjectiveBands
      hp (C i) htpos ht hdelta0 hdelta1 hc0 hcpi
  omega

#print axioms exists_cut_decomposition_of_pairwise
#print axioms centreExponent_le_missing_cutProjectiveBands
#print axioms cutProjectiveBandPartition_active_card_le_deficit

end JSP000404Research
