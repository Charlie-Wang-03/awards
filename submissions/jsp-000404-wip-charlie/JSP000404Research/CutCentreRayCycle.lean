import JSP000404Research.CutCentreTransitionPath
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic

/-!
# Centre ray cycle sorted at an arbitrary projective cut

A canonical CentreProjectiveCycle is sorted at the fixed cut theta=0.  For a
new cut c, split that list into

  low  = rays with theta < c,
  high = rays with c <= theta,

and rotate to

  high ++ low.

The adjusted cut parameters are theta-c on the high block and
theta+pi-c on the low block, hence the rotated list is sorted by cutRayTheta.
It still lists every OtherVertex exactly once.

This object gives the same index/equivalence interface as CentreRayIndex, but
for an arbitrary projective cut.
-/

namespace JSP000404Research

/-- A complete enumeration of the centre rays, sorted by the adjusted
projective parameter at cut c. -/
structure CentreCutRayCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    (c : ℝ) where
  rays : List (OtherVertex i)
  complete : rays.toFinset = Finset.univ
  nodup : rays.Nodup
  nonempty : rays ≠ []
  cutTheta_sorted :
    rays.Pairwise
      (fun a b =>
        cutRayTheta hp c i a ≤
          cutRayTheta hp c i b)

theorem cutRayTheta_eq_add_pi_sub_of_lt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {c : ℝ} {i : V} {j : OtherVertex i}
    (h : rayThetaAt hp i j < c) :
    cutRayTheta hp c i j =
      rayThetaAt hp i j + Real.pi - c := by
  simp [cutRayTheta, h]

theorem cutRayTheta_eq_sub_of_ge
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {c : ℝ} {i : V} {j : OtherVertex i}
    (h : c ≤ rayThetaAt hp i j) :
    cutRayTheta hp c i j =
      rayThetaAt hp i j - c := by
  simp [cutRayTheta, not_lt.mpr h]

/-- A theta-sorted list splits monotonically at any cut. -/
theorem exists_ray_split_at_cut
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (xs : List (OtherVertex i))
    (hsorted :
      xs.Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b))
    (c : ℝ) :
    ∃ low high : List (OtherVertex i),
      xs = low ++ high ∧
      (∀ j ∈ low, rayThetaAt hp i j < c) ∧
      (∀ j ∈ high, c ≤ rayThetaAt hp i j) := by
  induction xs with
  | nil =>
      exact ⟨[], [], rfl, by simp, by simp⟩
  | cons a xs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      by_cases ha : rayThetaAt hp i a < c
      · obtain ⟨low, high, hsplit, hlow, hhigh⟩ :=
          ih hpair.2
        refine ⟨a :: low, high, ?_, ?_, hhigh⟩
        · simp [hsplit]
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact ha
          · exact hlow j hj
      · have hca : c ≤ rayThetaAt hp i a :=
          le_of_not_gt ha
        refine ⟨[], a :: xs, by simp, by simp, ?_⟩
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hca
        · exact hca.trans (hpair.1 j hj)

/-- A canonically theta-sorted block lying entirely above the cut remains
sorted after subtracting the cut. -/
theorem pairwise_cutRayTheta_of_all_ge_cut
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V} (c : ℝ)
    (xs : List (OtherVertex i))
    (hsorted :
      xs.Pairwise
        (fun a b => rayThetaAt hp i a ≤ rayThetaAt hp i b))
    (hall : ∀ j ∈ xs, c ≤ rayThetaAt hp i j) :
    xs.Pairwise
      (fun a b =>
        cutRayTheta hp c i a ≤ cutRayTheta hp c i b) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have hp0 := List.pairwise_cons.mp hsorted
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        rw [cutRayTheta_eq_sub_of_ge hp (hall a (by simp)),
            cutRayTheta_eq_sub_of_ge hp (hall b (by simp [hb]))]
        exact hp0.1 b hb
      · apply ih hp0.2
        intro b hb
        exact hall b (by simp [hb])

/-- A canonically theta-sorted block lying entirely below the cut remains
sorted after the common +pi-c lift. -/
theorem pairwise_cutRayTheta_of_all_lt_cut
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V} (c : ℝ)
    (xs : List (OtherVertex i))
    (hsorted :
      xs.Pairwise
        (fun a b => rayThetaAt hp i a ≤ rayThetaAt hp i b))
    (hall : ∀ j ∈ xs, rayThetaAt hp i j < c) :
    xs.Pairwise
      (fun a b =>
        cutRayTheta hp c i a ≤ cutRayTheta hp c i b) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have hp0 := List.pairwise_cons.mp hsorted
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        rw [cutRayTheta_eq_add_pi_sub_of_lt hp (hall a (by simp)),
            cutRayTheta_eq_add_pi_sub_of_lt hp (hall b (by simp [hb]))]
        exact hp0.1 b hb
      · apply ih hp0.2
        intro b hb
        exact hall b (by simp [hb])

/-- Rotating the canonical ray list at the cut produces a complete
cutTheta-sorted centre cycle. -/
theorem exists_centreCutRayCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (c : ℝ) :
    Nonempty (CentreCutRayCycle hp i c) := by
  obtain ⟨low, high, hdecomp, hlow, hhigh⟩ :=
    exists_ray_split_at_cut hp C.rays C.theta_sorted c
  let rays := high ++ low

  have hperm : C.rays.Perm rays := by
    dsimp [rays]
    rw [hdecomp]
    exact List.Perm.append_comm low high

  have hnodup : rays.Nodup := by
    exact (hperm.nodup_iff).mp C.nodup

  have hcomplete : rays.toFinset = Finset.univ := by
    classical
    ext j
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    have hj : j ∈ C.rays := C.mem_rays_iff j
    rw [hdecomp, List.mem_append] at hj
    dsimp [rays]
    rw [List.mem_append]
    exact hj.elim Or.inr Or.inl

  have hnonempty : rays ≠ [] := by
    intro hnil
    have hlen := hperm.length_eq
    rw [hnil] at hlen
    have : C.rays.length = 0 := by simpa using hlen
    exact C.nonempty (List.length_eq_zero.mp this)

  have hcanonPair :
      low.Pairwise
          (fun a b =>
            rayThetaAt hp i a ≤ rayThetaAt hp i b)
      ∧
      high.Pairwise
          (fun a b =>
            rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    have hpair :
        (low ++ high).Pairwise
          (fun a b =>
            rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
      rw [← hdecomp]
      exact C.theta_sorted
    have hh := List.pairwise_append.mp hpair
    exact ⟨hh.1, hh.2.1⟩

  have hhighPair :
      high.Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤
            cutRayTheta hp c i b) :=
    pairwise_cutRayTheta_of_all_ge_cut
      hp c high hcanonPair.2 hhigh

  have hlowPair :
      low.Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤
            cutRayTheta hp c i b) :=
    pairwise_cutRayTheta_of_all_lt_cut
      hp c low hcanonPair.1 hlow

  have hcross :
      ∀ a ∈ high, ∀ b ∈ low,
        cutRayTheta hp c i a ≤
          cutRayTheta hp c i b := by
    intro a ha b hb
    rw [cutRayTheta_eq_sub_of_ge hp (hhigh a ha),
        cutRayTheta_eq_add_pi_sub_of_lt hp (hlow b hb)]
    have haPi := rayThetaAt_lt_pi hp i a
    have hb0 := rayThetaAt_nonneg hp i b
    linarith

  have hsorted :
      rays.Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤
            cutRayTheta hp c i b) := by
    dsimp [rays]
    exact List.pairwise_append.mpr
      ⟨hhighPair, hlowPair, hcross⟩

  exact ⟨{
    rays := rays
    complete := hcomplete
    nodup := hnodup
    nonempty := hnonempty
    cutTheta_sorted := hsorted
  }⟩

namespace CentreCutRayCycle

theorem mem_rays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    (R : CentreCutRayCycle hp i c)
    (j : OtherVertex i) :
    j ∈ R.rays := by
  have : j ∈ R.rays.toFinset := by
    rw [R.complete]
    simp
  simpa using this

noncomputable def rayEquiv
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    (R : CentreCutRayCycle hp i c) :
    Fin R.rays.length ≃ OtherVertex i := by
  classical
  exact R.nodup.getEquivOfForallMemList
    R.rays R.nodup (fun j => R.mem_rays j)

noncomputable def rayIndex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    (R : CentreCutRayCycle hp i c)
    (j : OtherVertex i) :
    Fin R.rays.length :=
  (R.rayEquiv).symm j

@[simp] theorem get_rayIndex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    (R : CentreCutRayCycle hp i c)
    (j : OtherVertex i) :
    R.rays.get (R.rayIndex j) = j := by
  change R.rayEquiv (R.rayIndex j) = j
  exact Equiv.apply_symm_apply R.rayEquiv j

theorem rayIndex_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    (R : CentreCutRayCycle hp i c) :
    Function.Injective R.rayIndex := by
  intro j k h
  have hget :=
    congrArg (fun q => R.rays.get q) h
  simpa using hget

theorem cutTheta_le_of_rayIndex_le
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    (R : CentreCutRayCycle hp i c)
    {j k : OtherVertex i}
    (hidx : R.rayIndex j ≤ R.rayIndex k) :
    cutRayTheta hp c i j ≤
      cutRayTheta hp c i k := by
  by_cases heq : R.rayIndex j = R.rayIndex k
  · have hjk : j = k := R.rayIndex_injective heq
    simp [hjk]
  · have hlt : R.rayIndex j < R.rayIndex k :=
      lt_of_le_of_ne hidx heq
    have hrel :=
      R.cutTheta_sorted.rel_get_of_lt hlt
    simpa using hrel

#print axioms exists_centreCutRayCycle
#print axioms CentreCutRayCycle.get_rayIndex
#print axioms CentreCutRayCycle.cutTheta_le_of_rayIndex_le

end CentreCutRayCycle
end JSP000404Research
