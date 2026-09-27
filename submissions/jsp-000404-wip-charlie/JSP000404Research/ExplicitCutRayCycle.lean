import JSP000404Research.CutCentreRayCycle
import Mathlib.Tactic

/-!
# Explicit centre cut cycle from a chosen canonical low/high split

CutCentreRayCycle proves existence of a cut-sorted cyclic rotation.  For the
final saturation-to-canonical-slot bridge we need to retain the actual split

  C.rays = low ++ high,

because the wrap edge of the rotated list high++low is then visibly the
canonical gap containing the cut.

This module packages the same construction with low/high supplied explicitly.
-/

namespace JSP000404Research

noncomputable def centreCutRayCycleOfSplit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (c : ℝ)
    (low high : List (OtherVertex i))
    (hdecomp : C.rays = low ++ high)
    (hlow : ∀ j ∈ low, rayThetaAt hp i j < c)
    (hhigh : ∀ j ∈ high, c ≤ rayThetaAt hp i j) :
    CentreCutRayCycle hp C c := by
  classical
  let rays := high ++ low
  have hperm : C.rays.Perm rays := by
    dsimp [rays]
    rw [hdecomp]
    exact List.Perm.append_comm low high
  have hnodup : rays.Nodup :=
    (hperm.nodup_iff).mp C.nodup
  have hcomplete : rays.toFinset = Finset.univ := by
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
  have hrotation :
      ∃ k : ℕ, rays = C.rays.rotate k := by
    refine ⟨low.length, ?_⟩
    dsimp [rays]
    rw [hdecomp, List.rotate_append_length_eq]
  exact {
    rays := rays
    rotation := hrotation
    complete := hcomplete
    nodup := hnodup
    nonempty := hnonempty
    cutTheta_sorted := hsorted
  }

@[simp] theorem centreCutRayCycleOfSplit_rays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (c : ℝ)
    (low high : List (OtherVertex i))
    (hdecomp : C.rays = low ++ high)
    (hlow : ∀ j ∈ low, rayThetaAt hp i j < c)
    (hhigh : ∀ j ∈ high, c ≤ rayThetaAt hp i j) :
    (centreCutRayCycleOfSplit
      hp C c low high hdecomp hlow hhigh).rays
      =
    high ++ low := by
  rfl

/-- Existence form retaining the canonical split and the exact rotated ray
list. -/
theorem exists_centreCutRayCycle_with_split
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (c : ℝ) :
    ∃ low high : List (OtherVertex i),
      ∃ R : CentreCutRayCycle hp C c,
        C.rays = low ++ high ∧
        (∀ j ∈ low, rayThetaAt hp i j < c) ∧
        (∀ j ∈ high, c ≤ rayThetaAt hp i j) ∧
        R.rays = high ++ low := by
  obtain ⟨low, high, hdecomp, hlow, hhigh⟩ :=
    exists_ray_split_at_cut hp C.rays C.theta_sorted c
  let R :=
    centreCutRayCycleOfSplit
      hp C c low high hdecomp hlow hhigh
  exact ⟨low, high, R, hdecomp, hlow, hhigh, rfl⟩

#print axioms centreCutRayCycleOfSplit
#print axioms exists_centreCutRayCycle_with_split

end JSP000404Research
