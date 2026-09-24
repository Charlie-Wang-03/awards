
import JSP000404Research.ProjectiveBandPartition
import Mathlib.Tactic

/-!
# Active colours are exactly occupied canonical projective bands

For one centre i, define its occupied projective bands as those unit bands
containing at least one canonical projective ray from i.

The direct ProjectiveBandPartition colours every edge by exactly this
projective band.  CanonicalRayReversal makes the same statement true at the
opposite endpoint of an incoming edge.

Hence the BinaryEdgePartition active-colour set at i is literally the set of
occupied canonical projective bands at i.

This is the local interface needed to compare global Hansel activity with the
CentreProjectiveCycle gap exponent.
-/

namespace JSP000404Research

open Real

noncomputable def occupiedProjectiveBands
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ) (n : ℕ) (i : V) :
    Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ j : OtherVertex i,
      RayInProjectiveBand hp t i j c

@[simp] theorem mem_occupiedProjectiveBands
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ) (n : ℕ) (i : V)
    (c : Fin (n + 1)) :
    c ∈ occupiedProjectiveBands hp t n i ↔
      ∃ j : OtherVertex i,
        RayInProjectiveBand hp t i j c := by
  classical
  simp [occupiedProjectiveBands]

/-- A ray at the first endpoint determines the edge's projective colour. -/
theorem projectiveBandColor_eq_of_lower_ray_mem
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v)
    (c : Fin (n + 1))
    (hc :
      RayInProjectiveBand hp t u ⟨v, huv.symm⟩ c) :
    projectiveBandColor hp ht n htop u v = c := by
  apply Fin.ext
  rw [projectiveBandColor_val hp ht n htop huv]
  have hx0 :
      0 ≤ normalizedRayTheta hp t u ⟨v, huv.symm⟩ :=
    normalizedRayTheta_nonneg hp ht.le u ⟨v, huv.symm⟩
  exact (Nat.floor_eq_iff hx0).2 (by
    simpa [RayInProjectiveBand] using hc)

/-- The same statement at the second endpoint, using projective reversal. -/
theorem projectiveBandColor_eq_of_upper_ray_mem
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {u v : V} (huv : u ≠ v)
    (c : Fin (n + 1))
    (hc :
      RayInProjectiveBand hp t v ⟨u, huv⟩ c) :
    projectiveBandColor hp ht n htop u v = c := by
  apply projectiveBandColor_eq_of_lower_ray_mem
    hp ht n htop huv c
  unfold RayInProjectiveBand at hc ⊢
  unfold normalizedRayTheta at hc ⊢
  have htheta :=
    rayThetaAt_reverse_eq hp huv
  rw [htheta]
  exact hc

/-- Exact active-set identification. -/
theorem projectiveBandPartition_active_eq_occupied
    {V : Type*} [LinearOrder V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V) :
    BinaryEdgePartition.active
        (projectiveBandPartition hp hcap ht hlam n htop) i
      =
    occupiedProjectiveBands hp t n i := by
  classical
  let P :=
    projectiveBandPartition hp hcap ht hlam n htop
  ext c
  constructor
  · intro hc
    have hc' :
        (∃ a, a < i ∧ P.edgeColor a i = c) ∨
        (∃ w, i < w ∧ P.edgeColor i w = c) := by
      simpa [BinaryEdgePartition.active, P] using hc
    apply (mem_occupiedProjectiveBands hp t n i c).2
    rcases hc' with ⟨a, hai, hcol⟩ | ⟨w, hiw, hcol⟩
    · let a' : OtherVertex i := ⟨a, ne_of_lt hai⟩
      refine ⟨a', ?_⟩
      have hmem :=
        projectiveBandColor_mem_upper
          hp ht n htop (ne_of_lt hai)
      change
        RayInProjectiveBand hp t i a'
          (projectiveBandColor hp ht n htop a i)
      simpa [P, a', hcol] using hmem
    · let w' : OtherVertex i := ⟨w, ne_of_gt hiw⟩
      refine ⟨w', ?_⟩
      have hmem :=
        projectiveBandColor_mem_lower
          hp ht n htop (ne_of_lt hiw)
      change
        RayInProjectiveBand hp t i w'
          (projectiveBandColor hp ht n htop i w)
      simpa [P, w', hcol] using hmem
  · intro hc
    obtain ⟨j, hjBand⟩ :=
      (mem_occupiedProjectiveBands hp t n i c).1 hc
    have hij : i ≠ j.1 := j.2.symm
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hcol :
          projectiveBandColor hp ht n htop i j.1 = c :=
        projectiveBandColor_eq_of_lower_ray_mem
          hp ht n htop hij c
          (by simpa using hjBand)
      have :
          (∃ a, a < i ∧ P.edgeColor a i = c) ∨
          (∃ w, i < w ∧ P.edgeColor i w = c) :=
        Or.inr ⟨j.1, hijlt, by simpa [P] using hcol⟩
      simpa [BinaryEdgePartition.active, P] using this
    · have hcol :
          projectiveBandColor hp ht n htop j.1 i = c :=
        projectiveBandColor_eq_of_upper_ray_mem
          hp ht n htop j.2 c
          (by simpa using hjBand)
      have :
          (∃ a, a < i ∧ P.edgeColor a i = c) ∨
          (∃ w, i < w ∧ P.edgeColor i w = c) :=
        Or.inl ⟨j.1, hjilt, by simpa [P] using hcol⟩
      simpa [BinaryEdgePartition.active, P] using this

/-- Cardinal form. -/
theorem projectiveBandPartition_active_card
    {V : Type*} [LinearOrder V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V) :
    (BinaryEdgePartition.active
      (projectiveBandPartition hp hcap ht hlam n htop) i).card
      =
    (occupiedProjectiveBands hp t n i).card := by
  rw [projectiveBandPartition_active_eq_occupied
    hp hcap ht hlam n htop i]

#print axioms projectiveBandColor_eq_of_lower_ray_mem
#print axioms projectiveBandPartition_active_eq_occupied
#print axioms projectiveBandPartition_active_card

end JSP000404Research
