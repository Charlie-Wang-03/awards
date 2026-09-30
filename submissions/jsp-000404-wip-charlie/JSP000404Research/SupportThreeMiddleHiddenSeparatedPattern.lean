import JSP000404Research.SupportThreeMiddleHiddenLargeBridge
import JSP000404Research.MiddleHiddenClusterSeparation
import Mathlib.Tactic

/-!
# Enriched middle-hidden certificate

The earlier SmallPerfectMatchingAwayFromTop abstraction retained only the two
zero-quotient small edges.  That loses the three positive-transition angles.

This structure keeps the full five-ray information, on one common ordered
quadruple r,b,c,d:

  top --large-- r --small-- b --large-- c --small-- d --large-- top.

All four non-top vertices are distinct and avoid both top and the centre.
The derived cluster-separation theorem states that every inter-cluster angle
for

  {top}, {r,b}, {c,d}

is larger than lambda.
-/

namespace JSP000404Research

structure MiddleHiddenSeparatedPatternAwayFromTop
    {V : Type*} (p : V → Plane)
    (top i : V) (delta lam : ℝ) where
  r : OtherVertex i
  b : OtherVertex i
  c : OtherVertex i
  d : OtherVertex i
  r_ne_top : r.1 ≠ top
  b_ne_top : b.1 ≠ top
  c_ne_top : c.1 ≠ top
  d_ne_top : d.1 ≠ top
  r_ne_b : r ≠ b
  r_ne_c : r ≠ c
  r_ne_d : r ≠ d
  b_ne_c : b ≠ c
  b_ne_d : b ≠ d
  c_ne_d : c ≠ d
  small_sum :
    EuclideanGeometry.angle (p r.1) (p i) (p b.1) +
      EuclideanGeometry.angle (p c.1) (p i) (p d.1)
      ≤ delta * lam
  top_r_large :
    (1 + delta) * lam <
      EuclideanGeometry.angle (p top) (p i) (p r.1)
  bridge_large :
    (1 + delta) * lam <
      EuclideanGeometry.angle (p b.1) (p i) (p c.1)
  d_top_large :
    (1 + delta) * lam <
      EuclideanGeometry.angle (p d.1) (p i) (p top)

namespace MiddleHiddenSeparatedPatternAwayFromTop

theorem cluster_separation
    {V : Type*} {p : V → Plane}
    {top i : V} {delta lam : ℝ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hdelta0 : 0 ≤ delta)
    (hlampos : 0 < lam) :
    lam < EuclideanGeometry.angle (p top) (p i) (p M.r.1)
      ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p M.b.1)
      ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p M.c.1)
      ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p M.d.1)
      ∧
    lam < EuclideanGeometry.angle (p M.r.1) (p i) (p M.c.1)
      ∧
    lam < EuclideanGeometry.angle (p M.r.1) (p i) (p M.d.1)
      ∧
    lam < EuclideanGeometry.angle (p M.b.1) (p i) (p M.c.1)
      ∧
    lam < EuclideanGeometry.angle (p M.b.1) (p i) (p M.d.1) := by
  exact middle_hidden_cluster_separation
    (p := p) hdelta0 hlampos
    M.small_sum M.top_r_large M.bridge_large M.d_top_large

/-- Every non-top/non-centre vertex is one of the four displayed vertices in
the six-point case. -/
theorem covers_every_other_nonTop
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {top i : V} {delta lam : ℝ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hcard : Fintype.card V = 6)
    (hit : i ≠ top)
    {v : V}
    (hvt : v ≠ top)
    (hvi : v ≠ i) :
    v = M.r.1 ∨ v = M.b.1 ∨ v = M.c.1 ∨ v = M.d.1 := by
  classical
  let S : Finset V := {M.r.1, M.b.1, M.c.1, M.d.1}
  let U : Finset V := (Finset.univ.erase top).erase i
  have hScard : S.card = 4 := by
    dsimp [S]
    have hrb : M.r.1 ≠ M.b.1 := fun h => M.r_ne_b (Subtype.ext h)
    have hrc : M.r.1 ≠ M.c.1 := fun h => M.r_ne_c (Subtype.ext h)
    have hrd : M.r.1 ≠ M.d.1 := fun h => M.r_ne_d (Subtype.ext h)
    have hbc : M.b.1 ≠ M.c.1 := fun h => M.b_ne_c (Subtype.ext h)
    have hbd : M.b.1 ≠ M.d.1 := fun h => M.b_ne_d (Subtype.ext h)
    have hcd : M.c.1 ≠ M.d.1 := fun h => M.c_ne_d (Subtype.ext h)
    simp [hrb,hrc,hrd,hbc,hbd,hcd]
  have hUcard : U.card = 4 := by
    dsimp [U]
    have hiMem :
        i ∈ (Finset.univ.erase top : Finset V) := by
      simp [hit]
    rw [Finset.card_erase_of_mem hiMem,
        Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]
    norm_num
  have hSsub : S ⊆ U := by
    intro w hw
    dsimp [S] at hw
    dsimp [U]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · simp [M.r_ne_top, M.r.2]
    · simp [M.b_ne_top, M.b.2]
    · simp [M.c_ne_top, M.c.2]
    · simp [M.d_ne_top, M.d.2]
  have hSU : S = U := by
    apply Finset.eq_of_subset_of_card_le hSsub
    rw [hScard,hUcard]
  have hvU : v ∈ U := by
    dsimp [U]
    simp [hvt,hvi]
  have hvS : v ∈ S := by
    rw [hSU]
    exact hvU
  dsimp [S] at hvS
  simpa [Finset.mem_insert, Finset.mem_singleton] using hvS

end MiddleHiddenSeparatedPatternAwayFromTop

/-- A pinned middle-hidden support-three centre with three sign transitions
produces the enriched ordered angle certificate. -/
theorem support_three_middle_hidden_separated_pattern
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i : V}
    (hit : i ≠ top)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hmiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ i by simpa using hit) C)
    (hthree :
      ∃ first rest,
        C.rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 3) :
    Nonempty
      (MiddleHiddenSeparatedPatternAwayFromTop
        p top i delta lam) := by
  obtain ⟨r,b,c,d,
      hrTop,hbTop,hcTop,hdTop,
      hrb,hrc,hrd,hbc,hbd,hcd,
      hsmall,hTopR,hBridge,hDTop⟩ :=
    support_three_middle_hidden_large_bridge
      hp hcap C hcard hn hdelta0 hdeltaHalf
      ht hlam hit hexp hsupport hmiddle hthree
  exact ⟨{
    r := r
    b := b
    c := c
    d := d
    r_ne_top := hrTop
    b_ne_top := hbTop
    c_ne_top := hcTop
    d_ne_top := hdTop
    r_ne_b := hrb
    r_ne_c := hrc
    r_ne_d := hrd
    b_ne_c := hbc
    b_ne_d := hbd
    c_ne_d := hcd
    small_sum := hsmall
    top_r_large := hTopR
    bridge_large := hBridge
    d_top_large := hDTop
  }⟩

#print axioms MiddleHiddenSeparatedPatternAwayFromTop.cluster_separation
#print axioms support_three_middle_hidden_separated_pattern

end JSP000404Research
