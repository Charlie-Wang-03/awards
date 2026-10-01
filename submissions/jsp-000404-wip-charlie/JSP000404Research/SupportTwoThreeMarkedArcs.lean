import JSP000404Research.SupportThreeZeroAngleBlocks
import JSP000404Research.SupportTwoNarrowClusters
import JSP000404Research.CyclicActualAngles
import JSP000404Research.ThreeMarkedRayAngleSplit
import Mathlib.Tactic

/-!
# Three-arc pigeonhole for support-two cycles

If a cyclic quotient/angle list is cut into three consecutive arc blocks and
the total quotient support is two, then one of the three blocks has no positive
quotient.  Hence every angle in that block contributes to the global
zero-angle mass.

This is the purely combinatorial core needed to turn a support-two centre and
three marked rays into a delta-small marked pair.
-/

namespace JSP000404Research

theorem three_blocks_positiveCount_two_has_zero_block
    (q₁ q₂ q₃ : List ℕ)
    (hsupport :
      listPositiveCount (q₁ ++ q₂ ++ q₃) = 2) :
    listPositiveCount q₁ = 0 ∨
      listPositiveCount q₂ = 0 ∨
      listPositiveCount q₃ = 0 := by
  rw [listPositiveCount_append,
      listPositiveCount_append] at hsupport
  omega

theorem zero_block_angle_sum_le_global_zero_mass
    (q₁ q₂ q₃ : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen₁ : q₁.length = A₁.length)
    (hlen₂ : q₂.length = A₂.length)
    (hlen₃ : q₃.length = A₃.length)
    (hzero₁ : listPositiveCount q₁ = 0)
    (hA0 :
      ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A) :
    A₁.sum ≤
      listZeroAngleMass
        (q₁ ++ q₂ ++ q₃)
        (A₁ ++ A₂ ++ A₃) := by
  have hq₁ :
      ∀ q ∈ q₁, q = 0 :=
    listPositiveCount_eq_zero_forall q₁ hzero₁
  have hmass₁ :
      listZeroAngleMass q₁ A₁ = A₁.sum :=
    listZeroAngleMass_eq_angle_sum_of_all_zero
      q₁ A₁ hlen₁ hq₁
  have hA₂0 : ∀ A ∈ A₂, 0 ≤ A := by
    intro A hA
    exact hA0 A (by
      apply List.mem_append_right A₁
      apply List.mem_append_left
      exact hA)
  have hA₃0 : ∀ A ∈ A₃, 0 ≤ A := by
    intro A hA
    exact hA0 A (by
      apply List.mem_append_right A₁
      apply List.mem_append_right A₂
      exact hA)
  have hmass₂0 :
      0 ≤ listZeroAngleMass q₂ A₂ :=
    listZeroAngleMass_nonneg q₂ A₂ hA₂0
  have hmass₃0 :
      0 ≤ listZeroAngleMass q₃ A₃ :=
    listZeroAngleMass_nonneg q₃ A₃ hA₃0
  rw [listZeroAngleMass_append
      q₁ (q₂ ++ q₃) A₁ (A₂ ++ A₃) hlen₁]
  have hlen₂₃ :
      (q₂ ++ q₃).length = (A₂ ++ A₃).length := by
    simp [hlen₂,hlen₃]
  rw [listZeroAngleMass_append
      q₂ q₃ A₂ A₃ hlen₂]
  rw [hmass₁]
  linarith

theorem three_blocks_support_two_has_small_zero_arc
    (q₁ q₂ q₃ : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen₁ : q₁.length = A₁.length)
    (hlen₂ : q₂.length = A₂.length)
    (hlen₃ : q₃.length = A₃.length)
    (hsupport :
      listPositiveCount (q₁ ++ q₂ ++ q₃) = 2)
    (hA0 :
      ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A)
    {D : ℝ}
    (hmass :
      listZeroAngleMass
        (q₁ ++ q₂ ++ q₃)
        (A₁ ++ A₂ ++ A₃) ≤ D) :
    (
      listPositiveCount q₁ = 0 ∧ A₁.sum ≤ D
    )
    ∨
    (
      listPositiveCount q₂ = 0 ∧ A₂.sum ≤ D
    )
    ∨
    (
      listPositiveCount q₃ = 0 ∧ A₃.sum ≤ D
    ) := by
  rcases
    three_blocks_positiveCount_two_has_zero_block
      q₁ q₂ q₃ hsupport
    with h₁ | h₂ | h₃
  · left
    refine ⟨h₁,?_⟩
    exact (zero_block_angle_sum_le_global_zero_mass
      q₁ q₂ q₃ A₁ A₂ A₃
      hlen₁ hlen₂ hlen₃ h₁ hA0).trans hmass
  · right; left
    have hrotateSupport :
        listPositiveCount (q₂ ++ q₃ ++ q₁) = 2 := by
      rw [listPositiveCount_append,
          listPositiveCount_append,
          listPositiveCount_append,
          listPositiveCount_append] at hsupport ⊢
      omega
    have hrotateMass :
        listZeroAngleMass
            (q₂ ++ q₃ ++ q₁)
            (A₂ ++ A₃ ++ A₁)
          =
        listZeroAngleMass
            (q₁ ++ q₂ ++ q₃)
            (A₁ ++ A₂ ++ A₃) := by
      rw [listZeroAngleMass_append
          q₂ (q₃ ++ q₁) A₂ (A₃ ++ A₁) hlen₂]
      rw [listZeroAngleMass_append
          q₃ q₁ A₃ A₁ hlen₃]
      rw [listZeroAngleMass_append
          q₁ (q₂ ++ q₃) A₁ (A₂ ++ A₃) hlen₁]
      rw [listZeroAngleMass_append
          q₂ q₃ A₂ A₃ hlen₂]
      ring
    have hArot :
        ∀ A ∈ A₂ ++ A₃ ++ A₁, 0 ≤ A := by
      intro A hA
      simp only [List.mem_append] at hA ⊢
      rcases hA with hA | hA | hA
      · exact hA0 A (by simp [hA])
      · exact hA0 A (by simp [hA])
      · exact hA0 A (by simp [hA])
    refine ⟨h₂,?_⟩
    have hle :=
      zero_block_angle_sum_le_global_zero_mass
        q₂ q₃ q₁ A₂ A₃ A₁
        hlen₂ hlen₃ hlen₁ h₂ hArot
    rw [hrotateMass] at hle
    exact hle.trans hmass
  · right; right
    have hrotateMass :
        listZeroAngleMass
            (q₃ ++ q₁ ++ q₂)
            (A₃ ++ A₁ ++ A₂)
          =
        listZeroAngleMass
            (q₁ ++ q₂ ++ q₃)
            (A₁ ++ A₂ ++ A₃) := by
      rw [listZeroAngleMass_append
          q₃ (q₁ ++ q₂) A₃ (A₁ ++ A₂) hlen₃]
      rw [listZeroAngleMass_append
          q₁ q₂ A₁ A₂ hlen₁]
      rw [listZeroAngleMass_append
          q₁ (q₂ ++ q₃) A₁ (A₂ ++ A₃) hlen₁]
      rw [listZeroAngleMass_append
          q₂ q₃ A₂ A₃ hlen₂]
      ring
    have hArot :
        ∀ A ∈ A₃ ++ A₁ ++ A₂, 0 ≤ A := by
      intro A hA
      simp only [List.mem_append] at hA ⊢
      rcases hA with hA | hA | hA
      · exact hA0 A (by simp [hA])
      · exact hA0 A (by simp [hA])
      · exact hA0 A (by simp [hA])
    refine ⟨h₃,?_⟩
    have hle :=
      zero_block_angle_sum_le_global_zero_mass
        q₃ q₁ q₂ A₃ A₁ A₂
        hlen₃ hlen₁ hlen₂ h₃ hArot
    rw [hrotateMass] at hle
    exact hle.trans hmass

#print axioms three_blocks_positiveCount_two_has_zero_block
#print axioms zero_block_angle_sum_le_global_zero_mass
#print axioms three_blocks_support_two_has_small_zero_arc


/-- Geometry-facing wrapper: once three marked rays cut a support-two cycle
into three aligned arc blocks, one marked pair is D-small. -/
theorem three_marked_arcs_support_two_small_pair
    {V : Type*} {p : V → Plane}
    (i a b c : V)
    (q₁ q₂ q₃ : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen₁ : q₁.length = A₁.length)
    (hlen₂ : q₂.length = A₂.length)
    (hlen₃ : q₃.length = A₃.length)
    (hsupport :
      listPositiveCount (q₁ ++ q₂ ++ q₃) = 2)
    (hA0 :
      ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A)
    {D : ℝ}
    (hmass :
      listZeroAngleMass
        (q₁ ++ q₂ ++ q₃)
        (A₁ ++ A₂ ++ A₃) ≤ D)
    (hab :
      EuclideanGeometry.angle (p a) (p i) (p b) ≤ A₁.sum)
    (hbc :
      EuclideanGeometry.angle (p b) (p i) (p c) ≤ A₂.sum)
    (hca :
      EuclideanGeometry.angle (p c) (p i) (p a) ≤ A₃.sum) :
    EuclideanGeometry.angle (p a) (p i) (p b) ≤ D
    ∨ EuclideanGeometry.angle (p b) (p i) (p c) ≤ D
    ∨ EuclideanGeometry.angle (p c) (p i) (p a) ≤ D := by
  rcases
    three_blocks_support_two_has_small_zero_arc
      q₁ q₂ q₃ A₁ A₂ A₃
      hlen₁ hlen₂ hlen₃ hsupport hA0 hmass
    with h₁ | h₂ | h₃
  · exact Or.inl (hab.trans h₁.2)
  · exact Or.inr (Or.inl (hbc.trans h₂.2))
  · exact Or.inr (Or.inr (hca.trans h₃.2))

#print axioms three_marked_arcs_support_two_small_pair


/-- Synchronize an arbitrary quotient list with three already-separated angle
blocks by cutting at the two angle-block lengths. -/
theorem aligned_three_angle_blocks_support_two_small_pair
    {V : Type*} {p : V → Plane}
    (i a b c : V)
    (qs : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen :
      qs.length = (A₁ ++ A₂ ++ A₃).length)
    (hsupport : listPositiveCount qs = 2)
    (hA0 :
      ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A)
    {D : ℝ}
    (hmass :
      listZeroAngleMass qs (A₁ ++ A₂ ++ A₃) ≤ D)
    (hab :
      EuclideanGeometry.angle (p a) (p i) (p b) ≤ A₁.sum)
    (hbc :
      EuclideanGeometry.angle (p b) (p i) (p c) ≤ A₂.sum)
    (hca :
      EuclideanGeometry.angle (p c) (p i) (p a) ≤ A₃.sum) :
    EuclideanGeometry.angle (p a) (p i) (p b) ≤ D
    ∨ EuclideanGeometry.angle (p b) (p i) (p c) ≤ D
    ∨ EuclideanGeometry.angle (p c) (p i) (p a) ≤ D := by
  let q₁ := qs.take A₁.length
  let qrest := qs.drop A₁.length
  let q₂ := qrest.take A₂.length
  let q₃ := qrest.drop A₂.length

  have hA₁le : A₁.length ≤ qs.length := by
    rw [hlen]
    simp
  have hq₁len : q₁.length = A₁.length := by
    dsimp [q₁]
    rw [List.length_take]
    exact Nat.min_eq_left hA₁le
  have hrestLen :
      qrest.length = A₂.length + A₃.length := by
    dsimp [qrest]
    rw [List.length_drop, hlen]
    simp
  have hA₂le : A₂.length ≤ qrest.length := by
    rw [hrestLen]
    omega
  have hq₂len : q₂.length = A₂.length := by
    dsimp [q₂]
    rw [List.length_take]
    exact Nat.min_eq_left hA₂le
  have hq₃len : q₃.length = A₃.length := by
    dsimp [q₃]
    rw [List.length_drop, hrestLen]
    omega

  have hsplit₁ :
      q₁ ++ qrest = qs := by
    dsimp [q₁,qrest]
    exact List.take_append_drop A₁.length qs
  have hsplit₂ :
      q₂ ++ q₃ = qrest := by
    dsimp [q₂,q₃]
    exact List.take_append_drop A₂.length qrest
  have hsplit :
      q₁ ++ q₂ ++ q₃ = qs := by
    rw [← hsplit₂]
    simpa [List.append_assoc] using hsplit₁

  have hsupport' :
      listPositiveCount (q₁ ++ q₂ ++ q₃) = 2 := by
    rw [hsplit]
    exact hsupport
  have hmass' :
      listZeroAngleMass
          (q₁ ++ q₂ ++ q₃)
          (A₁ ++ A₂ ++ A₃) ≤ D := by
    rw [hsplit]
    exact hmass
  exact three_marked_arcs_support_two_small_pair
    (p := p) i a b c
    q₁ q₂ q₃ A₁ A₂ A₃
    hq₁len hq₂len hq₃len
    hsupport' hA0 hmass'
    hab hbc hca

#print axioms aligned_three_angle_blocks_support_two_small_pair

end JSP000404Research
