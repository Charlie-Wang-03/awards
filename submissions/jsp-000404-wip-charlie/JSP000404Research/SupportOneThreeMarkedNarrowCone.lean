import JSP000404Research.FullQuotientZeroAngleMass
import JSP000404Research.SupportTwoThreeMarkedArcs
import JSP000404Research.CyclicEdgeRotation
import JSP000404Research.ThreeMarkedCyclicDecomposition
import JSP000404Research.DeficitTwo
import Mathlib.Tactic

/-!
# Three-marked narrow cone at a second-layer support-one centre

For quotient support one, three marked arcs contain only one positive quotient
in total.  Therefore, for each marked pair, either its direct arc is all-zero
or the complementary two arcs are both all-zero.

The zero-angle mass in the second-layer support-one regime is at most

  (1 + delta) * lambda.

Using the triangle inequality through the third marked ray in the second case,
all three marked pair angles satisfy the same bound.

This recovers exactly the local narrow-cone information needed by the
four-vertex whole-cube terminal without constructing a transition-interval
certificate.
-/

namespace JSP000404Research

theorem zeroAngleMass_three_cyclic_rotate
    (q₁ q₂ q₃ : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen₁ : q₁.length = A₁.length)
    (hlen₂ : q₂.length = A₂.length)
    (hlen₃ : q₃.length = A₃.length) :
    listZeroAngleMass
        (q₂ ++ q₃ ++ q₁)
        (A₂ ++ A₃ ++ A₁)
      =
    listZeroAngleMass
        (q₁ ++ q₂ ++ q₃)
        (A₁ ++ A₂ ++ A₃) := by
  rw [zeroAngleMass_append_three
      q₂ q₃ q₁ A₂ A₃ A₁ hlen₂ hlen₃ hlen₁]
  rw [zeroAngleMass_append_three
      q₁ q₂ q₃ A₁ A₂ A₃ hlen₁ hlen₂ hlen₃]
  ring

theorem two_zero_arc_sums_le_global_zero_mass
    (q₁ q₂ q₃ : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen₁ : q₁.length = A₁.length)
    (hlen₂ : q₂.length = A₂.length)
    (hlen₃ : q₃.length = A₃.length)
    (hzero₂ : listPositiveCount q₂ = 0)
    (hzero₃ : listPositiveCount q₃ = 0)
    (hA0 : ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A) :
    A₂.sum + A₃.sum ≤
      listZeroAngleMass
        (q₁ ++ q₂ ++ q₃)
        (A₁ ++ A₂ ++ A₃) := by
  have hq₂ :
      ∀ q ∈ q₂, q = 0 :=
    positiveCount_zero_forall q₂ hzero₂
  have hq₃ :
      ∀ q ∈ q₃, q = 0 :=
    positiveCount_zero_forall q₃ hzero₃
  have hm₂ :
      listZeroAngleMass q₂ A₂ = A₂.sum :=
    zeroAngleMass_eq_sum_of_all_zero
      q₂ A₂ hlen₂ hq₂
  have hm₃ :
      listZeroAngleMass q₃ A₃ = A₃.sum :=
    zeroAngleMass_eq_sum_of_all_zero
      q₃ A₃ hlen₃ hq₃
  have hA₁0 : ∀ A ∈ A₁, 0 ≤ A := by
    intro A hA
    exact hA0 A (by
      apply List.mem_append_left
      exact hA)
  have hm₁0 :
      0 ≤ listZeroAngleMass q₁ A₁ :=
    listZeroAngleMass_nonneg q₁ A₁ hA₁0
  rw [zeroAngleMass_append_three
      q₁ q₂ q₃ A₁ A₂ A₃ hlen₁ hlen₂ hlen₃]
  rw [hm₂, hm₃]
  linarith

/-- Pure three-block support-one theorem: every marked pair is controlled by
the total zero-angle mass. -/
theorem three_marked_arcs_support_one_all_pairs
    {V : Type*} {p : V → Plane}
    (i a b c : V)
    (q₁ q₂ q₃ : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen₁ : q₁.length = A₁.length)
    (hlen₂ : q₂.length = A₂.length)
    (hlen₃ : q₃.length = A₃.length)
    (hsupport :
      listPositiveCount (q₁ ++ q₂ ++ q₃) = 1)
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
    ∧
    EuclideanGeometry.angle (p b) (p i) (p c) ≤ D
    ∧
    EuclideanGeometry.angle (p c) (p i) (p a) ≤ D := by
  have hcount :
      listPositiveCount q₁ +
        listPositiveCount q₂ +
        listPositiveCount q₃ = 1 := by
    simpa [positiveCount_append, add_assoc] using hsupport

  have hAB :
      EuclideanGeometry.angle (p a) (p i) (p b) ≤ D := by
    by_cases hq₁ : listPositiveCount q₁ = 0
    · exact hab.trans
        ((zero_block_angle_sum_le_global_zero_mass
          q₁ q₂ q₃ A₁ A₂ A₃
          hlen₁ hlen₂ hlen₃ hq₁ hA0).trans hmass)
    · have hq₂ : listPositiveCount q₂ = 0 := by omega
      have hq₃ : listPositiveCount q₃ = 0 := by omega
      have h23 :=
        two_zero_arc_sums_le_global_zero_mass
          q₁ q₂ q₃ A₁ A₂ A₃
          hlen₁ hlen₂ hlen₃ hq₂ hq₃ hA0
      have htri :=
        EuclideanGeometry.angle_le_angle_add_angle
          (p i) (p a) (p c) (p b)
      have hac' :
          EuclideanGeometry.angle (p a) (p i) (p c) ≤ A₃.sum := by
        simpa [EuclideanGeometry.angle_comm] using hca
      have hcb' :
          EuclideanGeometry.angle (p c) (p i) (p b) ≤ A₂.sum := by
        simpa [EuclideanGeometry.angle_comm] using hbc
      linarith

  have hBC :
      EuclideanGeometry.angle (p b) (p i) (p c) ≤ D := by
    by_cases hq₂ : listPositiveCount q₂ = 0
    · have hrotMass :=
        zeroAngleMass_three_cyclic_rotate
          q₁ q₂ q₃ A₁ A₂ A₃ hlen₁ hlen₂ hlen₃
      have hArot :
          ∀ A ∈ A₂ ++ A₃ ++ A₁, 0 ≤ A := by
        intro A hA
        apply hA0 A
        simp only [List.mem_append] at hA ⊢
        aesop
      have hle :=
        zero_block_angle_sum_le_global_zero_mass
          q₂ q₃ q₁ A₂ A₃ A₁
          hlen₂ hlen₃ hlen₁ hq₂ hArot
      rw [hrotMass] at hle
      exact hbc.trans (hle.trans hmass)
    · have hq₁ : listPositiveCount q₁ = 0 := by omega
      have hq₃ : listPositiveCount q₃ = 0 := by omega
      have h31 :=
        two_zero_arc_sums_le_global_zero_mass
          q₂ q₃ q₁ A₂ A₃ A₁
          hlen₂ hlen₃ hlen₁ hq₃ hq₁
          (by
            intro A hA
            apply hA0 A
            simp only [List.mem_append] at hA ⊢
            aesop)
      have hrotMass :=
        zeroAngleMass_three_cyclic_rotate
          q₁ q₂ q₃ A₁ A₂ A₃ hlen₁ hlen₂ hlen₃
      rw [hrotMass] at h31
      have htri :=
        EuclideanGeometry.angle_le_angle_add_angle
          (p i) (p b) (p a) (p c)
      have hba' :
          EuclideanGeometry.angle (p b) (p i) (p a) ≤ A₁.sum := by
        simpa [EuclideanGeometry.angle_comm] using hab
      have hac' :
          EuclideanGeometry.angle (p a) (p i) (p c) ≤ A₃.sum := by
        simpa [EuclideanGeometry.angle_comm] using hca
      linarith

  have hCA :
      EuclideanGeometry.angle (p c) (p i) (p a) ≤ D := by
    by_cases hq₃ : listPositiveCount q₃ = 0
    · have hrot1 :=
        zeroAngleMass_three_cyclic_rotate
          q₁ q₂ q₃ A₁ A₂ A₃ hlen₁ hlen₂ hlen₃
      have hrot2 :=
        zeroAngleMass_three_cyclic_rotate
          q₂ q₃ q₁ A₂ A₃ A₁ hlen₂ hlen₃ hlen₁
      have hArot :
          ∀ A ∈ A₃ ++ A₁ ++ A₂, 0 ≤ A := by
        intro A hA
        apply hA0 A
        simp only [List.mem_append] at hA ⊢
        aesop
      have hle :=
        zero_block_angle_sum_le_global_zero_mass
          q₃ q₁ q₂ A₃ A₁ A₂
          hlen₃ hlen₁ hlen₂ hq₃ hArot
      rw [hrot2, hrot1] at hle
      exact hca.trans (hle.trans hmass)
    · have hq₁ : listPositiveCount q₁ = 0 := by omega
      have hq₂ : listPositiveCount q₂ = 0 := by omega
      have h12 :=
        two_zero_arc_sums_le_global_zero_mass
          q₃ q₁ q₂ A₃ A₁ A₂
          hlen₃ hlen₁ hlen₂ hq₁ hq₂
          (by
            intro A hA
            apply hA0 A
            simp only [List.mem_append] at hA ⊢
            aesop)
      have hrot1 :=
        zeroAngleMass_three_cyclic_rotate
          q₁ q₂ q₃ A₁ A₂ A₃ hlen₁ hlen₂ hlen₃
      have hrot2 :=
        zeroAngleMass_three_cyclic_rotate
          q₂ q₃ q₁ A₂ A₃ A₁ hlen₂ hlen₃ hlen₁
      rw [hrot2, hrot1] at h12
      have htri :=
        EuclideanGeometry.angle_le_angle_add_angle
          (p i) (p c) (p b) (p a)
      have hcb' :
          EuclideanGeometry.angle (p c) (p i) (p b) ≤ A₂.sum := by
        simpa [EuclideanGeometry.angle_comm] using hbc
      have hba' :
          EuclideanGeometry.angle (p b) (p i) (p a) ≤ A₁.sum := by
        simpa [EuclideanGeometry.angle_comm] using hab
      linarith

  exact ⟨hAB,hBC,hCA⟩

/-- Synchronize an arbitrary support-one quotient list with three already
separated angle blocks. -/
theorem aligned_three_angle_blocks_support_one_all_pairs
    {V : Type*} {p : V → Plane}
    (i a b c : V)
    (qs : List ℕ)
    (A₁ A₂ A₃ : List ℝ)
    (hlen : qs.length = (A₁ ++ A₂ ++ A₃).length)
    (hsupport : listPositiveCount qs = 1)
    (hA0 : ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A)
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
    ∧
    EuclideanGeometry.angle (p b) (p i) (p c) ≤ D
    ∧
    EuclideanGeometry.angle (p c) (p i) (p a) ≤ D := by
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
  have hsplit₁ : q₁ ++ qrest = qs := by
    dsimp [q₁,qrest]
    exact List.take_append_drop A₁.length qs
  have hsplit₂ : q₂ ++ q₃ = qrest := by
    dsimp [q₂,q₃]
    exact List.take_append_drop A₂.length qrest
  have hsplit : q₁ ++ q₂ ++ q₃ = qs := by
    rw [List.append_assoc, hsplit₂]
    exact hsplit₁
  have hsupport' :
      listPositiveCount (q₁ ++ q₂ ++ q₃) = 1 := by
    rw [hsplit]
    exact hsupport
  have hmass' :
      listZeroAngleMass
          (q₁ ++ q₂ ++ q₃)
          (A₁ ++ A₂ ++ A₃) ≤ D := by
    rw [hsplit]
    exact hmass
  exact three_marked_arcs_support_one_all_pairs
    (p := p) i a b c
    q₁ q₂ q₃ A₁ A₂ A₃
    hq₁len hq₂len hq₃len
    hsupport' hA0 hmass'
    hab hbc hca

/-- Geometry-facing rotated-cycle theorem. -/
theorem supportOne_three_marked_all_pairs_of_rotated_decomposition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1)
    (a b c : OtherVertex i)
    (X Y Z : List (OtherVertex i))
    (k : ℕ)
    (hrot :
      C.rays.rotate k =
        a :: (X ++ b :: Y ++ c :: Z)) :
    EuclideanGeometry.angle (p a.1) (p i) (p b.1)
        ≤ (1 + delta) * lam
    ∧
    EuclideanGeometry.angle (p b.1) (p i) (p c.1)
        ≤ (1 + delta) * lam
    ∧
    EuclideanGeometry.angle (p c.1) (p i) (p a.1)
        ≤ (1 + delta) * lam := by
  classical
  obtain ⟨first0,rest0,hrays0⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases hR : C.rays with
    | nil => exact False.elim (C.nonempty hR)
    | cons first rest => exact ⟨first,rest,rfl⟩

  let qs := quotientList t C.gaps
  let As := cyclicRayAngles (p := p) i first0 rest0
  let qR := qs.rotate k
  let AR := As.rotate k

  have hqA : qs.length = As.length := by
    dsimp [qs,As]
    rw [quotientList_length, C.gaps_length,
        cyclicRayAngles_length]
    simpa [hrays0]

  have hsupport0 :
      listPositiveCount qs = 1 := by
    dsimp [qs]
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hsupportR :
      listPositiveCount qR = 1 := by
    dsimp [qR]
    rw [listPositiveCount_rotate]
    exact hsupport0

  have hdelta1 : delta < 1 := by linarith
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 2 := by
    change n - centreExponent C t = 2
    rw [hexp]
    omega
  have hstruct :=
    deficit_two_structure
      (centreQuotient C t) n hn3 hQ hdef
  have hsumFn :
      (∑ r, centreQuotient C t r) = n - 1 := by
    rcases hstruct with h1 | h2
    · exact h1.2
    · rw [hsupport] at h2
      omega
  have hsumList :
      (quotientList t C.gaps).sum = n - 1 := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn

  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have htone : 1 ≤ t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hmass0 :
      listZeroAngleMass qs As ≤ (1 + delta) * lam := by
    dsimp [qs,As]
    exact
      centre_zeroAngleMass_le_one_add_delta_lam_of_quotient_sum_n_sub_one
        hp hcap (by omega : 1 ≤ n) ht htpos htone hlam
        i C first0 rest0 hrays0 hsumList
  have hmassR :
      listZeroAngleMass qR AR ≤ (1 + delta) * lam := by
    dsimp [qR,AR]
    rw [listZeroAngleMass_rotate qs As hqA k]
    exact hmass0

  let w :=
    fun u v : OtherVertex i =>
      EuclideanGeometry.angle (p u.1) (p i) (p v.1)
  have hAsEdge :
      As = cyclicEdgeValues w C.rays := by
    dsimp [As,w]
    rw [hrays0]
    exact cyclicRayAngles_eq_cyclicEdgeValues
      (p := p) i first0 rest0
  have hAR :
      AR =
        cyclicRayAngles (p := p) i a
          (X ++ b :: Y ++ c :: Z) := by
    calc
      AR = As.rotate k := rfl
      _ = (cyclicEdgeValues w C.rays).rotate k := by rw [hAsEdge]
      _ = cyclicEdgeValues w (C.rays.rotate k) := by
          symm
          exact cyclicEdgeValues_rotate w C.rays k
      _ = cyclicEdgeValues w
            (a :: (X ++ b :: Y ++ c :: Z)) := by rw [hrot]
      _ = cyclicRayAngles (p := p) i a
            (X ++ b :: Y ++ c :: Z) := by
          symm
          exact cyclicRayAngles_eq_cyclicEdgeValues
            (p := p) i a (X ++ b :: Y ++ c :: Z)

  let A₁ := consecutiveRayAngles (p := p) i a (X ++ [b])
  let A₂ := consecutiveRayAngles (p := p) i b (Y ++ [c])
  let A₃ := consecutiveRayAngles (p := p) i c (Z ++ [a])
  have hsplitA : AR = A₁ ++ A₂ ++ A₃ := by
    rw [hAR]
    dsimp [A₁,A₂,A₃]
    exact cyclicRayAngles_three_marked_split
      (p := p) i a b c X Y Z

  have hlen :
      qR.length = (A₁ ++ A₂ ++ A₃).length := by
    have hrotLen : qR.length = AR.length := by
      dsimp [qR,AR]
      simpa using hqA
    rw [hsplitA] at hrotLen
    exact hrotLen
  have hA0 :
      ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A := by
    intro A hA
    have hARmem : A ∈ AR := by
      rw [hsplitA]
      exact hA
    rw [hAR] at hARmem
    exact all_cyclicRayAngles_nonneg
      (p := p) i a (X ++ b :: Y ++ c :: Z) A hARmem
  have hmass :
      listZeroAngleMass qR (A₁ ++ A₂ ++ A₃)
        ≤ (1 + delta) * lam := by
    rw [← hsplitA]
    exact hmassR
  have hpaths :=
    three_marked_path_endpoint_bounds
      (p := p) i a b c X Y Z
  exact aligned_three_angle_blocks_support_one_all_pairs
    (p := p) i a.1 b.1 c.1
    qR A₁ A₂ A₃ hlen hsupportR hA0 hmass
    hpaths.1 hpaths.2.1 hpaths.2.2

/-- Order-free four-point form: at a second-layer support-one centre, any
three distinct other vertices are pairwise seen inside the narrow cone. -/
theorem supportOne_three_other_vertices_all_angles_le_one_add_delta_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i a b c : V}
    (hia : i ≠ a) (hib : i ≠ b) (hic : i ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    EuclideanGeometry.angle (p a) (p i) (p b)
        ≤ (1 + delta) * lam
    ∧
    EuclideanGeometry.angle (p b) (p i) (p c)
        ≤ (1 + delta) * lam
    ∧
    EuclideanGeometry.angle (p c) (p i) (p a)
        ≤ (1 + delta) * lam := by
  classical
  let ao : OtherVertex i := ⟨a,hia.symm⟩
  let bo : OtherVertex i := ⟨b,hib.symm⟩
  let co : OtherVertex i := ⟨c,hic.symm⟩
  have hao : ao ∈ C.rays := C.mem_rays_iff ao
  have hbo : bo ∈ C.rays := C.mem_rays_iff bo
  have hco : co ∈ C.rays := C.mem_rays_iff co
  have habo : ao ≠ bo := by
    intro h; exact hab (congrArg Subtype.val h)
  have haco : ao ≠ co := by
    intro h; exact hac (congrArg Subtype.val h)
  have hbco : bo ≠ co := by
    intro h; exact hbc (congrArg Subtype.val h)
  obtain ⟨k,horder | horder⟩ :=
    three_marked_cyclic_decomposition
      C.rays hao hbo hco habo haco hbco
  · obtain ⟨X,Y,Z,hrot⟩ := horder
    simpa [ao,bo,co] using
      (supportOne_three_marked_all_pairs_of_rotated_decomposition
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        C hexp hsupport ao bo co X Y Z k hrot)
  · obtain ⟨X,Y,Z,hrot⟩ := horder
    have h :=
      supportOne_three_marked_all_pairs_of_rotated_decomposition
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        C hexp hsupport ao co bo X Y Z k hrot
    rcases h with ⟨hAC,hCB,hBA⟩
    exact ⟨
      by simpa [ao,bo,co,EuclideanGeometry.angle_comm] using hBA,
      by simpa [ao,bo,co,EuclideanGeometry.angle_comm] using hCB,
      by simpa [ao,bo,co,EuclideanGeometry.angle_comm] using hAC
    ⟩

#print axioms three_marked_arcs_support_one_all_pairs
#print axioms aligned_three_angle_blocks_support_one_all_pairs
#print axioms supportOne_three_other_vertices_all_angles_le_one_add_delta_lam

end JSP000404Research
