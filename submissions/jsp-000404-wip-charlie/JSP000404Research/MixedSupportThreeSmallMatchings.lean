import JSP000404Research.MixedSupportThreeNonExposed
import JSP000404Research.SixPointHardSupportReduction
import JSP000404Research.SupportThreeMiddleHiddenMatching
import Mathlib.Tactic

/-!
# Two small perfect matchings in the hard mixed branch

In the mixed six-point hard branch, fix a support-one minimum a.

The exposure budget forces two further minima b,c to be non-exposed
support-three centres.  If compensated minimum deletion is excluded, every
support-three centre is forced into the pinned middle-hidden shape.  Each such
shape supplies two disjoint non-top angular edges whose total angle is at most
delta*lambda.

Because there are exactly five minima, the four endpoints at each centre are
precisely all other minima.  Thus each centre carries a perfect matching on the
remaining four minima.

This packages the remaining mixed branch as a finite five-vertex matching
problem.
-/

namespace JSP000404Research

structure SmallPerfectMatchingAwayFromTop
    {V : Type*} {p : V → Plane}
    (top i : V) (delta lam : ℝ) where
  a : OtherVertex i
  b : OtherVertex i
  c : OtherVertex i
  d : OtherVertex i
  a_ne_top : a.1 ≠ top
  b_ne_top : b.1 ≠ top
  c_ne_top : c.1 ≠ top
  d_ne_top : d.1 ≠ top
  a_ne_b : a ≠ b
  a_ne_c : a ≠ c
  a_ne_d : a ≠ d
  b_ne_c : b ≠ c
  b_ne_d : b ≠ d
  c_ne_d : c ≠ d
  small_sum :
    EuclideanGeometry.angle (p a.1) (p i) (p b.1) +
      EuclideanGeometry.angle (p c.1) (p i) (p d.1)
      ≤ delta * lam

namespace SmallPerfectMatchingAwayFromTop

theorem covers_every_other_nonTop
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {top i : V} {delta lam : ℝ}
    (M : SmallPerfectMatchingAwayFromTop
      (p := p) top i delta lam)
    (hcard : Fintype.card V = 6)
    (hit : i ≠ top)
    {v : V}
    (hvt : v ≠ top)
    (hvi : v ≠ i) :
    v = M.a.1 ∨ v = M.b.1 ∨
      v = M.c.1 ∨ v = M.d.1 := by
  classical
  let S : Finset V := {M.a.1, M.b.1, M.c.1, M.d.1}
  let U : Finset V := (Finset.univ.erase top).erase i

  have habv : M.a.1 ≠ M.b.1 := by
    intro h
    exact M.a_ne_b (Subtype.ext h)
  have hacv : M.a.1 ≠ M.c.1 := by
    intro h
    exact M.a_ne_c (Subtype.ext h)
  have hadv : M.a.1 ≠ M.d.1 := by
    intro h
    exact M.a_ne_d (Subtype.ext h)
  have hbcv : M.b.1 ≠ M.c.1 := by
    intro h
    exact M.b_ne_c (Subtype.ext h)
  have hbdv : M.b.1 ≠ M.d.1 := by
    intro h
    exact M.b_ne_d (Subtype.ext h)
  have hcdv : M.c.1 ≠ M.d.1 := by
    intro h
    exact M.c_ne_d (Subtype.ext h)

  have hScard : S.card = 4 := by
    dsimp [S]
    simp [habv, hacv, hadv, hbcv, hbdv, hcdv]

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
    intro x hx
    dsimp [S] at hx
    dsimp [U]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [M.a_ne_top, M.a.2]
    · simp [M.b_ne_top, M.b.2]
    · simp [M.c_ne_top, M.c.2]
    · simp [M.d_ne_top, M.d.2]

  have hSU : S = U := by
    apply Finset.eq_of_subset_of_card_le hSsub
    rw [hScard, hUcard]

  have hvU : v ∈ U := by
    dsimp [U]
    simp [hvt, hvi]
  have hvS : v ∈ S := by
    rw [hSU]
    exact hvU
  dsimp [S] at hvS
  simpa [Finset.mem_insert, Finset.mem_singleton] using hvS

/-- Reorient the perfect matching so that a prescribed other minimum v is the
first endpoint.  The partner x and the remaining pair y-z are all distinct,
non-top, and different from the centre. -/
theorem reorient_around
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {top i : V} {delta lam : ℝ}
    (M : SmallPerfectMatchingAwayFromTop
      (p := p) top i delta lam)
    (hcard : Fintype.card V = 6)
    (hit : i ≠ top)
    {v : V}
    (hvt : v ≠ top)
    (hvi : v ≠ i) :
    ∃ x y z : V,
      x ≠ top ∧ y ≠ top ∧ z ≠ top ∧
      x ≠ i ∧ y ≠ i ∧ z ≠ i ∧
      x ≠ v ∧ y ≠ v ∧ z ≠ v ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EuclideanGeometry.angle (p v) (p i) (p x) +
        EuclideanGeometry.angle (p y) (p i) (p z)
        ≤ delta * lam := by
  rcases M.covers_every_other_nonTop hcard hit hvt hvi with
    hvA | hvB | hvC | hvD
  · refine ⟨M.b.1, M.c.1, M.d.1,
      M.b_ne_top, M.c_ne_top, M.d_ne_top,
      M.b.2, M.c.2, M.d.2, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · intro h
      apply M.a_ne_b
      apply Subtype.ext
      simpa [hvA] using h.symm
    · intro h
      apply M.a_ne_c
      apply Subtype.ext
      simpa [hvA] using h.symm
    · intro h
      apply M.a_ne_d
      apply Subtype.ext
      simpa [hvA] using h.symm
    · intro h; exact M.b_ne_c (Subtype.ext h)
    · intro h; exact M.b_ne_d (Subtype.ext h)
    · intro h; exact M.c_ne_d (Subtype.ext h)
    · simpa [hvA] using M.small_sum
  · refine ⟨M.a.1, M.c.1, M.d.1,
      M.a_ne_top, M.c_ne_top, M.d_ne_top,
      M.a.2, M.c.2, M.d.2, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · intro h
      apply M.a_ne_b
      apply Subtype.ext
      simpa [hvB] using h
    · intro h
      apply M.b_ne_c
      apply Subtype.ext
      simpa [hvB] using h.symm
    · intro h
      apply M.b_ne_d
      apply Subtype.ext
      simpa [hvB] using h.symm
    · intro h; exact M.a_ne_c (Subtype.ext h)
    · intro h; exact M.a_ne_d (Subtype.ext h)
    · intro h; exact M.c_ne_d (Subtype.ext h)
    · have hcomm :
          EuclideanGeometry.angle (p M.a.1) (p i) (p M.b.1) =
            EuclideanGeometry.angle (p M.b.1) (p i) (p M.a.1) :=
        EuclideanGeometry.angle_comm _ _ _
      simpa [hvB, hcomm] using M.small_sum
  · refine ⟨M.d.1, M.a.1, M.b.1,
      M.d_ne_top, M.a_ne_top, M.b_ne_top,
      M.d.2, M.a.2, M.b.2, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · intro h
      apply M.c_ne_d
      apply Subtype.ext
      simpa [hvC] using h.symm
    · intro h
      apply M.a_ne_c
      apply Subtype.ext
      simpa [hvC] using h
    · intro h
      apply M.b_ne_c
      apply Subtype.ext
      simpa [hvC] using h
    · intro h; exact M.a_ne_d (Subtype.ext h.symm)
    · intro h; exact M.b_ne_d (Subtype.ext h.symm)
    · intro h; exact M.a_ne_b (Subtype.ext h)
    · have hcomm :
          EuclideanGeometry.angle (p M.c.1) (p i) (p M.d.1) =
            EuclideanGeometry.angle (p M.d.1) (p i) (p M.c.1) :=
        EuclideanGeometry.angle_comm _ _ _
      simpa [hvC, hcomm, add_comm] using M.small_sum
  · refine ⟨M.c.1, M.a.1, M.b.1,
      M.c_ne_top, M.a_ne_top, M.b_ne_top,
      M.c.2, M.a.2, M.b.2, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · intro h
      apply M.c_ne_d
      apply Subtype.ext
      simpa [hvD] using h
    · intro h
      apply M.a_ne_d
      apply Subtype.ext
      simpa [hvD] using h
    · intro h
      apply M.b_ne_d
      apply Subtype.ext
      simpa [hvD] using h
    · intro h; exact M.a_ne_c (Subtype.ext h.symm)
    · intro h; exact M.b_ne_c (Subtype.ext h.symm)
    · intro h; exact M.a_ne_b (Subtype.ext h)
    · simpa [hvD, add_comm] using M.small_sum

theorem three_remaining_vertices_exhaust
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 6)
    {top b c x y z : V}
    (hTopB : top ≠ b)
    (hTopC : top ≠ c)
    (hbc : b ≠ c)
    (hxTop : x ≠ top) (hyTop : y ≠ top) (hzTop : z ≠ top)
    (hxB : x ≠ b) (hyB : y ≠ b) (hzB : z ≠ b)
    (hxC : x ≠ c) (hyC : y ≠ c) (hzC : z ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {v : V}
    (hvTop : v ≠ top) (hvB : v ≠ b) (hvC : v ≠ c) :
    v = x ∨ v = y ∨ v = z := by
  classical
  let S : Finset V := {x,y,z}
  let U : Finset V := (((Finset.univ.erase top).erase b).erase c)
  have hScard : S.card = 3 := by
    dsimp [S]
    simp [hxy,hxz,hyz]
  have hUcard : U.card = 3 := by
    dsimp [U]
    have hbMem :
        b ∈ (Finset.univ.erase top : Finset V) := by
      simp [hTopB.symm]
    have hcMem :
        c ∈ ((Finset.univ.erase top).erase b : Finset V) := by
      simp [hTopC.symm, hbc.symm]
    rw [Finset.card_erase_of_mem hcMem,
        Finset.card_erase_of_mem hbMem,
        Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]
    norm_num
  have hSsub : S ⊆ U := by
    intro w hw
    dsimp [S] at hw
    dsimp [U]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simp [hxTop, hxB, hxC]
    · simp [hyTop, hyB, hyC]
    · simp [hzTop, hzB, hzC]
  have hSU : S = U := by
    apply Finset.eq_of_subset_of_card_le hSsub
    rw [hScard,hUcard]
  have hvU : v ∈ U := by
    dsimp [U]
    simp [hvTop,hvB,hvC]
  have hvS : v ∈ S := by
    rw [hSU]
    exact hvU
  dsimp [S] at hvS
  simpa [Finset.mem_insert, Finset.mem_singleton] using hvS

/-- Two small perfect matchings at distinct centres can be reoriented
around each other with distinct partners.  Equal partners would give a
triangle with two delta-small angles. -/
theorem two_smallPerfectMatchings_have_distinct_partners
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {top b c : V} {delta lam : ℝ}
    (hcard : Fintype.card V = 6)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    (hbTop : b ≠ top)
    (hcTop : c ≠ top)
    (hbc : b ≠ c)
    (Mb : SmallPerfectMatchingAwayFromTop
      (p := p) top b delta lam)
    (Mc : SmallPerfectMatchingAwayFromTop
      (p := p) top c delta lam) :
    ∃ xb yb zb xc yc zc : V,
      xb ≠ top ∧ yb ≠ top ∧ zb ≠ top ∧
      xb ≠ b ∧ yb ≠ b ∧ zb ≠ b ∧
      xb ≠ c ∧ yb ≠ c ∧ zb ≠ c ∧
      xb ≠ yb ∧ xb ≠ zb ∧ yb ≠ zb ∧
      xc ≠ top ∧ yc ≠ top ∧ zc ≠ top ∧
      xc ≠ c ∧ yc ≠ c ∧ zc ≠ c ∧
      xc ≠ b ∧ yc ≠ b ∧ zc ≠ b ∧
      xc ≠ yc ∧ xc ≠ zc ∧ yc ≠ zc ∧
      xb ≠ xc ∧
      EuclideanGeometry.angle (p c) (p b) (p xb) +
          EuclideanGeometry.angle (p yb) (p b) (p zb)
        ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p c) (p xc) +
          EuclideanGeometry.angle (p yc) (p c) (p zc)
        ≤ delta * lam := by
  obtain ⟨xb,yb,zb,
      hxbTop,hybTop,hzbTop,
      hxbB,hybB,hzbB,
      hxbC,hybC,hzbC,
      hxbYb,hxbZb,hybZb,hsmallB⟩ :=
    Mb.reorient_around hcard hbTop hcTop hbc.symm
  obtain ⟨xc,yc,zc,
      hxcTop,hycTop,hzcTop,
      hxcC,hycC,hzcC,
      hxcB,hycB,hzcB,
      hxcYc,hxcZc,hycZc,hsmallC⟩ :=
    Mc.reorient_around hcard hcTop hbTop hbc
  have hpartner : xb ≠ xc := by
    intro hEq
    subst xc
    have hzeroB :
        0 ≤ EuclideanGeometry.angle (p yb) (p b) (p zb) :=
      EuclideanGeometry.angle_nonneg _ _ _
    have hzeroC :
        0 ≤ EuclideanGeometry.angle (p yc) (p c) (p zc) :=
      EuclideanGeometry.angle_nonneg _ _ _
    have hsmallB0 :
        EuclideanGeometry.angle (p c) (p b) (p xb)
          ≤ delta * lam := by
      linarith
    have hsmallC0 :
        EuclideanGeometry.angle (p b) (p c) (p xb)
          ≤ delta * lam := by
      linarith
    exact impossible_two_delta_small_angles_under_cap
      hp hcap hdeltaHalf hlam
      hbc hxbB hxbC
      hsmallB0 hsmallC0
  exact ⟨xb,yb,zb,xc,yc,zc,
    hxbTop,hybTop,hzbTop,
    hxbB,hybB,hzbB,
    hxbC,hybC,hzbC,
    hxbYb,hxbZb,hybZb,
    hxcTop,hycTop,hzcTop,
    hxcC,hycC,hzcC,
    hxcB,hycB,hzcB,
    hxcYc,hxcZc,hycZc,
    hpartner,hsmallB,hsmallC⟩

/-- Complete finite classification of the no-direct-triangle branch.  Two
small perfect matchings at b and c force a Hamiltonian-path pattern through
the three remaining minima. -/
theorem two_smallPerfectMatchings_hamiltonian_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {top b c : V} {delta lam : ℝ}
    (hcard : Fintype.card V = 6)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    (hbTop : b ≠ top)
    (hcTop : c ≠ top)
    (hbc : b ≠ c)
    (Mb : SmallPerfectMatchingAwayFromTop
      (p := p) top b delta lam)
    (Mc : SmallPerfectMatchingAwayFromTop
      (p := p) top c delta lam) :
    ∃ x y z : V,
      x ≠ top ∧ y ≠ top ∧ z ≠ top ∧
      x ≠ b ∧ y ≠ b ∧ z ≠ b ∧
      x ≠ c ∧ y ≠ c ∧ z ≠ c ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam := by
  obtain ⟨xb,yb,zb,xc,yc,zc,
      hxbTop,hybTop,hzbTop,
      hxbB,hybB,hzbB,
      hxbC,hybC,hzbC,
      hxbYb,hxbZb,hybZb,
      hxcTop,hycTop,hzcTop,
      hxcC,hycC,hzcC,
      hxcB,hycB,hzcB,
      hxcYc,hxcZc,hycZc,
      hpartner,hsmallB,hsmallC⟩ :=
    two_smallPerfectMatchings_have_distinct_partners
      hp hcap hcard hdelta0 hdeltaHalf hlam
      hbTop hcTop hbc Mb Mc

  have hxcCase :
      xc = yb ∨ xc = zb := by
    rcases three_remaining_vertices_exhaust
        hcard hbTop.symm hcTop.symm hbc
        hxbTop hybTop hzbTop
        hxbB hybB hzbB
        hxbC hybC hzbC
        hxbYb hxbZb hybZb
        hxcTop hxcB hxcC
      with hxb | hyb | hzb
    · exact False.elim (hpartner hxb.symm)
    · exact Or.inl hyb
    · exact Or.inr hzb

  rcases hxcCase with hxcY | hxcZ
  · subst xc
    have hycCase :
        yc = xb ∨ yc = zb := by
      rcases three_remaining_vertices_exhaust
          hcard hbTop.symm hcTop.symm hbc
          hxbTop hybTop hzbTop
          hxbB hybB hzbB
          hxbC hybC hzbC
          hxbYb hxbZb hybZb
          hycTop hycB hycC
        with hxb | hyb | hzb
      · exact Or.inl hxb
      · exact False.elim (hxcYc hxb.symm)
      · exact Or.inr hzb
    have hzcCase :
        zc = xb ∨ zc = zb := by
      rcases three_remaining_vertices_exhaust
          hcard hbTop.symm hcTop.symm hbc
          hxbTop hybTop hzbTop
          hxbB hybB hzbB
          hxbC hybC hzbC
          hxbYb hxbZb hybZb
          hzcTop hzcB hzcC
        with hxb | hyb | hzb
      · exact Or.inl hxb
      · exact False.elim (hxcZc hxb.symm)
      · exact Or.inr hzb
    have hpairC :
        EuclideanGeometry.angle (p xb) (p c) (p zb)
          ≤
        EuclideanGeometry.angle (p yc) (p c) (p zc) := by
      rcases hycCase with rfl | rfl <;>
        rcases hzcCase with rfl | rfl
      · exact False.elim (hycZc rfl)
      · exact le_rfl
      · simpa [EuclideanGeometry.angle_comm] using
          (show EuclideanGeometry.angle (p zb) (p c) (p xb)
              ≤ EuclideanGeometry.angle (p zb) (p c) (p xb) from le_rfl)
      · exact False.elim (hycZc rfl)
    have hsmallC' :
        EuclideanGeometry.angle (p b) (p c) (p yb) +
            EuclideanGeometry.angle (p xb) (p c) (p zb)
          ≤ delta * lam := by
      exact add_le_add_left hpairC _ |>.trans hsmallC
    exact ⟨xb,yb,zb,
      hxbTop,hybTop,hzbTop,
      hxbB,hybB,hzbB,
      hxbC,hybC,hzbC,
      hxbYb,hxbZb,hybZb,
      hsmallB,hsmallC'⟩

  · subst xc
    have hycCase :
        yc = xb ∨ yc = yb := by
      rcases three_remaining_vertices_exhaust
          hcard hbTop.symm hcTop.symm hbc
          hxbTop hybTop hzbTop
          hxbB hybB hzbB
          hxbC hybC hzbC
          hxbYb hxbZb hybZb
          hycTop hycB hycC
        with hxb | hyb | hzb
      · exact Or.inl hxb
      · exact Or.inr hyb
      · exact False.elim (hxcYc hzb.symm)
    have hzcCase :
        zc = xb ∨ zc = yb := by
      rcases three_remaining_vertices_exhaust
          hcard hbTop.symm hcTop.symm hbc
          hxbTop hybTop hzbTop
          hxbB hybB hzbB
          hxbC hybC hzbC
          hxbYb hxbZb hybZb
          hzcTop hzcB hzcC
        with hxb | hyb | hzb
      · exact Or.inl hxb
      · exact Or.inr hyb
      · exact False.elim (hxcZc hzb.symm)
    have hpairC :
        EuclideanGeometry.angle (p xb) (p c) (p yb)
          ≤
        EuclideanGeometry.angle (p yc) (p c) (p zc) := by
      rcases hycCase with rfl | rfl <;>
        rcases hzcCase with rfl | rfl
      · exact False.elim (hycZc rfl)
      · exact le_rfl
      · simpa [EuclideanGeometry.angle_comm] using
          (show EuclideanGeometry.angle (p yb) (p c) (p xb)
              ≤ EuclideanGeometry.angle (p yb) (p c) (p xb) from le_rfl)
      · exact False.elim (hycZc rfl)
    have hsmallC' :
        EuclideanGeometry.angle (p b) (p c) (p zb) +
            EuclideanGeometry.angle (p xb) (p c) (p yb)
          ≤ delta * lam := by
      exact add_le_add_left hpairC _ |>.trans hsmallC
    have hsmallB' :
        EuclideanGeometry.angle (p c) (p b) (p xb) +
            EuclideanGeometry.angle (p zb) (p b) (p yb)
          ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hsmallB
    exact ⟨xb,zb,yb,
      hxbTop,hzbTop,hybTop,
      hxbB,hzbB,hybB,
      hxbC,hzbC,hybC,
      hxbZb,hxbYb,hybZb.symm,
      hsmallB',hsmallC'⟩

end SmallPerfectMatchingAwayFromTop

theorem support_three_middle_smallPerfectMatching
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    {top i : V}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hit : i ≠ top)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hmiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ i by simpa using hit) C) :
    Nonempty
      (SmallPerfectMatchingAwayFromTop
        (p := p) top i delta lam) := by
  obtain ⟨a,b,c,d,
      hat,hbt,hct,hdt,
      hab,hac,had,hbc,hbd,hcd,
      hsmall⟩ :=
    support_three_middle_hidden_small_matching
      hp hcap C hcard hn hdelta0 hdeltaHalf
      ht hlam hit hexp hsupport hmiddle
  exact ⟨{
    a := a
    b := b
    c := c
    d := d
    a_ne_top := hat
    b_ne_top := hbt
    c_ne_top := hct
    d_ne_top := hdt
    a_ne_b := hab
    a_ne_c := hac
    a_ne_d := had
    b_ne_c := hbc
    b_ne_d := hbd
    c_ne_d := hcd
    small_sum := hsmall
  }⟩

/-- Mixed support-one hard branch: two distinct support-three minima each carry
a delta-small perfect matching on the other four minima. -/
theorem mixed_support_one_has_two_smallPerfectMatchings
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top a : V)
    (hta : top ≠ a)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ b c : V,
      b ≠ top ∧ c ≠ top ∧
      b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      positiveSupport (centreQuotient (C b) t) = 3 ∧
      positiveSupport (centreQuotient (C c) t) = 3 ∧
      Nonempty
        (SmallPerfectMatchingAwayFromTop
          (p := p) top b delta lam) ∧
      Nonempty
        (SmallPerfectMatchingAwayFromTop
          (p := p) top c delta lam) := by
  obtain ⟨b,c,
      hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,
      _hbTrans,_hcTrans⟩ :=
    mixed_support_one_has_two_three_transition_centres
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA

  have hbMiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ b by simpa using hbTop)
        (C b) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hbTop hbSup3
  have hcMiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ c by simpa using hcTop)
        (C c) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hcTop hcSup3

  refine ⟨b,c,
    hbTop,hcTop,hbA,hcA,hbc,
    hbSup3,hcSup3,?_,?_⟩
  · exact support_three_middle_smallPerfectMatching
      hp hcap (C b) hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hbTop (hMin b hbTop) hbSup3 hbMiddle
  · exact support_three_middle_smallPerfectMatching
      hp hcap (C c) hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hcTop (hMin c hcTop) hcSup3 hcMiddle

#print axioms support_three_middle_smallPerfectMatching
#print axioms mixed_support_one_has_two_smallPerfectMatchings

end JSP000404Research
