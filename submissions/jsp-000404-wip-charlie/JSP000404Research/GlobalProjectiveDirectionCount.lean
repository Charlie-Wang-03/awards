import JSP000404Research.CanonicalRayReversal
import JSP000404Research.SixPointPhaseGapArithmetic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Global projective edge-direction set

For every directed non-loop edge u->v, record its canonical projective
parameter theta in [0,pi).  Reversal preserves theta.

Choose one directed representative for each distinct projective direction.
The two orientations of that representative are distinct ordered vertex pairs,
and distinct directions cannot collide after orientation.  Therefore

  directions x Bool -> V x V

is injective.

Consequently

  2 * number_of_projective_directions <= |V|^2.

For six vertices this gives the quick bound 18.  It is deliberately weaker
than the sharp C(6,2)=15 bound, but already suffices for the n>=9 terminal.
-/

namespace JSP000404Research

abbrev DirectedNonloopEdge (V : Type*) :=
  {e : V × V // e.1 ≠ e.2}

noncomputable def directedNonloopEdgeTheta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (e : DirectedNonloopEdge V) : ℝ :=
  rayThetaAt hp e.1.1 ⟨e.1.2, e.2.symm⟩

noncomputable def projectiveEdgeDirections
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) : Finset ℝ := by
  classical
  exact Finset.univ.image (directedNonloopEdgeTheta hp)

@[simp] theorem mem_projectiveEdgeDirections
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (theta : ℝ) :
    theta ∈ projectiveEdgeDirections hp ↔
      ∃ e : DirectedNonloopEdge V,
        directedNonloopEdgeTheta hp e = theta := by
  classical
  simp [projectiveEdgeDirections]

noncomputable def projectiveDirectionRepresentative
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (theta : {x : ℝ // x ∈ projectiveEdgeDirections hp}) :
    DirectedNonloopEdge V :=
  Classical.choose
    ((mem_projectiveEdgeDirections hp theta.1).1 theta.2)

theorem projectiveDirectionRepresentative_theta
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (theta : {x : ℝ // x ∈ projectiveEdgeDirections hp}) :
    directedNonloopEdgeTheta hp
      (projectiveDirectionRepresentative hp theta) = theta.1 :=
  Classical.choose_spec
    ((mem_projectiveEdgeDirections hp theta.1).1 theta.2)

def reverseDirectedNonloopEdge
    {V : Type*}
    (e : DirectedNonloopEdge V) :
    DirectedNonloopEdge V :=
  ⟨(e.1.2, e.1.1), e.2.symm⟩

theorem directedNonloopEdgeTheta_reverse
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (e : DirectedNonloopEdge V) :
    directedNonloopEdgeTheta hp
        (reverseDirectedNonloopEdge e)
      =
    directedNonloopEdgeTheta hp e := by
  unfold directedNonloopEdgeTheta reverseDirectedNonloopEdge
  exact rayThetaAt_reverse_eq hp e.2 |>.symm

/-- Two orientations of one non-loop edge are distinct ordered pairs. -/
theorem directed_pair_ne_reverse
    {V : Type*}
    (e : DirectedNonloopEdge V) :
    e.1 ≠ (reverseDirectedNonloopEdge e).1 := by
  intro h
  have hfirst := congrArg Prod.fst h
  exact e.2 hfirst

noncomputable def directionOrientationPair
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) :
    ({x : ℝ // x ∈ projectiveEdgeDirections hp} × Bool) →
      (V × V)
  | (theta, false) =>
      (projectiveDirectionRepresentative hp theta).1
  | (theta, true) =>
      (reverseDirectedNonloopEdge
        (projectiveDirectionRepresentative hp theta)).1

theorem directionOrientationPair_theta
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (theta : {x : ℝ // x ∈ projectiveEdgeDirections hp})
    (b : Bool) :
    let e : DirectedNonloopEdge V :=
      if b then
        reverseDirectedNonloopEdge
          (projectiveDirectionRepresentative hp theta)
      else
        projectiveDirectionRepresentative hp theta
    directedNonloopEdgeTheta hp e = theta.1 := by
  dsimp
  cases b
  · simpa using projectiveDirectionRepresentative_theta hp theta
  · rw [directedNonloopEdgeTheta_reverse]
    exact projectiveDirectionRepresentative_theta hp theta

theorem directionOrientationPair_injective
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) :
    Function.Injective (directionOrientationPair hp) := by
  intro x y hxy
  rcases x with ⟨theta, bx⟩
  rcases y with ⟨phi, byy⟩
  have htheta : theta = phi := by
    apply Subtype.ext
    let ex : DirectedNonloopEdge V :=
      if bx then
        reverseDirectedNonloopEdge
          (projectiveDirectionRepresentative hp theta)
      else
        projectiveDirectionRepresentative hp theta
    let ey : DirectedNonloopEdge V :=
      if byy then
        reverseDirectedNonloopEdge
          (projectiveDirectionRepresentative hp phi)
      else
        projectiveDirectionRepresentative hp phi
    have hpair : ex.1 = ey.1 := by
      cases bx <;> cases byy <;>
        simpa [directionOrientationPair, ex, ey] using hxy
    have hthetaX :
        directedNonloopEdgeTheta hp ex = theta.1 := by
      simpa [ex] using
        directionOrientationPair_theta hp theta bx
    have hthetaY :
        directedNonloopEdgeTheta hp ey = phi.1 := by
      simpa [ey] using
        directionOrientationPair_theta hp phi byy
    have heqTheta :
        directedNonloopEdgeTheta hp ex =
          directedNonloopEdgeTheta hp ey := by
      unfold directedNonloopEdgeTheta
      rw [hpair]
    rw [hthetaX, hthetaY] at heqTheta
    exact heqTheta
  subst phi
  congr
  cases bx <;> cases byy
  · rfl
  · exfalso
    have hne :=
      directed_pair_ne_reverse
        (projectiveDirectionRepresentative hp theta)
    exact hne (by
      simpa [directionOrientationPair] using hxy)
  · exfalso
    have hne :=
      directed_pair_ne_reverse
        (projectiveDirectionRepresentative hp theta)
    exact hne (by
      have := hxy.symm
      simpa [directionOrientationPair] using this)
  · rfl

noncomputable def diagonalOrderedPairs
    (V : Type*) [Fintype V] :
    Finset (V × V) := by
  classical
  exact Finset.univ.image (fun v : V => (v,v))

noncomputable def nonloopOrderedPairs
    (V : Type*) [Fintype V] :
    Finset (V × V) := by
  classical
  exact Finset.univ \ diagonalOrderedPairs V

theorem mem_nonloopOrderedPairs_iff
    {V : Type*} [Fintype V]
    (e : V × V) :
    e ∈ nonloopOrderedPairs V ↔ e.1 ≠ e.2 := by
  classical
  simp [nonloopOrderedPairs, diagonalOrderedPairs]
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem diagonalOrderedPairs_card
    (V : Type*) [Fintype V] :
    (diagonalOrderedPairs V).card = Fintype.card V := by
  classical
  unfold diagonalOrderedPairs
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg Prod.fst h

theorem nonloopOrderedPairs_card
    (V : Type*) [Fintype V] :
    (nonloopOrderedPairs V).card =
      Fintype.card V * Fintype.card V -
        Fintype.card V := by
  classical
  unfold nonloopOrderedPairs
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [diagonalOrderedPairs_card]
  simp [Fintype.card_prod]

theorem directionOrientationPair_mem_nonloop
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (x :
      {x : ℝ // x ∈ projectiveEdgeDirections hp} × Bool) :
    directionOrientationPair hp x ∈ nonloopOrderedPairs V := by
  rcases x with ⟨theta, b⟩
  apply (mem_nonloopOrderedPairs_iff _).2
  cases b
  · simpa [directionOrientationPair] using
      (projectiveDirectionRepresentative hp theta).2
  · simpa [directionOrientationPair, reverseDirectedNonloopEdge] using
      (projectiveDirectionRepresentative hp theta).2.symm

/-- Sharp count via the 30 non-loop ordered pairs: each projective direction
uses two opposite orientations. -/
theorem two_mul_projectiveEdgeDirections_card_le_nonloop
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) :
    2 * (projectiveEdgeDirections hp).card ≤
      Fintype.card V * Fintype.card V -
        Fintype.card V := by
  classical
  let A :=
    (Finset.univ :
      Finset
        ({x : ℝ // x ∈ projectiveEdgeDirections hp} × Bool))
  let imagePairs : Finset (V × V) :=
    A.image (directionOrientationPair hp)
  have hcardImage :
      imagePairs.card =
        2 * (projectiveEdgeDirections hp).card := by
    dsimp [imagePairs, A]
    rw [Finset.card_image_of_injective
      _ (directionOrientationPair_injective hp)]
    simp [Fintype.card_prod, Fintype.card_coe,
      Nat.mul_comm]
  have hsub :
      imagePairs ⊆ nonloopOrderedPairs V := by
    intro e he
    dsimp [imagePairs, A] at he
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp he
    exact directionOrientationPair_mem_nonloop hp x
  have hle :
      imagePairs.card ≤ (nonloopOrderedPairs V).card :=
    Finset.card_le_card hsub
  rw [hcardImage, nonloopOrderedPairs_card] at hle
  exact hle

theorem projectiveEdgeDirections_card_le_fifteen_of_card_six
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcard : Fintype.card V = 6) :
    (projectiveEdgeDirections hp).card ≤ 15 := by
  have h :=
    two_mul_projectiveEdgeDirections_card_le_nonloop hp
  rw [hcard] at h
  norm_num at h ⊢
  omega

/-- Coarse but very robust global direction-count bound. -/
theorem two_mul_projectiveEdgeDirections_card_le_square
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) :
    2 * (projectiveEdgeDirections hp).card ≤
      Fintype.card V * Fintype.card V := by
  classical
  have hcard :=
    Fintype.card_le_of_injective
      (directionOrientationPair hp)
      (directionOrientationPair_injective hp)
  simpa [Fintype.card_prod, Fintype.card_coe,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

theorem projectiveEdgeDirections_card_le_eighteen_of_card_six
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcard : Fintype.card V = 6) :
    (projectiveEdgeDirections hp).card ≤ 18 := by
  have h :=
    two_mul_projectiveEdgeDirections_card_le_square hp
  rw [hcard] at h
  norm_num at h ⊢
  omega

/-- The global projective direction set is nonempty as soon as there are at
least two vertices. -/
theorem projectiveEdgeDirections_nonempty_of_two_le_card
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcard : 2 ≤ Fintype.card V) :
    (projectiveEdgeDirections hp).Nonempty := by
  classical
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton V := ⟨h⟩
    have hle : Fintype.card V ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  let e : DirectedNonloopEdge V := ⟨(u,v), huv⟩
  refine ⟨directedNonloopEdgeTheta hp e, ?_⟩
  exact (mem_projectiveEdgeDirections hp _).2 ⟨e, rfl⟩

#print axioms directedNonloopEdgeTheta_reverse
#print axioms directionOrientationPair_injective
#print axioms two_mul_projectiveEdgeDirections_card_le_nonloop
#print axioms projectiveEdgeDirections_card_le_fifteen_of_card_six
#print axioms two_mul_projectiveEdgeDirections_card_le_square
#print axioms projectiveEdgeDirections_card_le_eighteen_of_card_six

end JSP000404Research
