import JSP000404Research.SixPointThirdLayerTerminal
import JSP000404Research.SharpPinnedSupportThreeShape
import JSP000404Research.ConcreteSecondDeletionBridge
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite support-three shape in the six-point terminal

Once the large n-3 minimum layer with a top centre has been reduced to six
vertices, every centre has exactly five projective rays.

For an n-3/support-three minimum centre i pinned by the sharp top centre s,
SharpPinnedSupportThreeShape gives

  qFirst :: qmid ++ [qLast],

where both end quotients are positive and qmid has positive support one.

The six-point cardinality now forces qmid.length = 3.  Hence qmid is one of

  [q,0,0], [0,q,0], [0,0,q]

for a unique positive q.

This converts the arbitrary-cardinality support-three geometry into a
three-position finite terminal.
-/

namespace JSP000404Research

/-- A complete nodup centre ray list has exactly one fewer element than the
ambient finite vertex type. -/
theorem centreRayList_length_eq_card_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.rays.length = Fintype.card V - 1 := by
  classical
  have hlistCard :
      C.rays.toFinset.card = C.rays.length :=
    List.toFinset_card_of_nodup C.nodup
  have hunivCard :
      C.rays.toFinset.card =
        Fintype.card (OtherVertex i) := by
    rw [C.complete]
    simp
  have hother :
      Fintype.card (OtherVertex i) =
        Fintype.card V - 1 := by
    simpa [OtherVertex, DeletedVertexType] using
      card_deletedVertexType i
  omega

theorem centreRayList_length_eq_five_of_card_six
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6) :
    C.rays.length = 5 := by
  rw [centreRayList_length_eq_card_sub_one C, hcard]
  norm_num

/-- A length-three natural list with exactly one positive entry has one of the
three obvious one-spike shapes. -/
theorem length_three_positiveCount_one_shape
    (qs : List ℕ)
    (hlen : qs.length = 3)
    (hcount : listPositiveCount qs = 1) :
    ∃ q : ℕ,
      q ≠ 0 ∧
      (qs = [q,0,0] ∨
       qs = [0,q,0] ∨
       qs = [0,0,q]) := by
  rcases qs with _ | q0 qs
  · simp at hlen
  rcases qs with _ | q1 qs
  · simp at hlen
  rcases qs with _ | q2 qs
  · simp at hlen
  rcases qs with _ | q3 qs
  · simp only [List.length_cons, List.length_nil] at hlen
    by_cases h0 : q0 = 0 <;>
      by_cases h1 : q1 = 0 <;>
      by_cases h2 : q2 = 0 <;>
      simp [listPositiveCount, h0, h1, h2] at hcount ⊢
  · simp at hlen

/-- Six-point specialization of the sharp-pinned support-three skeleton. -/
theorem exists_six_point_sharp_pinned_support_three_shape
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    ∃ first0 : OtherVertex i,
      ∃ rest0 : List (OtherVertex i),
      ∃ k : ℕ,
      ∃ r : OtherVertex i,
      ∃ rest : List (OtherVertex i),
      ∃ qFirst qLast qHidden : ℕ,
      ∃ qmid : List ℕ,
        C.rays = first0 :: rest0 ∧
        C.rays.rotate k =
          (⟨s, hsi⟩ : OtherVertex i) :: r :: rest ∧
        (quotientList t C.gaps).rotate k =
          qFirst :: qmid ++ [qLast] ∧
        1 ≤ qFirst ∧
        1 ≤ qLast ∧
        qmid.length = 3 ∧
        qHidden ≠ 0 ∧
        (qmid = [qHidden,0,0] ∨
         qmid = [0,qHidden,0] ∨
         qmid = [0,0,qHidden]) := by
  obtain ⟨first0, rest0, k, r, rest,
      qFirst, qLast, qmid,
      hrays0, hrotRays, hqRot,
      hqFirst, hqLast, hmidCount, _hmidLen,
      _hmassRot, _hangleRot⟩ :=
    exists_sharp_pinned_support_three_shape
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport
  have hqLen :
      ((quotientList t C.gaps).rotate k).length = 5 := by
    rw [List.length_rotate, quotientList_length, C.gaps_length,
      centreRayList_length_eq_five_of_card_six C hcard]
  have hmidLen : qmid.length = 3 := by
    rw [hqRot] at hqLen
    simp at hqLen
    omega
  obtain ⟨qHidden, hqHidden, hshape⟩ :=
    length_three_positiveCount_one_shape
      qmid hmidLen hmidCount
  exact ⟨first0, rest0, k, r, rest,
    qFirst, qLast, qHidden, qmid,
    hrays0, hrotRays, hqRot,
    hqFirst, hqLast, hmidLen, hqHidden, hshape⟩

#print axioms centreRayList_length_eq_card_sub_one
#print axioms length_three_positiveCount_one_shape
#print axioms exists_six_point_sharp_pinned_support_three_shape

end JSP000404Research
