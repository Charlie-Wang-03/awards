import JSP000404Research.SupportTwoThreeMarkedSmallPair
import JSP000404Research.ZeroBlockSignRigidity
import JSP000404Research.CentreSignPath
import JSP000404Research.CanonicalMarkedSideSemantics
import Mathlib.Tactic

/-!
# Partial sign provenance for three-marked support-two arcs

For a displayed cyclic ray list

  a :: X ++ b :: Y ++ c :: Z,

the quotient list splits canonically into the two ordinary marked arcs a->b,
b->c and the final cyclic arc c->a containing the projective wrap.

For the first two arcs, zero positive support forces all quotients to vanish.
ChangesOnlyOnPositive then forces the endpoint canonical ray signs to agree.
This is enough to turn two of the three small-pair alternatives into explicit
canonical same-side statements; only the wrap arc remains as a separate
terminal.
-/

namespace JSP000404Research

def markedQuotientArc₁
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (a b : OtherVertex i)
    (X : List (OtherVertex i)) : List ℕ :=
  consecutiveRayQuotients hp i t a (X ++ [b])

def markedQuotientArc₂
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (b c : OtherVertex i)
    (Y : List (OtherVertex i)) : List ℕ :=
  consecutiveRayQuotients hp i t b (Y ++ [c])

def markedQuotientArc₃
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (a c : OtherVertex i)
    (Z : List (OtherVertex i)) : List ℕ :=
  consecutiveRayQuotients hp i t c Z ++
    [wrapRayQuotient hp i t a (Z.getLastD c)]

theorem consecutiveRayQuotients_append_cons
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (prev : OtherVertex i)
    (xs : List (OtherVertex i))
    (y : OtherVertex i)
    (ys : List (OtherVertex i)) :
    consecutiveRayQuotients hp i t prev (xs ++ y :: ys)
      =
    consecutiveRayQuotients hp i t prev (xs ++ [y]) ++
      consecutiveRayQuotients hp i t y ys := by
  induction xs generalizing prev with
  | nil =>
      simp [consecutiveRayQuotients]
  | cons x xs ih =>
      simp only [List.cons_append, consecutiveRayQuotients]
      rw [ih x]
      simp [List.append_assoc]

theorem quotientList_three_marked_split
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V} (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (a b c : OtherVertex i)
    (X Y Z : List (OtherVertex i))
    (hrays :
      C.rays = a :: (X ++ b :: Y ++ c :: Z)) :
    quotientList t C.gaps =
      markedQuotientArc₁ hp i t a b X ++
      markedQuotientArc₂ hp i t b c Y ++
      markedQuotientArc₃ hp i t a c Z := by
  rw [centreQuotientList_decompose C t
      a (X ++ b :: Y ++ c :: Z) hrays]
  rw [consecutiveRayQuotients_append_cons
      hp i t a X b (Y ++ c :: Z)]
  rw [consecutiveRayQuotients_append_cons
      hp i t b Y c Z]
  unfold markedQuotientArc₁ markedQuotientArc₂ markedQuotientArc₃
  have hlast :
      (X ++ b :: Y ++ c :: Z).getLastD a =
        Z.getLastD c := by
    simp
  rw [hlast]
  simp [List.append_assoc]

theorem boolLastFrom_map_append_singleton
    {α : Type*}
    (f : α → Bool)
    (a : Bool)
    (xs : List α)
    (y : α) :
    boolLastFrom a ((xs ++ [y]).map f) = f y := by
  rw [boolLastFrom_eq_getLastD]
  simp

theorem zero_marked_arc₁_sign_eq
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    {i : V}
    (a b : OtherVertex i)
    (X : List (OtherVertex i))
    (hnodup : (a :: (X ++ [b])).Nodup)
    (hsorted :
      (a :: (X ++ [b])).Pairwise
        (fun u v =>
          rayThetaAt hp i u ≤ rayThetaAt hp i v))
    (hzero :
      listPositiveCount
        (markedQuotientArc₁ hp i t a b X) = 0) :
    raySignAt hp i a = raySignAt hp i b := by
  have hchanges :=
    consecutive_changesOnlyOnPositive
      hp hcap ht hlam i a (X ++ [b]) hnodup hsorted
  have hallZero :
      ∀ q ∈ markedQuotientArc₁ hp i t a b X, q = 0 :=
    listPositiveCount_eq_zero_forall _ hzero
  have hlast :=
    lastSign_eq_entry_of_zero_block
      (raySignAt hp i a)
      ((X ++ [b]).map (raySignAt hp i))
      (markedQuotientArc₁ hp i t a b X)
      hchanges hallZero
  unfold markedQuotientArc₁ at hlast
  rw [boolLastFrom_map_append_singleton] at hlast
  exact hlast.symm

theorem zero_marked_arc₂_sign_eq
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    {i : V}
    (b c : OtherVertex i)
    (Y : List (OtherVertex i))
    (hnodup : (b :: (Y ++ [c])).Nodup)
    (hsorted :
      (b :: (Y ++ [c])).Pairwise
        (fun u v =>
          rayThetaAt hp i u ≤ rayThetaAt hp i v))
    (hzero :
      listPositiveCount
        (markedQuotientArc₂ hp i t b c Y) = 0) :
    raySignAt hp i b = raySignAt hp i c := by
  have hchanges :=
    consecutive_changesOnlyOnPositive
      hp hcap ht hlam i b (Y ++ [c]) hnodup hsorted
  have hallZero :
      ∀ q ∈ markedQuotientArc₂ hp i t b c Y, q = 0 :=
    listPositiveCount_eq_zero_forall _ hzero
  have hlast :=
    lastSign_eq_entry_of_zero_block
      (raySignAt hp i b)
      ((Y ++ [c]).map (raySignAt hp i))
      (markedQuotientArc₂ hp i t b c Y)
      hchanges hallZero
  unfold markedQuotientArc₂ at hlast
  rw [boolLastFrom_map_append_singleton] at hlast
  exact hlast.symm

theorem zero_marked_arc₁_canonical_sameSide
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    {i : V}
    (a b : OtherVertex i)
    (X : List (OtherVertex i))
    (hnodup : (a :: (X ++ [b])).Nodup)
    (hsorted :
      (a :: (X ++ [b])).Pairwise
        (fun u v =>
          rayThetaAt hp i u ≤ rayThetaAt hp i v))
    (hzero :
      listPositiveCount
        (markedQuotientArc₁ hp i t a b X) = 0) :
    CanonicalSameSide p i a.1 b.1 := by
  have hsign :=
    zero_marked_arc₁_sign_eq
      hp hcap ht hlam a b X hnodup hsorted hzero
  exact
    (raySign_eq_iff_canonicalSameSide
      hp a.2.symm b.2.symm).1 hsign

theorem zero_marked_arc₂_canonical_sameSide
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    {i : V}
    (b c : OtherVertex i)
    (Y : List (OtherVertex i))
    (hnodup : (b :: (Y ++ [c])).Nodup)
    (hsorted :
      (b :: (Y ++ [c])).Pairwise
        (fun u v =>
          rayThetaAt hp i u ≤ rayThetaAt hp i v))
    (hzero :
      listPositiveCount
        (markedQuotientArc₂ hp i t b c Y) = 0) :
    CanonicalSameSide p i b.1 c.1 := by
  have hsign :=
    zero_marked_arc₂_sign_eq
      hp hcap ht hlam b c Y hnodup hsorted hzero
  exact
    (raySign_eq_iff_canonicalSameSide
      hp b.2.symm c.2.symm).1 hsign

#print axioms quotientList_three_marked_split
#print axioms zero_marked_arc₁_sign_eq
#print axioms zero_marked_arc₂_sign_eq
#print axioms zero_marked_arc₁_canonical_sameSide
#print axioms zero_marked_arc₂_canonical_sameSide

end JSP000404Research
