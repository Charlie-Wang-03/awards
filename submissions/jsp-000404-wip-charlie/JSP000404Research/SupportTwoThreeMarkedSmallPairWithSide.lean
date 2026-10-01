import JSP000404Research.SupportTwoThreeMarkedSignProvenance
import JSP000404Research.SupportTwoThreeMarkedArcs
import Mathlib.Tactic

/-!
# Sign-aware small marked pair

Strengthen the support-two three-marked small-pair theorem by retaining the
canonical side provenance of the zero quotient arc.

For a displayed cyclic order

  a ... b ... c ... (wrap to a),

one of the following holds:

* a-b is delta*lambda-small and a,b are on the same canonical side of i;
* b-c is delta*lambda-small and b,c are on the same canonical side of i;
* c-a is delta*lambda-small and c,a are on opposite canonical sides of i.

This is the finite-order information needed to sharpen the Q/T/T/T small-pair
matching terminal.
-/

namespace JSP000404Research

theorem consecutiveRayQuotients_length
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i)) :
    (consecutiveRayQuotients hp i t prev rs).length = rs.length := by
  induction rs generalizing prev with
  | nil => rfl
  | cons r rs ih =>
      simp [consecutiveRayQuotients, ih]

theorem supportTwo_three_marked_small_pair_with_side_of_cyclic_decomposition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (a b c : OtherVertex i)
    (X Y Z : List (OtherVertex i))
    (hrays :
      C.rays = a :: (X ++ b :: Y ++ c :: Z)) :
    (
      EuclideanGeometry.angle (p a.1) (p i) (p b.1)
          ≤ delta * lam ∧
      CanonicalSameSide p i a.1 b.1
    )
    ∨
    (
      EuclideanGeometry.angle (p b.1) (p i) (p c.1)
          ≤ delta * lam ∧
      CanonicalSameSide p i b.1 c.1
    )
    ∨
    (
      EuclideanGeometry.angle (p c.1) (p i) (p a.1)
          ≤ delta * lam ∧
      CanonicalOppositeSides p i c.1 a.1
    ) := by
  let q₁ := markedQuotientArc₁ hp i t a b X
  let q₂ := markedQuotientArc₂ hp i t b c Y
  let q₃ := markedQuotientArc₃ hp i t a c Z
  let A₁ :=
    consecutiveRayAngles (p := p) i a (X ++ [b])
  let A₂ :=
    consecutiveRayAngles (p := p) i b (Y ++ [c])
  let A₃ :=
    consecutiveRayAngles (p := p) i c (Z ++ [a])

  have hqSplit :
      quotientList t C.gaps = q₁ ++ q₂ ++ q₃ := by
    simpa [q₁,q₂,q₃] using
      quotientList_three_marked_split
        hp C t a b c X Y Z hrays

  have hangleSplit :
      cyclicRayAngles (p := p) i a
          (X ++ b :: Y ++ c :: Z)
        =
      A₁ ++ A₂ ++ A₃ := by
    dsimp [A₁,A₂,A₃]
    exact cyclicRayAngles_three_marked_split
      (p := p) i a b c X Y Z

  have hlen₁ : q₁.length = A₁.length := by
    simp [q₁,A₁,markedQuotientArc₁,
      consecutiveRayQuotients_length,
      consecutiveRayAngles_length]
  have hlen₂ : q₂.length = A₂.length := by
    simp [q₂,A₂,markedQuotientArc₂,
      consecutiveRayQuotients_length,
      consecutiveRayAngles_length]
  have hlen₃ : q₃.length = A₃.length := by
    simp [q₃,A₃,markedQuotientArc₃,
      consecutiveRayQuotients_length,
      consecutiveRayAngles_length]

  have hsupportList :
      listPositiveCount (q₁ ++ q₂ ++ q₃) = 2 := by
    rw [← hqSplit]
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport

  have hdelta1 : delta < 1 := by linarith
  have hmass0 :
      listZeroAngleMass
          (quotientList t C.gaps)
          (cyclicRayAngles (p := p) i a
            (X ++ b :: Y ++ c :: Z))
        ≤ delta * lam :=
    centre_zeroAngleMass_le_delta_lam
      hp hcap hn3 hdelta0 hdelta1 ht hlam
      i C hexp hsupport
      a (X ++ b :: Y ++ c :: Z) hrays
  have hmass :
      listZeroAngleMass
          (q₁ ++ q₂ ++ q₃)
          (A₁ ++ A₂ ++ A₃)
        ≤ delta * lam := by
    rw [← hqSplit, ← hangleSplit]
    exact hmass0

  have hA0 :
      ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A := by
    intro A hA
    apply all_cyclicRayAngles_nonneg
      (p := p) i a (X ++ b :: Y ++ c :: Z)
    rw [hangleSplit]
    exact hA

  have hpaths :=
    three_marked_path_endpoint_bounds
      (p := p) i a b c X Y Z

  have hnodFull :
      (a :: (X ++ b :: Y ++ c :: Z)).Nodup := by
    simpa [hrays] using C.nodup
  have hpairFull :
      (a :: (X ++ b :: Y ++ c :: Z)).Pairwise
        (fun u v => rayThetaAt hp i u ≤ rayThetaAt hp i v) := by
    simpa [hrays] using C.theta_sorted

  have hnod1 :
      (a :: (X ++ [b])).Nodup := by
    have hrewrite :
        a :: (X ++ b :: Y ++ c :: Z)
          =
        (a :: (X ++ [b])) ++ (Y ++ c :: Z) := by
      simp [List.append_assoc]
    rw [hrewrite] at hnodFull
    exact (List.nodup_append.mp hnodFull).1
  have hpair1 :
      (a :: (X ++ [b])).Pairwise
        (fun u v => rayThetaAt hp i u ≤ rayThetaAt hp i v) := by
    have hrewrite :
        a :: (X ++ b :: Y ++ c :: Z)
          =
        (a :: (X ++ [b])) ++ (Y ++ c :: Z) := by
      simp [List.append_assoc]
    rw [hrewrite] at hpairFull
    exact (List.pairwise_append.mp hpairFull).1

  have hnod2 :
      (b :: (Y ++ [c])).Nodup := by
    have hrewrite :
        a :: (X ++ b :: Y ++ c :: Z)
          =
        (a :: X) ++ ((b :: (Y ++ [c])) ++ Z) := by
      simp [List.append_assoc]
    have h := hnodFull
    rw [hrewrite] at h
    have hsuffix := (List.nodup_append.mp h).2.1
    exact (List.nodup_append.mp hsuffix).1
  have hpair2 :
      (b :: (Y ++ [c])).Pairwise
        (fun u v => rayThetaAt hp i u ≤ rayThetaAt hp i v) := by
    have hrewrite :
        a :: (X ++ b :: Y ++ c :: Z)
          =
        (a :: X) ++ ((b :: (Y ++ [c])) ++ Z) := by
      simp [List.append_assoc]
    have h := hpairFull
    rw [hrewrite] at h
    have hsuffix := (List.pairwise_append.mp h).2.1
    exact (List.pairwise_append.mp hsuffix).1

  have hnod3 :
      (c :: Z).Nodup := by
    have hrewrite :
        a :: (X ++ b :: Y ++ c :: Z)
          =
        (a :: (X ++ b :: Y)) ++ (c :: Z) := by
      simp [List.append_assoc]
    have h := hnodFull
    rw [hrewrite] at h
    exact (List.nodup_append.mp h).2.1
  have hpair3 :
      (c :: Z).Pairwise
        (fun u v => rayThetaAt hp i u ≤ rayThetaAt hp i v) := by
    have hrewrite :
        a :: (X ++ b :: Y ++ c :: Z)
          =
        (a :: (X ++ b :: Y)) ++ (c :: Z) := by
      simp [List.append_assoc]
    have h := hpairFull
    rw [hrewrite] at h
    exact (List.pairwise_append.mp h).2.1

  have hac : a ≠ c := by
    intro h
    subst c
    have hnot := (List.nodup_cons.mp hnodFull).1
    apply hnot
    simp
  have haZ : a ∉ Z := by
    intro ha
    have hnot := (List.nodup_cons.mp hnodFull).1
    apply hnot
    simp [ha]
  have hlastMem :
      Z.getLastD c ∈ c :: Z := by
    by_cases hZ : Z = []
    · subst Z
      simp
    · exact List.mem_cons_of_mem c
        (getLastD_mem_of_ne_nil c Z hZ)
  have hlastTail :
      Z.getLastD c ∈ X ++ b :: Y ++ c :: Z := by
    rcases hlastMem with hlastEq | hlastZ
    · subst hlastEq
      simp
    · simp [hlastZ]
  have horderWrap :
      rayThetaAt hp i a ≤ rayThetaAt hp i (Z.getLastD c) :=
    (List.pairwise_cons.mp hpairFull).1
      (Z.getLastD c) hlastTail

  rcases
    three_blocks_support_two_has_small_zero_arc
      q₁ q₂ q₃ A₁ A₂ A₃
      hlen₁ hlen₂ hlen₃
      hsupportList hA0 hmass
    with h₁ | h₂ | h₃
  · left
    refine ⟨hpaths.1.trans h₁.2,?_⟩
    exact zero_marked_arc₁_canonical_sameSide
      hp hcap
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
      hlam a b X hnod1 hpair1
      (by simpa [q₁] using h₁.1)
  · right; left
    refine ⟨hpaths.2.1.trans h₂.2,?_⟩
    exact zero_marked_arc₂_canonical_sameSide
      hp hcap
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
      hlam b c Y hnod2 hpair2
      (by simpa [q₂] using h₂.1)
  · right; right
    refine ⟨hpaths.2.2.trans h₃.2,?_⟩
    exact zero_marked_arc₃_canonical_oppositeSides
      hp hcap
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
      hlam a c Z hac haZ hnod3 hpair3 horderWrap
      (by simpa [q₃] using h₃.1)

#print axioms supportTwo_three_marked_small_pair_with_side_of_cyclic_decomposition

end JSP000404Research
