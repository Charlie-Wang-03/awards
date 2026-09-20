import JSP000404Research.ConcreteHighExponentTransition
import JSP000404Research.TransitionRaySplit
import JSP000404Research.TransitionSplitExposure
import JSP000404Research.CanonicalSignGap
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

/-!
# Concrete high-exponent centres are strictly exposed

This closes the geometric chain

  large Sendov exponent
    -> quotient support at most two
    -> one actual sign transition
    -> two canonical sign blocks (or a wrap transition)
    -> strict supporting line.

No abstract sign-path or projective-interval hypothesis remains.

If the unique transition is at the projective wrap, every canonical ray has
one common sign, so its finite theta range has width strictly below pi.

If it is an ordinary transition, the sorted ray cycle splits into two
opposite-sign blocks.  The last ray of the first block and first ray of the
second block have opposite canonical signs.  The global angle cap forces a
strictly positive projective gap between them, and the two-block exposure
lemma supplies a strict supporting line.

Thus every actual centre with exponent at least n-2 is strictly exposed.
-/

namespace JSP000404Research

open Real

/-- Pointwise sign consequence of a mapped-replicate block. -/
theorem raySign_eq_of_block_map
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (sigma : Bool)
    (xs : List (OtherVertex i))
    (hmap :
      xs.map (raySignAt hp i) =
        List.replicate xs.length sigma) :
    ∀ j ∈ xs, raySignAt hp i j = sigma := by
  intro j hj
  exact sign_eq_of_mem_map_replicate
    (raySignAt hp i) sigma xs hmap hj

/-- Main concrete high-exponent exposure theorem. -/
theorem concrete_centre_large_exponent_strictlyExposed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hlarge : n - 2 ≤ centreExponent C t) :
    StrictlyExposedAt p i := by
  obtain ⟨first, rest, pre, post, qe,
      hrays, hqe, hq, hsignLift⟩ :=
    concrete_centre_large_exponent_has_positive_transition_gap
      hp hcap hn hdelta0 hdelta1 ht hlam i C hlarge
  let sigma : Bool := raySignAt hp i first
  have hsplitLift :
      rest.map (raySignAt hp i) ++ [!sigma] =
        List.replicate pre.length sigma ++
          List.replicate (post.length + 1) (!sigma) := by
    simpa [liftedCentreSignPath, sigma] using hsignLift
  obtain ⟨before, after, hrest, hbeforeLen, hafterLen,
      hbeforeMap, hafterMap⟩ :=
    exists_ray_split_of_lifted_sign_blocks
      (raySignAt hp i) sigma rest
      pre.length post.length hsplitLift
  have hbeforeMapLen :
      before.map (raySignAt hp i) =
        List.replicate before.length sigma := by
    rw [hbeforeLen]
    exact hbeforeMap
  have hafterMapLen :
      after.map (raySignAt hp i) =
        List.replicate after.length (!sigma) := by
    rw [hafterLen]
    exact hafterMap
  cases hafter : after with
  | nil =>
      have hrestEq : rest = before := by
        rw [hafter] at hrest
        simpa using hrest
      have hfull : C.rays = first :: before := by
        rw [hrays, hrestEq]
      apply strictlyExposedAt_of_common_canonical_sign
        hp sigma C.rays
      · intro j
        exact C.mem_rays_iff j
      · intro j hj
        rw [hfull] at hj
        rcases List.mem_cons.mp hj with hj | hj
        · subst j
          rfl
        · exact raySign_eq_of_block_map
            hp sigma before hbeforeMapLen j hj
      · exact C.nonempty
      · exact C.theta_sorted
  | cons right tail =>
      have hrestEq :
          rest = before ++ right :: tail := by
        simpa [hafter] using hrest
      have hfull :
          C.rays = (first :: before) ++ (right :: tail) := by
        rw [hrays, hrestEq]
        rfl
      have hpair :
          ((first :: before) ++ (right :: tail)).Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        rw [← hfull]
        exact C.theta_sorted
      have hpairs :
          (first :: before).Pairwise
              (fun a b =>
                rayThetaAt hp i a ≤ rayThetaAt hp i b) ∧
            (right :: tail).Pairwise
              (fun a b =>
                rayThetaAt hp i a ≤ rayThetaAt hp i b) ∧
            (∀ a ∈ first :: before, ∀ b ∈ right :: tail,
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        simpa only [List.pairwise_append] using hpair
      let left : OtherVertex i :=
        (first :: before).getLast (by simp)
      have hleftMem : left ∈ first :: before := by
        dsimp [left]
        exact List.getLast_mem _
      have hrightMem : right ∈ right :: tail := by
        simp
      have hleftSign :
          raySignAt hp i left = sigma := by
        rcases List.mem_cons.mp hleftMem with hlf | hlt
        · subst left
          rfl
        · exact raySign_eq_of_block_map
            hp sigma before hbeforeMapLen left hlt
      have hrightSign :
          raySignAt hp i right = !sigma := by
        have hrightAfter : right ∈ after := by
          rw [hafter]
          simp
        exact raySign_eq_of_block_map
          hp (!sigma) after hafterMapLen right hrightAfter
      have hsignNe :
          raySignAt hp i left ≠
            raySignAt hp i right := by
        rw [hleftSign, hrightSign]
        cases sigma <;> decide
      have hleftRight : left ≠ right := by
        intro h
        apply hsignNe
        exact congrArg (raySignAt hp i) h
      have horder :
          rayThetaAt hp i left ≤
            rayThetaAt hp i right :=
        hpairs.2.2 left hleftMem right hrightMem
      have htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
      have hone :=
        one_le_t_mul_gap_of_canonical_sign_ne
          hp hcap htpos hlam i
          hleftRight horder hsignNe
      have hgap :
          rayThetaAt hp i left <
            rayThetaAt hp i right := by
        by_contra hnot
        have hdiff :
            rayThetaAt hp i right -
              rayThetaAt hp i left ≤ 0 := by
          linarith
        have hfrac :
            (rayThetaAt hp i right -
                rayThetaAt hp i left) / Real.pi ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hdiff Real.pi_pos.le
        have hprod :
            t * ((rayThetaAt hp i right -
              rayThetaAt hp i left) / Real.pi) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos htpos.le hfrac
        linarith
      have hbeforeTheta :
          ∀ j ∈ first :: before,
            rayThetaAt hp i j ≤ rayThetaAt hp i left := by
        intro j hj
        dsimp [left]
        exact hpairs.1.rel_getLast hj
      have hafterTheta :
          ∀ j ∈ right :: tail,
            rayThetaAt hp i right ≤ rayThetaAt hp i j := by
        intro j hj
        rcases List.mem_cons.mp hj with hj | hj
        · subst j
          rfl
        · exact (List.pairwise_cons.mp hpairs.2.1).1 j hj
      have hbeforeSign :
          ∀ j ∈ first :: before,
            raySignAt hp i j = sigma := by
        intro j hj
        rcases List.mem_cons.mp hj with hj | hj
        · subst j
          rfl
        · exact raySign_eq_of_block_map
            hp sigma before hbeforeMapLen j hj
      have hafterSign :
          ∀ j ∈ right :: tail,
            raySignAt hp i j = !sigma := by
        intro j hj
        have hjAfter : j ∈ after := by
          rw [hafter]
          exact hj
        exact raySign_eq_of_block_map
          hp (!sigma) after hafterMapLen j hjAfter
      have hcover :
          ∀ j : OtherVertex i,
            j ∈ first :: before ∨ j ∈ right :: tail := by
        intro j
        have hj : j ∈ C.rays := C.mem_rays_iff j
        rw [hfull, List.mem_append] at hj
        exact hj
      exact strictlyExposedAt_of_two_sign_blocks
        hp sigma
        (first :: before) (right :: tail)
        hcover hbeforeSign hafterSign
        hbeforeTheta hafterTheta
        (rayThetaAt_nonneg hp i left)
        (rayThetaAt_lt_pi hp i right)
        hgap

#print axioms raySign_eq_of_block_map
#print axioms concrete_centre_large_exponent_strictlyExposed

end JSP000404Research
