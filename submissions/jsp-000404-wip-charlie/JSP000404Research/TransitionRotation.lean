import JSP000404Research.UniqueTransitionGap
import JSP000404Research.SignedRayMonodromy
import Mathlib.Tactic

/-!
# Rotating a one-transition sign path at its transition gap

After the unique transition is located,

  signs = a^|pre| ++ (!a)^(|post|+1)

and the quotient list is

  qs = pre ++ q :: post,   q != 0.

Cutting the cyclic order at q rotates the quotient gaps to

  post ++ pre ++ [q],

so q becomes the final gap.

The ray signs in the corresponding rotated order are

  (!a)^(|post|+1) ++ a^|pre|.

The second block is represented after adding pi to its projective parameters.
By signed-ray antiperiodicity, adding pi and flipping the Boolean sign leaves
the actual oriented ray unchanged.  Hence every ray of the rotated lift may
be represented with the common sign !a.

This file isolates the list algebra and the pointwise signed-ray identity.
-/

namespace JSP000404Research

/-- Quotient-gap rotation that moves the unique transition gap to the end. -/
def rotateQuotientsAtTransition
    (pre post : List ℕ) (q : ℕ) : List ℕ :=
  post ++ pre ++ [q]

theorem rotateQuotientsAtTransition_length
    (pre post : List ℕ) (q : ℕ) :
    (rotateQuotientsAtTransition pre post q).length =
      pre.length + post.length + 1 := by
  simp [rotateQuotientsAtTransition, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

theorem rotateQuotientsAtTransition_last
    (pre post : List ℕ) (q : ℕ) :
    (rotateQuotientsAtTransition pre post q).getLast? = some q := by
  simp [rotateQuotientsAtTransition]

/-- The rotated ray-sign order before changing projective representatives. -/
def rotatedRawSigns
    (a : Bool) (pre post : List ℕ) : List Bool :=
  List.replicate (post.length + 1) (!a) ++
    List.replicate pre.length a

/-- After flipping the second block, every sign is the same. -/
theorem rotated_signs_common_after_flip
    (a : Bool) (pre post : List ℕ) :
    List.replicate (post.length + 1) (!a) ++
        (List.replicate pre.length a).map (!·)
      =
    List.replicate (post.length + 1 + pre.length) (!a) := by
  rw [List.map_replicate]
  simp [List.replicate_add]

/-- Equivalent form using the raw rotated sign list: the tail block is the
only block requiring sign reversal. -/
theorem rotatedRawSigns_eq_blocks
    (a : Bool) (pre post : List ℕ) :
    rotatedRawSigns a pre post =
      List.replicate (post.length + 1) (!a) ++
        List.replicate pre.length a := rfl

/-- A ray represented with sign a at theta can be represented with sign !a
at theta+pi without changing the actual direction. -/
theorem same_ray_after_pi_shift_to_common_sign
    (a : Bool) (theta : ℝ) :
    signedRayDirection a theta =
      signedRayDirection (!a) (theta + Real.pi) := by
  symm
  simpa using signedRayDirection_not_add_pi a theta

/-- The symmetric shift identity, useful when the common sign is chosen as the
first block rather than the second. -/
theorem same_ray_before_pi_shift_from_common_sign
    (a : Bool) (theta : ℝ) :
    signedRayDirection (!a) theta =
      signedRayDirection a (theta - Real.pi) := by
  symm
  simpa using signedRayDirection_not_sub_pi (!a) theta

#print axioms rotateQuotientsAtTransition_last
#print axioms rotated_signs_common_after_flip
#print axioms same_ray_after_pi_shift_to_common_sign
#print axioms same_ray_before_pi_shift_from_common_sign

end JSP000404Research
