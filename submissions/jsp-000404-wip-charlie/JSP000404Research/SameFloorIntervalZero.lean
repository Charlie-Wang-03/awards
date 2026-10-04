import JSP000404Research.CyclicProjectiveGaps
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Same-floor intervals in a sorted real list

If two entries of a nondecreasing real list lie in the same unit floor band,
then every consecutive gap on the list segment between them has floor zero.
Moreover the sum of those consecutive real gaps telescopes to the endpoint
difference.
-/

namespace JSP000404Research

private theorem sameFloor_natFloor_sub_eq_zero
    {a b : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b)
    (hfloor : Nat.floor a = Nat.floor b) :
    Nat.floor (b - a) = 0 := by
  have hfa : ((Nat.floor a : ℕ) : ℝ) ≤ a :=
    Nat.floor_le ha0
  have hfb : b < ((Nat.floor b : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one b
  have hgaplt : b - a < 1 := by
    rw [← hfloor] at hfb
    linarith
  exact Nat.floor_eq_zero.mpr hgaplt

theorem floor_eq_of_between_floor_eq
    {a b x : ℝ}
    (hax : a ≤ x)
    (hxb : x ≤ b)
    (hfloor : Nat.floor a = Nat.floor b) :
    Nat.floor x = Nat.floor a := by
  have h1 : Nat.floor a ≤ Nat.floor x :=
    Nat.floor_mono hax
  have h2 : Nat.floor x ≤ Nat.floor b :=
    Nat.floor_mono hxb
  rw [← hfloor] at h2
  omega

theorem successiveDiffsFrom_all_floor_zero_of_same_floor
    (a : ℝ) (mid : List ℝ) (b : ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: (mid ++ [b])).Pairwise (· ≤ ·))
    (hfloor : Nat.floor a = Nat.floor b) :
    ∀ d ∈ successiveDiffsFrom a (mid ++ [b]),
      Nat.floor d = 0 := by
  induction mid generalizing a with
  | nil =>
      simp only [List.nil_append, successiveDiffsFrom, List.mem_singleton]
      intro d hd
      subst d
      have hab : a ≤ b :=
        (List.pairwise_cons.mp hsorted).1 b (by simp)
      exact sameFloor_natFloor_sub_eq_zero ha0 hab hfloor
  | cons x xs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      have hax : a ≤ x := hpair.1 x (by simp)
      have hx0 : 0 ≤ x := ha0.trans hax
      have htailSorted :
          (x :: (xs ++ [b])).Pairwise (· ≤ ·) :=
        hpair.2
      have hxb : x ≤ b :=
        (List.pairwise_cons.mp htailSorted).1 b (by simp)
      have hfloorX :
          Nat.floor x = Nat.floor a :=
        floor_eq_of_between_floor_eq hax hxb hfloor
      have hhead :
          Nat.floor (x - a) = 0 :=
        sameFloor_natFloor_sub_eq_zero ha0 hax
          hfloorX.symm
      have hfloorXB :
          Nat.floor x = Nat.floor b := by
        rw [hfloorX,hfloor]
      have htail :=
        ih x hx0 htailSorted hfloorXB
      change ∀ d ∈
        (x - a) :: successiveDiffsFrom x (xs ++ [b]),
        Nat.floor d = 0
      intro d hd
      rcases hd with rfl | hd
      · exact hhead
      · exact htail d hd

theorem successiveDiffsFrom_sum_eq_endpoint_sub
    (a b : ℝ) (mid : List ℝ) :
    (successiveDiffsFrom a (mid ++ [b])).sum = b - a := by
  induction mid generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      simp [successiveDiffsFrom, ih]

#print axioms floor_eq_of_between_floor_eq
#print axioms successiveDiffsFrom_all_floor_zero_of_same_floor
#print axioms successiveDiffsFrom_sum_eq_endpoint_sub

end JSP000404Research
