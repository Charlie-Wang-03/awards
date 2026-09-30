import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# Hall from uniform left degree and bounded right load

For a finite family of candidate sets A_x, Hall expansion follows from a
simple incidence count whenever every left vertex has at least d candidates
and every right value belongs to at most d candidate sets.

For any finite S of left vertices,

  d * card S
    <= sum_{x in S} card A_x
    =  sum_{y in union A_x} load_S(y)
    <= d * card (union A_x).

Hence card S <= card union whenever d is positive.
-/

namespace JSP000404Research

theorem hall_of_uniform_degree_bounded_load
    {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (candidates : L → Finset R)
    (d : ℕ)
    (hd : 1 ≤ d)
    (hleft : ∀ x, d ≤ (candidates x).card)
    (hright :
      ∀ y : R,
        ((Finset.univ : Finset L).filter
          (fun x => y ∈ candidates x)).card ≤ d) :
    ∀ s : Finset L,
      s.card ≤ (s.biUnion candidates).card := by
  intro s
  have hdc :=
    Finset.sum_card_eq_sum_biUnion_card candidates s

  have hlower :
      d * s.card ≤
        ∑ x ∈ s, (candidates x).card := by
    calc
      d * s.card =
          ∑ _x ∈ s, d := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ s, (candidates x).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact hleft x

  have hupper :
      (∑ y ∈ s.biUnion candidates,
          ({x | x ∈ s ∧ y ∈ candidates x} : Finset L).card)
        ≤
      d * (s.biUnion candidates).card := by
    calc
      (∑ y ∈ s.biUnion candidates,
          ({x | x ∈ s ∧ y ∈ candidates x} : Finset L).card)
          ≤
        ∑ _y ∈ s.biUnion candidates, d := by
          apply Finset.sum_le_sum
          intro y hy
          have hsub :
              ({x | x ∈ s ∧ y ∈ candidates x} : Finset L) ⊆
                (Finset.univ : Finset L).filter
                  (fun x => y ∈ candidates x) := by
            intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨Finset.mem_univ x, hx.2⟩
          exact (Finset.card_le_card hsub).trans (hright y)
      _ = d * (s.biUnion candidates).card := by
          simp [Nat.mul_comm]

  have hmul :
      d * s.card ≤
        d * (s.biUnion candidates).card := by
    calc
      d * s.card
          ≤ ∑ x ∈ s, (candidates x).card := hlower
      _ =
          ∑ y ∈ s.biUnion candidates,
            ({x | x ∈ s ∧ y ∈ candidates x} : Finset L).card := hdc
      _ ≤ d * (s.biUnion candidates).card := hupper

  exact Nat.le_of_mul_le_mul_left hmul hd

theorem exists_injective_of_uniform_degree_bounded_load
    {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (candidates : L → Finset R)
    (d : ℕ)
    (hd : 1 ≤ d)
    (hleft : ∀ x, d ≤ (candidates x).card)
    (hright :
      ∀ y : R,
        ((Finset.univ : Finset L).filter
          (fun x => y ∈ candidates x)).card ≤ d) :
    ∃ f : L → R,
      Function.Injective f ∧
      ∀ x, f x ∈ candidates x := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective
    candidates).1
  exact hall_of_uniform_degree_bounded_load
    candidates d hd hleft hright

#print axioms hall_of_uniform_degree_bounded_load
#print axioms exists_injective_of_uniform_degree_bounded_load

end JSP000404Research
