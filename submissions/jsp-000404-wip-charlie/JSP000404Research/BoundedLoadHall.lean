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
    <= total incidences from S
    <= d * card (union_{x in S} A_x),

hence card S <= card union.

This criterion is tailored to the two-exit loss expansion: if each unresolved
target unit has two candidate exits and no Boolean word can serve more than two
such units, Hall follows without constructing augmenting paths explicitly.
-/

namespace JSP000404Research

theorem hall_of_uniform_degree_bounded_load
    {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (candidates : L → Finset R)
    (d : ℕ)
    (hleft : ∀ x, d ≤ (candidates x).card)
    (hright :
      ∀ y : R,
        ((Finset.univ : Finset L).filter
          (fun x => y ∈ candidates x)).card ≤ d) :
    ∀ s : Finset L,
      s.card ≤ (s.biUnion candidates).card := by
  intro s
  by_cases hd0 : d = 0
  · subst d
    simp
  have hdpos : 1 ≤ d := by omega
  let I : Finset (L × R) :=
    (s.product (s.biUnion candidates)).filter
      (fun p => p.2 ∈ candidates p.1)
  have hlower :
      d * s.card ≤ I.card := by
    calc
      d * s.card
          ≤ ∑ x ∈ s, (candidates x).card := by
              have h := Finset.sum_le_sum
                (fun x hx => hleft x)
              simpa [Finset.sum_const_nat, Nat.mul_comm] using h
      _ = I.card := by
          classical
          rw [show I.card =
              ∑ x ∈ s,
                ((s.biUnion candidates).filter
                  (fun y => y ∈ candidates x)).card by
            unfold I
            rw [Finset.card_filter]
            symm
            exact Finset.sum_card_fiberwise
              (s := s)
              (t := s.biUnion candidates)
              (r := fun x y => y ∈ candidates x)]
          apply Finset.sum_congr rfl
          intro x hx
          have hsub :
              candidates x ⊆ s.biUnion candidates := by
            intro y hy
            exact Finset.mem_biUnion.mpr ⟨x,hx,hy⟩
          rw [Finset.filter_eq_self.2]
          exact fun y hy => hsub hy
  have hupper :
      I.card ≤ d * (s.biUnion candidates).card := by
    calc
      I.card
          =
        ∑ y ∈ s.biUnion candidates,
          (s.filter (fun x => y ∈ candidates x)).card := by
            unfold I
            rw [Finset.card_filter]
            exact Finset.sum_card_fiberwise
              (s := s.biUnion candidates)
              (t := s)
              (r := fun y x => y ∈ candidates x)
      _ ≤
        ∑ _y ∈ s.biUnion candidates, d := by
          apply Finset.sum_le_sum
          intro y hy
          have hsub :
              s.filter (fun x => y ∈ candidates x) ⊆
                (Finset.univ : Finset L).filter
                  (fun x => y ∈ candidates x) := by
            intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨Finset.mem_univ x,hx.2⟩
          exact (Finset.card_le_card hsub).trans (hright y)
      _ = d * (s.biUnion candidates).card := by
          simp [Nat.mul_comm]
  omega

theorem exists_injective_of_uniform_degree_bounded_load
    {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (candidates : L → Finset R)
    (d : ℕ)
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
    candidates d hleft hright

#print axioms hall_of_uniform_degree_bounded_load
#print axioms exists_injective_of_uniform_degree_bounded_load

end JSP000404Research
