import PC5488.Aggregate

namespace PC5488

private theorem card_union2_inter_le
    {α : Type*} [DecidableEq α]
    (A B C : Finset α) :
    ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
  calc
    ((A ∪ B) ∩ C).card = ((A ∩ C) ∪ (B ∩ C)).card := by
      congr 1
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    _ ≤ (A ∩ C).card + (B ∩ C).card := Finset.card_union_le _ _

private theorem card_union3_inter_le
    {α : Type*} [DecidableEq α]
    (A B C D : Finset α) :
    (((A ∪ B) ∪ C) ∩ D).card ≤
      (A ∩ D).card + (B ∩ D).card + (C ∩ D).card := by
  have htop :
      (((A ∪ B) ∪ C) ∩ D).card =
        (((A ∩ D) ∪ (B ∩ D)) ∪ (C ∩ D)).card := by
    congr 1
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [htop]
  have hAB := Finset.card_union_le (A ∩ D) (B ∩ D)
  have hABC := Finset.card_union_le ((A ∩ D) ∪ (B ∩ D)) (C ∩ D)
  omega

private theorem card_union4_inter_le
    {α : Type*} [DecidableEq α]
    (A B C D E : Finset α) :
    ((((A ∪ B) ∪ C) ∪ D) ∩ E).card ≤
      (A ∩ E).card + (B ∩ E).card + (C ∩ E).card + (D ∩ E).card := by
  have htop :
      ((((A ∪ B) ∪ C) ∪ D) ∩ E).card =
        ((((A ∩ E) ∪ (B ∩ E)) ∪ (C ∩ E)) ∪ (D ∩ E)).card := by
    congr 1
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [htop]
  have hAB := Finset.card_union_le (A ∩ E) (B ∩ E)
  have hABC := Finset.card_union_le ((A ∩ E) ∪ (B ∩ E)) (C ∩ E)
  have hABCD := Finset.card_union_le (((A ∩ E) ∪ (B ∩ E)) ∪ (C ∩ E)) (D ∩ E)
  omega

/-- Second-order Bonferroni inequality for five finite sets, written without
natural-number subtraction. -/
theorem card_union5_bonferroni
    {α : Type*} [DecidableEq α]
    (A B C D E : Finset α) :
    A.card + B.card + C.card + D.card + E.card ≤
      ((((A ∪ B) ∪ C) ∪ D) ∪ E).card +
        (A ∩ B).card +
        (A ∩ C).card + (B ∩ C).card +
        (A ∩ D).card + (B ∩ D).card + (C ∩ D).card +
        (A ∩ E).card + (B ∩ E).card + (C ∩ E).card + (D ∩ E).card := by
  have h2 := Finset.card_union_add_card_inter A B
  have h3 := Finset.card_union_add_card_inter (A ∪ B) C
  have h4 := Finset.card_union_add_card_inter ((A ∪ B) ∪ C) D
  have h5 := Finset.card_union_add_card_inter (((A ∪ B) ∪ C) ∪ D) E
  have hi3 := card_union2_inter_le A B C
  have hi4 := card_union3_inter_le A B C D
  have hi5 := card_union4_inter_le A B C D E
  omega

/-- The support used by `countMultiples5` is exactly the union of the five
single-generator multiple sets. -/
theorem support5_eq_union_multiples
    (q₁ q₂ q₃ q₄ q₅ n : ℕ) :
    support5 q₁ q₂ q₃ q₄ q₅ n =
      ((((multiplesUpTo q₁ n ∪ multiplesUpTo q₂ n) ∪ multiplesUpTo q₃ n) ∪
          multiplesUpTo q₄ n) ∪ multiplesUpTo q₅ n) := by
  ext e
  simp only [mem_support5, mem_multiplesUpTo, Finset.mem_union]
  tauto

/-- For coprime generators, the intersection of their positive multiples up to
`n` is the set of positive multiples of their product. -/
theorem inter_multiplesUpTo_eq_mul
    {a b n : ℕ}
    (hcop : Nat.Coprime a b) :
    multiplesUpTo a n ∩ multiplesUpTo b n = multiplesUpTo (a * b) n := by
  ext e
  simp only [Finset.mem_inter, mem_multiplesUpTo]
  constructor
  · rintro ⟨⟨he, ha⟩, ⟨_, hb⟩⟩
    exact ⟨he, hcop.mul_dvd_of_dvd_of_dvd ha hb⟩
  · rintro ⟨he, hab⟩
    exact ⟨⟨he, dvd_of_mul_right_dvd hab⟩, ⟨he, dvd_of_mul_left_dvd hab⟩⟩

/-- Cardinality of a pair intersection under coprimality. -/
theorem card_inter_multiplesUpTo_of_coprime
    {a b n : ℕ}
    (hcop : Nat.Coprime a b) :
    (multiplesUpTo a n ∩ multiplesUpTo b n).card = n / (a * b) := by
  rw [inter_multiplesUpTo_eq_mul hcop, card_multiplesUpTo]

/-- The second-order Bonferroni lower bound specialized to the five multiple sets. -/
theorem M_le_count_add_D
    {q₁ q₂ q₃ q₄ q₅ n : ℕ}
    (hc12 : Nat.Coprime q₁ q₂)
    (hc13 : Nat.Coprime q₁ q₃)
    (hc14 : Nat.Coprime q₁ q₄)
    (hc15 : Nat.Coprime q₁ q₅)
    (hc23 : Nat.Coprime q₂ q₃)
    (hc24 : Nat.Coprime q₂ q₄)
    (hc25 : Nat.Coprime q₂ q₅)
    (hc34 : Nat.Coprime q₃ q₄)
    (hc35 : Nat.Coprime q₃ q₅)
    (hc45 : Nat.Coprime q₄ q₅) :
    M q₁ q₂ q₃ q₄ q₅ n ≤
      countMultiples5 q₁ q₂ q₃ q₄ q₅ n + D q₁ q₂ q₃ q₄ q₅ n := by
  let A := multiplesUpTo q₁ n
  let B := multiplesUpTo q₂ n
  let C := multiplesUpTo q₃ n
  let E := multiplesUpTo q₄ n
  let F := multiplesUpTo q₅ n
  have hbon := card_union5_bonferroni A B C E F
  dsimp [A, B, C, E, F] at hbon
  have hsupp := support5_eq_union_multiples q₁ q₂ q₃ q₄ q₅ n
  rw [← hsupp] at hbon
  simp only [card_multiplesUpTo] at hbon
  rw [card_inter_multiplesUpTo_of_coprime hc12,
      card_inter_multiplesUpTo_of_coprime hc13,
      card_inter_multiplesUpTo_of_coprime hc23,
      card_inter_multiplesUpTo_of_coprime hc14,
      card_inter_multiplesUpTo_of_coprime hc24,
      card_inter_multiplesUpTo_of_coprime hc34,
      card_inter_multiplesUpTo_of_coprime hc15,
      card_inter_multiplesUpTo_of_coprime hc25,
      card_inter_multiplesUpTo_of_coprime hc35,
      card_inter_multiplesUpTo_of_coprime hc45] at hbon
  unfold M D countMultiples5
  omega

end PC5488
