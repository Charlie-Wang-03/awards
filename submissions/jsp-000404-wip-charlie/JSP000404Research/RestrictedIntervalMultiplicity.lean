import JSP000404Research.RestrictedCriticalPhaseCover
import Mathlib.Tactic

/-!
# Bounded overlap multiplicity on a genuine phase-domain

The previous interval-multiplicity formalization used a finite global
cover of all Real (impossible for bounded intervals).
These theorems repeat the local geometric argument using a restricted
phase-domain, so a real finite cover CAN satisfy their hypotheses.
-/

namespace JSP000404Research
attribute [local instance] Classical.propDecidable

/-- Restricted irredundancy strictly orders the right endpoints when
the left endpoints are weakly ordered. -/
theorem irredundant_on_right_strict
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop) (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCoverOn Domain (InClosedInterval L R) S)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) (hLij : L i ≤ L j) :
    R i < R j := by
  by_contra hnot
  have hR : R j ≤ R i := le_of_not_gt hnot
  have hn :=
    irredundant_on_intervals_not_nested
      Domain L R S hmin hi hj hij
  exact hn (Or.inl ⟨hLij, hR⟩)

/-- Ordered three-interval form of the multiplicity-two statement. -/
theorem restricted_no_threefold_overlap_ordered
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCoverOn Domain (InClosedInterval L R) S)
    {i j k : I}
    (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hLij : L i ≤ L j)
    (hLjk : L j ≤ L k)
    {x : ℝ}
    (hxi : InClosedInterval L R i x)
    (hxj : InClosedInterval L R j x)
    (hxk : InClosedInterval L R k x) :
    False := by
  have hRij :
      R i < R j :=
    irredundant_on_right_strict
      Domain L R S hmin hi hj hij hLij
  have hRjk :
      R j < R k :=
    irredundant_on_right_strict
      Domain L R S hmin hj hk hjk hLjk
  obtain ⟨y, _, hyj, hyprivate⟩ :=
    exists_private_phase_of_irredundant_on
      Domain (InClosedInterval L R) S hmin hj
  have hyNotI : ¬ InClosedInterval L R i y :=
    hyprivate i hi hij
  have hyNotK : ¬ InClosedInterval L R k y :=
    hyprivate k hk hjk.symm
  have hyRightI : R i < y := by
    by_contra hnot
    have hyRi : y ≤ R i := le_of_not_gt hnot
    apply hyNotI
    exact ⟨hLij.trans hyj.1, hyRi⟩
  have hyLeftK : y < L k := by
    by_contra hnot
    have hLky : L k ≤ y := le_of_not_gt hnot
    apply hyNotK
    exact ⟨hLky, hyj.2.trans hRjk.le⟩
  have hLkRi : L k ≤ R i := by
    exact hxk.1.trans (hxi.2)
  linarith

/-- Any three distinct members of an irredundant real-interval cover have empty
triple intersection. -/
theorem restricted_no_threefold_overlap
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCoverOn Domain (InClosedInterval L R) S)
    {i j k : I}
    (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {x : ℝ}
    (hxi : InClosedInterval L R i x)
    (hxj : InClosedInterval L R j x)
    (hxk : InClosedInterval L R k x) :
    False := by
  rcases le_total (L i) (L j) with hijL | hjiL
  · rcases le_total (L j) (L k) with hjkL | hkjL
    · exact restricted_no_threefold_overlap_ordered
        Domain L R S hmin hi hj hk hij hjk hik
        hijL hjkL hxi hxj hxk
    · rcases le_total (L i) (L k) with hikL | hkiL
      · -- i <= k <= j
        exact restricted_no_threefold_overlap_ordered
          Domain L R S hmin hi hk hj hik hjk.symm hij
          hikL hkjL hxi hxk hxj
      · -- k <= i <= j
        exact restricted_no_threefold_overlap_ordered
          Domain L R S hmin hk hi hj hik.symm hij hjk.symm
          hkiL hijL hxk hxi hxj
  · rcases le_total (L i) (L k) with hikL | hkiL
    · -- j <= i <= k
      exact restricted_no_threefold_overlap_ordered
        Domain L R S hmin hj hi hk hij.symm hik hjk
        hjiL hikL hxj hxi hxk
    · rcases le_total (L j) (L k) with hjkL | hkjL
      · -- j <= k <= i
        exact restricted_no_threefold_overlap_ordered
          Domain L R S hmin hj hk hi hjk hik.symm hij.symm
          hjkL hkiL hxj hxk hxi
      · -- k <= j <= i
        exact restricted_no_threefold_overlap_ordered
          Domain L R S hmin hk hj hi hjk.symm hij.symm hik.symm
          hkjL hjiL hxk hxj hxi

/-- Cardinality form: at every real phase, at most two members of an
irredundant interval cover contain that phase. -/
theorem restricted_interval_point_multiplicity_le_two
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCoverOn Domain (InClosedInterval L R) S)
    (x : ℝ) :
    (S.filter (fun i => InClosedInterval L R i x)).card ≤ 2 := by
  classical
  by_contra hnot
  have h3 :
      3 ≤ (S.filter (fun i => InClosedInterval L R i x)).card := by
    omega
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (s := S.filter (fun i => InClosedInterval L R i x))
      h3
  have hcard3 : T.card = 3 := by
    simpa using hTcard
  obtain ⟨i, j, k, hij, hik, hjk, hT⟩ :=
    T.card_eq_three.mp hcard3
  have hiT : i ∈ T := by simp [hT]
  have hjT : j ∈ T := by simp [hT]
  have hkT : k ∈ T := by simp [hT]
  have hiF := hTsub hiT
  have hjF := hTsub hjT
  have hkF := hTsub hkT
  simp only [Finset.mem_filter] at hiF hjF hkF
  exact restricted_no_threefold_overlap
    Domain L R S hmin
    hiF.1 hjF.1 hkF.1
    hij hjk hik
    hiF.2 hjF.2 hkF.2

#print axioms irredundant_on_right_strict
#print axioms restricted_no_threefold_overlap_ordered
#print axioms restricted_no_threefold_overlap
#print axioms restricted_interval_point_multiplicity_le_two

end JSP000404Research
