import JSP000404Research.MinimalPhaseCover
import Mathlib.Tactic

/-!
# Multiplicity two for irredundant interval covers

An inclusion-irredundant family of real intervals cannot have three distinct
members through one common point.

Indeed, order the three intervals by left endpoint.  Irredundancy orders their
right endpoints in the same strict order.  A private point of the middle
interval would then have to lie simultaneously

  to the right of the first interval,
  to the left of the third interval.

But the assumed common point forces the third left endpoint to lie no later
than the first right endpoint.

Thus every phase belongs to at most two selected intervals.  This is a useful
structural strengthening for the minimum-cover phase route: selected
obstructions form a one-dimensional overlap chain rather than an arbitrary
hypergraph.
-/

namespace JSP000404Research

/-- Ordered three-interval form of the multiplicity-two statement. -/
theorem no_threefold_overlap_of_irredundant_ordered
    {I : Type*} [DecidableEq I]
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCover (InClosedInterval L R) S)
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
    irredundant_interval_right_strict
      L R S hmin hi hj hij hLij
  have hRjk :
      R j < R k :=
    irredundant_interval_right_strict
      L R S hmin hj hk hjk hLjk
  obtain ⟨y, hyj, hyprivate⟩ :=
    exists_private_phase_of_irredundant
      (InClosedInterval L R) S hmin hj
  have hyNotI : ¬ InClosedInterval L R i y :=
    hyprivate i hi hij.symm
  have hyNotK : ¬ InClosedInterval L R k y :=
    hyprivate k hk hjk
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
theorem no_threefold_overlap_of_irredundant
    {I : Type*} [DecidableEq I]
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCover (InClosedInterval L R) S)
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
    · exact no_threefold_overlap_of_irredundant_ordered
        L R S hmin hi hj hk hij hjk hik
        hijL hjkL hxi hxj hxk
    · rcases le_total (L i) (L k) with hikL | hkiL
      · -- i <= k <= j
        exact no_threefold_overlap_of_irredundant_ordered
          L R S hmin hi hk hj hik hjk.symm hij
          hikL hkjL hxi hxk hxj
      · -- k <= i <= j
        exact no_threefold_overlap_of_irredundant_ordered
          L R S hmin hk hi hj hik.symm hij hjk.symm
          hkiL hijL hxk hxi hxj
  · rcases le_total (L i) (L k) with hikL | hkiL
    · -- j <= i <= k
      exact no_threefold_overlap_of_irredundant_ordered
        L R S hmin hj hi hk hij.symm hik hjk
        hjiL hikL hxj hxi hxk
    · rcases le_total (L j) (L k) with hjkL | hkjL
      · -- j <= k <= i
        exact no_threefold_overlap_of_irredundant_ordered
          L R S hmin hj hk hi hjk hik.symm hij.symm
          hjkL hkiL hxj hxk hxi
      · -- k <= j <= i
        exact no_threefold_overlap_of_irredundant_ordered
          L R S hmin hk hj hi hjk.symm hij.symm hik.symm
          hkjL hjiL hxk hxj hxi

/-- Cardinality form: at every real phase, at most two members of an
irredundant interval cover contain that phase. -/
theorem irredundant_interval_point_multiplicity_le_two
    {I : Type*} [DecidableEq I]
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCover (InClosedInterval L R) S)
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
  exact no_threefold_overlap_of_irredundant
    L R S hmin
    hiF.1 hjF.1 hkF.1
    hij hik hjk
    hiF.2 hjF.2 hkF.2

#print axioms no_threefold_overlap_of_irredundant
#print axioms irredundant_interval_point_multiplicity_le_two

end JSP000404Research
