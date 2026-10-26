import JSP000404Research.PlanarIntegerNextLayerSupportRigidity
import JSP000404Research.ThreeFiveExactOverweightEquivalence
import Mathlib.Tactic

/-!
# UNCONDITIONAL original n=4, six-centre, integer-scale dyadic capacity

At the ACTUAL integer endpoint t=4 with six distinct original planar
centres satisfying AngleCap, the independently certified original
strict-gap lemma excludes exponent 3, so k(i) is in {0,1,2}.

Every exponent-2 centre has ONE positive quotient support. Three such
centres together with a fourth centre of exponent at least one would
violate the original AngleCap transition packing by the previously
verified integer next-layer three-plus-one exclusion.

With six actual vertices:
* if there are at most two exponent-2 centres, mass ≤16;
* if there are three, every other centre has exponent zero and mass=15.

Four exponent-2 centres are impossible by the same genuine geometry.
This closes the COMPLETE ORIGINAL n=4, |V|=6, δ=0 geometric capacity
without an assumed Hall expansion, Boolean hole or any sorry.

The positive-reminder case and other cardinalities remain open.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Extract three distinct REAL elements from an original finite set,
without an external choice or source-count assumption. -/
theorem exists_three_distinct_mem_of_card_ge_three
    {V : Type*} [DecidableEq V] (S : Finset V)
    (hthree : 3 ≤ S.card) :
    ∃ s a b : V, s ∈ S ∧ a ∈ S ∧ b ∈ S ∧
      s ≠ a ∧ s ≠ b ∧ a ≠ b := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp
    (show 0 < S.card by omega)
  have hremtwo : 2 ≤ (S.erase s).card := by
    rw [Finset.card_erase_of_mem hs]
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp
    (show 0 < (S.erase s).card by omega)
  have hremone : 1 ≤ ((S.erase s).erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp
    (show 0 < ((S.erase s).erase a).card by omega)
  obtain ⟨has, haS⟩ := Finset.mem_erase.mp ha
  obtain ⟨hba, hbS0⟩ := Finset.mem_erase.mp hb
  obtain ⟨hbs, hbS⟩ := Finset.mem_erase.mp hbS0
  exact ⟨s,a,b,hs,haS,hbS,has.symm,hbs.symm,hba.symm⟩

/-- Genuine ORIGINAL six-centre n=4 exact-integer capacity; no
external dyadic payment or artificial source token appears. -/
theorem planar_four_six_exact_integer_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaExact : delta = 0)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) ≤ 16 := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  let S1 : Finset V := Finset.univ.filter (fun i => k i = 1)
  let S2 : Finset V := Finset.univ.filter (fun i => k i = 2)
  have htFour : t = 4 := by rw [hdeltaExact] at ht; linarith
  have hcard6 : (4 : ℕ) + 2 ≤ Fintype.card V := by omega
  have hk : ∀ i : V, k i ≤ 2 := by
    intro i
    exact planar_exact_integer_many_centres_exponent_le_n_sub_two
      hp hcap (by decide : 2 ≤ (4 : ℕ)) hcard6 htFour hlam i (C i)
  have hmass := ternary_dyadic_sum_exact k hk
  change (∑ i : V, (2 : ℕ) ^ k i) =
      Fintype.card V + S1.card + 3 * S2.card at hmass
  have hdisj : Disjoint S1 S2 := by
    apply Finset.disjoint_left.mpr
    intro i hi1 hi2
    have hk1 : k i = 1 := (Finset.mem_filter.mp hi1).2
    have hk2 : k i = 2 := (Finset.mem_filter.mp hi2).2
    omega
  have hcount : S1.card + S2.card ≤ 6 := by
    have hsub := Finset.card_le_univ (S1 ∪ S2)
    rw [Finset.card_union_of_disjoint hdisj] at hsub
    omega
  by_cases hthree : 3 ≤ S2.card
  · obtain ⟨s,a,b,hs,ha,hb,hsa,hsb,hab⟩ :=
      exists_three_distinct_mem_of_card_ge_three S2 hthree
    have hks : k s = 2 := (Finset.mem_filter.mp hs).2
    have hka : k a = 2 := (Finset.mem_filter.mp ha).2
    have hkb : k b = 2 := (Finset.mem_filter.mp hb).2
    have hrest (c : V)
        (hcs : c ≠ s) (hca : c ≠ a) (hcb : c ≠ b) :
        k c = 0 := by
      by_contra hnonzero
      have hcpos : 1 ≤ k c := by omega
      exact planar_integer_no_three_next_with_third_layer_companion
        hp hcap (by decide : 3 ≤ (4 : ℕ)) hcard6
        htFour hlam hsa hsb hcs.symm hab hca.symm hcb.symm
        C (by simpa [k] using hks) (by simpa [k] using hka)
        (by simpa [k] using hkb) (by simpa [k] using hcpos)
    have hS2sub : S2 ⊆ ({s, a, b} : Finset V) := by
      intro c hc
      by_cases hcs : c = s
      · subst c
        simp
      by_cases hca : c = a
      · subst c
        simp
      by_cases hcb : c = b
      · subst c
        simp
      have hc0 := hrest c hcs hca hcb
      have hc2 : k c = 2 := (Finset.mem_filter.mp hc).2
      omega
    have hcount2 : S2.card ≤ 3 := by
      calc
        S2.card ≤ ({s,a,b} : Finset V).card :=
          Finset.card_le_card hS2sub
        _ = 3 := by simp [hsa, hsb, hab]
    have hS1empty : S1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have hc1 : k c = 1 := (Finset.mem_filter.mp hc).2
      have hcs : c ≠ s := by
        intro h
        rw [h, hks] at hc1
        omega
      have hca : c ≠ a := by
        intro h
        rw [h, hka] at hc1
        omega
      have hcb : c ≠ b := by
        intro h
        rw [h, hkb] at hc1
        omega
      have hc0 := hrest c hcs hca hcb
      omega
    rw [hS1empty] at hmass
    simp only [Finset.card_empty, add_zero] at hmass
    omega
  · have hcount2 : S2.card ≤ 2 := by omega
    omega

#print axioms exists_three_distinct_mem_of_card_ge_three
#print axioms planar_four_six_exact_integer_dyadic_capacity

end JSP000404Research
