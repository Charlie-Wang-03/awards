import JSP000404Research.WeightedBlockHallOutlet
import JSP000404Research.MinimalHallObstruction
import Mathlib.Tactic

/-!
# Minimal dyadic-unit Hall obstruction for a vertex block family

Given vertex demands 2^k(v) and a common candidate block B(v) for all units of
vertex v, explode each vertex into its dyadic target units.

If vertex-block expansion fails, then Hall fails for the exploded unit family.
Choose an inclusion-minimal deficient unit set S.

The general MinimalHallObstruction theorem immediately gives:

  card N(S) = card S - 1,

and deleting any one target unit leaves exactly the same neighbourhood.

Hence the final weighted obstruction has deficiency exactly one at the unit
level.  This is sharper than working only with a minimal deficient vertex
support.
-/

namespace JSP000404Research

noncomputable def blockUnitCandidates
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    (x : DyadicTargetUnit exponent) :
    Finset (Fin n → Bool) :=
  blocks x.1

theorem block_expansion_failure_gives_unit_hall_failure
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    (hfail :
      ¬ ∀ S : Finset V,
        (∑ v ∈ S, 2 ^ exponent v) ≤
          (S.biUnion blocks).card) :
    ∃ s : Finset (DyadicTargetUnit exponent),
      FiniteHall.Deficient
        (blockUnitCandidates exponent blocks) s := by
  classical
  push_neg at hfail
  obtain ⟨S,hS⟩ := hfail
  let s : Finset (DyadicTargetUnit exponent) :=
    (S.sigma fun v => Finset.univ : Finset (DyadicTargetUnit exponent))
  have hsCard :
      s.card = ∑ v ∈ S, 2 ^ exponent v := by
    simp [s]
  have hsUnion :
      s.biUnion (blockUnitCandidates exponent blocks) =
        S.biUnion blocks := by
    ext word
    constructor
    · intro hw
      rcases Finset.mem_biUnion.mp hw with ⟨x,hxs,hword⟩
      rcases Finset.mem_sigma.mp hxs with ⟨hxS,hxUnit⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨x.1,hxS,hword⟩
    · intro hw
      rcases Finset.mem_biUnion.mp hw with ⟨v,hvS,hword⟩
      have hnonempty : (Finset.univ : Finset (Fin (2 ^ exponent v))).Nonempty := by
        simp
      obtain ⟨i,hi⟩ := hnonempty
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨v,i⟩,?_,?_⟩
      · apply Finset.mem_sigma.mpr
        exact ⟨hvS,Finset.mem_univ i⟩
      · exact hword
  refine ⟨s,?_⟩
  unfold FiniteHall.Deficient
  rw [hsUnion,hsCard]
  exact hS

theorem exists_minimal_dyadic_unit_obstruction_of_block_failure
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    (hfail :
      ¬ ∀ S : Finset V,
        (∑ v ∈ S, 2 ^ exponent v) ≤
          (S.biUnion blocks).card) :
    ∃ s : Finset (DyadicTargetUnit exponent),
      FiniteHall.InclusionMinimalDeficient
        (blockUnitCandidates exponent blocks) s ∧
      (s.biUnion (blockUnitCandidates exponent blocks)).card =
        s.card - 1 ∧
      ∀ x ∈ s,
        ((s.erase x).biUnion
          (blockUnitCandidates exponent blocks)) =
        s.biUnion (blockUnitCandidates exponent blocks) := by
  classical
  obtain ⟨s0,hs0⟩ :=
    block_expansion_failure_gives_unit_hall_failure
      exponent blocks hfail
  let candidates :=
    (s0.powerset).filter
      (fun s =>
        FiniteHall.Deficient
          (blockUnitCandidates exponent blocks) s)
  have hnonempty : candidates.Nonempty := by
    refine ⟨s0,?_⟩
    simp [candidates,hs0]
  let m := Nat.find
    (show ∃ k : ℕ,
      ∃ s ∈ candidates, s.card = k by
        exact ⟨s0.card,s0,by simp [candidates,hs0],rfl⟩)
  have hmSpec := Nat.find_spec
    (show ∃ k : ℕ,
      ∃ s ∈ candidates, s.card = k by
        exact ⟨s0.card,s0,by simp [candidates,hs0],rfl⟩)
  obtain ⟨s,hsCand,hsCard⟩ := hmSpec
  have hsData := Finset.mem_filter.mp hsCand
  have hsMin :
      ∀ t : Finset (DyadicTargetUnit exponent),
        t ⊂ s →
        ¬ FiniteHall.Deficient
          (blockUnitCandidates exponent blocks) t := by
    intro t hts htDef
    have htSubS0 : t ⊆ s0 :=
      hts.1.trans (Finset.mem_powerset.mp hsData.1)
    have htCand : t ∈ candidates := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr htSubS0,htDef⟩
    have hP :
        ∃ q ∈ candidates, q.card = t.card :=
      ⟨t,htCand,rfl⟩
    have hmLe :=
      Nat.find_min'
        (show ∃ k : ℕ,
          ∃ q ∈ candidates, q.card = k by
            exact ⟨s0.card,s0,by simp [candidates,hs0],rfl⟩)
        hP
    have hlt := Finset.card_lt_card hts
    rw [hsCard] at hlt
    omega
  have hminimal :
      FiniteHall.InclusionMinimalDeficient
        (blockUnitCandidates exponent blocks) s :=
    ⟨hsData.2,hsMin⟩
  refine ⟨s,hminimal,
    FiniteHall.minimalDeficient_neighborhood_card_eq
      _ hminimal,?_⟩
  intro x hx
  exact FiniteHall.minimalDeficient_biUnion_erase_eq
    _ hminimal hx

theorem minimal_dyadic_unit_obstruction_no_unique_candidate
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    {s : Finset (DyadicTargetUnit exponent)}
    (hmin :
      FiniteHall.InclusionMinimalDeficient
        (blockUnitCandidates exponent blocks) s) :
    ∀ x ∈ s,
      ∀ word ∈ blocks x.1,
        ∃ y ∈ s,
          y ≠ x ∧
          word ∈ blocks y.1 := by
  intro x hx word hword
  exact FiniteHall.minimalDeficient_no_unique_target
    (blockUnitCandidates exponent blocks)
    hmin hx hword

#print axioms block_expansion_failure_gives_unit_hall_failure
#print axioms exists_minimal_dyadic_unit_obstruction_of_block_failure
#print axioms minimal_dyadic_unit_obstruction_no_unique_candidate

end JSP000404Research
