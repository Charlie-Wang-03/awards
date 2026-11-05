import JSP000404Research.NinePhaseMatching
import JSP000404Research.NinePhaseFiveRowObstruction

/-!
# Capacity twenty for coherent nine-phase rows

Complete each partial row to the verified catalog. The twofold cover first bounds the
family by twenty-one. Equality fills every slot and triggers the explicit matching
certificate, while triple coherence excludes both of its five-row cores.
-/

namespace JSP000404Research.NinePhase

open scoped BigOperators

theorem Shared.mono {r s r' s' : Fin 9 → Option Bool} {c : Fin 9}
    (hr : Extends r r') (hs : Extends s s') (h : Shared r s c) : Shared r' s' c := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨hr c true ha, hs c false hb⟩
  · exact Or.inr ⟨hr c false ha, hs c true hb⟩

theorem before_eq_of_shared_extension {r s r' : Fin 9 → Option Bool} {c : Fin 9}
    (hr : Extends r r') (h : Shared r s c) : before r' c = before r c := by
  rcases h with ⟨ha, _⟩ | ⟨ha, _⟩
  · simp only [before, hr c true ha, ha]
  · simp only [before, hr c false ha, ha]

theorem coherent_of_extensions {V : Type*} {r s : V → Fin 9 → Option Bool}
    {phase : V → V → Fin 9} (hextends : ∀ v, Extends (r v) (s v))
    (hshared : ∀ v w, v ≠ w → Shared (r v) (r w) (phase v w))
    (hcoherent : Coherent r phase) : Coherent s phase := by
  intro a b c hab hac hbc
  rw [before_eq_of_shared_extension (hextends a) (hshared a b hab),
    before_eq_of_shared_extension (hextends a) (hshared a c hac),
    before_eq_of_shared_extension (hextends b) (hshared b c hbc)]
  exact hcoherent a b c hab hac hbc

theorem card_le_twenty_of_coherent_rows {V : Type*} [Fintype V]
    (r : V → Fin 9 → Option Bool) (hvalid : ∀ v, OddWire.PartialValid (r v))
    (phase : V → V → Fin 9)
    (hshared : ∀ v w, v ≠ w → Shared (r v) (r w) (phase v w))
    (hcoherent : Coherent r phase) : Fintype.card V ≤ 20 := by
  classical
  choose code hextends using fun v ↦ catalog_completion (r v)
    (localValid_of_partialValid (hvalid v))
  have hsharedCode (v w : V) (hvw : v ≠ w) :
      Shared (row (code v)) (row (code w)) (phase v w) :=
    (hshared v w hvw).mono (hextends v) (hextends w)
  have hcoherentCode : Coherent (fun v ↦ row (code v)) phase :=
    coherent_of_extensions hextends hshared hcoherent
  have hsep (v w : V) (hvw : v ≠ w) : Separated (code v) (code w) := by
    apply (separated_iff_rows _ _).mpr
    rcases hsharedCode v w hvw with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨phase v w, true, false, ha, hb, by decide⟩
    · exact ⟨phase v w, false, true, ha, hb, by decide⟩
  let support (v : V) := (Finset.univ : Finset (Fin 42)).filter
    (fun slot ↦ covers (code v) slot = true)
  have hdisjoint : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint support := by
    intro v _ w _ hvw
    apply Finset.disjoint_left.mpr
    intro slot hv hw
    have hfalse := separated_disjoint_covers _ _ (hsep v w hvw) slot
      (Finset.mem_filter.mp hv).2
    have htrue := (Finset.mem_filter.mp hw).2
    exact Bool.noConfusion (htrue.symm.trans hfalse)
  have hsum : ((Finset.univ : Finset V).biUnion support).card = Fintype.card V * 2 := by
    rw [Finset.card_biUnion hdisjoint]
    simp only [support, catalog_coverage, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  by_contra hlarge
  have hupper := Finset.card_le_card
    (Finset.subset_univ ((Finset.univ : Finset V).biUnion support))
  rw [hsum] at hupper
  simp only [Finset.card_univ, Fintype.card_fin] at hupper
  have hcard : Fintype.card V = 21 := by omega
  have hunion : (Finset.univ : Finset V).biUnion support = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [hsum, hcard]
    norm_num
  let selected (i : Fin 78) : Bool := decide (∃ v, code v = i)
  have hcover : ∀ slot, ∃ i, covers i slot = true ∧ selected i = true := by
    intro slot
    have hmem : slot ∈ (Finset.univ : Finset V).biUnion support := by rw [hunion]; simp
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hmem
    exact ⟨code v, (Finset.mem_filter.mp hv).2, by simp [selected]⟩
  have hsepSelected : ∀ i j, i ≠ j → selected i = true → selected j = true →
      Separated i j := by
    intro i j hij hi hj
    obtain ⟨v, hv⟩ : ∃ v, code v = i := by simpa [selected] using hi
    obtain ⟨w, hw⟩ : ∃ w, code w = j := by simpa [selected] using hj
    have hvw : v ≠ w := by rintro rfl; exact hij (hv.symm.trans hw)
    simpa only [hv, hw] using hsep v w hvw
  have hnoCore (flip : Bool) : ¬∀ i : Fin 5, selected (coreCode flip i) = true := by
    intro hall
    have hexists (i : Fin 5) : ∃ v, code v = coreCode flip i := by
      simpa [selected] using hall i
    choose vertex hvertex using hexists
    have hcoreInjective : Function.Injective (coreCode flip) :=
      (by decide : ∀ flip, Function.Injective (coreCode flip)) flip
    have hinjective : Function.Injective vertex := by
      intro i j hij
      apply hcoreInjective
      rw [← hvertex i, ← hvertex j, hij]
    apply core_not_coherent flip (fun i j ↦ phase (vertex i) (vertex j))
    · intro i j hij
      simpa only [hvertex] using hsharedCode (vertex i) (vertex j) (hinjective.ne hij)
    · intro i j k hij hik hjk
      simpa only [hvertex] using hcoherentCode (vertex i) (vertex j) (vertex k)
        (hinjective.ne hij) (hinjective.ne hik) (hinjective.ne hjk)
  apply no_full_cover_avoiding_cores selected hcover hsepSelected
  · rintro ⟨h25, h54, h70, h11, h44⟩
    apply hnoCore false
    intro i
    fin_cases i
    · exact h25
    · exact h54
    · exact h70
    · exact h11
    · exact h44
  · rintro ⟨h24, h55, h71, h10, h45⟩
    apply hnoCore true
    intro i
    fin_cases i
    · exact h24
    · exact h55
    · exact h71
    · exact h10
    · exact h45

#print axioms card_le_twenty_of_coherent_rows

end JSP000404Research.NinePhase
