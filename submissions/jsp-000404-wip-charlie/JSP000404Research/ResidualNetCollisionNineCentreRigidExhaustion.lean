import JSP000404Research.ResidualNetCollisionOriginalBridgeMatchingDominance
import JSP000404Research.ResidualTerminalTwinStrictPartition
import Mathlib.Tactic

/-!
# Positive NET duplicate debt on <=9 centres exhausts all hard carriers

A genuine double-hit diagonal requires FOUR DIFFERENT hard carriers:
two safe forward carriers and two strict-descending rigid carriers.
ALL hard carriers form a vertex matching. On at most nine original
centres there is ROOM FOR AT MOST FOUR hard carriers total.

Hence, given any two distinct same-target genuine NET source words
and |V|<=9, the entire HARD carrier set is EXACTLY these four
source witnesses. Since forward pairs are safely transportable and
reverse pairs are strict-descending rigid, every NET terminal rigid
carrier must be one of the two strict reverse carriers. In particular
there is NO terminal equal-exponent TWIN rigid carrier.

This is a source-native elimination of an independent category in
the global six-family dyadic ledger, CONDITIONAL on actual positive
NET duplication and <=9 original centres. It does NOT establish
the complete lower-branch theorem, nor make NET targets true holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- With at most NINE centres, two distinct actual same-diagonal
NET collision sources already use EVERY hard overlap carrier.
This is stronger than the previous "at least eight centres"
obstruction: all other hard faces vanish in this small-cardinality
positive-duplicate regime. -/
theorem net_collision_two_sources_nine_centres_exhaust_hard_carriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 9)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hne : s ≠ t) :
    hardOverlapCarrierPairs C =
      {netCollisionForwardHardPair C exponent hexp honeLoss s,
       netCollisionForwardHardPair C exponent hexp honeLoss t,
       netCollisionReverseHardPair C exponent hexp honeLoss s,
       netCollisionReverseHardPair C exponent hexp honeLoss t} := by
  classical
  let ps := netCollisionForwardHardPair C exponent hexp honeLoss s
  let pt := netCollisionForwardHardPair C exponent hexp honeLoss t
  let qs := netCollisionReverseHardPair C exponent hexp honeLoss s
  let qt := netCollisionReverseHardPair C exponent hexp honeLoss t
  have hpst : ps ≠ pt :=
    net_collision_distinct_same_target_forward_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hqst : qs ≠ qt :=
    net_collision_distinct_same_target_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hpsqs : ps ≠ qs :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s s
  have hpsqt : ps ≠ qt :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t
  have hptqs : pt ≠ qs :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss t s
  have hptqt : pt ≠ qt :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss t t
  let A : Finset (V × V) := {ps,pt,qs,qt}
  have hsubset : A ⊆ hardOverlapCarrierPairs C := by
    intro r hr
    change r ∈ ({ps,pt,qs,qt} : Finset (V × V)) at hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss s).1
    · exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss t).1
    · exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss s).1
    · exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss t).1
  have hA : A.card = 4 := by
    change ({ps,pt,qs,qt} : Finset (V × V)).card = 4
    simp [hpst,hpsqs,hpsqt,hptqs,hptqt,hqst]
  have hh := hardOverlapCarrierPairs_two_mul_card_le_vertices C
  have hcard : (hardOverlapCarrierPairs C).card ≤ A.card := by omega
  have heq : A = hardOverlapCarrierPairs C :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  exact heq.symm

/-- In the same <=9-centre POSITIVE collision case, the entire
NET terminal rigid carrier set consists of exactly TWO genuinely
strict-descending original reverse hard pairs. Thus no other
rigid hard carrier can contribute twin terminal weight. -/
theorem net_collision_two_sources_nine_centres_rigid_eq_two_strict
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 9)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hne : s ≠ t) :
    netRigidHardCarriers C exponent =
      {netCollisionReverseHardPair C exponent hexp honeLoss s,
       netCollisionReverseHardPair C exponent hexp honeLoss t} := by
  classical
  let ps := netCollisionForwardHardPair C exponent hexp honeLoss s
  let pt := netCollisionForwardHardPair C exponent hexp honeLoss t
  let qs := netCollisionReverseHardPair C exponent hexp honeLoss s
  let qt := netCollisionReverseHardPair C exponent hexp honeLoss t
  have hhard :=
    net_collision_two_sources_nine_centres_exhaust_hard_carriers
      C exponent hexp honeLoss hsmall s t hdiag hne
  have hqs : qs ∈ netStrictDescentRigidCarriers C exponent :=
    (strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)).2
  have hqt : qt ∈ netStrictDescentRigidCarriers C exponent :=
    (strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss t)).2
  have hqsrigid : qs ∈ netRigidHardCarriers C exponent :=
    (mem_netStrictDescentRigidCarriers C exponent qs).mp hqs |>.1
  have hqtrigid : qt ∈ netRigidHardCarriers C exponent :=
    (mem_netStrictDescentRigidCarriers C exponent qt).mp hqt |>.1
  ext r
  constructor
  · intro hr
    have hhardmem : r ∈ hardOverlapCarrierPairs C :=
      (mem_netUnpaidHardCarrierPairs C exponent r).mp
        ((mem_netRigidHardCarriers C exponent r).mp hr).1 |>.1
    rw [hhard] at hhardmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hhardmem
    rcases hhardmem with hps | hpt | hqs' | hqt'
    · have hntr := ((mem_netRigidHardCarriers C exponent r).mp hr).2
      subst r
      exact False.elim (hntr
        (net_collision_forward_hard_pair_safe
          C exponent hexp honeLoss s).2)
    · have hntr := ((mem_netRigidHardCarriers C exponent r).mp hr).2
      subst r
      exact False.elim (hntr
        (net_collision_forward_hard_pair_safe
          C exponent hexp honeLoss t).2)
    · simp [hqs']
    · simp [hqt']
  · intro hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hqsrigid
    · exact hqtrigid

/-- Actual positive NET duplicate debt at <=9 original centres
eliminates the entire terminal TWIN rigid carrier family.
This removes an ACTUAL independent class from the six-source
geometric ledger in this regime; it does not yet pay for SOFT,
covered fifth-centre, mixed or projected-profile terms. -/
theorem net_collision_positive_duplicate_nine_centres_no_twin_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 9)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    netTwinRigidCarriers C exponent = ∅ := by
  classical
  obtain ⟨s,t,hne,hdiag⟩ :=
    net_collision_positive_duplicate_has_distinct_source_pair
      C exponent hexp honeLoss hpositive
  have hrigid :=
    net_collision_two_sources_nine_centres_rigid_eq_two_strict
      C exponent hexp honeLoss hsmall s t hdiag hne
  ext r
  constructor
  · intro hr
    have htwin := (mem_netTwinRigidCarriers C exponent r).mp hr
    have hmem : r ∈
        ({netCollisionReverseHardPair C exponent hexp honeLoss s,
          netCollisionReverseHardPair C exponent hexp honeLoss t} :
          Finset (V × V)) := by
      rw [← hrigid]
      exact htwin.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hr | hr
    · have hstrict :
          exponent (netCollisionReverseHardPair C exponent hexp honeLoss s).2 <
          exponent (netCollisionReverseHardPair C exponent hexp honeLoss s).1 :=
        (mem_netStrictDescentRigidCarriers C exponent
          (netCollisionReverseHardPair C exponent hexp honeLoss s)).mp
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)).2 |>.2
      rw [hr] at htwin
      omega
    · have hstrict :
          exponent (netCollisionReverseHardPair C exponent hexp honeLoss t).2 <
          exponent (netCollisionReverseHardPair C exponent hexp honeLoss t).1 :=
        (mem_netStrictDescentRigidCarriers C exponent
          (netCollisionReverseHardPair C exponent hexp honeLoss t)).mp
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource C exponent hexp honeLoss t)).2 |>.2
      rw [hr] at htwin
      omega
  · intro hr
    simpa using hr


/-- For ALL eligible source-native residual colourings on <=9 vertices,
TWO distinct global debts cannot coexist: either the genuine NET
duplicate-image excess is ZERO, or the equal-exponent terminal
TWIN rigid carrier family is EMPTY. This is unconditional with
respect to whether any collision source pair exists. -/
theorem net_collision_nine_centres_duplicate_or_twin_zero
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 9) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 ∨
    netTwinRigidCarriers C exponent = ∅ := by
  by_cases hd :
      netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0
  · exact Or.inl hd
  · exact Or.inr
      (net_collision_positive_duplicate_nine_centres_no_twin_rigid
        C exponent hexp honeLoss hsmall (Nat.pos_of_ne_zero hd))

/-- The actual twin-rigid DYADIC WEIGHT and genuine NET duplicate
debt are mutually exclusive on <=9 original centres. No credit
or payment is invented: the product vanishes because ONE actual
source-dependent term vanishes. -/
theorem net_collision_nine_centres_duplicate_times_twin_mass_zero
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 9) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss *
      (∑ p ∈ netTwinRigidCarriers C exponent,
        (2 : ℕ) ^ exponent p.2) = 0 := by
  rcases net_collision_nine_centres_duplicate_or_twin_zero
      C exponent hexp honeLoss hsmall with hd | htwin
  · simp [hd]
  · simp [htwin]

/-- The two competing net-duplicate and terminal-twin dyadic
liabilities add by MAX, not their independent sum, when |V|<=9.
This is a useful EXACT LEDGER IDENTITY rather than a speculative
net-collision exclusion. It does not pay either surviving debt. -/
theorem net_collision_nine_centres_duplicate_plus_twin_mass_eq_max
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 9) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (∑ p ∈ netTwinRigidCarriers C exponent,
        (2 : ℕ) ^ exponent p.2) =
    max (netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss)
      (∑ p ∈ netTwinRigidCarriers C exponent,
        (2 : ℕ) ^ exponent p.2) := by
  rcases net_collision_nine_centres_duplicate_or_twin_zero
      C exponent hexp honeLoss hsmall with hd | htwin
  · simp [hd]
  · simp [htwin]

/-- Under positive actual NET duplication on <=9 centres, every
terminal RIGID HARD word is actually a STRICT DESCENDING reverse-
transportable rigid word. Hence the independent equal-exponent
twin word mass disappears as a genuine FINITE WORD SET. -/
theorem net_collision_positive_duplicate_nine_centres_all_rigid_words_strict
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 9)
    (hpositive : 0 <
      netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss) :
    netRigidHardWords C exponent =
      netStrictDescentRigidWords C exponent := by
  classical
  obtain ⟨s,t,hne,hdiag⟩ :=
    net_collision_positive_duplicate_has_distinct_source_pair
      C exponent hexp honeLoss hpositive
  have hpair :=
    net_collision_two_sources_nine_centres_rigid_eq_two_strict
      C exponent hexp honeLoss hsmall s t hdiag hne
  have hcarriers :
      netRigidHardCarriers C exponent =
        netStrictDescentRigidCarriers C exponent := by
    ext p
    constructor
    · intro hp
      have he : p ∈
          ({netCollisionReverseHardPair C exponent hexp honeLoss s,
            netCollisionReverseHardPair C exponent hexp honeLoss t} :
            Finset (V × V)) := by
        rw [← hpair]
        exact hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)).2
      · exact (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss t)).2
    · intro hp
      exact ((mem_netStrictDescentRigidCarriers C exponent p).mp hp).1
  unfold netRigidHardWords netStrictDescentRigidWords
  rw [hcarriers]

#print axioms net_collision_nine_centres_duplicate_or_twin_zero
#print axioms net_collision_nine_centres_duplicate_times_twin_mass_zero
#print axioms net_collision_nine_centres_duplicate_plus_twin_mass_eq_max
#print axioms net_collision_positive_duplicate_nine_centres_all_rigid_words_strict

#print axioms net_collision_two_sources_nine_centres_exhaust_hard_carriers
#print axioms net_collision_two_sources_nine_centres_rigid_eq_two_strict
#print axioms net_collision_positive_duplicate_nine_centres_no_twin_rigid

end OrderedEdgeColoring
end JSP000404Research
