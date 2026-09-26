
import JSP000404Research.ExactAngleWitnessRestriction
import JSP000404Research.ConcreteMinimumOverweightRigidity
import JSP000404Research.MinimalOverweightParity
import Mathlib.Tactic

/-!
# A minimum-exponent exact-normalization deletion outside the witness triple

Fix one exact maximum-angle witness W=(a,b,c).  If the minimum-exponent layer
has more than three vertices, at least one minimum vertex lies outside this
triple.

Deleting such a vertex preserves the same exact angle normalization lambda.
Hence an induction hypothesis stated for exact-normalized children may be
applied at the unchanged t=pi/lambda.

Once that one child is known to satisfy the sharp 2^n capacity, the
one-column minimal-overweight rigidity theorem forces:

* old overweight excess = the deleted minimum dyadic weight;
* post-deletion mass = 2^n;
* every survivor exponent is unchanged.

This file packages the exact-normalization selection and the one-column
rigidity in one interface.
-/

namespace JSP000404Research

open scoped BigOperators

/-- If the minimum layer has more than three vertices, one minimum vertex
avoids any prescribed triple. -/
theorem exists_minimum_outside_triple_of_three_lt_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (r0 a b c : V)
    (hmin :
      ∀ i : V, exponent r0 ≤ exponent i)
    (hcard :
      3 < (minimumExponentVertices exponent r0).card) :
    ∃ r : V,
      exponent r = exponent r0 ∧
      r ≠ a ∧ r ≠ b ∧ r ≠ c := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsub :
      minimumExponentVertices exponent r0 ⊆ {a,b,c} := by
    intro r hr
    have hrmin :
        exponent r = exponent r0 :=
      (mem_minimumExponentVertices exponent r0 r).1 hr
    have hcases := hnone r hrmin
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcases
  have hle :=
    Finset.card_le_card hsub
  have htriple : ({a,b,c} : Finset V).card ≤ 3 := by
    simp
    omega
  omega

/-- Exact-witness specialization of the preceding selection theorem. -/
theorem exists_minimum_avoiding_exactWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane} {lam : ℝ}
    (exponent : V → ℕ)
    (r0 : V)
    (hmin :
      ∀ i : V, exponent r0 ≤ exponent i)
    (W : ExactAngleWitness p lam)
    (hcard :
      3 < (minimumExponentVertices exponent r0).card) :
    ∃ r : V,
      exponent r = exponent r0 ∧
      r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c := by
  exact exists_minimum_outside_triple_of_three_lt_card
    exponent r0 W.a W.b W.c hmin hcard

/-- Main exact-normalization one-column rigidity package.

If the minimum layer has more than three vertices, choose a minimum centre
outside the fixed exact witness triple.  Its deletion preserves the exact
angle normalization.  If that child is bounded by the induction hypothesis,
then the deletion column is completely rigid.
-/
theorem exists_exact_minimum_deletion_rigidity
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hV : 3 ≤ Fintype.card V)
    (ht0 : 0 ≤ t)
    (n : ℕ)
    (r0 : V)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hminCard :
      3 <
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card)
    (hchild :
      ∀ r : V,
        r ≠ W.a → r ≠ W.b → r ≠ W.c →
        deletionPostWeight
            (concreteDeletionAfter C hV t) r
          ≤ 2 ^ n) :
    ∃ r : V,
      centreExponent (C r) t =
          centreExponent (C r0) t
      ∧ r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c
      ∧ ExactAngleCap (deletePoint p r) lam
      ∧ deletionPostWeight
          (concreteDeletionAfter C hV t) r = 2 ^ n
      ∧ ∀ i : V, i ≠ r →
          concreteDeletionAfter C hV t r i =
            centreExponent (C i) t := by
  classical
  obtain ⟨r, hrmin, hra, hrb, hrc⟩ :=
    exists_minimum_avoiding_exactWitness
      (fun i => centreExponent (C i) t)
      r0 hmin W hminCard
  have hminR :
      ∀ i : V,
        centreExponent (C r) t ≤
          centreExponent (C i) t := by
    intro i
    rw [hrmin]
    exact hmin i
  have hchildR :
      deletionPostWeight
          (concreteDeletionAfter C hV t) r
        ≤ 2 ^ n :=
    hchild r hra hrb hrc
  have hrig :=
    concrete_minimum_deletion_rigidity_of_child_bound
      C hV ht0 n r hexp hover hchildR hminR
  have hexact :
      ExactAngleCap (deletePoint p r) lam :=
    exactAngleCap_deletePoint_of_avoids_witness
      hcap W r hra hrb hrc
  exact ⟨r, hrmin, hra, hrb, hrc, hexact,
    hrig.2.1, hrig.2.2⟩

/-- Dichotomy form convenient for induction: either the minimum layer has at
most three vertices, or there is an exact-normalization-preserving rigid
minimum deletion. -/
theorem minimum_layer_le_three_or_exact_rigid_deletion
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hV : 3 ≤ Fintype.card V)
    (ht0 : 0 ≤ t)
    (n : ℕ)
    (r0 : V)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        r ≠ W.a → r ≠ W.b → r ≠ W.c →
        deletionPostWeight
            (concreteDeletionAfter C hV t) r
          ≤ 2 ^ n) :
    (minimumExponentVertices
      (fun i => centreExponent (C i) t) r0).card ≤ 3
    ∨
    ∃ r : V,
      centreExponent (C r) t =
          centreExponent (C r0) t
      ∧ r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c
      ∧ ExactAngleCap (deletePoint p r) lam
      ∧ deletionPostWeight
          (concreteDeletionAfter C hV t) r = 2 ^ n
      ∧ ∀ i : V, i ≠ r →
          concreteDeletionAfter C hV t r i =
            centreExponent (C i) t := by
  classical
  by_cases hsmall :
      (minimumExponentVertices
        (fun i => centreExponent (C i) t) r0).card ≤ 3
  · exact Or.inl hsmall
  · right
    apply exists_exact_minimum_deletion_rigidity
      hcap W C hV ht0 n r0 hexp hover hmin
  · omega
  · exact hchild


/-- Five minimum-layer vertices force two distinct minima outside any prescribed
triple. -/
theorem exists_two_minimum_outside_triple_of_five_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (r0 a b c : V)
    (hmin :
      ∀ i : V, exponent r0 ≤ exponent i)
    (hcard :
      5 ≤ (minimumExponentVertices exponent r0).card) :
    ∃ r s : V,
      r ≠ s ∧
      exponent r = exponent r0 ∧
      exponent s = exponent r0 ∧
      r ≠ a ∧ r ≠ b ∧ r ≠ c ∧
      s ≠ a ∧ s ≠ b ∧ s ≠ c := by
  classical
  let M := minimumExponentVertices exponent r0
  let T : Finset V := {a,b,c}
  let O := M \ T
  have hTcard : T.card ≤ 3 := by
    dsimp [T]
    simp
    omega
  have hInter :
      (M ∩ T).card ≤ 3 := by
    have hle :
        (M ∩ T).card ≤ T.card :=
      Finset.card_le_card (Finset.inter_subset_right)
    omega
  have hsplit :=
    Finset.card_sdiff_add_card_inter M T
  have hOcard : 1 < O.card := by
    dsimp [O]
    omega
  obtain ⟨r, hrO, s, hsO, hrs⟩ :=
    Finset.one_lt_card.mp hOcard
  have hrData :
      r ∈ M ∧ r ∉ T := by
    simpa [O] using hrO
  have hsData :
      s ∈ M ∧ s ∉ T := by
    simpa [O] using hsO
  have hrMin :
      exponent r = exponent r0 := by
    exact (mem_minimumExponentVertices
      exponent r0 r).1 hrData.1
  have hsMin :
      exponent s = exponent r0 := by
    exact (mem_minimumExponentVertices
      exponent r0 s).1 hsData.1
  have hrAvoid :
      r ≠ a ∧ r ≠ b ∧ r ≠ c := by
    simpa [T] using hrData.2
  have hsAvoid :
      s ≠ a ∧ s ≠ b ∧ s ≠ c := by
    simpa [T] using hsData.2
  exact ⟨r, s, hrs, hrMin, hsMin,
    hrAvoid.1, hrAvoid.2.1, hrAvoid.2.2,
    hsAvoid.1, hsAvoid.2.1, hsAvoid.2.2⟩

/-- Once one witness-avoiding minimum child is bounded, the minimum layer is
odd; therefore a layer already known to have more than three vertices actually
has at least five. -/
theorem five_le_minimum_layer_of_three_lt_and_exact_child
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hV : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (n : ℕ)
    (r0 r : V)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hminStrict :
      centreExponent (C r0) t < n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hrMin :
      centreExponent (C r) t =
        centreExponent (C r0) t)
    (hchildR :
      deletionPostWeight
          (concreteDeletionAfter C hV t) r
        ≤ 2 ^ n)
    (hthree :
      3 <
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card) :
    5 ≤
      (minimumExponentVertices
        (fun i => centreExponent (C i) t) r0).card := by
  have hminR :
      ∀ i : V,
        centreExponent (C r) t ≤
          centreExponent (C i) t := by
    intro i
    rw [hrMin]
    exact hmin i
  have hmonoR :
      ∀ i, i ≠ r →
        centreExponent (C i) t ≤
          concreteDeletionAfter C hV t r i := by
    intro i hir
    exact concreteDeletionAfter_mono
      C hV ht0 hir
  have hodd :
      Odd
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r).card :=
    minimumExponentVertices_card_odd_of_child_bound
      (fun i => centreExponent (C i) t)
      (concreteDeletionAfter C hV t)
      n r hexp
      (by rw [hrMin]; exact hminStrict)
      hmonoR hover hchildR hminR
  have hset :
      minimumExponentVertices
          (fun i => centreExponent (C i) t) r
        =
      minimumExponentVertices
          (fun i => centreExponent (C i) t) r0 := by
    ext i
    simp [hrMin]
  rw [hset] at hodd
  have hmod :
      (minimumExponentVertices
        (fun i => centreExponent (C i) t) r0).card % 2 = 1 :=
    Nat.odd_iff.mp hodd
  omega

/-- Large minimum-layer branch: after one exact child gives parity, there are
two distinct minimum centres outside the fixed exact witness triple. -/
theorem exists_two_exact_minima_avoiding_witness
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hV : 3 ≤ Fintype.card V)
    (ht0 : 0 ≤ t)
    (n : ℕ)
    (r0 : V)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hminStrict :
      centreExponent (C r0) t < n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hminCard :
      3 <
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card)
    (hchild :
      ∀ r : V,
        r ≠ W.a → r ≠ W.b → r ≠ W.c →
        deletionPostWeight
            (concreteDeletionAfter C hV t) r
          ≤ 2 ^ n) :
    ∃ r s : V,
      r ≠ s ∧
      centreExponent (C r) t =
        centreExponent (C r0) t ∧
      centreExponent (C s) t =
        centreExponent (C r0) t ∧
      r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c ∧
      s ≠ W.a ∧ s ≠ W.b ∧ s ≠ W.c ∧
      ExactAngleCap (deletePoint p r) lam ∧
      ExactAngleCap (deletePoint p s) lam := by
  classical
  obtain ⟨r, hrMin, hra, hrb, hrc⟩ :=
    exists_minimum_avoiding_exactWitness
      (fun i => centreExponent (C i) t)
      r0 hmin W hminCard
  have hfive :
      5 ≤
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card :=
    five_le_minimum_layer_of_three_lt_and_exact_child
      C hV ht0 n r0 r hexp hminStrict hover hmin
      hrMin (hchild r hra hrb hrc) hminCard
  obtain ⟨r', s', hrs, hrMin', hsMin',
      hra', hrb', hrc', hsa', hsb', hsc'⟩ :=
    exists_two_minimum_outside_triple_of_five_le_card
      (fun i => centreExponent (C i) t)
      r0 W.a W.b W.c hmin hfive
  have hexactR :
      ExactAngleCap (deletePoint p r') lam :=
    exactAngleCap_deletePoint_of_avoids_witness
      hcap W r' hra' hrb' hrc'
  have hexactS :
      ExactAngleCap (deletePoint p s') lam :=
    exactAngleCap_deletePoint_of_avoids_witness
      hcap W s' hsa' hsb' hsc'
  exact ⟨r', s', hrs, hrMin', hsMin',
    hra', hrb', hrc', hsa', hsb', hsc',
    hexactR, hexactS⟩

#print axioms exists_minimum_outside_triple_of_three_lt_card
#print axioms exists_minimum_avoiding_exactWitness
#print axioms exists_exact_minimum_deletion_rigidity
#print axioms minimum_layer_le_three_or_exact_rigid_deletion

end JSP000404Research
