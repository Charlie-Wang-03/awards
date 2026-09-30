import JSP000404Research.CanonicalSignOrder
import Mathlib.Tactic

/-!
# Canonical rank terminal for middle-hidden centres

The canonical Boolean sign is the strict lexicographic order of the embedded
points.  Define the rank of a point as the number of embedded vertices
strictly below it in that order.

A six-point middle-hidden support-three centre has one of two signatures:

* centre < top and rank = 2;
* top < centre and rank = 3.

Two distinct centres cannot both have such signatures.  Equal-side cases
would force equal ranks for comparable distinct points.  Opposite-side cases
would place top strictly between two consecutive ranks 2 and 3, while rank
must increase twice.

This file proves the order-theoretic contradiction independently of the
remaining projective-sign alignment bridge.
-/

namespace JSP000404Research

noncomputable def canonicalRank
    {V : Type*} [Fintype V]
    (p : V → Plane) (i : V) : ℕ :=
  (Finset.univ.filter (fun v => CanonicalPointLt p v i)).card

theorem canonicalRank_lt_of_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {a b : V}
    (hab : CanonicalPointLt p a b) :
    canonicalRank p a < canonicalRank p b := by
  classical
  let A : Finset V :=
    Finset.univ.filter (fun v => CanonicalPointLt p v a)
  let B : Finset V :=
    Finset.univ.filter (fun v => CanonicalPointLt p v b)
  have hsub : insert a A ⊆ B := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hvA
    · simp [B, hab]
    · have hva : CanonicalPointLt p v a := by
        simpa [A] using hvA
      have hvb : CanonicalPointLt p v b :=
        canonicalPointLt_trans hva hab
      simp [B, hvb]
  have haA : a ∉ A := by
    simp [A, canonicalPointLt_irrefl]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem haA] at hcard
  change A.card < B.card
  omega

theorem canonicalRank_add_two_le_of_chain
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {a m b : V}
    (ham : CanonicalPointLt p a m)
    (hmb : CanonicalPointLt p m b) :
    canonicalRank p a + 2 ≤ canonicalRank p b := by
  have h1 := canonicalRank_lt_of_lt (p := p) ham
  have h2 := canonicalRank_lt_of_lt (p := p) hmb
  omega

def MiddleHiddenRankSignature
    {V : Type*} [Fintype V]
    (p : V → Plane) (top i : V) : Prop :=
  (CanonicalPointLt p i top ∧ canonicalRank p i = 2) ∨
  (CanonicalPointLt p top i ∧ canonicalRank p i = 3)

/-- Two distinct points cannot both carry the six-point middle-hidden rank
signature relative to the same top point. -/
theorem no_two_middleHiddenRankSignatures
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {top b c : V}
    (hbc : b ≠ c)
    (hb : MiddleHiddenRankSignature p top b)
    (hc : MiddleHiddenRankSignature p top c) :
    False := by
  rcases hb with hb | hb
  · rcases hc with hc | hc
    · rcases canonicalPointLt_total_of_ne hp hbc with hlt | hgt
      · have hr := canonicalRank_lt_of_lt (p := p) hlt
        omega
      · have hr := canonicalRank_lt_of_lt (p := p) hgt
        omega
    · have hr :=
        canonicalRank_add_two_le_of_chain
          (p := p) hb.1 hc.1
      omega
  · rcases hc with hc | hc
    · have hr :=
        canonicalRank_add_two_le_of_chain
          (p := p) hc.1 hb.1
      omega
    · rcases canonicalPointLt_total_of_ne hp hbc with hlt | hgt
      · have hr := canonicalRank_lt_of_lt (p := p) hlt
        omega
      · have hr := canonicalRank_lt_of_lt (p := p) hgt
        omega

#print axioms canonicalRank_lt_of_lt
#print axioms canonicalRank_add_two_le_of_chain
#print axioms no_two_middleHiddenRankSignatures

end JSP000404Research
