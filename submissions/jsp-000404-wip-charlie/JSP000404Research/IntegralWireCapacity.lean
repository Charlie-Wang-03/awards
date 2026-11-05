import JSP000404Research.CyclicHalfGrid
import JSP000404Research.WeightedHansel
import Mathlib.Data.Int.ModEq

/-!
# Integer-period wire coding

An integral cyclic event schedule gives a Boolean coordinate for each residue band. Crossing
the period seam reverses the original movement sign. The local gap conditions ensure that
all events in one band at one centre have the same reversed sign. Each common event then
separates its two endpoints, giving the dyadic cardinality bound.

The local incident-gap hypotheses are explicit. Their construction from the planar wire
graph remains a separate geometric connection.
-/

namespace JSP000404Research
namespace IntegralWire

open Quiver

/-- Below a half-integer source threshold, the rounded schedule can use integer times. -/
theorem exists_integer_retiming
    {E : Type*} [Quiver E] (delay wrap : ∀ {u v : E}, (u ⟶ v) → ℤ) (period : ℤ)
    (original : E → ℝ) (root : E)
    (hconnected : ∀ u v : E, Nonempty (Path u v))
    (hsource : ∀ {u v : E} (e : u ⟶ v),
      (delay e : ℝ) < original v - original u + (wrap e : ℝ) * ((period : ℝ) + 1 / 2))
    (hwinding : ∀ (v : E) (p : Path v v), p.vertices.dropLast.Nodup → p.length ≠ 0 →
      CyclicGraph.pathWeight wrap p = 1 ∨ CyclicGraph.pathWeight wrap p = 2) :
    ∃ time : E → ℤ, ∀ {u v : E} (e : u ⟶ v),
      delay e ≤ time v - time u + period * wrap e := by
  obtain ⟨doubled, hdoubled⟩ := CyclicGraph.exists_half_grid_retiming
    delay wrap (2 * period) original root hconnected (by
      intro u v e
      have h := hsource e
      push_cast
      nlinarith) hwinding
  refine ⟨fun v ↦ doubled v / 2, ?_⟩
  intro u v e
  have h := hdoubled e
  have heq : 2 * period * wrap e = 2 * (period * wrap e) := by ring
  rw [heq] at h
  dsimp only
  omega

/-- Transport a movement sign through every crossed period seam. -/
def phaseSign (period time : ℤ) (sign : Bool) : Bool :=
  if (time / period) % 2 = 0 then sign else !sign

theorem phaseSign_ne {period time : ℤ} {a b : Bool} (hab : a ≠ b) :
    phaseSign period time a ≠ phaseSign period time b := by
  cases a <;> cases b <;> simp_all [phaseSign]

/-- Congruent event times with the allowed signed gaps determine the same transported sign. -/
theorem phaseSign_eq_of_congruent
    {period a b : ℤ} (hperiod : 0 < period) {sa sb : Bool}
    (hmod : a % period = b % period) (hspan : |b - a| ≤ period)
    (hsame : sa = sb → |b - a| < period)
    (hdifferent : sa ≠ sb → 1 ≤ |b - a|) :
    phaseSign period a sa = phaseSign period b sb := by
  obtain ⟨turns, hb⟩ := Int.modEq_iff_add_fac.mp hmod
  have hbounds := abs_le.mp hspan
  have hturns : -1 ≤ turns ∧ turns ≤ 1 := by
    constructor
    · by_contra h
      have ht : turns ≤ -2 := by omega
      nlinarith
    · by_contra h
      have ht : 2 ≤ turns := by omega
      nlinarith
  by_cases hsign : sa = sb
  · have hsmall := abs_lt.mp (hsame hsign)
    have hz : turns = 0 := by
      rcases lt_trichotomy turns 0 with h | rfl | h
      · have ht : turns ≤ -1 := by omega
        nlinarith
      · rfl
      · have ht : 1 ≤ turns := by omega
        nlinarith
    simp only [hz, mul_zero, add_zero] at hb
    simp [hb, hsign]
  · have hlarge := hdifferent hsign
    have hnonzero : turns ≠ 0 := by
      intro hz
      simp [hz] at hb
      simp [hb] at hlarge
    have hsteps : turns = -1 ∨ turns = 1 := by omega
    have hquot : b / period = a / period + turns := by
      rw [hb, Int.add_mul_ediv_left a turns (ne_of_gt hperiod)]
    have hparity : (a / period + turns) % 2 = 0 ↔ (a / period) % 2 ≠ 0 := by
      rcases hsteps with rfl | rfl <;> omega
    have hflip : sb = !sa := by cases sa <;> cases sb <;> simp_all
    by_cases ha : (a / period) % 2 = 0
    · have hbodd : (a / period + turns) % 2 ≠ 0 := by simpa [ha] using hparity
      simp [phaseSign, hquot, ha, hbodd, hflip]
    · have hbeven : (a / period + turns) % 2 = 0 := hparity.mpr ha
      simp [phaseSign, hquot, ha, hbeven, hflip]

/-- Cardinality bound for integral cyclic events with separated incident movement signs. -/
theorem card_le_two_pow_of_integral_events
    {V E : Type*} [Fintype V] (period : ℕ) (hperiod : 0 < period)
    (time : E → ℤ) (incident : V → E → Prop) (sign : V → E → Bool)
    (hspan : ∀ v e f, incident v e → incident v f → |time f - time e| ≤ period)
    (hsame : ∀ v e f, incident v e → incident v f → sign v e = sign v f →
      |time f - time e| < period)
    (hdifferent : ∀ v e f, incident v e → incident v f → sign v e ≠ sign v f →
      1 ≤ |time f - time e|)
    (hpair : ∀ v w, v ≠ w → ∃ e, incident v e ∧ incident w e ∧ sign v e ≠ sign w e) :
    Fintype.card V ≤ 2 ^ period := by
  classical
  have hp : (0 : ℤ) < period := by exact_mod_cast hperiod
  let band (e : E) : Fin period := ⟨(time e % period).toNat, by
    have hlo := Int.emod_nonneg (time e) (ne_of_gt hp)
    have hhi := Int.emod_lt_of_pos (time e) hp
    omega⟩
  let bit (v : V) (c : Fin period) : Bool :=
    if ∃ e, incident v e ∧ band e = c ∧ phaseSign period (time e) (sign v e) = true
    then true else false
  have hconsistent (v : V) (e f : E) (he : incident v e) (hf : incident v f)
      (hband : band e = band f) :
      phaseSign period (time e) (sign v e) = phaseSign period (time f) (sign v f) := by
    have hval := congrArg Fin.val hband
    have hemod := Int.emod_nonneg (time e) (ne_of_gt hp)
    have hfmod := Int.emod_nonneg (time f) (ne_of_gt hp)
    have hmod : time e % period = time f % period := by
      dsimp [band] at hval
      omega
    exact phaseSign_eq_of_congruent hp hmod (hspan v e f he hf)
      (hsame v e f he hf) (hdifferent v e f he hf)
  have hbit (v : V) (e : E) (he : incident v e) :
      bit v (band e) = phaseSign period (time e) (sign v e) := by
    cases hvalue : phaseSign period (time e) (sign v e) with
    | false =>
      have hnone : ¬ ∃ f, incident v f ∧ band f = band e ∧
          phaseSign period (time f) (sign v f) = true := by
        rintro ⟨f, hf, hband, htrue⟩
        have h := hconsistent v e f he hf hband.symm
        simp [hvalue, htrue] at h
      simp [bit, hnone]
    | true =>
      have hex : ∃ f, incident v f ∧ band f = band e ∧
          phaseSign period (time f) (sign v f) = true := ⟨e, he, rfl, hvalue⟩
      simp [bit, hex]
  have hsep : ∀ v w, v ≠ w → ∃ c : Fin period, bit v c ≠ bit w c := by
    intro v w hvw
    obtain ⟨e, he, hw, hsign⟩ := hpair v w hvw
    refine ⟨band e, ?_⟩
    rw [hbit v e he, hbit w e hw]
    exact phaseSign_ne hsign
  have hcapacity := weighted_hansel bit (fun _ ↦ Finset.univ) (by
    intro v w hvw
    obtain ⟨c, hc⟩ := hsep v w hvw
    exact ⟨c, Finset.mem_univ c, Finset.mem_univ c, hc⟩)
  simpa using hcapacity

#print axioms phaseSign_ne
#print axioms exists_integer_retiming
#print axioms phaseSign_eq_of_congruent
#print axioms card_le_two_pow_of_integral_events

end IntegralWire
end JSP000404Research
