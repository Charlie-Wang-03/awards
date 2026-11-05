import JSP000404Research.CyclicWireLocalGaps

/-!
# Three- and five-phase cyclic wire capacities

Doubled event times have a two-unit delay between opposite movement signs. Their parity
transports the signs into partial colourings of an odd coordinate cycle. On three or five
coordinates, every such partial colouring extends to one of respectively three or five
fixed maximal-independent-set codes. Shared events make the resulting wire codes distinct.
-/

namespace JSP000404Research
namespace OddWire

def eventBit (time : ℤ) (sign : Bool) : Bool :=
  if time % 2 = 0 then sign else !sign

theorem eventBit_ne {time : ℤ} {a b : Bool} (hab : a ≠ b) :
    eventBit time a ≠ eventBit time b := by
  cases a <;> cases b <;> simp_all [eventBit]

theorem eventBit_eq_of_congruent {q : ℤ} (hq : q = 3 ∨ q = 5 ∨ q = 7)
    {a b : ℤ} {sa sb : Bool} (hmod : a % q = b % q)
    (hspan : |b - a| ≤ q) (hsame : sa = sb → |b - a| ≤ q - 2)
    (hdifferent : sa ≠ sb → 2 ≤ |b - a|) : eventBit a sa = eventBit b sb := by
  rcases le_total a b with hab | hba
  all_goals first
    | simp only [abs_of_nonneg (sub_nonneg.mpr hab)] at hspan hsame hdifferent
    | simp only [abs_of_nonpos (sub_nonpos.mpr hba)] at hspan hsame hdifferent
  all_goals rcases hq with rfl | rfl | rfl <;>
    cases sa <;> cases sb <;> simp_all only [ne_eq, Bool.false_eq_true, Bool.true_eq_false,
      not_true_eq_false, not_false_eq_true, false_implies, forall_const,
      eventBit, Bool.not_true, Bool.not_false]
    <;> split_ifs <;> first | decide | omega

theorem eventBit_ne_of_adjacent {q : ℤ} (hq : q = 3 ∨ q = 5 ∨ q = 7)
    {a b : ℤ} {sa sb : Bool} (hadj : (a % q + 1) % q = b % q)
    (hspan : |b - a| ≤ q) (hsame : sa = sb → |b - a| ≤ q - 2)
    (hdifferent : sa ≠ sb → 2 ≤ |b - a|) : eventBit a sa ≠ eventBit b sb := by
  rcases le_total a b with hab | hba
  all_goals first
    | simp only [abs_of_nonneg (sub_nonneg.mpr hab)] at hspan hsame hdifferent
    | simp only [abs_of_nonpos (sub_nonpos.mpr hba)] at hspan hsame hdifferent
  all_goals rcases hq with rfl | rfl | rfl <;>
    cases sa <;> cases sb <;> simp_all only [ne_eq, Bool.false_eq_true, Bool.true_eq_false,
      not_true_eq_false, not_false_eq_true, false_implies, forall_const,
      eventBit, Bool.not_true, Bool.not_false]
    <;> split_ifs <;> first | decide | omega

def Adjacent (q : ℕ) (a b : Fin q) : Prop := (a.val + 1) % q = b.val

def PartialValid {q : ℕ} (row : Fin q → Option Bool) : Prop :=
  ∀ a b, Adjacent q a b → ∀ sign, row a = some sign → row b ≠ some sign

def smallCode {q : ℕ} (code coordinate : Fin q) : Bool :=
  decide (coordinate = code ∨ (q = 5 ∧ coordinate.val = (code.val + 2) % q))

instance {q : ℕ} (row : Fin q → Option Bool) : Decidable (PartialValid row) :=
  inferInstanceAs (Decidable (∀ a b, (a.val + 1) % q = b.val →
    ∀ sign, row a = some sign → row b ≠ some sign))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem completion_three : ∀ row : Fin 3 → Option Bool, PartialValid row →
    ∃ code : Fin 3, ∀ coordinate sign,
      row coordinate = some sign → smallCode code coordinate = sign := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem completion_five : ∀ row : Fin 5 → Option Bool, PartialValid row →
    ∃ code : Fin 5, ∀ coordinate sign,
      row coordinate = some sign → smallCode code coordinate = sign := by
  decide

theorem smallCode_completion {q : ℕ} (hq : q = 3 ∨ q = 5)
    (row : Fin q → Option Bool) (hvalid : PartialValid row) :
    ∃ code : Fin q, ∀ coordinate sign,
      row coordinate = some sign → smallCode code coordinate = sign := by
  rcases hq with rfl | rfl
  · exact completion_three row hvalid
  · exact completion_five row hvalid

theorem card_le_small_period_of_rows {V : Type*} [Fintype V]
    {q : ℕ} (hq : q = 3 ∨ q = 5) (row : V → Fin q → Option Bool)
    (hvalid : ∀ v, PartialValid (row v))
    (hsep : ∀ v w, v ≠ w → ∃ c a b, row v c = some a ∧ row w c = some b ∧ a ≠ b) :
    Fintype.card V ≤ q := by
  classical
  choose code hcode using fun v ↦ smallCode_completion hq (row v) (hvalid v)
  have hinjective : Function.Injective code := by
    intro v w hequal
    by_contra hvw
    obtain ⟨c, a, b, ha, hb, hab⟩ := hsep v w hvw
    have hv := hcode v c a ha
    have hw := hcode w c b hb
    have hsameCode := congrArg (fun k ↦ smallCode k c) hequal
    rw [hv, hw] at hsameCode
    exact hab hsameCode
  simpa using Fintype.card_le_of_injective code hinjective

/-- Every event is retained in a consistent, pairwise separated partial cycle colouring. -/
theorem exists_partial_rows_of_events
    {V E : Type*} (q : ℕ) (hq : q = 3 ∨ q = 5 ∨ q = 7)
    (time : E → ℤ) (incident : V → E → Prop) (sign : V → E → Bool)
    (hspan : ∀ v e f, incident v e → incident v f → |time f - time e| ≤ q)
    (hsame : ∀ v e f, incident v e → incident v f → sign v e = sign v f →
      |time f - time e| ≤ (q : ℤ) - 2)
    (hdifferent : ∀ v e f, incident v e → incident v f → sign v e ≠ sign v f →
      2 ≤ |time f - time e|)
    (hpair : ∀ v w, v ≠ w → ∃ e, incident v e ∧ incident w e ∧ sign v e ≠ sign w e) :
    ∃ row : V → Fin q → Option Bool, (∀ v, PartialValid (row v)) ∧
      ∀ v w, v ≠ w → ∃ c a b, row v c = some a ∧ row w c = some b ∧ a ≠ b := by
  classical
  have hqint : (q : ℤ) = 3 ∨ (q : ℤ) = 5 ∨ (q : ℤ) = 7 := by omega
  have hqpos : (0 : ℤ) < q := by omega
  let band (e : E) : Fin q := ⟨(time e % q).toNat, by
    have hlo := Int.emod_nonneg (time e) (ne_of_gt hqpos)
    have hhi := Int.emod_lt_of_pos (time e) hqpos
    omega⟩
  have hphase (e : E) : ((band e).val : ℤ) = time e % q :=
    Int.toNat_of_nonneg (Int.emod_nonneg (time e) (ne_of_gt hqpos))
  have hconsistent (v : V) (e f : E) (he : incident v e) (hf : incident v f)
      (hband : band e = band f) : eventBit (time e) (sign v e) =
        eventBit (time f) (sign v f) := by
    have hmod : time e % q = time f % q := by
      rw [← hphase e, ← hphase f, hband]
    exact eventBit_eq_of_congruent hqint hmod (hspan v e f he hf)
      (hsame v e f he hf) (hdifferent v e f he hf)
  let row (v : V) (c : Fin q) : Option Bool :=
    if h : ∃ e, incident v e ∧ band e = c then
      some (eventBit (time h.choose) (sign v h.choose)) else none
  have hrow_event (v : V) (e : E) (he : incident v e) :
      row v (band e) = some (eventBit (time e) (sign v e)) := by
    have hex : ∃ f, incident v f ∧ band f = band e := ⟨e, he, rfl⟩
    dsimp only [row]
    rw [dite_eq_left hex]
    exact congrArg some (hconsistent v hex.choose e hex.choose_spec.1 he hex.choose_spec.2)
  have hrow_some (v : V) (c : Fin q) (b : Bool) (hrow : row v c = some b) :
      ∃ e, incident v e ∧ band e = c ∧ eventBit (time e) (sign v e) = b := by
    by_cases hex : ∃ e, incident v e ∧ band e = c
    · simp only [row, dite_eq_left hex] at hrow
      exact ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, Option.some.inj hrow⟩
    · simp [row, hex] at hrow
  have hvalid (v : V) : PartialValid (row v) := by
    intro a b hadj bit ha hb
    obtain ⟨e, he, hbe, hse⟩ := hrow_some v a bit ha
    obtain ⟨f, hf, hbf, hsf⟩ := hrow_some v b bit hb
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hadj
    have hmod : (time e % q + 1) % q = time f % q := by
      change (((a.val + 1) % q : ℕ) : ℤ) = b.val at hcast
      push_cast at hcast
      rw [← hbe, ← hbf, hphase e, hphase f] at hcast
      exact hcast
    have hne := eventBit_ne_of_adjacent hqint hmod (hspan v e f he hf)
      (hsame v e f he hf) (hdifferent v e f he hf)
    exact hne (hse.trans hsf.symm)
  refine ⟨row, hvalid, ?_⟩
  intro v w hvw
  obtain ⟨e, he, hw, hsign⟩ := hpair v w hvw
  exact ⟨band e, eventBit (time e) (sign v e), eventBit (time e) (sign w e),
    hrow_event v e he, hrow_event w e hw, eventBit_ne hsign⟩

/-- The three- and five-phase bounds use every incident sign, including the period seam. -/
theorem card_le_small_period_of_events
    {V E : Type*} [Fintype V] (q : ℕ) (hq : q = 3 ∨ q = 5)
    (time : E → ℤ) (incident : V → E → Prop) (sign : V → E → Bool)
    (hspan : ∀ v e f, incident v e → incident v f → |time f - time e| ≤ q)
    (hsame : ∀ v e f, incident v e → incident v f → sign v e = sign v f →
      |time f - time e| ≤ (q : ℤ) - 2)
    (hdifferent : ∀ v e f, incident v e → incident v f → sign v e ≠ sign v f →
      2 ≤ |time f - time e|)
    (hpair : ∀ v w, v ≠ w → ∃ e, incident v e ∧ incident w e ∧ sign v e ≠ sign w e) :
    Fintype.card V ≤ q := by
  classical
  obtain ⟨row, hvalid, hsep⟩ := exists_partial_rows_of_events q (by omega)
    time incident sign hspan hsame hdifferent hpair
  exact card_le_small_period_of_rows hq row hvalid hsep

#print axioms card_le_small_period_of_events

end OddWire
end JSP000404Research
