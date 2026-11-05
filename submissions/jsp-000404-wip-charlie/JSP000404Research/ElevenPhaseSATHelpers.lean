import JSP000404Research.ElevenPhaseCores
import Mathlib.Tactic.Sat.FromLRAT

/-! Elementary semantic lemmas for the finite LRAT encoding. -/

namespace JSP000404Research.ElevenPhase

open scoped BigOperators

theorem satisfies_pos_member (v : Sat.Valuation) (c : Sat.Clause) (n : ℕ)
    (hm : Sat.Literal.pos n ∈ (show List Sat.Literal from c)) (hv : v n) : v.satisfies c := by
  induction c with
  | nil => cases hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst a
      exact fun hn ↦ (hn hv).elim
    · exact fun _ ↦ ih hm

theorem satisfies_neg_member (v : Sat.Valuation) (c : Sat.Clause) (n : ℕ)
    (hm : Sat.Literal.neg n ∈ (show List Sat.Literal from c)) (hv : ¬v n) : v.satisfies c := by
  induction c with
  | nil => cases hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst a
      exact fun hn ↦ (hv hn).elim
    · exact fun _ ↦ ih hm

theorem satisfies_append (v : Sat.Valuation) {a b : Sat.Fmla}
    (ha : v.satisfies_fmla a) (hb : v.satisfies_fmla b) : v.satisfies_fmla (a ++ b) := by
  constructor
  intro clause h
  rcases List.mem_append.mp h with h | h
  · exact ha.1 clause h
  · exact hb.1 clause h

theorem satisfies_mapped_positive (v : Sat.Valuation) (xs : List ℕ)
    (h : ∃ n ∈ xs, v n) : v.satisfies (xs.map Sat.Literal.pos) := by
  obtain ⟨n, hn, hv⟩ := h
  apply satisfies_pos_member v _ n _ hv
  exact List.mem_map.mpr ⟨n, hn, rfl⟩

theorem satisfies_mapped_negative (v : Sat.Valuation) (xs : List ℕ)
    (h : ¬∀ n ∈ xs, v n) : v.satisfies (xs.map Sat.Literal.neg) := by
  classical
  push_neg at h
  obtain ⟨n, hn, hv⟩ := h
  apply satisfies_neg_member v _ n _ hv
  exact List.mem_map.mpr ⟨n, hn, rfl⟩

def prefixCount (input : ℕ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if input i then 1 else 0

theorem prefixCount_succ (input : ℕ → Bool) (n : ℕ) :
    prefixCount input (n + 1) = prefixCount input n + if input n then 1 else 0 := by
  simp only [prefixCount, Finset.sum_range_succ]

end JSP000404Research.ElevenPhase
