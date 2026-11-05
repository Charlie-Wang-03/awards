"""Generate the semantic wrapper for the explicit nine-phase Boolean proof."""

from pathlib import Path
import generate_nine_phase_boolean_certificate as certificate
from check_nine_phase_capacity import indexed_catalog, SLOTS


rows = indexed_catalog()
slots = [j for j, word in enumerate(SLOTS) if any(
    (p | n).bit_count() == 6 and word & p == p and word & n == 0 for p, n in rows)]
header = '''import JSP000404Research.NinePhaseData
import JSP000404Research.NinePhaseBooleanCertificate

/-!
# Semantic interpretation of the nine-phase matching certificate

Full coverage by separated catalog rows forces one of two specified five-row cores.
Each numerical premise of the generated Boolean proof is discharged against the
explicit row and slot definitions by ordinary kernel reduction.
-/

namespace JSP000404Research.NinePhase

private theorem positive_clause (selected : Fin 78 → Bool) (slot : Fin 42)
    (indices : List (Fin 78)) (hindices : ∀ i, covers i slot = true → i ∈ indices)
    (hcover : ∀ slot, ∃ i, covers i slot = true ∧ selected i = true) :
    indices.any selected = true := by
  obtain ⟨i, hic, his⟩ := hcover slot
  exact List.any_eq_true.mpr ⟨i, hindices i hic, his⟩

private theorem negative_clause (selected : Fin 78 → Bool) (i j : Fin 78)
    (hne : i ≠ j) (hbad : ¬Separated i j)
    (hsep : ∀ i j, i ≠ j → selected i = true → selected j = true → Separated i j) :
    selected i = false ∨ selected j = false := by
  cases hi : selected i with
  | false => exact Or.inl rfl
  | true =>
    cases hj : selected j with
    | false => exact Or.inr rfl
    | true => exact (hbad (hsep i j hne hi hj)).elim

private theorem five_clause (a b c d e : Bool)
    (h : ¬(a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true)) :
    a = false ∨ b = false ∨ c = false ∨ d = false ∨ e = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

theorem no_full_cover_avoiding_cores (selected : Fin 78 → Bool)
    (hcover : ∀ slot, ∃ i, covers i slot = true ∧ selected i = true)
    (hsep : ∀ i j, i ≠ j → selected i = true → selected j = true → Separated i j)
    (hcore : ¬(selected 25 = true ∧ selected 54 = true ∧ selected 70 = true ∧
      selected 11 = true ∧ selected 44 = true))
    (hflip : ¬(selected 24 = true ∧ selected 55 = true ∧ selected 71 = true ∧
      selected 10 = true ∧ selected 45 = true)) : False := by
  apply BooleanCertificate.clauses_impossible
'''
lines = [header.rstrip()]
for start in range(0, len(certificate.active), 6):
    lines.append('    ' + ' '.join(f'(selected {i})' for i in certificate.active[start:start + 6]))
for number in sorted(certificate.used):
    clause = certificate.clauses[number]
    if clause[0][1]:
        assert number < len(slots)
        indices = '[' + ', '.join(str(i) for i, _ in clause) + ']'
        lines += ['  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,',
                  '      Bool.false_eq_true, or_false] using',
                  f'      positive_clause selected {slots[number]} {indices} (by decide) hcover']
    elif len(clause) == 2:
        i, j = [entry[0] for entry in clause]
        lines.append(f'  · exact negative_clause selected {i} {j} (by decide) (by decide) hsep')
    else:
        hypothesis = 'hcore' if number == len(certificate.clauses) - 2 else 'hflip'
        lines.append('  · exact five_clause ' + ' '.join(f'(selected {i})' for i, _ in clause))
        lines.append('      ' + hypothesis)
lines += ['', '#print axioms no_full_cover_avoiding_cores', '',
          'end JSP000404Research.NinePhase', '']
text = '\n'.join(lines)
assert all(len(line) <= 100 for line in text.splitlines())
Path('JSP000404Research/NinePhaseMatching.lean').write_text(text, encoding='utf-8', newline='\n')
print('Generated nine-phase semantic matching theorem')
