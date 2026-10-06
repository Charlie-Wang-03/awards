import JSP000404Research.WholeCubeQTPairCore
import Mathlib.Tactic

/-!
# Same-palette translated intersection upgrades to whole-cube equality

Completion cubes are Boolean subcubes obtained by fixing all retained-active
coordinates.  Therefore two such cubes with the same active coordinate set are
either disjoint or equal.

Likewise, for an active coordinate c, the translated cube T_c(u) fixes exactly
the same active set as Q_u, with only the c-bit toggled.  If another completion
cube Q_v has the same active palette and meets T_c(u) at one word, that witness
identifies all fixed bits.  Hence the entire translated cube equals Q_v.

This is the local amplification needed to turn a one-word T/Q augmentation
into a new WholeCubeQTPair.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedCompletionWords_eq_of_same_palette_nonempty_inter
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hactive :
      retainedActive C u = retainedActive C v)
    (hinter :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).Nonempty) :
    retainedCompletionWords C u =
      retainedCompletionWords C v := by
  obtain ⟨base,hbase⟩ := hinter
  have hparts := Finset.mem_inter.mp hbase
  have hbaseU := hparts.1
  have hbaseV := hparts.2
  ext word
  constructor
  · intro hwordU
    apply (mem_retainedCompletionWords C v word).2
    intro d hdV
    have hdU : d ∈ retainedActive C u := by
      rw [hactive]
      exact hdV
    have hu :=
      (mem_retainedCompletionWords C u word).1 hwordU d hdU
    have hbaseU' :=
      (mem_retainedCompletionWords C u base).1 hbaseU d hdU
    have hbaseV' :=
      (mem_retainedCompletionWords C v base).1 hbaseV d hdV
    exact hu.trans (hbaseU'.symm.trans hbaseV')
  · intro hwordV
    apply (mem_retainedCompletionWords C u word).2
    intro d hdU
    have hdV : d ∈ retainedActive C v := by
      rw [← hactive]
      exact hdU
    have hv :=
      (mem_retainedCompletionWords C v word).1 hwordV d hdV
    have hbaseV' :=
      (mem_retainedCompletionWords C v base).1 hbaseV d hdV
    have hbaseU' :=
      (mem_retainedCompletionWords C u base).1 hbaseU d hdU
    exact hv.trans (hbaseV'.symm.trans hbaseU')

theorem translatedCompletionWords_eq_completion_of_same_palette_nonempty_inter
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    (hactive :
      retainedActive C u = retainedActive C v)
    (hcU : c ∈ retainedActive C u)
    (hinter :
      (translatedCompletionWords C u c ∩
        retainedCompletionWords C v).Nonempty) :
    translatedCompletionWords C u c =
      retainedCompletionWords C v := by
  obtain ⟨base,hbase⟩ := hinter
  have hparts := Finset.mem_inter.mp hbase
  have hbaseT := hparts.1
  have hbaseV := hparts.2
  have hcV : c ∈ retainedActive C v := by
    rw [← hactive]
    exact hcU
  ext word
  constructor
  · intro hwordT
    have hwordSrc :
        flipBoolWordAt word c ∈ retainedCompletionWords C u :=
      (mem_translatedCompletionWords C u c word).1 hwordT
    have hbaseSrc :
        flipBoolWordAt base c ∈ retainedCompletionWords C u :=
      (mem_translatedCompletionWords C u c base).1 hbaseT
    apply (mem_retainedCompletionWords C v word).2
    intro d hdV
    have hdU : d ∈ retainedActive C u := by
      rw [hactive]
      exact hdV
    by_cases hdc : d = c
    · subst d
      have hw :=
        (mem_retainedCompletionWords C u
          (flipBoolWordAt word c)).1 hwordSrc c hcU
      have hbU :=
        (mem_retainedCompletionWords C u
          (flipBoolWordAt base c)).1 hbaseSrc c hcU
      have hbV :=
        (mem_retainedCompletionWords C v base).1 hbaseV c hcV
      rw [flipBoolWordAt_at] at hw hbU
      cases hwordc : word c <;>
        cases hbasec : base c <;>
        simp_all
    · have hw :=
        (mem_retainedCompletionWords C u
          (flipBoolWordAt word c)).1 hwordSrc d hdU
      have hbU :=
        (mem_retainedCompletionWords C u
          (flipBoolWordAt base c)).1 hbaseSrc d hdU
      have hbV :=
        (mem_retainedCompletionWords C v base).1 hbaseV d hdV
      rw [flipBoolWordAt_off word hdc,
          flipBoolWordAt_off base hdc] at hw hbU
      exact hw.trans (hbU.symm.trans hbV)
  · intro hwordV
    apply (mem_translatedCompletionWords C u c word).2
    apply (mem_retainedCompletionWords C u
      (flipBoolWordAt word c)).2
    intro d hdU
    have hdV : d ∈ retainedActive C v := by
      rw [← hactive]
      exact hdU
    by_cases hdc : d = c
    · subst d
      have hwV :=
        (mem_retainedCompletionWords C v word).1 hwordV c hcV
      have hbV :=
        (mem_retainedCompletionWords C v base).1 hbaseV c hcV
      have hbSrc :=
        (mem_retainedCompletionWords C u
          (flipBoolWordAt base c)).1 hbaseSrc c hcU
      rw [flipBoolWordAt_at] at hbSrc ⊢
      cases hwordc : word c <;>
        cases hbasec : base c <;>
        simp_all
    · have hwV :=
        (mem_retainedCompletionWords C v word).1 hwordV d hdV
      have hbV :=
        (mem_retainedCompletionWords C v base).1 hbaseV d hdV
      have hbSrc :=
        (mem_retainedCompletionWords C u
          (flipBoolWordAt base c)).1 hbaseSrc d hdU
      rw [flipBoolWordAt_off base hdc] at hbSrc
      rw [flipBoolWordAt_off word hdc]
      exact hwV.trans (hbV.symm.trans hbSrc)

theorem wholeCubeQTPair_of_same_palette_translated_intersection
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c : Fin n}
    (hactive :
      retainedActive C v = retainedActive C s)
    (hcV : c ∈ retainedActive C v)
    (hinter :
      (translatedCompletionWords C v c ∩
        retainedCompletionWords C s).Nonempty) :
    WholeCubeQTPair C s v c := by
  refine ⟨hactive,?_⟩
  exact translatedCompletionWords_eq_completion_of_same_palette_nonempty_inter
    C hactive hcV hinter

#print axioms retainedCompletionWords_eq_of_same_palette_nonempty_inter
#print axioms translatedCompletionWords_eq_completion_of_same_palette_nonempty_inter
#print axioms wholeCubeQTPair_of_same_palette_translated_intersection

end OrderedEdgeColoring
end JSP000404Research
