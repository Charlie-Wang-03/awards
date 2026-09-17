# Sources and provenance

The submitted proof modules were developed with OpenAI Codex assistance for
this project. Mathematical facts about permutations, rotation systems, bridges,
and Euler characteristic are standard; no mathematical discovery priority is
claimed. All executable imports are supplied modules or pinned Mathlib modules.

The motivation is JSP-000512 / Erdős #631 and Thomassen's known theorem:
Carsten Thomassen, *Every Planar Graph Is 5-Choosable*, 1994,
[DOI 10.1006/jctb.1994.1062](https://doi.org/10.1006/jctb.1994.1062).
The upper bound is proved here for the explicit finite genus-zero rotation
model. The general upper-bound correspondence with geometric planarity remains
unproved; the explicit geometric lower-bound witness described below is proved.

Prior sources inspected during the broader investigation:

- [plby/lean-proofs, Erdos631.lean at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos631.lean).
  Its recursive plane-expression certificate motivated investigation of the
  missing representation bridge. Its coloring code is not included or imported.
- [Minimum-balanced-bipartitions-of-planar-graphs at 034a1f54467fc2e7d588f85ea8ffa6546b6df4b0](https://github.com/abhishan82/Minimum-balanced-bipartitions-of-planar-graphs/tree/034a1f54467fc2e7d588f85ea8ffa6546b6df4b0).
  README and combinatorial-map source were inspected. No source or unproved
  assumptions from that repository are imported here.
- [zonal-graphs](https://github.com/walidelkersh/zonal-graphs): README inspected
  for the distinction between face-data interfaces and rotation systems;
  not built or imported.
- Wood and Linusson, *Thomassen's Choosability Argument Revisited*, 2010,
  [author PDF](https://users.monash.edu/~davidwo/papers/Thomassen.pdf).
  Inspected as an alternative minor-based route; not formalized or imported.

No completeness claim is made about the search for other formalizations.
Local NetworkX experiments and finite recursive coloring certificates from
an earlier feasibility probe are excluded from this submission. They neither
establish the general results above nor form part of this proof's trust base.

The sharpness modules implement the 86-vertex intermediate graph H in Section 2
of Shai Gutner, *The complexity of planar graph choosability*,
[arXiv:0802.2668](https://arxiv.org/html/0802.2668). The paper subsequently merges
vertices to obtain 75; that minimization is not used. The previously inspected
Erdos631 code uses the same published block construction. The present modules
specify the graph directly and prove noncrossing real line segments from integer
coordinates; that external code and its recursive planarity definition are not
imported. Attribution is to the published construction, not a new counterexample.

NetworkX 3.4.2 proposed a planar layout, followed by deterministic small integer
perturbations after scaling. The supplied `GutnerCoordinates.lean` contains all
coordinates and kernel-checked finite sign tests. Coordinate generation is not a
trusted step or a prerequisite for reproducing the Lean proof. The Python
rotation/Euler checks from exploration are not asserted as Lean theorems.
