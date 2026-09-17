# Sources and provenance

The submitted proof modules were developed with OpenAI Codex assistance for
this project. Mathematical facts about permutations, rotation systems, bridges,
and Euler characteristic are standard; no mathematical discovery priority is
claimed. All executable imports are supplied modules or pinned Mathlib modules.

The motivation is JSP-000512 / Erdős #631 and Thomassen's known theorem:
Carsten Thomassen, *Every Planar Graph Is 5-Choosable*, 1994,
[DOI 10.1006/jctb.1994.1062](https://doi.org/10.1006/jctb.1994.1062).
The upper bound is proved here for the explicit finite genus-zero rotation
model. Its correspondence with geometric planarity and its sharpness remain
unproved.

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
