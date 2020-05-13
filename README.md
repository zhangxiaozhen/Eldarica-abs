Eldarica-abs
========

Eldarica-abs is a variant of Eldarica and it mainly concentrates on the modification of the exploration of abstraction lattices. Eldarica is a model checker for Horn clauses, Numerical Transition Systems, and software programs. The inputs of Eldarica-abs are the same as Eldarica and they can be read in a variety of formats, including SMT-LIB 2 and Prolog for Horn clauses, and fragments of Scala and C for software programs. These inputs can be analysed using a variant of the Counterexample-Guided Abstraction Refinement (CEGAR) method. Eldarica is fast and includes sophisticated interpolation-based techniques for synthesising new predicates for CEGAR, enabling it to solve a wide range of verification problems. Based on these techniques, Eldarica-abs mainly concentrates on modifying the exploration method of abstraction lattices in Eldarica and takes the cost-guided bidirectional heuristic search strategy.

Eldarica has been developed by Hossein Hojjat and Philipp Ruemmer, with further contributions by Filip Konecny and Pavle Subotic. The modification on the exploration part of abstraction lattice in Eldarica-abs is mainly contributed by Xiaozhen Zhang and Weiqiang Kong.

Documentation
-------------

The compilation and calling of Eldarica-abs are the same as Eldarica. For more information, see https://github.com/uuverifiers/eldarica.  

