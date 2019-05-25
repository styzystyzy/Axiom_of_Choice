# Axiom of Choice

The axiom of Choice (AC) is an important axiom in axiomatic set theory and it has a wide range of applications in modern mathematics. In this work, we formalize AC and several of its famous equivalent theorems. These theorems include Tukey's lemma, the Hausdorff maximal principle, the maximal principle, Zermelo's postulate, Zorn's Lemma, and the well-ordering theorem. We prove the equivalence between them in Coq. The work is based on the ``axiomatic set theory'' formal system that we developed.

# Files and Modules

1. Logic_Property.v
  Defines notations shared by all of the other modules.
2. Axiomatic_Set_Theory.v
  Provieds a simplified and modified version of the "axiomatic set theory" formal system.
3. Basic_Definitions.v
  Defines some notations and provides basic properties.
4. Finite_Character.v
  Defines the set of finite character based on the definitions of integers and cardinal numbers.
5. Tukey_Lemma.v
  Proves Tukey's lemma according to AC.
6. Hausdorff_Maximal_Principle.v
  Proves the Hausdorff maximal principle.
7. Maximal_Principle.v
  Proves the maximal principle.
8. Zermelo_Postulate.v
  Proves Zermelo's postulate according to the maximal principle.
9. Zorn_Lemma.v
  Proves Zorn's lemma on the basis of the maximal principle.
10. Wellordering_Theorem.v
  Proves the well-ordering theorem.
11. Zermelo_Proof_AC.v
  Proves AC based on Zermelo's postulate.
12. WO_Proof_AC.v
  Proves AC based on the well-ordering theorem.

# Author

Tianyu Sun. stycyj@bupt.edu.cn
