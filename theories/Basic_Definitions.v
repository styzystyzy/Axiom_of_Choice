Require Export Axiomatic_Set_Theory.


(** Some necessary and additional definitions for the proof **)

Module BasicDefinition.

(* Choice Function *)
(* For the independence of the formalization of AC and its related theorems,
   we redefine the choice function as below and restate AC in Tukey_Lemma.v.
   The following choice function is more specific and there is no contradiction
   between the two descriptions of AC. *)

Definition Choice_Function ε X : Prop :=
  Function ε /\ ran(ε) ⊂ X /\ dom(ε) = pow(X)~[Φ] /\
  (forall A, A ∈ dom(ε) -> ε[A] ∈ A).

Hint Unfold Choice_Function : Axiom_of_Choice.


(* Maximial Member : F is a maximal member of f iff no member of f is properly contained in F. *)

Definition MaxMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ F ⊊ x).

Hint Unfold MaxMember : Axiom_of_Choice.


(* Minimial Member : Similarly F is a minimal member of f iff no member of f is properly contained in F. *)

Definition MinMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ x ⊊ F).

Hint Unfold MaxMember MinMember : Axiom_of_Choice.


(* Orders of this paper are all limited to a set, the definition of well orders
  in Axiomatic_Set_Theory.v is more general and doesn't have this limitation. *)
(* In addition, we add partial orders, total orders. *)

(* Partial Order, Partially Ordered Set *)

Definition Reflexivity le X := forall a, a∈X -> Rrelation a le a.

Definition Antisymmetry le X :=
  forall x y, x∈X /\ y∈X -> (Rrelation x le y /\ Rrelation y le x -> x = y).

Definition Transitivity r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x) /\
  (Rrelation u r v /\ Rrelation v r w) -> Rrelation u r w.

Definition PartialOrder le X : Prop :=
  Ensemble X /\ (Relation le /\ le ⊂ X × X) /\
  Reflexivity le X /\ Antisymmetry le X /\ Transitivity le X.

Definition PartialOrderSet X le := PartialOrder le X.

Hint Unfold PartialOrder PartialOrderSet: Axiom_of_Choice.


(* Upper Bound, Lower Bound *)

Definition BoundU x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation a le x).

Definition BoundL x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation x le a).

Hint Unfold BoundU BoundL : Axiom_of_Choice.


(* Maximal Element : We say that x∈X is a maximal element if *)

Definition MaxElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation x le y /\ x ≠ y)).

(* Minimal Element *)

Definition MinElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation y le x /\ x ≠ y)).

Hint Unfold MaxElement MinElement : Axiom_of_Choice.


(* Total Order, Totally Ordered Set *)

Definition TotalOrder le X := 
  PartialOrder le X /\ (forall x y, x∈X /\ y∈X ->
  (x ≠ y -> Rrelation x le y \/ Rrelation y le x)).

Definition TotalOrderSet X le := TotalOrder le X.

Hint Unfold TotalOrder TotalOrderSet : Axiom_of_Choice.


(* Chain *)

Definition Chain A X le : Prop :=
  PartialOrder le X -> (A ⊂ X /\ A ≠ Φ) /\ TotalOrder (le ∩ (A × A)) A.

Hint Unfold Chain : Axiom_of_Choice.


(* Well Order Set *)

Definition WellOrder le X :=
  TotalOrder le X /\ (forall A, A⊂X /\ A≠Φ -> exists z, MinElement z A le).

Definition WellOrderSet X le := WellOrder le X.

Hint Unfold WellOrderSet : Axiom_of_Choice.


(* Initial_Segment *)

Definition Initial_Segment Y X le := Y ⊂ X /\ WellOrder le X /\
  (forall u v, (u ∈ X /\ v ∈ Y /\ Rrelation u le v ) -> u ∈ Y).

Hint Unfold WellOrderSet : Axiom_of_Choice.


End BasicDefinition.

Export BasicDefinition.

