Require Export Kelley_Set_Theory.


(** Some necessary and additional definitions for the proof **)

Module BasicDefinition.

(* Nest *)

Definition Nest f : Prop := forall A B, A∈f /\ B∈f -> A⊂B \/ B⊂A.

Hint Unfold Nest : Axiom_of_Chioce.


(* Finite Characteristic Set *)

Definition FiniteSet f : Prop :=
  Ensemble f /\ (forall F, F∈f -> (forall z, z ⊂ F /\ Finite z -> z∈f))
  /\ (forall F, Ensemble F /\ (forall z, z ⊂ F /\ Finite z -> z∈f) -> F∈f).

Hint Unfold FiniteSet : Axiom_of_Chioce.


(* Property of Finite Characteristic Set *)

Hypothesis HPF_def : forall A φ, A ⊂ ∪ φ -> Finite A ->
  exists C0 C1 C2, (C0∈φ /\ C1∈φ /\ C2∈φ) /\ A ⊂ (C0 ∪ C1 ∪ C2).

Proposition Property_FinSet : forall f: Class,
  FiniteSet f /\ f ≠ Φ -> (forall A B, A ∈ f /\ B ⊂ A -> B ∈ f)
  /\ (forall φ, φ ⊂ f /\ Nest φ -> (∪φ) ∈ f).
Proof.
  intros; destruct H.
  unfold FiniteSet in H; destruct H; split; intros.
  - destruct H2; apply H1; intros; split.
    + apply Theorem33 in H3; Ens.
    + intros; destruct H4; apply H1 with (z:=z) in H2; auto.
      split; try (apply Theorem28 with (y:=B); split); auto.
  - destruct H2; apply H1.
    split; try (apply AxiomVI; apply Theorem33 in H2); auto.
    intro A; intros; destruct H4.
    unfold Nest in H3; apply HPF_def in H4; auto.
    destruct H4 as [C0 H4]; destruct H4 as [C1 H4].
    destruct H4 as [C2 H4]; destruct H4, H4, H7.
    assert (C0 ∈ φ /\ C1 ∈ φ). { split; auto. }
    assert (C1 ∈ φ /\ C2 ∈ φ). { split; auto. }
    assert (C0 ∈ φ /\ C2 ∈ φ). { split; auto. }
    apply H3 in H10; destruct H10.
    + apply Theorem29 in H10; rewrite H10 in H6.
      apply H3 in H11; destruct H11.
      * apply Theorem29 in H11; rewrite H11 in H6.
        unfold Included in H2; apply H2 in H8.
        apply H1 with (z:=A) in H8; auto.
      * apply Theorem29 in H11; rewrite Theorem6 in H11.
        rewrite H11 in H6; unfold Included in H2; apply H2 in H4.
        apply H1 with (z:=A) in H4; auto.
    + apply Theorem29 in H10; rewrite Theorem6 in H10.
      rewrite H10 in H6; apply H3 in H9; destruct H9.
      * apply Theorem29 in H9; rewrite H9 in H6.
        unfold Included in H2; apply H2 in H7.
        apply H1 with (z:=A) in H7; auto.
      * apply Theorem29 in H9; rewrite Theorem6 in H9.
        rewrite H9 in H6; unfold Included in H2; apply H2 in H4.
        apply H1 with (z:=A) in H4; auto.
Qed.


(* Maximial Member : F is a maximal member of f iff no member of f is properly contained in F. [K55] *)

Definition MaxMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ F ⊊ x).

Hint Unfold MaxMember : Axiom_of_Choice.


(* Minimial Member : Similarly F is a minimal member of f iff no member of f is properly contained in F. [K55] *)

Definition MinMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ x ⊊ F).

Hint Unfold MaxMember MinMember : Axiom_of_Choice.


(* Choice Function *)

Definition Choice_Function ε X : Prop :=
  Function ε /\ ran(ε) ⊂ X /\ dom(ε) = pow(X)~[Φ] /\ 
  (forall A, A ∈ dom(ε) -> ε[A] ∈ A).

Hint Unfold Choice_Function : Axiom_of_Choice.


(** Order **)

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

Hint Unfold PartialOrder PartialOrderSet: Axiom_of_Chioce.


(* Upper Bound, Lower Bound *)

Definition BoundU x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation a le x).

Definition BoundD x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation x le a).

Hint Unfold BoundU BoundD : Axiom_of_Chioce.


(* Maximal Element : We say that x∈X is a maximal element if *)

Definition MaxElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation x le y /\ x ≠ y)).

(* Minimal Element *)

Definition MinElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation y le x /\ x ≠ y)).

Hint Unfold MaxElement MinElement : Axiom_of_Chioce.


(* Total Order, Totally Ordered Set *)

Definition TotalOrder le X := 
  PartialOrder le X /\ (forall x y, x∈X /\ y∈X ->
  (x ≠ y -> Rrelation x le y \/ Rrelation y le x)).

Definition TotalOrderSet X le := TotalOrder le X.

Hint Unfold TotalOrder TotalOrderSet : Axiom_of_Chioce.


(* Chain *)

Definition Chain A X le : Prop :=
  PartialOrder le X -> (A ⊂ X /\ A ≠ Φ) /\ TotalOrder (le ∩ (A × A)) A.

Hint Unfold Chain : Axiom_of_Chioce.


(* Well Order Set *)

Definition WellOrder le X :=
  TotalOrder le X /\ (forall A, A⊂X /\ A≠Φ -> exists z, MinElement z A le).

Definition WellOrderSet X le := WellOrder le X.

Hint Unfold WellOrderSet : Axiom_of_Chioce.


(* Initial_Segment *)

Definition Initial_Segment Y X le := Y ⊂ X /\ WellOrder le X /\
  (forall u v, (u ∈ X /\ v ∈ Y /\ Rrelation u le v ) -> u ∈ Y).

Hint Unfold WellOrderSet : Axiom_of_Chioce.


End BasicDefinition.

Export BasicDefinition.



