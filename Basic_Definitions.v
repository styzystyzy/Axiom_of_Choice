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
    intro A; intros; destruct H4; unfold Finite in H5.
    generalize (classic (φ = Φ)); intros; destruct H6.
    + rewrite H6 in *; clear H6; rewrite Theorem24' in H4.
      add (Φ ⊂ A) H4; try apply (Theorem26 A); apply Theorem27 in H4.
      rewrite H4 in *; clear H4; apply Property_NotEmpty in H0.
      destruct H0; generalize (Theorem26 x); intros.
      apply H1 with (z:= Φ) in H0; auto.
    + assert (Ensemble A).
      { apply Theorem33 in H2; auto; apply AxiomVI in H2.
        apply Theorem33 in H4; auto. }
      double H7; apply Theorem153 in H8; apply Theorem146 in H8.
      assert (forall D, D ∈ \{ λ D, D ≈ P [A] /\ D ⊂ ∪ φ \} ->
              exists B, B ∈ φ /\ D ⊂ B).
      { apply Mathematical_Induction with (n:= P[A]); auto; intros.
        - apply AxiomII in H9; destruct H9, H10.
          generalize (classic (D = Φ)); intros; destruct H12.
          + rewrite H12 in *; apply Property_NotEmpty in H6; destruct H6.
            exists x; split; auto; apply Theorem26.
          + unfold Equivalent in H10; destruct H10 as [g H10], H10, H13, H10.
            apply Property_NotEmpty in H12; destruct H12; rewrite <- H13 in H12.
            apply Property_Value in H12; auto; apply Property_ran in H12.
            rewrite H14 in H12; generalize (Theorem16 g[x]); contradiction.
        - clear H H0 H2 H4 H5 H6 H7 H8 A.
          destruct H9; apply AxiomII in H10; destruct H10, H4.
          unfold Equivalent in H4; destruct H4 as [g H4], H4, H4, H6.
          assert (k ∈ (PlusOne k)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply AxiomII; split; Ens. }
          rewrite <- H8 in H9; unfold Range in H9; apply AxiomII in H9.
          destruct H9, H10; double H10; apply Property_dom in H11.
          rewrite H6 in H11.
          assert ((D ~ [x]) ∈ \{ λ D0, D0 ≈ k /\ D0 ⊂ ∪ φ \}).
          { apply AxiomII; repeat split.
            - unfold Setminus; apply Theorem33 with (x:= D); auto.
              unfold Included; intros; apply Theorem4' in H12; apply H12.
            - clear H0 H1; unfold Equivalent; exists (g | (D ~ [x])).
              repeat split; unfold Relation; intros.
              + unfold Restriction in H0; apply Theorem4' in H0.
                destruct H0; PP H1 a b; Ens.
              + destruct H0; apply Theorem4' in H0; apply Theorem4' in H1.
                destruct H0 as [H0 _], H1 as [H1 _].
                apply H4 with (x:= x0); auto.
              + PP H0 a b; Ens.
              + destruct H0; apply AxiomII_P in H0; apply AxiomII_P in H1.
                destruct H0, H1; apply Theorem4' in H12; apply Theorem4' in H13.
                destruct H12 as [H12 _], H13 as [H13 _]; apply H7 with (x:=x0).
                split; apply AxiomII_P; Ens.
              + apply AxiomI; split; intros.
                * unfold Domain in H0; apply AxiomII in H0; destruct H0, H1.
                  unfold Restriction in H1; apply Theorem4' in H1; destruct H1.
                  unfold Cartesian in H12; apply AxiomII_P in H12; apply H12.
                * unfold Domain; apply AxiomII; split; Ens.
                  double H0; unfold Setminus in H1; apply Theorem4' in H1.
                  destruct H1 as [H1 _]; rewrite <- H6 in H1.
                  apply Property_Value in H1; auto; exists g[z].
                  unfold Restriction; apply Theorem4'; split; auto.
                  unfold Cartesian; apply AxiomII_P; repeat split; Ens.
                  AssE [z,g[z]]; apply Theorem49 in H12; destruct H12.
                  apply Theorem19; auto.
              + apply AxiomI; split; intros.
                * unfold Range in H0; apply AxiomII in H0; destruct H0, H1.
                  unfold Restriction in H1; apply Theorem4' in H1.
                  destruct H1; unfold Cartesian in H12; apply AxiomII_P in H12.
                  destruct H12, H13 as [H13 _]; unfold Setminus in H13.
                  apply Theorem4' in H13; destruct H13; double H1.
                  apply Property_ran in H15; rewrite H8 in H15.
                  apply Theorem4 in H15; destruct H15; auto; clear H0.
                  unfold Singleton in H15; apply AxiomII in H15; destruct H15.
                  rewrite H15 in H1; try apply Theorem19; Ens; clear H0 H12 H15.
                  assert ([k,x] ∈ g⁻¹ /\ [k,x0] ∈ g⁻¹).
                  { split; apply AxiomII_P; split; try apply Theorem49; Ens. }
                  apply H7 in H0; rewrite <- H0 in H14; apply AxiomII in H14.
                  destruct H14, H14; apply AxiomII; auto.
                * unfold Range; apply AxiomII; split; Ens.
                  assert (z ∈ ran(g)). { rewrite H8; apply Theorem4; tauto. }
                  apply AxiomII in H1; destruct H1, H12; exists x0.
                  unfold Restriction; apply Theorem4'; split; auto.
                  unfold Cartesian; apply AxiomII_P; split; Ens.
                  split; try apply Theorem19; auto; unfold Setminus.
                  double H12; apply Property_dom in H13; rewrite H6 in H13.
                  apply Theorem4'; split; auto; unfold Complement.
                  apply AxiomII; split; Ens; intro; apply AxiomII in H14.
                  destruct H14; rewrite H15 in H12; try apply Theorem19; Ens.
                  add ([x, z] ∈ g) H10; apply H4 in H10; rewrite H10 in H0.
                  generalize (Theorem101 z); intros; contradiction.
            - unfold Included, Setminus; intros; apply Theorem4' in H12.
              destruct H12; apply H5 in H12; auto. }
          apply H0 in H12; clear H0; destruct H12 as [B H12]; apply H5 in H11.
          clear H4 H6 H7 H8 H9 H10; apply AxiomII in H11; destruct H11.
          destruct H4 as [C H4], H4, H12; assert (B ∈ φ /\ C ∈ φ); auto.
          unfold Nest in H3; apply H3 in H9; destruct H9.
          + add (B ⊂ C) H8; apply Theorem28 in H8; clear H9.
            exists C; split; auto; unfold Included; intros.
            generalize (classic (z = x)); intros; destruct H10.
            * rewrite H10; auto.
            * apply H8; unfold Setminus; apply Theorem4'; split; auto.
              unfold Complement; apply AxiomII; split; Ens; intro.
              destruct H10; apply AxiomII in H11; apply H11.
              apply Theorem19; auto.
          + apply H9 in H4; clear H9; exists B; split; auto; unfold Included.
            intros; generalize (classic (z = x)); intros; destruct H10.
            * rewrite H10; auto.
            * apply H8; unfold Setminus; apply Theorem4'; split; auto.
              unfold Complement; apply AxiomII; split; Ens; intro.
              destruct H10; apply AxiomII in H11; apply H11.
              apply Theorem19; auto. }
    assert (A ∈ \{ λ D0, D0 ≈ P [A] /\ D0 ⊂ ∪ φ \}).
    { apply AxiomII; repeat split; auto. }
    apply H9 in H10; clear H9; destruct H10 as [B H10], H10.
    apply H2 in H9; apply H1 with (z:= A) in H9; auto.
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



