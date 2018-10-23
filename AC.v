Require Import Kelley_Set_Theory.


(** Some necessary and additional definitions for the proof **)

(* Proper Subset *)

Definition ProperSubset x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperSubset x y) (at level 70).

Lemma Property_ProperSubset : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperSubset; auto.
Qed.

Lemma Property_ProperSubset' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperSubset in H; destruct H.
  generalize (Theorem27 x y); intros.
  apply definition_not with (B:= (x ⊂ y /\ y ⊂ x)) in H0; try tauto.
  apply property_not in H0; destruct H0; try tauto.
  unfold Included in H0.
  apply not_all_ex_not in H0; destruct H0.
  apply imply_to_and in H0.
  exists x0; auto.
Qed.

Lemma Property_ProperSubset'' : forall (x y: Class),
  x ⊂ y \/ y ⊂ x -> ~ (x ⊂ y) -> y ⊊ x.
Proof.
  intros; destruct H.
  - elim H0; auto.
  - unfold ProperSubset; split; auto.
    intro; rewrite H1 in H.
    pattern x at 2 in H; rewrite <- H1 in H.
    contradiction.
Qed.

Hint Unfold ProperSubset : Axiom_of_Choice.
Hint Resolve Property_ProperSubset Property_ProperSubset'
             Property_ProperSubset'': Axiom_of_Chioce.


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


(** Axiom of Choice **)

Module Type Axiom_Choice.

Axiom Choice_Axiom : forall (X: Class),
  Ensemble X -> exists ε, Choice_Function ε X.

Hint Resolve Choice_Axiom : Axiom_of_Choice.

End Axiom_Choice.


(** Tukey's Lemma **)

Module Type Tukey_Lemma.

Declare Module AC : Axiom_Choice.

(* Hypotheses *)

Definition En_F' F f :=  \{ λ x, x ∈ (∪f) /\ (F ∪ [x])∈f \}.

Definition eq_dec (A : Type) := forall x y: A, {x = y} + {x <> y}.
Parameter beq : eq_dec Class.
Definition Function_χ (F f ε: Class) : Class :=
  match beq ((En_F' F f) ~ F) Φ with
  | left _ => F
  | right _ => F ∪ [ε[(En_F' F f)~F]]
  end.

Definition tSubset f' f ε : Prop :=
  f' ⊂ f /\ Φ∈f' /\ (forall F, F∈f' -> (Function_χ F f ε) ∈ f')
  /\ (forall φ, φ ⊂ f' /\ Nest φ -> (∪φ) ∈ f').

Definition tSub_f'0 f ε := ∩ \{ λ f', tSubset f' f ε \}.

Definition En_u C f ε := \{ λ A, A ∈ (tSub_f'0 f ε) /\ (A ⊂ C \/ C ⊂ A) \}.

Definition En_f'1 f ε : Class :=
  \{ λ C, C ∈ (tSub_f'0 f ε) /\ (En_u C f ε) = (tSub_f'0 f ε) \}.

Definition En_ν D f ε : Class :=
  \{ λ A, A ∈ (tSub_f'0 f ε) /\ (A⊂D \/ (Function_χ D f ε) ⊂ A) \}.


(* Property Proof *)

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperSubset in H; destruct H; auto.
    apply Property_ProperSubset' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Setminus; apply Theorem4'; split; auto.
      unfold Complement; apply AxiomII; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply AxiomI; split; intros.
    + unfold Setminus in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply AxiomII in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.

Lemma Property_χ : forall ε F f,
  Choice_Function ε (∪f) -> F∈f -> F ⊂ (Function_χ F f ε).
Proof.
  intros.
  generalize (classic ((En_F' F f) ~ F = Φ)); intros; destruct H1.
  - unfold Function_χ; destruct (beq (En_F' F f ~ F) Φ); try tauto.
    unfold Included; intros; auto.
  - unfold Function_χ; destruct (beq (En_F' F f ~ F) Φ); try tauto.
    unfold Included; intros; apply Theorem4; tauto.
Qed.

Lemma Ens_F'F : forall f F, Ensemble (∪ f) -> Ensemble (En_F' F f ~ F).
Proof.
  intros.
  assert (En_F' F f ~ F ⊂ ∪ f).
  { unfold Included; intros.
    unfold Setminus in H0; apply Theorem4' in H0; destruct H0.
    unfold En_F' in H0; apply AxiomII in H0; apply H0. }
  apply Theorem33 in H0; auto.
Qed.

Lemma Property_f'0 : forall f ε,
  FiniteSet f /\ f ≠ Φ -> Choice_Function ε (∪f) -> tSubset (tSub_f'0 f ε) f ε
  /\ (forall f', f' ⊂ f /\ tSubset f' f ε -> (tSub_f'0 f ε) ⊂ f').
Proof.
  intros; double H.
  apply Property_FinSet in H; unfold FiniteSet in H1; destruct H1, H1.
  apply Property_NotEmpty in H2; destruct H2 as [F H2]; split.
  - assert (tSubset f f ε).
    { unfold tSubset; repeat split; try apply H; intros.
      - unfold Included; intros; auto.
      - generalize (Theorem26 F); intros.
        apply H with (A:=F); split; auto.
      - generalize (classic((En_F' F0 f) ~ F0 = Φ)); intros; destruct H5.
        + unfold Function_χ; destruct (beq (En_F' F0 f ~ F0) Φ); tauto.
        + double H5; unfold Function_χ.
          destruct (beq (En_F' F0 f ~ F0) Φ); try tauto.
          unfold Choice_Function in H0; destruct H0, H7, H8.
          assert ((En_F' F0 f ~ F0) ∈ dom( ε)).
          { rewrite H8; unfold Setminus at 2; apply Theorem4'; split.
            - unfold PowerSet; apply AxiomII; apply AxiomVI in H1.
              split; try (apply Ens_F'F); auto.
              unfold Included; intros; unfold Setminus in H10.
              apply Theorem4' in H10; destruct H10.
              unfold En_F' in H10; apply AxiomII in H10; apply H10.
            - unfold Complement; apply AxiomII; double H1.
              apply AxiomVI in H10; split; try (apply Ens_F'F); auto.
              intro; unfold Singleton in H11; apply AxiomII in H11.
              destruct H11; rewrite H12 in H6; try contradiction.
              apply Theorem19; generalize (Theorem26 f); intros.
              apply Theorem33 in H13; auto. }
           apply H9 in H10; unfold Setminus in H10.
           apply Theorem4' in H10; destruct H10.
           unfold En_F' at 2 in H10; apply AxiomII in H10; apply H10. }
    assert ((tSub_f'0 f ε) ⊂ f).
    { unfold tSub_f'0; unfold Included; intros.
      unfold Element_I in H5; apply AxiomII in H5.
      apply H5; apply AxiomII; split; auto. }
    unfold tSubset; repeat split; auto.
    + unfold tSub_f'0; apply AxiomII; split; intros.
      * generalize (Theorem26 f); intros; apply Theorem33 in H6; auto.
      * apply AxiomII in H6; destruct H6; unfold tSubset in H7; apply H7.
    + intros; double H6; unfold Included in H5.
      apply H5 in H7; unfold tSubset in H4; apply H4 in H7.
      unfold tSub_f'0; apply AxiomII; split; intros; Ens.
      apply AxiomII in H8; destruct H8.
      double H9; unfold tSubset in H9; apply H9.
      unfold tSub_f'0 in H6; apply AxiomII in H6; destruct H6.
      apply H11; apply AxiomII; split; auto.
    + intros; unfold tSubset in H4; destruct H6; double H6.
      add ((tSub_f'0 f ε) ⊂ f) H6; apply Theorem28 in H6.
      add (Nest φ) H6; apply H4 in H6; unfold tSub_f'0; apply AxiomII.
      split; Ens; intros; apply AxiomII in H9; destruct H9.
      unfold tSubset in H10; apply H10; split; auto.
      assert ((tSub_f'0 f ε) ⊂ y).
      { unfold Included; intros; unfold tSub_f'0 in H11.
        unfold Element_I; apply AxiomII in H11.
        destruct H11; apply H12; apply AxiomII; split; auto. }
      add ((tSub_f'0 f ε) ⊂ y) H8; apply Theorem28 in H8; auto.
  - intros; destruct H4; unfold Included; intros.
    unfold tSub_f'0 in H6; unfold Element_I in H6.
    apply AxiomII in H6; destruct H6; apply H7.
    apply AxiomII; apply Theorem33 in H4; auto.
Qed.

Lemma FF' : forall (f ε F: Class),
  FiniteSet f /\ f ≠ Φ -> Choice_Function ε (∪f) -> F∈f ->
  (En_F' F f)~F ≠ Φ ->  F = F ∪ [ε[(En_F' F f)~F]] -> False.
Proof.
  intros.
  unfold Choice_Function in H0; assert (F~F=Φ).
  { unfold Φ; apply AxiomI; split; intros.
    - unfold Setminus in H4; apply Theorem4' in H4; destruct H4.
      apply AxiomII in H5; destruct H5; contradiction.
    - apply AxiomII in H4; destruct H4; contradiction. }
  assert (F~F≠Φ); try contradiction.
  { rewrite H3 at 1; apply Property_NotEmpty; exists (ε [En_F' F f ~ F]).
    assert ((En_F' F f ~ F) ∈ dom( ε)).
    { destruct H0, H5, H6; rewrite H6; assert (En_F' F f ~ F ⊂ ∪ f).
      { unfold Included; intros; apply Theorem4' in H8; destruct H8.
        unfold En_F' in H8; apply AxiomII in H8; apply H8. }
      assert (Ensemble (En_F' F f ~ F)).
      { apply Theorem33 in H8; auto; destruct H.
        unfold FiniteSet in H; destruct H; apply AxiomVI; auto. }
      unfold Setminus at 2; apply Theorem4'; split.
      - unfold PowerSet; apply AxiomII; split; auto.
      - unfold Complement; apply AxiomII; split; auto.
        unfold NotIn; intro; unfold Singleton in H10.
        apply AxiomII in H10; destruct H10; assert (Φ ∈ μ).
        { apply Theorem19; generalize (Theorem26 (∪ f)); intros.
          unfold FiniteSet in H; destruct H.
          apply Theorem33 in H12; auto; apply AxiomVI; apply H. }
        apply H11 in H12; contradiction. }
    apply H0 in H5; unfold Setminus in H5.
    apply AxiomII in H5; destruct H5, H6; unfold Setminus.
    apply Theorem4'; split; auto; apply Theorem4; right.
    unfold Singleton; apply AxiomII; split; auto. }
Qed.

Lemma Property_F' : forall F f, F ∈ f -> F ⊂ (En_F' F f).
Proof.
  unfold En_F', Included; intros.
  apply AxiomII; repeat split; Ens.
  - unfold Element_U; apply AxiomII; split; Ens.
  - assert (F ∪ [z] = F).
    { apply AxiomI; split; intros; try (apply Theorem4; tauto).
      apply Theorem4 in H1; destruct H1; auto.
      unfold Singleton in H1; apply AxiomII in H1.
      destruct H1; rewrite H2; auto; apply Theorem19; Ens. }
    rewrite H1; auto.
Qed.


(* Lemma Proof *)

Lemma LemmaT1 : forall f ε,
  FiniteSet f /\ f ≠ Φ -> Choice_Function ε (∪f) ->
  (forall D, D ∈ (En_f'1 f ε) -> tSubset (En_ν D f ε) f ε).
Proof.
  intros.
  apply (Property_f'0 _ ε) in H; auto; destruct H.
  assert ((En_ν D f ε) ⊂ f).
  { unfold En_ν; unfold Included; intros.
    apply AxiomII in H3; destruct H3, H4.
    unfold tSubset in H; destruct H.
    unfold Included in H; apply H in H4; auto. }
  unfold tSubset; repeat split; auto.
  - unfold En_ν; apply AxiomII.
    unfold tSubset in H; destruct H, H4.
    repeat split; Ens; left; apply Theorem26.
  - intro A; intros.
    double H4; unfold Included in H3; apply H3 in H4.
    unfold En_ν in H5; unfold En_ν.
    apply AxiomII; apply AxiomII in H5; destruct H5, H6.
    double H6; unfold tSubset in H; apply H in H8.
    repeat split; Ens; destruct H7.
    + apply Property_ProperSubset in H7; destruct H7.
      * left; generalize (classic ((Function_χ A f ε) ⊂ D)); intros.
        destruct H9; auto; unfold En_f'1 in H1; apply AxiomII in H1.
        destruct H1, H10; rewrite <- H11 in H8.
        unfold En_u in H8; apply AxiomII in H8; destruct H8, H12.
        apply Property_ProperSubset'' in H13; auto.
        double H7; apply Property_ProperSubset' in H7.
        double H13; apply Property_ProperSubset' in H13.
        destruct H7, H13, H7, H13.
        generalize (classic (x=x0)); intros; destruct H18.
        -- rewrite H18 in H7; contradiction.
        -- unfold ProperSubset in H15; destruct H15.
           unfold Included in H15; apply H15 in H7.
           assert (x0 ∉ A).
           { unfold NotIn; intro; unfold ProperSubset in H14.
             destruct H14; unfold Included in H14.
             apply H14 in H20; contradiction. }
           generalize (classic ((En_F' A f)~A=Φ)); intros; destruct H21.
           ++ unfold Function_χ in H13; unfold NotIn in H20.
              destruct (beq (En_F' A f ~ A) Φ); tauto.
           ++ unfold Function_χ in H7, H8, H13.
              destruct (beq (En_F' A f ~ A) Φ); try tauto.
              apply Theorem4 in H7; apply Theorem4 in H13.
              destruct H7, H13; try contradiction.
              unfold Singleton in H13; apply AxiomII in H13.
              unfold Singleton in H7; apply AxiomII in H7; destruct H13, H7.
              apply AxiomIV' in H8; destruct H8.
              apply Theorem42' in H24; apply Theorem19 in H24.
              double H24; apply H22 in H24; apply H23 in H25.
              rewrite <- H24 in H25; contradiction.
      * right; rewrite H7.
        unfold Included; intros; auto.
    + apply (Property_χ ε _ _) in H4; auto.
      add (A ⊂ Function_χ A f ε) H7; apply Theorem28 in H7; auto.
  - intro ϑ; intros; destruct H4.
    unfold En_ν; apply AxiomII.
    assert ((∪ ϑ) ∈ (tSub_f'0 f ε)).
    { unfold tSubset in H; apply H; split; auto.
      red; intros; unfold Included in H4.
      apply H4 in H6; unfold En_ν in H6.
      apply AxiomII in H6; apply H6. }
    repeat split; Ens.
    generalize (classic (forall B, B∈ϑ -> B ⊂ D)).
    intros; destruct H7.
    + left; unfold Included; intros.
      unfold Element_U in H8; apply AxiomII in H8.
      destruct H8, H9, H9; apply H7 in H10.
      unfold Included in H10; apply H10 in H9; auto.
    + apply not_all_ex_not in H7; destruct H7.
      apply imply_to_and in H7; destruct H7.
      double H7; unfold Included in H4; apply H4 in H7.
      unfold En_ν in H7; apply AxiomII in H7.
      destruct H7, H10, H11; try contradiction.
      right; unfold Included; intros.
      unfold Element_U; apply AxiomII; split; Ens.
Qed.

Lemma LemmaT2 : forall f ε,
  FiniteSet f /\ f ≠ Φ -> Choice_Function ε (∪f) ->
  (forall D, D ∈ (En_f'1 f ε) -> (Function_χ D f ε) ∈ (En_f'1 f ε)).
Proof.
  intros; double H1.
  unfold En_f'1 in H2; apply AxiomII in H2.
  destruct H2, H3; double H3; unfold tSub_f'0 in H5.
  double H; apply (Property_f'0 _ ε) in H6; auto.
  destruct H6; unfold tSubset in H6.
  double H3; apply H6 in H8; double H8.
  unfold tSub_f'0 in H9; destruct H6.
  unfold Included in H6; apply H6 in H3.
  apply (Property_χ ε _ _) in H3; auto.
  assert ((En_ν D f ε) ⊂ (En_u (Function_χ D f ε) f ε)).
  { unfold En_ν, En_u, Included; intros.
    apply AxiomII in H11; apply AxiomII; destruct H11, H12.
    repeat split; auto; destruct H13; auto. }
  assert ((En_u (Function_χ D f ε) f ε) ⊂ (tSub_f'0 f ε)).
  { unfold En_u, Included; intros.
    apply AxiomII in H12; apply H12. }
  apply (LemmaT1 f ε) in H1; auto.
  unfold FiniteSet in H; destruct H, H.
  assert ((En_ν D f ε) ⊂ f /\ tSubset (En_ν D f ε) f ε).
  { split; auto; unfold En_ν, Included; intros.
    apply AxiomII in H15; destruct H15, H16.
    apply H6 in H16; auto. }
  apply H7 in H15; add ((En_ν D f ε) ⊂ (En_u (Function_χ D f ε) f ε)) H15.
  apply Theorem28 in H15.
  add ((tSub_f'0 f ε) ⊂ (En_u (Function_χ D f ε) f ε)) H12.
  apply Theorem27 in H12; auto.
  unfold En_f'1; apply AxiomII; repeat split; Ens.
Qed.

Lemma LemmaT3 : forall f ε,
  FiniteSet f /\ f ≠ Φ -> Choice_Function ε (∪f) -> Nest (tSub_f'0 f ε).
Proof.
  intros; double H.
  apply (Property_f'0 _ ε) in H1; auto; destruct H1.
  assert ((En_f'1 f ε) ⊂ (tSub_f'0 f ε) /\ Nest (En_f'1 f ε)).
  { assert ((En_f'1 f ε) ⊂ (tSub_f'0 f ε)).
    { unfold Included; intros.
      unfold En_f'1 in H3; apply AxiomII in H3; apply H3. }
    split; auto; unfold tSubset in H1.
    add ((tSub_f'0 f ε) ⊂ f) H3; try apply H1.
    apply Theorem28 in H3; unfold FiniteSet in H; destruct H, H.
    apply Theorem33 with (z:=(En_f'1 f ε)) in H; auto.
    unfold Nest; intros; unfold En_f'1 in H6; destruct H6.
    apply AxiomII in H6; apply AxiomII in H7.
    destruct H6, H7, H8, H9; rewrite <- H11 in H8.
    unfold En_u in H8; apply AxiomII in H8; apply H8. }
  destruct H3.
  assert ((En_f'1 f ε) ⊂ f /\ tSubset (En_f'1 f ε) f ε).
  { unfold tSubset in H1.
    add ((tSub_f'0 f ε) ⊂ f) H3; try apply H1.
    apply Theorem28 in H3; split; auto.
    unfold tSubset; repeat split; auto; intros.
    - unfold En_f'1; apply AxiomII.
      destruct H1, H5; repeat split; Ens.
      apply AxiomI; split; intros.
      + unfold En_u; apply AxiomII in H7; apply H7.
      + unfold En_u; apply AxiomII; repeat split; Ens.
        right; apply Theorem26.
    - apply (LemmaT2 _ ε); auto.
    - unfold En_f'1; apply AxiomII.
      assert ((∪ φ) ∈ (tSub_f'0 f ε)).
      { destruct H5; assert (φ ⊂ (tSub_f'0 f ε)).
        { unfold Included; intros.
          unfold Included in H5; apply H5 in H7.
          unfold En_f'1; apply AxiomII in H7; apply H7. }
        add (Nest φ) H7; apply H1 in H7; auto. }
      repeat split; Ens.
      apply AxiomI; split; intros.
      + unfold En_u in H7; apply AxiomII in H7; apply H7.
      + unfold En_u; apply AxiomII; repeat split; Ens.
        generalize (classic (forall B, B ∈ φ -> B ⊂ z)).
        intros; destruct H8.
        * right; unfold Included; intros.
          unfold Element_U in H9; apply AxiomII in H9.
          destruct H9, H10, H10; apply H8 in H11.
          unfold Included in H11; apply H11; auto.
        * apply not_all_ex_not in H8; destruct H8.
          apply imply_to_and in H8; destruct H5, H8.
          double H8; unfold Included in H5; apply H5 in H8.
          unfold En_f'1 in H8; apply AxiomII in H8; destruct H8, H12.
          rewrite <- H13 in H7; unfold En_u in H7; apply AxiomII in H7.
          destruct H7, H14; destruct H15; try contradiction.
          left; unfold Included; intros.
          unfold Element_U; apply AxiomII; split; Ens. }
  apply H2 in H5; add ((En_f'1 f ε) ⊂ (tSub_f'0 f ε)) H5.
  apply Theorem27 in H5; auto; rewrite H5; auto.
Qed.

Lemma LemmaT4 : forall f ε,
  FiniteSet f /\ f ≠ Φ -> Choice_Function ε (∪f) -> (∪ tSub_f'0 f ε) ∈ f /\
  (Function_χ (∪ (tSub_f'0 f ε)) f ε) = ∪ (tSub_f'0 f ε).
Proof.
  intros; double H.
  apply (Property_f'0 _ ε) in H1; auto.
  destruct H1; unfold tSubset in H1.
  assert ((tSub_f'0 f ε) ⊂ (tSub_f'0 f ε) /\ Nest (tSub_f'0 f ε)).
  { split; try unfold Included; auto.
    apply (LemmaT3 _ ε) in H; auto. }
  apply H1 in H3; split.
  - destruct H1; unfold Included in H1; apply H1 in H3; auto.
  - unfold tSub_f'0 at 2 in H3; destruct H1.
    unfold Included in H1; double H3; apply H1 in H5.
    apply (Property_χ ε _ _) in H5; auto.
    assert ((Function_χ (∪ (tSub_f'0 f ε)) f ε) ⊂ ∪ (tSub_f'0 f ε)).
    { apply H4 in H3; unfold Included; intros.
    unfold Element_U; apply AxiomII; split; Ens. }
    apply Theorem27; auto.
Qed.


(* Tukey's Lemma Proof *)

Theorem Tukey : forall (f: Class),
  FiniteSet f /\ f ≠ Φ -> exists x, MaxMember x f.
Proof.
  intros; double H.
  unfold FiniteSet in H0; destruct H0, H0.
  assert (Ensemble (∪f)). { apply AxiomVI in H0; auto. }
  apply AC.Choice_Axiom in H3; destruct H3 as [ε H3].
  assert (exists F, F∈f /\ (En_F' F f) ~ F = Φ).
  { exists (∪(tSub_f'0 f ε)); double H3.
    apply (LemmaT4 _ ε) in H4; auto; destruct H4; split; auto.
    generalize (classic(En_F'(∪ tSub_f'0 f ε)f~(∪ tSub_f'0 f ε)=Φ)).
    intros; destruct H6; auto.
    assert ((Function_χ (∪ (tSub_f'0 f ε)) f ε) = (∪ tSub_f'0 f ε) ∪
    [ε [En_F' (∪ tSub_f'0 f ε) f ~ (∪ tSub_f'0 f ε)]]).
    { unfold Function_χ; destruct (beq (En_F' (∪ tSub_f'0 f ε) f ~
      (∪ tSub_f'0 f ε)) Φ); tauto. }
    rewrite H5 in H7; apply FF' in H7; auto; inversion H7. }
  destruct H4 as [F H4]; destruct H4; exists F.
  apply -> Property_Φ in H5; try (apply Property_F'; auto).
  unfold MaxMember; intro; clear H6; repeat split; auto; intros F' H6; intro.
  double H7; rewrite <- H5 in H8; apply Property_ProperSubset' in H8.
  destruct H8 as [z H8], H8; assert (F' ⊂ (En_F' F f)).
  { unfold En_F', Included; intros; apply AxiomII; repeat split; Ens.
    - unfold Element_U; apply AxiomII; split; Ens.
    - assert ((F ∪ [z0]) ⊂ F').
      { unfold ProperSubset in H7; destruct H7.
        unfold Included in H7; unfold Included; intros.
        apply Theorem4 in H12; destruct H12; try (apply H7 in H12; auto).
        unfold Singleton in H12; apply AxiomII in H12.
        destruct H12; rewrite H13; auto; apply Theorem19; Ens. }
      apply Property_FinSet in H; apply H with (A:= F'); split; auto. }
  unfold Included in H10; apply H10 in H8; contradiction.
Qed.

Hint Resolve Tukey : Axiom_of_Choice.

End Tukey_Lemma.


(** Hausdorff Maximum Principle **)

Module Type Husdorff_Principle.

Declare Module Tu : Tukey_Lemma.

(* LemmaH1 *)

Definition En_f1 f A := \{ λ F, F∈f /\ (F ∪ A) ∈ f \}.

Lemma LemmaH1_1 : forall (f A: Class),
  FiniteSet f -> A∈f -> FiniteSet (En_f1 f A).
Proof.
  intros.
  assert (f ≠ Φ). { apply Property_NotEmpty; try exists A; auto. }
  double H; add (f ≠ Φ) H2; apply Property_FinSet in H2; destruct H2.
  unfold FiniteSet in H; destruct H; unfold FiniteSet; repeat split.
  - unfold En_f1; assert (\{ λ F,F∈f /\ (F∪A)∈f \} ⊂ f).
    { unfold Included; intros; apply AxiomII in H5; apply H5. }
    apply Theorem33 in H5; auto.
  - intro B; intro; intro B1; intros; unfold En_f1 in H5.
    apply AxiomII in H5; destruct H5, H7; unfold En_f1; apply AxiomII.
    elim H6; intros; apply H4 in H6; auto; repeat split; Ens.
    assert ((B1 ∪ A)⊂(B ∪ A)).
    { unfold Included; intros; apply Theorem4 in H11.
      apply Theorem4; destruct H11; try tauto.
      unfold Included in H9; apply H9 in H11; auto. }
    add (B1∪A ⊂ B∪A) H8; apply H2 in H8; auto.
  - intro B; intros; destruct H5.
    unfold En_f1; apply AxiomII; repeat split; auto.
    + apply H4; split; auto; intros; apply H6 in H7.
      unfold En_f1 in H7; apply AxiomII in H7; apply H7.
    + apply H4; split; try (apply AxiomIV; split; Ens).
      intro A1; intros; destruct H7.
      assert ((B∩A1) ⊂ B /\ Finite (B∩A1)).
      { split.
        - unfold Included; intros; apply Theorem4' in H9; apply H9.
        - rewrite Theorem6'; apply Property_Finite with (A:=A1); auto.
          unfold Included; intros; apply Theorem4' in H9; apply H9. }
      apply H6 in H9; unfold En_f1 in H9; apply AxiomII in H9.
      destruct H9, H10; assert (A1 ⊂ (B∩A1) ∪ A).
      { unfold Included; intros; double H12; unfold Included in H7.
        apply H7 in H13; apply Theorem4 in H13; apply Theorem4.
        destruct H13; try tauto; left; apply Theorem4'; split; auto. }
      apply H2 with (A:= (B∩A1) ∪ A); auto.
Qed.

Theorem LemmaH1 : forall (f A: Class),
  FiniteSet f -> A∈f -> (exists M, MaxMember M f /\ A ⊂ M).
Proof.
  intros; double H.
  assert (A ∈ (En_f1 f A)).
  { unfold En_f1; apply AxiomII; repeat split; Ens.
    rewrite Theorem5; auto. }
  assert ((En_f1 f A) ≠ Φ).
  { generalize (classic ((En_f1 f A) = Φ)); intros.
    destruct H3; auto; generalize (Theorem16 A); intros.
    rewrite H3 in H2; contradiction. }
  apply LemmaH1_1 with (A:=A) in H1; auto.
  add ((En_f1 f A) ≠ Φ) H1; apply Tu.Tukey in H1.
  destruct H1 as [M H1]; exists M; unfold MaxMember in H1.
  double H3; apply H1 in H4; clear H1; destruct H4.
  assert ((M ∪ A) ∈ (En_f1 f A)).
  { unfold En_f1; apply AxiomII.
    unfold En_f1 in H1; apply AxiomII in H1; destruct H1, H5.
    unfold En_f1 in H2; apply AxiomII in H2; destruct H2, H7.
    repeat split; try (apply AxiomIV; split); auto.
    rewrite Theorem7; rewrite Theorem5; auto. }
  apply H4 in H5; unfold ProperSubset in H5.
  apply property_not in H5; destruct H5.
  - cut (M ⊂ M ∪ A); intros; try contradiction.
    unfold Included; intros; apply Theorem4; auto.
  - apply NNPP in H5; assert (A ⊂ M).
    { rewrite H5; unfold Included; intros; apply Theorem4; auto. }
    split; auto; unfold MaxMember; unfold FiniteSet in H; destruct H.
    unfold En_f1 in H1; apply AxiomII in H1; destruct H1, H8; intros.
    clear H10; repeat split; auto; intro K; intros; intro.
    unfold ProperSubset in H11; destruct H11.
    add (M ⊂ K) H6; apply Theorem28 in H6; apply Theorem29 in H6.
    double H10; rewrite Theorem6 in H6; rewrite <- H6 in H13.
    assert (K ∈ (En_f1 f A)).
    { unfold En_f1; apply AxiomII; repeat split; Ens. }
    apply H4 in H14; unfold ProperSubset in H14; tauto.
Qed.

Hint Resolve LemmaH1 : Axiom_of_Choice.


(* LemmaH2 *)

(* Hypothesis HH2 : forall (A1 F: Class), A1 ⊂ F /\ Finite A1. *)

Lemma LemmaH2 : forall (A: Class),
  Ensemble A -> FiniteSet \{ λ n, n ⊂ A /\ Nest n \}.
Proof.
  intros.
  unfold FiniteSet; repeat split; intros.
  - apply Theorem38 in H; auto.
    assert (\{ λ n, n ⊂ A /\ Nest n \} ⊂ pow(A)).
    { unfold Included at 1; intros.
      unfold PowerSet; apply AxiomII.
      apply AxiomII in H0; destruct H0, H1; split; auto. }
    apply Theorem33 in H0; auto.
  - apply AxiomII in H0; apply AxiomII; destruct H0, H1, H2.
    double H1; add (F ⊂ A) H5; apply Theorem28 in H5; double H5.
    apply Theorem33 in H6; repeat split; auto; intros; unfold Nest.
    intros; unfold Nest in H4; destruct H7; unfold Included in H1.
    apply H1 in H7; apply H1 in H8; add (B∈F) H7.
  - destruct H0; apply AxiomII; repeat split; auto; intros.
    + unfold Included; intros; assert ([z] ⊂ F /\ Finite ([z])).
      { split; try (apply Finite_Single; Ens).
        unfold Included; intros; apply AxiomII in H3.
        destruct H3; rewrite H4; auto; apply Theorem19; Ens. }
      apply H1 in H3; apply AxiomII in H3; destruct H3, H4.
      unfold Included in H4; apply H4; apply AxiomII; Ens.
    + unfold Nest; intros; destruct H2.
      assert ([A0|B] ⊂ F /\ Finite ([A0|B])).
      { split.
        - unfold Included; intros; unfold Unordered in H4.
          apply Theorem4 in H4; destruct H4.
          + unfold Singleton in H4; apply AxiomII in H4.
            destruct H4; rewrite H5; auto; apply Theorem19; Ens.
          + unfold Singleton in H4; apply AxiomII in H4.
            destruct H4; rewrite H5; auto; apply Theorem19; Ens.
        - unfold Unordered; apply Theorem168.
          split; apply Finite_Single; Ens. }
      apply H1 in H4; apply AxiomII in H4; destruct H4, H5.
      unfold Nest in H6; apply H6; split.
      * unfold Unordered; apply Theorem4; left.
        unfold Singleton; apply AxiomII; Ens.
      * unfold Unordered; apply Theorem4; right.
        unfold Singleton; apply AxiomII; Ens.
Qed.

Hint Resolve LemmaH2 : Axiom_of_Choice.


(* Hausdorff Maximum Principle*)

Theorem Hausdorff : forall (A N: Class),
  Ensemble A -> N ⊂ A /\ Nest N ->
  (exists u, MaxMember u \{ λ n, n⊂A /\ Nest n \} /\ N ⊂ u).
Proof.
  intros; destruct H0; double H.
  apply LemmaH2 in H2; double H0; apply Theorem33 in H0; auto.
  apply LemmaH1 with (A:=N) in H2; auto.
  apply AxiomII; auto.
Qed.

Hint Resolve Hausdorff : Axiom_of_Choice.

End Husdorff_Principle.


(** Maximum Principle **)

Module Type Maximum_Principle.

Declare Module Hus : Husdorff_Principle.

Lemma Ex_Nest : forall A, exists N, N ⊂ A /\ Nest N.
Proof.
  intros.
  exists Φ; split; try apply Theorem26; unfold Nest; intros.
  destruct H; generalize (Theorem16 B); contradiction.
Qed.

Theorem MaxPrinciple : forall (A: Class),
  Ensemble A ->
  (forall n, n⊂A /\ Nest n -> exists N, N∈A /\ (forall u, u∈n -> u⊂N))
  -> exists M, MaxMember M A.
Proof.
  intros.
  generalize (Ex_Nest A); intros; destruct H1 as [n H1].
  assert (\{ λ n, n ⊂ A /\ Nest n \} ≠ Φ).
  { apply Property_NotEmpty; exists n; destruct H1.
    apply AxiomII; repeat split; auto; apply Theorem33 in H1; auto. }
  apply Hus.Hausdorff in H1; auto; destruct H1 as [u H1], H1.
  unfold MaxMember in H1; apply H1 in H2; clear H1; destruct H2.
  apply AxiomII in H1; destruct H1; elim H4; intros; apply H0 in H4.
  destruct H4 as [N H4]; exists N; unfold MaxMember; destruct H4; intro.
  clear H8; repeat split; auto; intro K; intros; intro.
  unfold ProperSubset in H9; destruct H9.
  assert ((u ∪ [K]) ∈ \{ λ n, n⊂A /\ Nest n \}).
  { apply AxiomII; assert (Ensemble (u ∪ [K])).
    { apply AxiomIV; split; auto; apply Theorem42; Ens. }
    repeat split; auto; intros.
    - unfold Included; intros; apply Theorem4 in H12; destruct H12.
      + unfold Included in H5; apply H5 in H12; auto.
      + unfold Singleton in H12; apply AxiomII in H12.
        destruct H12; rewrite H13; auto; apply Theorem19; Ens.
    - unfold Nest; intros; destruct H12.
      apply Theorem4 in H12; apply Theorem4 in H13.
      assert (K ∈ μ). { apply Theorem19; Ens. }
      unfold Nest in H6; destruct H12, H13.
      + add (B ∈ u) H12.
      + unfold Singleton in H13; apply AxiomII in H13.
        destruct H13; rewrite <- H15 in H9; auto; apply H7 in H12.
        add (N ⊂ B) H12; apply Theorem28 in H12; tauto.
      + unfold Singleton in H12; apply AxiomII in H12.
        destruct H12; rewrite <- H15 in H9; auto; apply H7 in H13.
        add (N ⊂ A0) H13; apply Theorem28 in H13; tauto.
      + unfold Singleton in H12, H13; apply AxiomII in H12.
        apply AxiomII in H13; destruct H12, H13; left.
        rewrite H15, H16; auto; unfold Included; auto. }
  apply H2 in H11; unfold ProperSubset in H11.
  apply property_not in H11; destruct H11.
  - absurd (u ⊂ u ∪ [K]); auto.
    unfold Included; intros; apply Theorem4; auto.
  - apply NNPP in H11; assert (K∈u).
    { rewrite H11; apply Theorem4; right.
      unfold Singleton; apply AxiomII; split; Ens. }
    apply H7 in H12; add (K ⊂ N) H9.
    apply Theorem27 in H9; contradiction.
Qed.

Hint Resolve MaxPrinciple : Axiom_of_Choice.

End Maximum_Principle.


(** Order **)

(* Partial Order, Partially Ordered Set *)

Definition Reflexivity le X := forall a, a∈X -> Rrelation a le a.

Definition Antisymmetry le X :=
  forall x y, x∈X /\ y∈X -> (Rrelation x le y /\ Rrelation y le x -> x = y).

Definition PartialOrder le X : Prop :=
  Ensemble X /\ (Relation le /\ le ⊂ X × X) /\
  Reflexivity le X /\ Antisymmetry le X /\ Transitive le X.

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


(* Cut *)

Definition Cut Y X le := Y ⊂ X /\ WellOrder le X /\
  (forall u v, (u ∈ X /\ v ∈ Y /\ Rrelation u le v ) -> u ∈ Y).

Hint Unfold WellOrderSet : Axiom_of_Chioce.


(** Zorn Lemma **)

Module Type Zorn_Lemma.

Declare Module Max : Maximum_Principle.

Definition En_Fs X le x := \{ λ u, u∈X /\ Rrelation u le x \}.

Definition En_FF X A le := \{ λ u, exists a, u = (En_Fs X le a) /\ a∈A \}.

Definition En_A X A le := \{ λ u, (En_Fs X le u) ∈ A \}.

Axiom Property_FF : forall X A le a,
  (En_Fs X le a) ∈ (En_FF X A le) ->
  (forall b, En_Fs X le a = En_Fs X le b -> a = b).

Lemma Property_Fs : forall X le u v,
  PartialOrder le X -> u∈X ->
  (En_Fs X le u ⊂ En_Fs X le v <-> Rrelation u le v).
Proof.
  intros; unfold PartialOrder in H.
  destruct H, H1, H2, H3; split; intros.
  - assert (u ∈ (En_Fs X le u)).
    { unfold En_Fs; apply AxiomII; repeat split; Ens. }
    unfold Included in H5; apply H5 in H6; unfold En_Fs in H6.
    apply AxiomII in H6; try apply H6.
  - unfold Included; intros; unfold En_Fs in H6; unfold En_Fs.
    apply AxiomII in H6; apply AxiomII; destruct H6, H7.
    repeat split; auto; unfold Transitive in H4; apply H4 with (v:=u).
    repeat split; auto; destruct H1; unfold Included in H9.
    unfold Rrelation in H5; apply H9 in H5; unfold Cartesian in H5.
    apply AxiomII_P in H5; apply H5.
Qed.

Lemma LemmaZorn_1 : forall A X le,
  PartialOrderSet X le ->
  (Chain A X le <-> (En_FF X A le)⊂(En_FF X X le) /\ Nest(En_FF X A le) /\ A≠Φ).
Proof.
  intros; split; intros.
  - double H; unfold PartialOrderSet in H1; unfold Chain in H0.
    apply H0 in H1; clear H0; destruct H1, H0; split.
    + unfold Included; intros; apply AxiomII in H3; apply AxiomII.
      destruct H3, H4, H4; split; auto; exists x; split; auto.
    + split; auto; unfold Nest; intros; destruct H3; apply AxiomII in H3.
      apply AxiomII in H4; destruct H3, H4, H5, H5, H6, H6.
      generalize (classic (x=x0)); intros; destruct H9.
      * rewrite H9 in H5; rewrite H5, H6.
        right; unfold Included; intros; auto.
      * unfold TotalOrder in H1; destruct H1; clear H1; double H7.
        add (x0∈A) H7; apply H10 in H7; auto; clear H10; clear H9.
        unfold PartialOrderSet in H; unfold PartialOrder in H.
        destruct H, H9, H10 as [H11 H10], H10 as [H12 H10]; clear H11 H12.
        unfold Transitive in H10; rewrite H5, H6; destruct H7.
        -- left; unfold Included; intros; apply AxiomII in H11.
           destruct H11, H12; apply AxiomII; repeat split; auto.
           assert (Rrelation x le x0).
           { unfold Rrelation in H7; unfold Rrelation.
             apply Theorem4' in H7; apply H7. }
           unfold Included in H0; apply H0 in H1; apply H0 in H8.
           apply H10 with (v:= x); auto.
        -- right; unfold Included; intros; apply AxiomII in H11.
           destruct H11, H12; apply AxiomII; repeat split; auto.
           assert (Rrelation x0 le x).
           { unfold Rrelation in H7; unfold Rrelation.
             apply Theorem4' in H7; apply H7. }
           unfold Included in H0; apply H0 in H1; apply H0 in H8.
           apply H10 with (v:= x0); auto.
  - destruct H0, H1; unfold Chain; intros; clear H3.
    assert (forall z, z∈A -> (En_Fs X le z) ∈ (En_FF X A le)).
    { intros; unfold En_FF; apply AxiomII; split.
      - assert (En_Fs X le z ⊂ X).
        { unfold Included; intros; apply AxiomII in H4; apply H4. }
        unfold PartialOrderSet in H; destruct H; clear H5.
        apply Theorem33 in H4; auto.
      - exists z; split; auto. }
    assert (A ⊂ X); try split; auto.
    { unfold Included; intros; unfold Included in H0.
      apply H3 in H4; apply H0 in H4; double H4; unfold En_FF in H5.
      apply AxiomII in H5; destruct H5, H6, H6.
      apply Property_FF with (A:=X) in H6; auto; rewrite H6; auto. }
    unfold PartialOrderSet in H; unfold PartialOrder in H; destruct H.
    destruct H5, H6, H7; unfold TotalOrder.
    split; try (apply Theorem33 with (x:=X); auto).
    unfold PartialOrder; repeat split; auto.
    + apply Theorem33 in H4; auto.
    + destruct H5; unfold Relation in H5; unfold Relation; intros.
      apply Theorem4' in H10; destruct H10; apply H5 in H10; auto.
    + unfold Included; intros; apply Theorem4' in H9; apply H9.
    + unfold Reflexivity; intros; unfold Rrelation; apply Theorem4'.
      unfold Reflexivity in H6; double H9; unfold Included in H4.
      apply H4 in H10; apply H6 in H10; unfold Rrelation in H10.
      split; auto; unfold Cartesian; apply AxiomII_P; Ens.
    + unfold Antisymmetry in H7; unfold Antisymmetry; intros.
      destruct H9, H10; apply H7; auto; unfold Rrelation in H10, H12.
      apply Theorem4' in H10; apply Theorem4' in H12; destruct H10, H12.
      unfold Rrelation; split; auto.
    + unfold Transitive in H8; unfold Transitive; intros.
      destruct H9, H10, H9, H12; assert ((u∈X /\ v∈X /\ w∈X) /\
      Rrelation u le v /\ Rrelation v le w).
      { unfold Included in H4; apply H4 in H9; apply H4 in H12.
        apply H4 in H13; repeat split; auto; unfold Rrelation.
        - unfold Rrelation in H10; apply Theorem4' in H10; apply H10.
        - unfold Rrelation in H11; apply Theorem4' in H11; apply H11. }
      apply H8 in H14; unfold Rrelation in H14; clear H8.
      unfold Rrelation; apply Theorem4'; split; auto.
      unfold Cartesian; apply AxiomII_P; Ens.
    + intros; destruct H9; unfold Nest in H1.
      assert ((En_Fs X le x) ∈ (En_FF X A le) /\ (En_Fs X le y) ∈ 
      (En_FF X A le)). { apply H3 in H9; apply H3 in H11; split; auto. }
      apply H1 in H12; clear H1; clear H2; destruct H12.
      * { left; unfold Rrelation; apply Theorem4'; split.
          - apply Property_ProperSubset in H1; destruct H1.
            + unfold ProperSubset in H1; destruct H1; clear H2.
              apply Property_Fs in H1; unfold Rrelation in H1; auto.
              unfold PartialOrder; auto.
            + assert ((En_Fs X le x) ∈ (En_FF X A le)).
              { unfold En_FF; apply AxiomII; double H9.
                apply H3 in H11; split; Ens. }
              apply Property_FF with (A:=A) in H1; auto; contradiction.
          - unfold Cartesian; apply AxiomII_P; repeat split; auto.
            apply Theorem49; split; Ens. }
      * { right; unfold Rrelation; apply Theorem4'; split.
          - apply Property_ProperSubset in H1; destruct H1.
            + unfold ProperSubset in H1; destruct H1; clear H2.
              apply Property_Fs in H1; unfold Rrelation in H1; auto.
              unfold PartialOrder; auto.
            + assert ((En_Fs X le y) ∈ (En_FF X A le)).
              { unfold En_FF; apply AxiomII; double H9.
                apply H3 in H11; split; Ens. }
              apply Property_FF with (A:=A) in H1; auto.
              symmetry in H1; contradiction.
          - unfold Cartesian; apply AxiomII_P; repeat split; auto.
            apply Theorem49; split; Ens. }
Qed.

Lemma LemmaZorn_2 : forall A X le y,
  PartialOrderSet X le /\ X ≠ Φ ->
  (BoundU y A X le -> (forall x, x ∈ (En_FF X A le) -> x ⊂ (En_Fs X le y))).
Proof.
  intros; double H.
  unfold BoundU in H0; apply H0 in H2; clear H0; destruct H2, H2.
  unfold En_FF in H1; apply AxiomII in H1; destruct H1.
  destruct H4 as [a H4], H4; rewrite H4; unfold Included; intros.
  unfold En_Fs in H6; unfold En_Fs; apply AxiomII in H6; apply AxiomII.
  double H5; apply H3 in H5; destruct H6, H8, H; clear H10.
  repeat split; auto; unfold PartialOrderSet, PartialOrder in H.
  destruct H, H10, H11, H12; unfold Transitive in H13.
  apply H13 with (v:=a); repeat split; auto.
Qed.

Lemma LemmaZorn_3 : forall X le y,
  PartialOrderSet X le /\ X ≠ Φ ->
  (MaxElement y X le <-> MaxMember (En_Fs X le y) (En_FF X X le)).
Proof.
  intros; destruct H; split; intros.
  - unfold MaxElement in H1; apply H1 in H0; clear H1; destruct H0.
    unfold PartialOrderSet, PartialOrder in H; destruct H.
    unfold MaxMember; intros; clear H3; repeat split; intros.
    + unfold En_FF; apply AxiomII; split.
      * assert ((En_Fs X le y) ⊂ X).
        { unfold Included; intros; apply AxiomII in H3; apply H3. }
        apply Theorem33 in H3; auto.
      * exists y; split; auto.
    + apply AxiomII in H3; destruct H3, H4, H4; rewrite H4; intro.
      apply H1 in H5; apply property_not in H5; destruct H5.
      * unfold ProperSubset in H6; destruct H6; clear H7.
        apply Property_Fs in H6; unfold Rrelation in H6; try apply H2; auto.
        unfold PartialOrder; auto.
      * apply NNPP in H5; rewrite H5 in H6; unfold ProperSubset in H6.
        destruct H6; contradiction.
  - unfold PartialOrderSet, PartialOrder in H; destruct H.
    unfold MaxElement; intros; clear H3.
    unfold MaxMember in H1; assert (En_FF X X le ≠ Φ).
    { apply Property_NotEmpty in H0; destruct H0.
      apply Property_NotEmpty; exists (En_Fs X le x).
      unfold En_FF; apply AxiomII; split.
      - apply Theorem33 with (x:= X); auto; unfold Included; intros.
        unfold En_Fs in H3; apply AxiomII in H3; apply H3.
      - exists x; split; auto. }
    apply H1 in H3; clear H1; clear H0; destruct H3; double H0.
    unfold En_FF in H3; apply AxiomII in H3; destruct H3, H4, H4.
    apply Property_FF with (A:= X) in H4; auto; rewrite <- H4 in H5.
    split; intros; auto; assert (En_Fs X le y0 ∈ (En_FF X X le)).
    { unfold En_FF; apply AxiomII; split.
      - assert (En_Fs X le y0 ⊂ X).
        { unfold Included; intros; apply AxiomII in H7; apply H7. }
        apply Theorem33 in H7; auto.
      - exists y0; split; auto. }
    apply H1 in H7; intro; elim H7; destruct H8.
    unfold ProperSubset; split.
    + apply Property_Fs; auto; unfold PartialOrder; auto.
    + intro; apply Property_FF with (A:=X) in H10; auto.
Qed.

Theorem Zorn : forall X le,
  PartialOrderSet X le -> (forall A, Chain A X le -> exists y, BoundU y A X le)
  -> exists v, MaxElement v X le.
Proof.
  intros.
  generalize (classic (X = Φ)); intros; destruct H1.
  - exists Φ; rewrite H1; unfold MaxElement; contradiction.
  - assert (Ensemble (En_FF X X le)).
    { unfold PartialOrderSet, PartialOrder in H; destruct H.
      clear H2; assert ((En_FF X X le) ⊂ pow(X)).
      { unfold Included; intros; unfold En_FF in H2.
        apply AxiomII in H2; destruct H2, H3, H3.
        unfold PowerSet; apply AxiomII; split; auto.
        rewrite H3; unfold Included; intros.
        unfold En_Fs in H5; apply AxiomII in H5; apply H5. }
      apply Theorem38 in H; auto; apply Theorem33 in H2; auto. }
    apply Max.MaxPrinciple in H2.
    + destruct H2 as [M H2]; double H2; unfold MaxMember in H3.
      assert (En_FF X X le ≠ Φ).
      { apply Property_NotEmpty in H1; destruct H1.
        apply Property_NotEmpty; exists (En_Fs X le x).
        unfold En_FF; apply AxiomII; split.
        - destruct H; apply Theorem33 with (x:= X); auto.
          unfold Included; intros; apply AxiomII in H5; apply H5.
        - exists x; split; auto. }
      apply H3 in H4; clear H3; destruct H4.
      unfold En_FF in H3; apply AxiomII in H3; destruct H3.
      destruct H5 as [v H5], H5; rewrite H5 in H2; add (X ≠ Φ) H.
      exists v; apply LemmaZorn_3 with (y:=v) in H; auto; apply H; auto.
    + intro A; intros; destruct H3.
      generalize (classic (A = Φ)); intros; destruct H5.
      { rewrite H5; apply Property_NotEmpty in H1.
        destruct H1 as [z H1]; exists (En_Fs X le z); split.
        - unfold En_FF; apply AxiomII; split.
          + destruct H; apply Theorem33 with (x:=X); auto.
            unfold Included; intros; apply AxiomII in H7; apply H7.
          + exists z; split; auto.
        - intros; generalize (Theorem16 u); contradiction. }
      assert ( (En_FF X (En_A X A le) le) ⊂ (En_FF X X le) /\
      Nest (En_FF X (En_A X A le) le) /\ (En_A X A le) ≠ Φ).
      { assert ((En_FF X (En_A X A le) le) ⊂ (En_FF X X le)).
        { intros; unfold Included; intros.
          apply AxiomII in H6; destruct H6, H7 as [a H7], H7.
          apply AxiomII in H8; destruct H8; apply AxiomII; split; auto.
          unfold Included in H3; apply H3 in H9; unfold En_FF in H8.
          double H9; apply AxiomII in H10; destruct H10, H11 as [a1 H11].
          destruct H11; apply Property_FF with (b:= a1) in H9; auto.
          rewrite H9 in H7; exists a1; auto. }
        repeat split; auto; unfold Nest; intros.
        - destruct H7; apply AxiomII in H7; apply AxiomII in H8.
          destruct H7, H8, H9 as [a H9], H10 as [b H10], H9, H10.
          apply AxiomII in H11; apply AxiomII in H12; destruct H11, H12.
          rewrite H9, H10; unfold Nest in H4; add ((En_Fs X le b) ∈ A) H13.
        - apply Property_NotEmpty in H5; destruct H5; double H5.
          apply H3 in H7; apply AxiomII in H7; destruct H7, H8, H8.
          rewrite H8 in H5; apply Property_NotEmpty; exists x0.
          apply AxiomII; split; Ens. }
      double H; apply LemmaZorn_1 with (A:= (En_A X A le)) in H7.
      apply H7 in H6; clear H7; double H6; apply H0 in H6; clear H0.
      destruct H6 as [y H0]; unfold Chain in H7; double H.
      unfold PartialOrderSet in H6; apply H7 in H6; clear H7.
      destruct H6; exists (En_Fs X le y); split; intros.
      * unfold BoundU in H0; double H; add (X≠Φ) H8; apply H0 in H8.
        clear H0; destruct H8, H8 as [H9 H8]; clear H9.
        unfold En_FF; apply AxiomII; split.
        -- assert (En_Fs X le y ⊂ X).
           { unfold Included; intros; apply AxiomII in H9; apply H9. }
           destruct H; apply Theorem33 in H9; auto.
        -- exists y; split; auto.
      * double H8; unfold Included in H3; apply H3 in H9.
        apply AxiomII in H9; destruct H9, H10, H10; add (X≠Φ) H.
        apply LemmaZorn_2 with (A:=En_A X A le)(y:=y)(x:=u) in H; auto.
        apply AxiomII; split; auto; exists x; split; auto.
        apply AxiomII; split; Ens; rewrite <- H10; auto.
Qed.

Hint Resolve Zorn : Axiom_of_Choice.

End Zorn_Lemma.


(** Well-Ordering Principle **)

Module Type WellOrder_Principle.

Declare Module Zorn : Zorn_Lemma.

Definition En_L X := \{\ λ Y le, Y ⊂ X /\ Y ≠ Φ /\ WellOrder le Y\}\.

Definition lee X: Class :=
  \{\ λ L1 L2, (L1 ∈ (En_L X) /\ L2 ∈ (En_L X)) /\
  (forall x y, x∈(First L1) /\ y∈(First L1) ->
  (Rrelation x (Second L1) y <-> Rrelation x (Second L2) y)) /\
  Cut (First L1) (First L2) (Second L2) \}\.

Definition En_Z K := \{ λ x, exists Y le, [Y,le] ∈ K /\ x∈Y \}.

Definition leeq K : Class :=
  \{\ λ u v, exists Y le, [Y,le] ∈ K /\ u∈Y /\ v∈Y /\ Rrelation u le v \}\.

Definition leep Y le x :=
  \{\ λ y1 y2, (y1∈Y /\ y2∈Y /\ Rrelation y1 le y2) \/ (y1∈(Y∪[x]) /\ y2=x) \}\.

Definition leq Y := \{\ λ y1 y2, y1∈Y /\ y2∈Y /\ y1 = y2 \}\.

Lemma Property_lee : forall Y1 Y2 le1 le2,
  Ensemble ([[Y1, le1],[Y2, le2]]) -> First ([Y1,le1]) = Y1 /\
  Second ([Y1,le1]) = le1 /\ First ([Y2,le2]) = Y2 /\ Second ([Y2,le2]) = le2.
Proof.
  intros.
  apply Theorem49 in H; destruct H.
  apply Theorem49 in H; apply Theorem54 in H; destruct H.
  apply Theorem49 in H0; apply Theorem54 in H0; destruct H0.
  repeat split; auto.
Qed.

Lemma Lemma_WP1 : forall X, Ensemble X -> PartialOrder (lee X) (En_L X).
Proof.
  intros.
  unfold PartialOrder; repeat split.
  - assert (Ensemble (pow(X)× pow(X×X))).
    { double H; apply Theorem38 in H0; auto; apply Theorem74.
      split; auto; apply Theorem38; auto; apply Theorem74; auto. }
    apply Theorem33 with (x:= pow(X)× pow(X×X)); auto.
    unfold Included; intros; PP H1 Y0 le0; apply AxiomII_P in H2.
    destruct H2, H3, H4; unfold WellOrder in H5; destruct H5; clear H6.
    unfold TotalOrder in H5; destruct H5; clear H6.
    unfold PartialOrder in H5; destruct H5, H6, H6.
    unfold Cartesian; apply AxiomII_P; repeat split; auto.
    + unfold PowerSet; apply AxiomII; split; auto.
    + unfold PowerSet; apply AxiomII; split; auto.
      * apply Theorem33 in H8; auto; apply Theorem74; auto.
      * unfold Included; intros; apply H8 in H9; PP H9 u v.
        apply AxiomII_P in H10; destruct H10, H11.
        apply AxiomII_P; repeat split; auto.
  - unfold Relation; intros; PP H0 x y; Ens.
  - unfold Included; intros; PP H0 u v; apply AxiomII_P in H1.
    destruct H1, H2, H2; apply AxiomII_P; auto.
  - unfold Reflexivity; intros; double H0; unfold En_L in H1.
    PP H1 u v; unfold Rrelation, lee; apply AxiomII_P.
    assert (Ensemble ([u,v])). { Ens. }
    split; try apply Theorem49; auto; apply Theorem49 in H3.
    apply Theorem54 in H3; destruct H3; rewrite H3, H4; clear H3 H4.
    split; Ens; split; intros.
    + split; intros; auto.
    + unfold Cut; split; try (unfold Included; auto).
      apply AxiomII_P in H2; destruct H2, H3, H4.
      split; try apply H5; intros; apply H6.
  - unfold Antisymmetry; intros; destruct H1.
    unfold Rrelation, lee in H1, H2; apply AxiomII_P in H1.
    apply AxiomII_P in H2; destruct H1, H2, H3, H4; clear H2 H3 H4.
    destruct H0; PP H0 Y1 le1; PP H2 Y2 le2; clear H0 H2 H3 H4.
    double H1; apply Property_lee in H1; destruct H1, H2, H3.
    rewrite H1, H2, H3, H4 in H5, H6; clear H1 H2 H3 H4.
    destruct H5, H6, H2, H4, H5, H6; apply Theorem49 in H0.
    destruct H0; clear H9; apply Theorem49 in H0.
    apply Theorem55; auto; split. 1: apply Theorem27; auto.
    clear H7 H8; unfold WellOrder in H5, H6; destruct H5, H6.
    clear H7 H8; unfold TotalOrder in H5, H6; destruct H5, H6.
    clear H7 H8; unfold PartialOrder in H5, H6; destruct H5, H6.
    clear H5 H6; destruct H7, H8; clear H6 H8; destruct H5, H7.
    clear x y; apply AxiomI; split; intros.
    + double H9; unfold Included in H8; apply H8 in H10.
      PP H10 x y; apply AxiomII_P in H11; destruct H11.
      apply H1 in H12; unfold Rrelation in H12; apply H12; auto.
    + double H9; unfold Included in H8; apply H6 in H10.
      PP H10 x y; apply AxiomII_P in H11; destruct H11.
      apply H3 in H12; unfold Rrelation in H12; apply H12; auto.
  - clear H; unfold Transitive; intros; destruct H, H0.
    elim H; intros; destruct H3; unfold En_L in H2, H3, H4.
    PP H2 Y1 le1; PP H3 Y2 le2; PP H4 Y3 le3; clear H H2 H3 H4 H5 H6 H7.
    unfold Rrelation; unfold lee; apply AxiomII_P.
    unfold Rrelation in H0, H1; unfold lee in H0, H1.
    apply AxiomII_P in H0; apply AxiomII_P in H1; destruct H0, H1; split.
    + apply Theorem49 in H; apply Theorem49 in H1; destruct H, H1.
      apply Theorem49; split; auto.
    + apply Property_lee in H; apply Property_lee in H1.
      destruct H, H1, H3, H4, H5, H6; clear H1 H4.
      rewrite H, H3, H5, H7 in H0; rewrite H5, H6, H7, H8 in H2.
      rewrite H, H3, H6, H8; clear H H3 H5 H7 H6 H8; destruct H0, H2.
      destruct H, H1; split; auto; clear H H1 H3 H4; destruct H0, H2.
      unfold Cut in H0, H2; destruct H0, H2, H3, H4; split; intros.
      * elim H7; intros; unfold Included in H0; apply H0 in H8.
        apply H0 in H9; add (y ∈ Y2) H8; clear H9; apply H1 in H8.
        apply H in H7; split; intros; tauto.
      * double H0; add (Y2 ⊂ Y3) H7; apply Theorem28 in H7.
        unfold Cut; repeat split; try apply H4; auto; intros.
        apply H5 with (v:=v0); destruct H8, H9; assert (u0 ∈ Y2).
        { apply H6 with (v:=v0); unfold Included in H0.
          apply H0 in H9; repeat split; auto. }
        repeat split; auto; unfold Included in H0; apply H0 in H9.
        add (v0 ∈ Y2) H11; apply H1 in H11; apply H11; auto.
Qed.

Lemma Lemma_WP2 : forall (X K : Class),
  Ensemble X -> Chain K (En_L X) (lee X) -> WellOrder (leeq K) (En_Z K).
Proof.
  intros; double H.
  unfold Chain in H0; apply (Lemma_WP1 X) in H1; apply H0 in H1.
  clear H0; destruct H1; unfold WellOrder; split.
  - unfold TotalOrder; split; intros.
    { unfold PartialOrder; repeat split.
      - assert ((En_Z K) ⊂ X).
        { unfold Included; intros; unfold En_Z in H2.
          apply AxiomII in H2; destruct H2, H3 as [Y [le H3]], H3.
          destruct H0; unfold Included in H0; apply H0 in H3.
          unfold En_L in H3; apply AxiomII_P in H3; destruct H3, H6.
          unfold Included in H6; apply H6 in H4; auto. }
        apply Theorem33 in H2; auto.
      - unfold Relation; intros; PP H2 Y0 le0; Ens.
      - unfold Included; intros; PP H2 Y0 le0; apply AxiomII_P in H3.
        destruct H3, H4 as [Y1 [le1 H4]], H4, H5, H6; apply AxiomII_P.
        repeat split; try (apply AxiomII; split); Ens.
      - unfold Reflexivity; intros; unfold En_Z in H2; apply AxiomII in H2.
        unfold Rrelation, leeq; apply AxiomII_P; destruct H2.
        destruct H3 as [Y [le H3]], H3; split; try apply Theorem49; auto.
        exists Y, le; repeat split; auto; unfold Included in H0.
        apply H0 in H3; unfold En_L in H3; apply AxiomII_P in H3.
        destruct H3, H5; unfold WellOrder in H6; destruct H6; clear H6.
        destruct H7; clear H7; unfold TotalOrder in H6; destruct H6; clear H7.
        unfold PartialOrder in H6; destruct H6, H7, H8; clear H9.
        unfold Reflexivity in H8; apply H8; auto.
      - unfold Antisymmetry; intros; destruct H3; apply AxiomII_P in H3.
        apply AxiomII_P in H4; destruct H3, H4; clear H4.
        destruct H5 as [Y1 [le1 H5]], H6 as [Y2 [le2 H6]].
        destruct H5, H6, H5, H7, H8, H9.
        generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H12.
        + assert (Ensemble ([Y1,le1])). { Ens. }
          apply Theorem49 in H13; apply Theorem55 in H12; auto.
          clear H13; destruct H12; rewrite H13 in H10; clear H12.
          clear H13; destruct H0; clear H12; unfold Included in H0.
          apply H0 in H6; apply AxiomII_P in H6; destruct H6, H12, H13.
          unfold WellOrder in H14; destruct H14; clear H15.
          unfold TotalOrder in H14; destruct H14; clear H15.
          unfold PartialOrder in H14; destruct H14, H15, H16, H17.
          unfold Antisymmetry in H17; apply H17; auto.
        + assert ([Y1, le1] ∈ K /\ [Y2, le2] ∈ K). { Ens. }
          clear H2; unfold TotalOrder in H1; destruct H1.
          apply H2 in H13; auto; clear H2 H12; destruct H13.
          * unfold Rrelation in H2; apply Theorem4' in H2; destruct H2.
            clear H12; unfold lee in H2; apply AxiomII_P in H2; destruct H2.
            apply Property_lee in H2; destruct H2, H13, H14.
            rewrite H2, H13, H14, H15 in H12; clear H2 H13 H14 H15.
            destruct H12, H12; apply H12 in H10; auto; clear H2 H12 H13.
            destruct H0; unfold Included in H0; apply H0 in H6.
            apply AxiomII_P in H6; destruct H6, H12, H13.
            unfold WellOrder in H14; destruct H14; clear H15.
            unfold TotalOrder in H14; destruct H14; clear H15.
            unfold PartialOrder in H14; destruct H14, H15, H16, H17.
            unfold Antisymmetry in H17; apply H17; auto.
          * unfold Rrelation in H2; apply Theorem4' in H2; destruct H2.
            clear H12; unfold lee in H2; apply AxiomII_P in H2; destruct H2.
            apply Property_lee in H2; destruct H2, H13, H14.
            rewrite H2, H13, H14, H15 in H12; clear H2 H13 H14 H15.
            destruct H12, H12; apply H12 in H10; auto; clear H2 H12 H13.
            destruct H0; unfold Included in H0; apply H0 in H6.
            apply AxiomII_P in H6; destruct H6, H12, H13.
            unfold WellOrder in H14; destruct H14; clear H15.
            unfold TotalOrder in H14; destruct H14; clear H15.
            unfold PartialOrder in H14; destruct H14, H15, H16, H17.
            unfold Antisymmetry in H17; apply H17; auto.
      - unfold Transitive; intros; destruct H2; clear H2; destruct H3.
        unfold Rrelation, leeq in H2, H3; apply AxiomII_P in H2.
        apply AxiomII_P in H3; destruct H2, H3; destruct H4 as [Y1 [le1 H4]].
        destruct H5 as [Y2 [le2 H5]], H4, H5, H6, H7, H8, H9.
        generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H12.
        + assert (Ensemble ([Y1, le1])); Ens.
          apply Theorem49 in H13; apply Theorem55 in H12; auto.
          clear H13; destruct H12; rewrite H12 in H6; rewrite H13 in H10.
          unfold Rrelation, leeq; apply AxiomII_P; split.
          * apply Theorem49; Ens.
          * exists Y2, le2; repeat split; auto.
            unfold Included in H0; apply H0 in H5; unfold En_L in H5.
            apply AxiomII_P in H5; destruct H5, H14, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitive in H19; apply H19 with (v:=v); auto.
        + unfold TotalOrder in H1; destruct H1; apply H13 in H12; auto.
          clear H13; destruct H12.
          * unfold Rrelation, lee in H12; apply Theorem4' in H12; destruct H12.
            clear H13; apply AxiomII_P in H12; destruct H12.
            apply Property_lee in H12; destruct H12, H14, H15.
            rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
            destruct H13, H13, H14; clear H15; unfold Rrelation, leeq.
            apply AxiomII_P; split; try (apply Theorem49; Ens).
            exists Y2, le2; repeat split; auto; double H6.
            add (v∈Y1) H15; apply H13 in H15; apply H15 in H10; clear H13 H15.
            unfold Included in H0; apply H0 in H5; unfold En_L in H5.
            apply AxiomII_P in H5; destruct H5, H13, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitive in H19; apply H19 with (v:=v); auto.
          * unfold Rrelation, lee in H12; apply Theorem4' in H12; destruct H12.
            clear H13; apply AxiomII_P in H12; destruct H12.
            apply Property_lee in H12; destruct H12, H14, H15.
            rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
            destruct H13, H13, H14; clear H15; unfold Rrelation, leeq.
            apply AxiomII_P; split; try (apply Theorem49; Ens).
            exists Y1, le1; repeat split; auto; double H7.
            add (w∈Y2) H15; apply H13 in H15; apply H15 in H11; clear H13 H15.
            unfold Included in H0; apply H0 in H4; unfold En_L in H4.
            apply AxiomII_P in H4; destruct H4, H13, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitive in H19; apply H19 with (v:=v); auto. }
    { unfold En_Z in H2; destruct H2; apply AxiomII in H2; apply AxiomII in H4.
      destruct H2, H4, H5 as [Y1 [le1 H5]], H6 as [Y2 [le2 H6]], H5, H6.
      generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H9.
      - assert (Ensemble ([Y1, le1])). { Ens. }
        apply Theorem49 in H10; apply Theorem55 in H9; auto.
        clear H10; destruct H9; rewrite H9 in H7; clear H9 H10; double H6.
        unfold Included in H0; apply H0 in H9; unfold En_L in H9.
        apply AxiomII_P in H9; destruct H9, H10; clear H9; clear H10.
        destruct H11 as [H12 H11]; clear H12; unfold WellOrder in H11.
        destruct H11; clear H10; unfold TotalOrder in H9; destruct H9.
        clear H9; double H7; add (y∈Y2) H9; apply H10 in H9; auto.
        clear H10 H3; destruct H9.
        + left; unfold Rrelation, leeq; apply AxiomII_P.
          split; try apply Theorem49; Ens.
          exists Y2, le2; repeat split; auto.
        + right; unfold Rrelation, leeq; apply AxiomII_P.
          split; try apply Theorem49; Ens.
          exists Y2, le2; repeat split; auto.
      - unfold TotalOrder in H1; destruct H1; apply H10 in H9; auto.
        clear H10; destruct H9.
        + unfold Rrelation, lee in H9; apply Theorem4' in H9; destruct H9.
          clear H10; apply AxiomII_P in H9; destruct H9.
          apply Property_lee in H9; destruct H9, H11, H12.
          rewrite H9, H11, H12, H13 in H10; clear H9 H11 H12 H13.
          destruct H10; clear H9; unfold Cut in H10; destruct H10, H10, H11.
          clear H12; unfold WellOrder in H11; destruct H11.
          clear H12; unfold TotalOrder in H11; destruct H11.
          unfold Included in H10; apply H10 in H7; double H7.
          add (y∈Y2) H13; apply H12 in H13; auto; clear H12; destruct H13.
          * left; unfold Rrelation, leeq; apply AxiomII_P.
            split; try apply Theorem49; Ens.
            exists Y2, le2; repeat split; auto.
          * right; unfold Rrelation, leeq; apply AxiomII_P.
            split; try apply Theorem49; Ens.
            exists Y2, le2; repeat split; auto.
        + unfold Rrelation, lee in H9; apply Theorem4' in H9; destruct H9.
          clear H10; apply AxiomII_P in H9; destruct H9.
          apply Property_lee in H9; destruct H9, H11, H12.
          rewrite H9, H11, H12, H13 in H10; clear H9 H11 H12 H13.
          destruct H10; clear H9; unfold Cut in H10; destruct H10, H10, H11.
          clear H12; unfold WellOrder in H11; destruct H11.
          clear H12; unfold TotalOrder in H11; destruct H11.
          unfold Included in H10; apply H10 in H8; double H7.
          add (y∈Y1) H13; apply H12 in H13; auto; clear H12; destruct H13.
          * left; unfold Rrelation, leeq; apply AxiomII_P.
            split; try apply Theorem49; Ens.
            exists Y1, le1; repeat split; auto.
          * right; unfold Rrelation, leeq; apply AxiomII_P.
            split; try apply Theorem49; Ens.
            exists Y1, le1; repeat split; auto. }
  - intro P; intros; destruct H2; apply Property_NotEmpty in H3.
    destruct H3 as [p H3]; double H3; unfold Included in H2.
    apply H2 in H4; clear H2; unfold En_Z in H4; apply AxiomII in H4.
    destruct H4, H4 as [Y [le H4]], H4; clear H2; double H4.
    apply H0 in H4; unfold En_L in H4; apply AxiomII_P in H4.
    destruct H4, H6; clear H4; clear H6; unfold WellOrdered in H7.
    destruct H7; clear H4; assert ((Y ∩ P) ⊂ Y /\ (Y ∩ P) ≠ Φ).
    { split.
      - unfold Included; intros; apply Theorem4' in H4; apply H4.
      - apply Property_NotEmpty; exists p; apply Theorem4'; auto. }
    clear H3; clear H5; elim H4; intros; apply H6 in H4; clear H6.
    clear H3; destruct H4 as [q H3]; unfold MinElement in H3.
    apply H3 in H5; clear H3; destruct H5; apply Theorem4' in H3.
    destruct H3; exists q; unfold MinElement; split; auto; clear H6.
    intro r; intros; intro; unfold Rrelation in H7; destruct H7.
    unfold leeq in H7; apply AxiomII_P in H7; destruct H7.
    clear H7; destruct H9 as [Y1 [le1 H7]], H7, H9, H10.
    unfold TotalOrder in H1; destruct H1; unfold Connect in H11.
    generalize (classic ([Y,le] = [Y1,le1])); intros; destruct H13.
    + assert (Ensemble ([Y, le])). { Ens. }
      apply Theorem49 in H14; apply Theorem55 in H13; auto.
      clear H14; destruct H13; rewrite <- H13 in H9; rewrite H14 in H4.
      apply H4 with (y:=r); try apply Theorem4'; auto.
    + apply H12 in H13; auto; clear H12; destruct H13.
      * unfold Rrelation in H12; apply Theorem4' in H12; destruct H12.
        clear H13; unfold lee in H12; apply AxiomII_P in H12.
        destruct H12; apply Property_lee in H12; destruct H12, H14, H15.
        rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
        destruct H13; unfold Cut in H13; destruct H13, H14.
        assert (r∈Y1 /\ q∈Y /\ Rrelation r le1 q).
        { repeat split; auto. } apply H15 in H16; clear H15.
        apply H4 with (y:=r); try apply Theorem4'; auto.
        split; auto; apply H13; auto.
      * unfold Rrelation in H12; apply Theorem4' in H12; destruct H12.
        clear H13; unfold lee in H12; apply AxiomII_P in H12.
        destruct H12; apply Property_lee in H12; destruct H12, H14, H15.
        rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
        destruct H13; unfold Cut in H13; destruct H13, H14.
        clear H15; double H9; unfold Included in H14; apply H14 in H15.
        apply H4 with (y:=r); try apply Theorem4'; auto.
        split; auto; apply H13; auto.
Qed.

Lemma Lemma_WP3 : forall (K X: Class),
  Ensemble X -> Chain K (En_L X) (lee X) -> exists y, BoundU y K (En_L X) (lee X).
Proof.
  intros; double H; double H0.
  apply Lemma_WP2 in H0; auto; exists ([(En_Z K),(leeq K)]).
  unfold Chain in H2; apply (Lemma_WP1 X) in H1; apply H2 in H1.
  clear H2; destruct H1; unfold BoundU; intros; destruct H3.
  assert ([En_Z K, leeq K] ∈ (En_L X)).
  { unfold En_L; apply AxiomII_P; split.
    - apply Theorem49; split.
      + assert ((En_Z K) ⊂ X).
        { unfold Included; intros; unfold En_Z in H5.
          apply AxiomII in H5; destruct H5, H6 as [Y [le H6]], H6.
          unfold Included in H1; apply H1 in H6; unfold En_L in H6.
          apply AxiomII_P in H6; destruct H6, H8; auto. }
        apply Theorem33 in H5; auto.
      + assert ((leeq K) ⊂ X × X ).
        { unfold Included; intros; unfold leeq in H5.
          PP H5 u v; apply AxiomII_P in H6; destruct H6.
          destruct H7 as [Y [le H7]], H7, H8, H9.
          unfold Included in H1; apply H1 in H7; unfold En_L in H7.
          apply AxiomII_P in H7; destruct H7, H11; unfold Included in H11.
          apply H11 in H8; apply H11 in H9; unfold Cartesian.
          apply AxiomII_P; repeat split; auto. }
        assert (Ensemble X /\ Ensemble X). { auto. }
        apply Theorem74 in H6; apply Theorem33 in H5; auto.
    - split.
      + unfold Included; intros; unfold En_Z in H5.
        apply AxiomII in H5; destruct H5, H6 as [Y [le H6]], H6.
        unfold Included in H1; apply H1 in H6; unfold En_L in H6.
        apply AxiomII_P in H6; destruct H6, H8; auto.
      + split; try apply H0; destruct H1; apply Property_NotEmpty in H5.
        destruct H5; apply Property_NotEmpty; double H5.
        unfold Included in H1; apply H1 in H6; PP H6 Y0 le0.
        apply AxiomII_P in H7; destruct H7, H8, H9.
        apply Property_NotEmpty in H9; destruct H9.
        exists x0; unfold En_Z; apply AxiomII; split; Ens. }
  repeat split; auto; try apply H1; intros.
  double H6; unfold Included in H1; apply H1 in H7.
  double H7; unfold En_L in H8; PP H8 Y1 le1; clear H9.
  unfold Rrelation; unfold lee; apply AxiomII_P.
  assert (Ensemble ([Y1,le1]) /\ Ensemble ([En_Z K,leeq K])). { Ens. }
  split; try apply Theorem49; auto; destruct H9.
  apply Theorem49 in H9; apply Theorem54 in H9; destruct H9.
  apply Theorem49 in H10; apply Theorem54 in H10; destruct H10.
  rewrite H9, H10, H11, H12; clear H9; clear H10; clear H11; clear H12.
  clear H3; clear H4; split; auto; split; intros.
  - destruct H3; split; intros.
    + unfold Rrelation, leeq; apply AxiomII_P.
      split; try apply Theorem49; Ens.
      exists Y1, le1; repeat split; auto.
    + unfold Rrelation, leeq in H9; apply AxiomII_P in H9.
      destruct H9, H10 as [Y2 [le2 H10]], H10, H11, H12, H2.
      generalize (classic ([Y1,le1] = [Y2,le2])); intros; destruct H15.
      * assert (Ensemble ([Y1, le1])). { Ens. }
        apply Theorem49 in H16; apply Theorem55 in H15; auto.
        clear H16; destruct H15; rewrite H16; auto.
      * apply H14 in H15; auto; clear H14; destruct H15.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII_P in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14; clear H16.
           clear H17; clear H18; destruct H15, H15; apply H15; auto.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII_P in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14; clear H16.
           clear H17; clear H18; destruct H15, H15; apply H15; auto.
  - unfold Cut; split.
    + unfold Included; intros; apply AxiomII; split; Ens.
    + split; try apply H0; intros; destruct H3, H4.
      unfold Rrelation, leeq in H9; apply AxiomII_P in H9.
      destruct H9, H10 as [Y2 [le2 H10]], H10, H11, H12, H2.
      generalize (classic ([Y1,le1] = [Y2,le2])); intros; destruct H15.
      * assert (Ensemble ([Y1, le1])). { Ens. }
        apply Theorem49 in H16; apply Theorem55 in H15; auto.
        clear H16; destruct H15; rewrite H15; auto.
      * apply H14 in H15; auto; clear H14; destruct H15.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII_P in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14 H16 H17 H18.
           destruct H15; clear H14; unfold Cut in H15.
           destruct H15, H15, H16; apply H17 with (v:=v); auto.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply AxiomII_P in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14 H16 H17 H18.
           destruct H15; clear H14; unfold Cut in H15.
           destruct H15, H15; auto.
Qed.

Theorem WellOrderPrinciple : forall (X: Class),
  Ensemble X -> exists le0: Class, WellOrder le0 X.
Proof.
  intros.
  assert (PartialOrderSet (En_L X) (lee X)).
  { unfold PartialOrderSet; try apply Lemma_WP1; auto. }
  double H0; apply Zorn.Zorn in H1; intros; try apply Lemma_WP3; auto.
  destruct H1 as [Y H1]; unfold MaxElement in H1.
  generalize (classic (X = Φ)); intros; destruct H2.
  { rewrite H2; exists Φ; unfold WellOrder; split; intros.
    - unfold TotalOrder; split; intros.
      + unfold PartialOrder; repeat split; intros.
        * apply Theorem33 with (x:=X); auto; unfold Included; intros.
          generalize (Theorem16 z); intros; contradiction.
        * unfold Relation; intros.
          generalize (Theorem16 z); intros; contradiction.
        * unfold Included; intros.
          generalize (Theorem16 z); intros; contradiction.
        * unfold Reflexivity; intros.
          generalize (Theorem16 a); intros; contradiction.
        * unfold Antisymmetry; intros; destruct H3.
          generalize (Theorem16 x); intros; contradiction.
        * unfold Transitive; intros; destruct H3, H3.
          generalize (Theorem16 u); intros; contradiction.
      + destruct H3; generalize (Theorem16 x); contradiction.
    - destruct H3; generalize (Theorem26 A); intros.
      absurd (A = Φ); auto; apply Theorem27; auto. }
  assert (En_L X ≠ Φ).
  { apply Property_NotEmpty in H2; destruct H2.
    apply Property_NotEmpty; exists ([[x],leq ([x])]).
    unfold En_L; apply AxiomII_P; repeat split; intros.
    - assert (Ensemble ([x])). { apply Theorem42; Ens. }
      apply Theorem49; split; auto.
      apply Theorem33 with (x:= ([x])×([x])); auto.
      + apply Theorem74; auto.
      + unfold Included; intros; PP H4 a b; unfold leq in H5.
        apply AxiomII_P in H5; destruct H5, H6, H7.
        unfold Cartesian; apply AxiomII_P; repeat split; auto.
    - unfold Included; intros; unfold Singleton in H3.
      apply AxiomII in H3; destruct H3; rewrite H4; auto.
      apply Theorem19; Ens.
    - apply Property_NotEmpty; exists x; apply AxiomII; Ens.
    - apply Theorem33 with (x:=X); auto; unfold Included; intros.
      unfold Singleton in H3; apply AxiomII in H3; destruct H3.
      rewrite H4; auto; apply Theorem19; Ens.
    - unfold Relation; intros; PP H3 a b; exists a, b; auto.
    - unfold Included; intros; PP H3 a b; unfold leq in H4.
      apply AxiomII_P in H4; destruct H4, H5, H6.
      unfold Cartesian; apply AxiomII_P; repeat split; auto.
    - unfold Reflexivity; intros; unfold Rrelation, leq.
      apply AxiomII_P; repeat split; auto; apply Theorem49; Ens.
    - unfold Antisymmetry; intros; destruct H3.
      unfold Singleton in H3, H5; apply AxiomII in H3.
      apply AxiomII in H5; destruct H3, H5.
      rewrite H6, H7; try apply Theorem19; Ens.
    - unfold Transitive; intros; destruct H3, H3, H5.
      apply AxiomII in H3; apply AxiomII in H6; destruct H3, H6.
      rewrite H7, H8; try apply Theorem19; Ens.
      unfold Rrelation, leq; apply AxiomII_P; repeat split; auto.
      + apply Theorem49; split; Ens.
      + unfold Singleton; apply AxiomII; Ens.
      + unfold Singleton; apply AxiomII; Ens.
    - destruct H3; apply AxiomII in H3; apply AxiomII in H5.
      destruct H3, H5; rewrite H6, H7 in H4; try apply Theorem19; Ens.
      contradiction.
    - destruct H3; apply Property_NotEmpty in H4; destruct H4.
      exists x0; unfold MinElement; intros; split; auto; intros.
      intro; destruct H7; unfold Rrelation, leq in H7.
      apply AxiomII_P in H7; destruct H7, H9, H10.
      rewrite H11 in H8; contradiction. }
  apply H1 in H3; clear H1 H2; destruct H3.
  unfold En_L in H1; PP H1 Y0 le0; apply AxiomII_P in H3.
  destruct H3, H4, H5; apply Property_ProperSubset in H4; destruct H4.
  - double H4; unfold ProperSubset in H7; destruct H7; clear H8.
    apply Property_ProperSubset' in H4; destruct H4, H4.
    assert (([Y0∪[x],(leep Y0 le0 x)]) ∈ (En_L X)).
    { unfold WellOrder in H6; destruct H6; unfold TotalOrder in H6; destruct H6.
      double H6; unfold PartialOrder in H11; destruct H11 as [H12 H11].
      clear H12; destruct H11; unfold En_L; apply AxiomII_P; repeat split; intros.
      - apply Theorem49 in H3; destruct H3; apply Theorem49; split.
        + apply AxiomIV; split; auto; apply Theorem42; Ens.
        + assert ((leep Y0 le0 x) ⊂ le0∪(X×X)).
          { unfold Included; intros; PP H14 y1 y2; apply AxiomII_P in H15.
            destruct H15; apply Theorem4; destruct H16.
            - left; destruct H16, H17; auto.
            - right; unfold Cartesian; apply AxiomII_P; destruct H16.
              rewrite H17; repeat split; try apply Theorem49; Ens.
              apply Theorem4 in H16; destruct H16; auto.
              unfold Singleton in H16; apply AxiomII in H16; destruct H16.
              rewrite H18; auto; apply Theorem19; Ens. }
          apply Theorem33 in H14; auto; apply AxiomIV; split; auto.
          apply Theorem74; auto.
      - unfold Included; intros; apply Theorem4 in H13; destruct H13.
        + unfold Included in H7; apply H7 in H13; auto.
        + unfold Singleton in H13; apply AxiomII in H13; destruct H13.
          rewrite H14; auto; apply Theorem19; Ens.
      - apply Property_NotEmpty in H5; destruct H5.
        apply Property_NotEmpty; exists x0; apply Theorem4; tauto.
      - apply Theorem33 with (x:=X); auto; unfold Included; intros.
        apply Theorem4 in H13; destruct H13; auto; unfold Singleton in H13.
        apply AxiomII in H13; destruct H13; rewrite H14; auto.
        apply Theorem19; Ens.
      - unfold Relation; intros; unfold leep in H13; PP H13 y1 y2; Ens.
      - unfold Included; intros; PP H13 y1 y2; apply AxiomII_P in H14.
        destruct H14; apply AxiomII_P; split; auto; destruct H15.
        + destruct H15, H16; split; try apply Theorem4; auto.
        + destruct H15; split; auto; rewrite H16; apply Theorem4.
          right; unfold Singleton; apply AxiomII; Ens.
      - unfold Reflexivity; intros; unfold Rrelation, leep; apply AxiomII_P.
        split; try apply Theorem49; Ens; apply Theorem4 in H13; destruct H13.
        + left; repeat split; auto; destruct H12; unfold Reflexivity in H12; auto.
        + right; unfold Singleton in H13; apply AxiomII in H13; destruct H13.
          rewrite H14; try apply Theorem19; Ens; split; auto.
          apply Theorem4; right; apply AxiomII; Ens.
      - unfold Antisymmetry; intros; clear H13; destruct H14.
        unfold Rrelation, leep in H13, H14; apply AxiomII_P in H13.
        apply AxiomII_P in H14; destruct H13, H14, H15, H16.
        + destruct H15, H16, H17, H18, H12, H21; clear H22.
          unfold Antisymmetry in H21; apply H21; auto.
        + destruct H15, H16; rewrite H18 in H15; contradiction.
        + destruct H15, H16; rewrite H17 in H16; contradiction.
        + destruct H15, H16; rewrite H17, H18; auto.
      - clear H11; destruct H12; clear H11; destruct H12; unfold Transitive.
        intros; unfold Transitive in H12; destruct H13, H14, H13, H16.
        unfold Rrelation; apply AxiomII_P; split; try apply Theorem49; Ens.
        unfold Rrelation, leep in H14, H15; apply AxiomII_P in H14.
        apply AxiomII_P in H15; destruct H14, H15, H18, H19.
        + left; destruct H18, H19, H20, H21; repeat split; auto.
          apply H12 with (v:=v); auto.
        + right; destruct H19; split; auto.
        + destruct H18, H19; rewrite H20 in H19; contradiction.
        + right; destruct H19; split; auto.
      - destruct H13; apply Theorem4 in H13.
        apply Theorem4 in H15; destruct H13, H15.
        + double H13; add (y∈Y0) H16; apply H10 in H16; auto.
          clear H10; destruct H16.
          * left; unfold Rrelation, leep; apply AxiomII_P.
            repeat split; try apply Theorem49; Ens.
          * right; unfold Rrelation, leep; apply AxiomII_P.
            repeat split; try apply Theorem49; Ens.
        + left; unfold Rrelation, leep; apply AxiomII_P.
          split; try apply Theorem49; Ens; right; split.
          * apply Theorem4; tauto.
          * apply AxiomII in H15; destruct H15; apply H16.
            apply Theorem19; Ens.
        + right; unfold Rrelation, leep; apply AxiomII_P.
          split; try apply Theorem49; Ens; right; split.
          * apply Theorem4; tauto.
          * apply AxiomII in H13; destruct H13; apply H16.
            apply Theorem19; Ens.
        + left; unfold Rrelation, leep; apply AxiomII_P.
          split; try apply Theorem49; Ens; right; split.
          * apply Theorem4; tauto.
          * apply AxiomII in H15; destruct H15; apply H16.
            apply Theorem19; Ens.
      - destruct H13; assert (A ⊂ Y0 \/ (exists B, B⊂Y0 /\ A = B∪[x])).
        (** 对 (A ⊂ Y0∪[x]) 进行划分 **)
        { generalize (classic (x ∈ A)); intros; destruct H15.
          - right; exists (A ~ [x]); split.
            + unfold Included; intros; unfold Setminus in H16.
              apply AxiomII in H16; destruct H16, H17.
              unfold Complement in H18; apply AxiomII in H18; destruct H18.
              unfold NotIn in H19; unfold Included in H13; apply H13 in H17.
              apply Theorem4 in H17; tauto.
            + unfold Setminus; apply AxiomI; split; intros.
              * unfold Included in H13; double H16; apply H13 in H17.
                apply Theorem4; apply Theorem4 in H17; destruct H17; try tauto.
                left; apply Theorem4'; split; auto; unfold Complement.
                apply AxiomII; split; Ens; unfold NotIn; intro.
                unfold Singleton in H18; apply AxiomII in H18; destruct H18.
                rewrite H19 in H17; try contradiction; try apply Theorem19; Ens.
              * apply Theorem4 in H16; destruct H16.
                -- apply Theorem4' in H16; apply H16.
                -- apply AxiomII in H16; destruct H16; rewrite H17; auto.
                   apply Theorem19; Ens.
          - left; unfold Included; intros; unfold Included in H13.
            double H16; apply H13 in H17; apply Theorem4 in H17.
            destruct H17; auto; apply AxiomII in H17; destruct H17.
            rewrite H18 in H16; try contradiction; apply Theorem19; Ens. }
        destruct H15.
        + double H15; add (A≠Φ) H16; apply H9 in H16; clear H9.
          destruct H16; exists x0; unfold MinElement in H9.
          apply H9 in H14; clear H9; destruct H14; unfold MinElement; intros.
          split; auto; intros; apply H14 in H17; intro; elim H17; clear H17.
          destruct H18; split; auto; unfold Rrelation, leep in H17.
          apply AxiomII_P in H17; destruct H17, H19; try apply H19.
          destruct H19; rewrite H20 in H9; apply H15 in H9; contradiction.
        + destruct H15 as [B H15], H15.
          generalize (classic (B = Φ)); intros; destruct H17.
          * rewrite H17 in H16; rewrite Theorem17 in H16; clear H17.
            rewrite H16; exists x; unfold MinElement; intros; split; intros.
            -- unfold Singleton; apply AxiomII; split; Ens.
            -- unfold Singleton in H18; apply AxiomII in H18; destruct H18.
               intro; destruct H20; rewrite H19 in H21; try contradiction.
               apply Theorem19; Ens.
          * rewrite H16; double H15; add (B≠Φ) H18; clear H16; apply H9 in H18.
            clear H9; destruct H18; exists x0; unfold MinElement in H9.
            apply H9 in H17; clear H9; destruct H17; unfold MinElement; intros.
            clear H17; split; try (apply Theorem4; tauto); intros.
            apply Theorem4 in H17; destruct H17.
            -- apply H16 in H17; intro; elim H17; clear H17.
               destruct H18; split; auto; unfold Rrelation, leep in H17.
               apply AxiomII_P in H17; destruct H17, H19; try apply H19.
               destruct H19; rewrite H20 in H9; apply H15 in H9; contradiction.
            -- intro; destruct H18; apply AxiomII in H17; destruct H17.
               rewrite H20 in H18, H19; try apply Theorem19; Ens.
               unfold Rrelation; apply AxiomII_P in H18; destruct H18, H21, H21.
               ++ destruct H22; contradiction.
               ++ contradiction. }
    double H9; apply H2 in H10; elim H10; clear H10; split.
    + unfold Rrelation, lee; apply AxiomII_P.
      assert (Ensemble ([[Y0,le0],[Y0∪[x],leep Y0 le0 x]])).
      { apply Theorem49; Ens. } split; auto.
      apply Property_lee in H10; destruct H10, H11, H12.
      rewrite H10, H11, H12, H13; clear H10 H11 H12 H13.
      split; try (split; auto; apply AxiomII_P; Ens); split; intros.
      * split; intros.
        -- destruct H10; unfold Rrelation, leep; apply AxiomII_P.
           split; try apply Theorem49; Ens; try tauto.
        -- unfold Rrelation, leep in H11; apply AxiomII_P in H11.
           destruct H11; destruct H12, H12; try apply H13.
           destruct H10; rewrite H13 in H14; contradiction.
      * unfold Cut; split.
        -- unfold Included; intros; apply Theorem4; tauto.
        -- unfold En_L in H9; apply AxiomII_P in H9; destruct H9, H10, H11.
           split; try apply H12; intros; destruct H13, H14.
           unfold Rrelation, leep; apply AxiomII_P in H15; destruct H15.
           destruct H16; try apply H16; destruct H16.
           rewrite H17 in H14; contradiction.
    + intro; apply Theorem49 in H3; apply Theorem55 in H10; auto.
      destruct H10; elim H8; rewrite H10; apply Theorem4; right.
      apply AxiomII; split; Ens.
  - rewrite H4 in H6; exists le0; auto.
Qed.

Hint Resolve WellOrderPrinciple : Axiom_of_Choice.

End WellOrder_Principle.


(** The proof of AC **)

Module Type AC_Proof.

Declare Module WellOrder : WellOrder_Principle.

Definition En_CF X le := \{\ λ x y, x ∈ (pow(X)~[Φ]) /\ y∈x /\ 
  (exists z0, MinElement z0 x le /\ y = z0) \}\.

Theorem WellOrder_Choice : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros.
  generalize (classic (X = Φ)); intros; destruct H0.
  (* X = Φ 的情况 *)
  - rewrite H0; exists Φ; unfold Choice_Function; repeat split; intros.
    + unfold Relation; intros.
      generalize (Theorem16 z); contradiction.
    + destruct H1; generalize (Theorem16 ([x,y])); contradiction.
    + unfold Included; intros; unfold Range in H1.
      apply AxiomII in H1; destruct H1, H2.
      generalize (Theorem16 ([x,z])); contradiction.
    + apply AxiomI; split; intros.
      * unfold Domain in H1; apply AxiomII in H1; destruct H1, H2.
        generalize (Theorem16 ([z,x])); contradiction.
      * unfold Setminus in H1; apply Theorem4' in H1; destruct H1.
        unfold Complement in H2; apply AxiomII in H2; destruct H2.
        unfold PowerSet in H1; apply AxiomII in H1; destruct H1.
        add (Φ ⊂ z) H4; try (apply Theorem26); apply Theorem27 in H4.
        assert (z ∈ [Φ]). { apply AxiomII; split; auto. }
        contradiction.
    + unfold Domain in H1; apply AxiomII in H1; destruct H1, H2.
      generalize (Theorem16 ([A,x])); contradiction.
  (* X ≠ Φ 的情况 *)
  - double H; apply WellOrder.WellOrderPrinciple in H1.
    destruct H1 as [le H1]; unfold WellOrder in H1; destruct H1.
    exists (En_CF X le); unfold Choice_Function.
    assert (Function (En_CF X le)).
    { unfold Function; split; intros.
      - unfold Relation; intros; PP H3 x y; exists x, y; auto.
      - destruct H3; apply AxiomII_P in H3; apply AxiomII_P in H4.
        destruct H3, H4, H5, H6, H7, H8, H9, H10, H9, H10.
        unfold TotalOrder in H1; destruct H1.
        assert (y ∈ X /\ z ∈ X).
        { unfold Setminus in H5; apply Theorem4' in H5; destruct H5.
          apply AxiomII in H5; destruct H5; split; auto. }
        generalize (classic (y = z)); intros; destruct H15; auto.
        apply H13 in H14; auto; clear H15.
        assert (x ≠ Φ). (* 要使用最小元素条件，所以要证明 x ≠ Φ *)
        { generalize (classic (x ≠ Φ)); intros; destruct H15; auto.
          apply NNPP in H15; rewrite H15 in H7.
          generalize (Theorem16 y); contradiction. }
        unfold MinElement in H9, H10; destruct H9, H10, H14; auto.
        + rewrite <- H12 in H17; apply H17 in H7.
          apply not_and_or in H7; destruct H7; try contradiction.
          apply NNPP in H7; symmetry; auto.
        + rewrite <- H11 in H16; apply H16 in H8.
          apply not_and_or in H8; destruct H8; try contradiction.
          apply NNPP in H8; symmetry; auto. }
    split; auto; repeat split; intros.
    + unfold Included; intros; apply AxiomII in H4.
      destruct H4, H5 as [y H5]; apply AxiomII_P in H5.
      destruct H5, H6, H7; clear H8; unfold Setminus in H6.
      apply Theorem4' in H6; destruct H6; clear H8.
      apply AxiomII in H6; destruct H6; auto.
    + apply AxiomI; intro A; split; intros.
      * apply AxiomII in H4; destruct H4, H5 as [y H5].
        apply AxiomII_P in H5; apply H5.
      * apply AxiomII; split; Ens; double H4.
        unfold Setminus in H5; apply Theorem4' in H5; destruct H5.
        apply AxiomII in H5; destruct H5; unfold Complement in H6.
        apply AxiomII in H6; destruct H6; clear H6; unfold NotIn in H8.
        assert (A ∈ [Φ] <-> Ensemble A /\ (Φ ∈ μ -> A = Φ)).
        { split; intros.
          - unfold Singleton in H5; apply AxiomII in H6; auto.
          - unfold Singleton; apply AxiomII; auto. }
        apply definition_not in H6; auto; clear H8.
        apply property_not in H6; destruct H6; try contradiction.
        apply imply_to_and in H6; destruct H6; clear H6.
        assert (A ⊂ X /\ A ≠ Φ). { split; auto. }
        apply H2 in H6; destruct H6 as [z0 H6]; double H6.
        unfold MinElement in H9; apply H9 in H8; clear H9; destruct H8.
        exists z0; apply AxiomII_P; repeat split; auto.
        -- apply Theorem49; split; Ens.
        -- exists z0; auto.
    + double H4; apply Property_Value in H4; auto; unfold Domain in H5.
      apply AxiomII in H5; destruct H5, H6 as [y H6]; double H6.
      apply AxiomII_P in H7; destruct H7, H8, H9; clear H10.
      add ([A,y] ∈ (En_CF X le)) H4; unfold Function in H3.
      apply H3 in H4; rewrite H4; auto.
Qed.

Hint Resolve WellOrder_Choice : Axiom_of_Choice.

End AC_Proof.


