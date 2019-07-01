Require Export Basic_Definitions.
Require Export Finite_Character.


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

Definition En_F' F f := \{ λ x, x ∈ (∪f) /\ (F ∪ [x])∈f \}.

Definition eq_dec (A : Type) := forall x y: A, {x = y} + {x <> y}.
Parameter beq : eq_dec Class.
Definition Fun_X (F f ε: Class) : Class :=
  match beq ((En_F' F f) ~ F) Φ with
  | left _ => F
  | right _ => F ∪ [ε[(En_F' F f)~F]]
  end.

Definition tSubclass f' f ε : Prop :=
  f' ⊂ f /\ Φ∈f' /\ (forall F, F∈f' -> (Fun_X F f ε) ∈ f')
  /\ (forall φ, φ ⊂ f' /\ Nest φ -> (∪φ) ∈ f').

Definition En_f'0 f ε := ∩ \{ λ f', tSubclass f' f ε \}.

Definition En_u C f ε := \{ λ A, A ∈ (En_f'0 f ε) /\ (A ⊂ C \/ C ⊂ A) \}.

Definition En_f'1 f ε : Class :=
  \{ λ C, C ∈ (En_f'0 f ε) /\ (En_u C f ε) = (En_f'0 f ε) \}.

Definition En_v D f ε : Class :=
  \{ λ A, A ∈ (En_f'0 f ε) /\ (A⊂D \/ (Fun_X D f ε) ⊂ A) \}.


(* Property Proof *)

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperSubclass in H; destruct H; auto.
    apply Property_ProperSubclass' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Setminus; apply Theorem4'; split; auto.
      unfold Complement; apply Axiom_Scheme; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply Axiom_Extent; split; intros.
    + unfold Setminus in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply Axiom_Scheme in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.

Lemma Property_x : forall ε F f,
  Choice_Function ε (∪f) -> F∈f -> F ⊂ (Fun_X F f ε).
Proof.
  intros.
  generalize (classic ((En_F' F f) ~ F = Φ)); intros; destruct H1.
  - unfold Fun_X; destruct (beq (En_F' F f ~ F) Φ); try tauto.
    unfold Subclass; intros; auto.
  - unfold Fun_X; destruct (beq (En_F' F f ~ F) Φ); try tauto.
    unfold Subclass; intros; apply Theorem4; tauto.
Qed.

Lemma Ens_F'F : forall f F, Ensemble (∪ f) -> Ensemble (En_F' F f ~ F).
Proof.
  intros.
  assert (En_F' F f ~ F ⊂ ∪ f).
  { unfold Subclass; intros.
    unfold Setminus in H0; apply Theorem4' in H0; destruct H0.
    unfold En_F' in H0; apply Axiom_Scheme in H0; apply H0. }
  apply Theorem33 in H0; auto.
Qed.

Lemma Property_f'0 : forall f ε,
  Finite_Character f /\ f ≠ Φ -> Choice_Function ε (∪f) -> tSubclass (En_f'0 f ε) f ε
  /\ (forall f', f' ⊂ f /\ tSubclass f' f ε -> (En_f'0 f ε) ⊂ f').
Proof.
  intros; double H.
  apply Property_FinChar in H; unfold Finite_Character in H1; destruct H1, H1.
  apply Property_NotEmpty in H2; destruct H2 as [F H2]; split.
  - assert (tSubclass f f ε).
    { unfold tSubclass; repeat split; try apply H; intros.
      - unfold Subclass; intros; auto.
      - generalize (Theorem26 F); intros.
        apply H with (A:=F); split; auto.
      - generalize (classic((En_F' F0 f) ~ F0 = Φ)); intros; destruct H5.
        + unfold Fun_X; destruct (beq (En_F' F0 f ~ F0) Φ); tauto.
        + double H5; unfold Fun_X.
          destruct (beq (En_F' F0 f ~ F0) Φ); try tauto.
          unfold Choice_Function in H0; destruct H0, H7, H8.
          assert ((En_F' F0 f ~ F0) ∈ dom( ε)).
          { rewrite H8; unfold Setminus at 2; apply Theorem4'; split.
            - unfold PowerClass; apply Axiom_Scheme.
              apply Axiom_Amalgamation in H1.
              split; try (apply Ens_F'F); auto.
              unfold Subclass; intros; unfold Setminus in H10.
              apply Theorem4' in H10; destruct H10.
              unfold En_F' in H10; apply Axiom_Scheme in H10; apply H10.
            - unfold Complement; apply Axiom_Scheme; double H1.
              apply Axiom_Amalgamation in H10; split; try (apply Ens_F'F); auto.
              intro; unfold Singleton in H11; apply Axiom_Scheme in H11.
              destruct H11; rewrite H12 in H6; try contradiction.
              apply Theorem19; generalize (Theorem26 f); intros.
              apply Theorem33 in H13; auto. }
           apply H9 in H10; unfold Setminus in H10.
           apply Theorem4' in H10; destruct H10.
           unfold En_F' at 2 in H10; apply Axiom_Scheme in H10; apply H10. }
    assert ((En_f'0 f ε) ⊂ f).
    { unfold En_f'0; unfold Subclass; intros.
      unfold Element_I in H5; apply Axiom_Scheme in H5.
      apply H5; apply Axiom_Scheme; split; auto. }
    unfold tSubclass; repeat split; auto.
    + unfold En_f'0; apply Axiom_Scheme; split; intros.
      * generalize (Theorem26 f); intros; apply Theorem33 in H6; auto.
      * apply Axiom_Scheme in H6; destruct H6; unfold tSubclass in H7; apply H7.
    + intros; double H6; unfold Subclass in H5.
      apply H5 in H7; unfold tSubclass in H4; apply H4 in H7.
      unfold En_f'0; apply Axiom_Scheme; split; intros; Ens.
      apply Axiom_Scheme in H8; destruct H8.
      double H9; unfold tSubclass in H9; apply H9.
      unfold En_f'0 in H6; apply Axiom_Scheme in H6; destruct H6.
      apply H11; apply Axiom_Scheme; split; auto.
    + intros; unfold tSubclass in H4; destruct H6; double H6.
      add ((En_f'0 f ε) ⊂ f) H6; apply Theorem28 in H6.
      add (Nest φ) H6; apply H4 in H6; unfold En_f'0; apply Axiom_Scheme.
      split; Ens; intros; apply Axiom_Scheme in H9; destruct H9.
      unfold tSubclass in H10; apply H10; split; auto.
      assert ((En_f'0 f ε) ⊂ y).
      { unfold Subclass; intros; unfold En_f'0 in H11.
        unfold Element_I; apply Axiom_Scheme in H11.
        destruct H11; apply H12; apply Axiom_Scheme; split; auto. }
      add ((En_f'0 f ε) ⊂ y) H8; apply Theorem28 in H8; auto.
  - intros; destruct H4; unfold Subclass; intros.
    unfold En_f'0 in H6; unfold Element_I in H6.
    apply Axiom_Scheme in H6; destruct H6; apply H7.
    apply Axiom_Scheme; apply Theorem33 in H4; auto.
Qed.

Lemma FF' : forall (f ε F: Class),
  Finite_Character f /\ f ≠ Φ -> Choice_Function ε (∪f) -> F∈f ->
  (En_F' F f)~F ≠ Φ ->  F = F ∪ [ε[(En_F' F f)~F]] -> False.
Proof.
  intros.
  unfold Choice_Function in H0; assert (F~F=Φ).
  { unfold Φ; apply Axiom_Extent; split; intros.
    - unfold Setminus in H4; apply Theorem4' in H4; destruct H4.
      apply Axiom_Scheme in H5; destruct H5; contradiction.
    - apply Axiom_Scheme in H4; destruct H4; contradiction. }
  assert (F~F≠Φ); try contradiction.
  { rewrite H3 at 1; apply Property_NotEmpty; exists (ε [En_F' F f ~ F]).
    assert ((En_F' F f ~ F) ∈ dom( ε)).
    { destruct H0, H5, H6; rewrite H6; assert (En_F' F f ~ F ⊂ ∪ f).
      { unfold Subclass; intros; apply Theorem4' in H8; destruct H8.
        unfold En_F' in H8; apply Axiom_Scheme in H8; apply H8. }
      assert (Ensemble (En_F' F f ~ F)).
      { apply Theorem33 in H8; auto; destruct H.
        unfold Finite_Character in H; destruct H; apply Axiom_Amalgamation; auto. }
      unfold Setminus at 2; apply Theorem4'; split.
      - unfold PowerClass; apply Axiom_Scheme; split; auto.
      - unfold Complement; apply Axiom_Scheme; split; auto.
        unfold NotIn; intro; unfold Singleton in H10.
        apply Axiom_Scheme in H10; destruct H10; assert (Φ ∈ μ).
        { apply Theorem19; generalize (Theorem26 (∪ f)); intros.
          unfold Finite_Character in H; destruct H.
          apply Theorem33 in H12; auto; apply Axiom_Amalgamation; apply H. }
        apply H11 in H12; contradiction. }
    apply H0 in H5; unfold Setminus in H5.
    apply Axiom_Scheme in H5; destruct H5, H6; unfold Setminus.
    apply Theorem4'; split; auto; apply Theorem4; right.
    unfold Singleton; apply Axiom_Scheme; split; auto. }
Qed.

Lemma Property_F' : forall F f, F ∈ f -> F ⊂ (En_F' F f).
Proof.
  unfold En_F', Subclass; intros.
  apply Axiom_Scheme; repeat split; Ens.
  - unfold Element_U; apply Axiom_Scheme; split; Ens.
  - assert (F ∪ [z] = F).
    { apply Axiom_Extent; split; intros; try (apply Theorem4; tauto).
      apply Theorem4 in H1; destruct H1; auto.
      unfold Singleton in H1; apply Axiom_Scheme in H1.
      destruct H1; rewrite H2; auto; apply Theorem19; Ens. }
    rewrite H1; auto.
Qed.


(* Lemma Proof *)

Lemma LemmaT1 : forall f ε,
  Finite_Character f /\ f ≠ Φ -> Choice_Function ε (∪f) ->
  (forall D, D ∈ (En_f'1 f ε) -> tSubclass (En_v D f ε) f ε).
Proof.
  intros.
  apply (Property_f'0 _ ε) in H; auto; destruct H.
  assert ((En_v D f ε) ⊂ f).
  { unfold En_v; unfold Subclass; intros.
    apply Axiom_Scheme in H3; destruct H3, H4.
    unfold tSubclass in H; destruct H.
    unfold Subclass in H; apply H in H4; auto. }
  unfold tSubclass; repeat split; auto.
  - unfold En_v; apply Axiom_Scheme.
    unfold tSubclass in H; destruct H, H4.
    repeat split; Ens; left; apply Theorem26.
  - intro A; intros.
    double H4; unfold Subclass in H3; apply H3 in H4.
    unfold En_v in H5; unfold En_v.
    apply Axiom_Scheme; apply Axiom_Scheme in H5; destruct H5, H6.
    double H6; unfold tSubclass in H; apply H in H8.
    repeat split; Ens; destruct H7.
    + apply Property_ProperSubclass in H7; destruct H7.
      * left; generalize (classic ((Fun_X A f ε) ⊂ D)); intros.
        destruct H9; auto; unfold En_f'1 in H1; apply Axiom_Scheme in H1.
        destruct H1, H10; rewrite <- H11 in H8.
        unfold En_u in H8; apply Axiom_Scheme in H8; destruct H8, H12.
        apply Property_ProperSubclass'' in H13; auto.
        double H7; apply Property_ProperSubclass' in H7.
        double H13; apply Property_ProperSubclass' in H13.
        destruct H7, H13, H7, H13.
        generalize (classic (x=x0)); intros; destruct H18.
        -- rewrite H18 in H7; contradiction.
        -- unfold ProperSubclass in H15; destruct H15.
           unfold Subclass in H15; apply H15 in H7.
           assert (x0 ∉ A).
           { unfold NotIn; intro; unfold ProperSubclass in H14.
             destruct H14; unfold Subclass in H14.
             apply H14 in H20; contradiction. }
           generalize (classic ((En_F' A f)~A=Φ)); intros; destruct H21.
           ++ unfold Fun_X in H13; unfold NotIn in H20.
              destruct (beq (En_F' A f ~ A) Φ); tauto.
           ++ unfold Fun_X in H7, H8, H13.
              destruct (beq (En_F' A f ~ A) Φ); try tauto.
              apply Theorem4 in H7; apply Theorem4 in H13.
              destruct H7, H13; try contradiction.
              unfold Singleton in H13; apply Axiom_Scheme in H13.
              unfold Singleton in H7; apply Axiom_Scheme in H7.
              destruct H13, H7; apply Axiom_Union' in H8; destruct H8.
              apply Theorem42' in H24; apply Theorem19 in H24.
              double H24; apply H22 in H24; apply H23 in H25.
              rewrite <- H24 in H25; contradiction.
      * right; rewrite H7.
        unfold Subclass; intros; auto.
    + apply (Property_x ε _ _) in H4; auto.
      add (A ⊂ Fun_X A f ε) H7; apply Theorem28 in H7; auto.
  - intro ϑ; intros; destruct H4.
    unfold En_v; apply Axiom_Scheme.
    assert ((∪ ϑ) ∈ (En_f'0 f ε)).
    { unfold tSubclass in H; apply H; split; auto.
      red; intros; unfold Subclass in H4.
      apply H4 in H6; unfold En_v in H6.
      apply Axiom_Scheme in H6; apply H6. }
    repeat split; Ens.
    generalize (classic (forall B, B∈ϑ -> B ⊂ D)).
    intros; destruct H7.
    + left; unfold Subclass; intros.
      unfold Element_U in H8; apply Axiom_Scheme in H8.
      destruct H8, H9, H9; apply H7 in H10.
      unfold Subclass in H10; apply H10 in H9; auto.
    + apply not_all_ex_not in H7; destruct H7.
      apply imply_to_and in H7; destruct H7.
      double H7; unfold Subclass in H4; apply H4 in H7.
      unfold En_v in H7; apply Axiom_Scheme in H7.
      destruct H7, H10, H11; try contradiction.
      right; unfold Subclass; intros.
      unfold Element_U; apply Axiom_Scheme; split; Ens.
Qed.

Lemma LemmaT2 : forall f ε,
  Finite_Character f /\ f ≠ Φ -> Choice_Function ε (∪f) ->
  (forall D, D ∈ (En_f'1 f ε) -> (Fun_X D f ε) ∈ (En_f'1 f ε)).
Proof.
  intros; double H1.
  unfold En_f'1 in H2; apply Axiom_Scheme in H2.
  destruct H2, H3; double H3; unfold En_f'0 in H5.
  double H; apply (Property_f'0 _ ε) in H6; auto.
  destruct H6; unfold tSubclass in H6.
  double H3; apply H6 in H8; double H8.
  unfold En_f'0 in H9; destruct H6.
  unfold Subclass in H6; apply H6 in H3.
  apply (Property_x ε _ _) in H3; auto.
  assert ((En_v D f ε) ⊂ (En_u (Fun_X D f ε) f ε)).
  { unfold En_v, En_u, Subclass; intros.
    apply Axiom_Scheme in H11; apply Axiom_Scheme; destruct H11, H12.
    repeat split; auto; destruct H13; auto. }
  assert ((En_u (Fun_X D f ε) f ε) ⊂ (En_f'0 f ε)).
  { unfold En_u, Subclass; intros.
    apply Axiom_Scheme in H12; apply H12. }
  apply (LemmaT1 f ε) in H1; auto.
  unfold Finite_Character in H; destruct H, H.
  assert ((En_v D f ε) ⊂ f /\ tSubclass (En_v D f ε) f ε).
  { split; auto; unfold En_v, Subclass; intros.
    apply Axiom_Scheme in H15; destruct H15, H16.
    apply H6 in H16; auto. }
  apply H7 in H15; add ((En_v D f ε) ⊂ (En_u (Fun_X D f ε) f ε)) H15.
  apply Theorem28 in H15.
  add ((En_f'0 f ε) ⊂ (En_u (Fun_X D f ε) f ε)) H12.
  apply Theorem27 in H12; auto.
  unfold En_f'1; apply Axiom_Scheme; repeat split; Ens.
Qed.

Lemma LemmaT3 : forall f ε,
  Finite_Character f /\ f ≠ Φ -> Choice_Function ε (∪f) -> Nest (En_f'0 f ε).
Proof.
  intros; double H.
  apply (Property_f'0 _ ε) in H1; auto; destruct H1.
  assert ((En_f'1 f ε) ⊂ (En_f'0 f ε) /\ Nest (En_f'1 f ε)).
  { assert ((En_f'1 f ε) ⊂ (En_f'0 f ε)).
    { unfold Subclass; intros.
      unfold En_f'1 in H3; apply Axiom_Scheme in H3; apply H3. }
    split; auto; unfold tSubclass in H1.
    add ((En_f'0 f ε) ⊂ f) H3; try apply H1.
    apply Theorem28 in H3; unfold Finite_Character in H; destruct H, H.
    apply Theorem33 with (z:=(En_f'1 f ε)) in H; auto.
    unfold Nest; intros; unfold En_f'1 in H6; destruct H6.
    apply Axiom_Scheme in H6; apply Axiom_Scheme in H7.
    destruct H6, H7, H8, H9; rewrite <- H11 in H8.
    unfold En_u in H8; apply Axiom_Scheme in H8; apply H8. }
  destruct H3.
  assert ((En_f'1 f ε) ⊂ f /\ tSubclass (En_f'1 f ε) f ε).
  { unfold tSubclass in H1.
    add ((En_f'0 f ε) ⊂ f) H3; try apply H1.
    apply Theorem28 in H3; split; auto.
    unfold tSubclass; repeat split; auto; intros.
    - unfold En_f'1; apply Axiom_Scheme.
      destruct H1, H5; repeat split; Ens.
      apply Axiom_Extent; split; intros.
      + unfold En_u; apply Axiom_Scheme in H7; apply H7.
      + unfold En_u; apply Axiom_Scheme; repeat split; Ens.
        right; apply Theorem26.
    - apply (LemmaT2 _ ε); auto.
    - unfold En_f'1; apply Axiom_Scheme.
      assert ((∪ φ) ∈ (En_f'0 f ε)).
      { destruct H5; assert (φ ⊂ (En_f'0 f ε)).
        { unfold Subclass; intros.
          unfold Subclass in H5; apply H5 in H7.
          unfold En_f'1; apply Axiom_Scheme in H7; apply H7. }
        add (Nest φ) H7; apply H1 in H7; auto. }
      repeat split; Ens.
      apply Axiom_Extent; split; intros.
      + unfold En_u in H7; apply Axiom_Scheme in H7; apply H7.
      + unfold En_u; apply Axiom_Scheme; repeat split; Ens.
        generalize (classic (forall B, B ∈ φ -> B ⊂ z)).
        intros; destruct H8.
        * right; unfold Subclass; intros.
          unfold Element_U in H9; apply Axiom_Scheme in H9.
          destruct H9, H10, H10; apply H8 in H11.
          unfold Subclass in H11; apply H11; auto.
        * apply not_all_ex_not in H8; destruct H8.
          apply imply_to_and in H8; destruct H5, H8.
          double H8; unfold Subclass in H5; apply H5 in H8.
          unfold En_f'1 in H8; apply Axiom_Scheme in H8; destruct H8, H12.
          rewrite <- H13 in H7; unfold En_u in H7; apply Axiom_Scheme in H7.
          destruct H7, H14; destruct H15; try contradiction.
          left; unfold Subclass; intros.
          unfold Element_U; apply Axiom_Scheme; split; Ens. }
  apply H2 in H5; add ((En_f'1 f ε) ⊂ (En_f'0 f ε)) H5.
  apply Theorem27 in H5; auto; rewrite H5; auto.
Qed.

Lemma LemmaT4 : forall f ε,
  Finite_Character f /\ f ≠ Φ -> Choice_Function ε (∪f) -> (∪ En_f'0 f ε) ∈ f /\
  (Fun_X (∪ (En_f'0 f ε)) f ε) = ∪ (En_f'0 f ε).
Proof.
  intros; double H.
  apply (Property_f'0 _ ε) in H1; auto.
  destruct H1; unfold tSubclass in H1.
  assert ((En_f'0 f ε) ⊂ (En_f'0 f ε) /\ Nest (En_f'0 f ε)).
  { split; try unfold Subclass; auto.
    apply (LemmaT3 _ ε) in H; auto. }
  apply H1 in H3; split.
  - destruct H1; unfold Subclass in H1; apply H1 in H3; auto.
  - unfold En_f'0 at 2 in H3; destruct H1.
    unfold Subclass in H1; double H3; apply H1 in H5.
    apply (Property_x ε _ _) in H5; auto.
    assert ((Fun_X (∪ (En_f'0 f ε)) f ε) ⊂ ∪ (En_f'0 f ε)).
    { apply H4 in H3; unfold Subclass; intros.
    unfold Element_U; apply Axiom_Scheme; split; Ens. }
    apply Theorem27; auto.
Qed.


(* Tukey's Lemma Proof *)

Theorem Tukey : forall (f: Class),
  Finite_Character f /\ f ≠ Φ -> exists x, MaxMember x f.
Proof.
  intros; double H.
  unfold Finite_Character in H0; destruct H0, H0.
  assert (Ensemble (∪f)). { apply Axiom_Amalgamation in H0; auto. }
  apply AC.Choice_Axiom in H3; destruct H3 as [ε H3].
  assert (exists F, F∈f /\ (En_F' F f) ~ F = Φ).
  { exists (∪(En_f'0 f ε)); double H3.
    apply (LemmaT4 _ ε) in H4; auto; destruct H4; split; auto.
    generalize (classic(En_F'(∪ En_f'0 f ε)f~(∪ En_f'0 f ε)=Φ)).
    intros; destruct H6; auto.
    assert ((Fun_X (∪ (En_f'0 f ε)) f ε) = (∪ En_f'0 f ε) ∪
    [ε [En_F' (∪ En_f'0 f ε) f ~ (∪ En_f'0 f ε)]]).
    { unfold Fun_X; destruct (beq (En_F' (∪ En_f'0 f ε) f ~
      (∪ En_f'0 f ε)) Φ); tauto. }
    rewrite H5 in H7; apply FF' in H7; auto; inversion H7. }
  destruct H4 as [F H4]; destruct H4; exists F.
  apply -> Property_Φ in H5; try (apply Property_F'; auto).
  unfold MaxMember; intro; clear H6; repeat split; auto; intros F' H6; intro.
  double H7; rewrite <- H5 in H8; apply Property_ProperSubclass' in H8.
  destruct H8 as [z H8], H8; assert (F' ⊂ (En_F' F f)).
  { unfold En_F', Subclass; intros; apply Axiom_Scheme; repeat split; Ens.
    - unfold Element_U; apply Axiom_Scheme; split; Ens.
    - assert ((F ∪ [z0]) ⊂ F').
      { unfold ProperSubclass in H7; destruct H7.
        unfold Subclass in H7; unfold Subclass; intros.
        apply Theorem4 in H12; destruct H12; try (apply H7 in H12; auto).
        unfold Singleton in H12; apply Axiom_Scheme in H12.
        destruct H12; rewrite H13; auto; apply Theorem19; Ens. }
      apply Property_FinChar in H; apply H with (A:= F'); split; auto. }
  unfold Subclass in H10; apply H10 in H8; contradiction.
Qed.

Hint Resolve Tukey : Axiom_of_Choice.

End Tukey_Lemma.
