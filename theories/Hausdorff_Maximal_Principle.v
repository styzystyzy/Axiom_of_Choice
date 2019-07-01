Require Export Tukey_Lemma.


(** Hausdorff Maximal Principle **)

Module Type Husdorff_Principle.

Declare Module Tu : Tukey_Lemma.

(* LemmaH1 *)

Definition En_f1 f A := \{ λ F, F∈f /\ (F ∪ A) ∈ f \}.

Lemma LemmaH1_1 : forall (f A: Class),
  Finite_Character f -> A∈f -> Finite_Character (En_f1 f A).
Proof.
  intros.
  assert (f ≠ Φ). { apply Property_NotEmpty; try exists A; auto. }
  double H; add (f ≠ Φ) H2; apply Property_FinChar in H2; destruct H2.
  unfold Finite_Character in H; destruct H; unfold Finite_Character; repeat split.
  - unfold En_f1; assert (\{ λ F,F∈f /\ (F∪A)∈f \} ⊂ f).
    { unfold Subclass; intros; apply Axiom_Scheme in H5; apply H5. }
    apply Theorem33 in H5; auto.
  - intro B; intro; intro B1; intros; unfold En_f1 in H5.
    apply Axiom_Scheme in H5; destruct H5, H7; unfold En_f1; apply Axiom_Scheme.
    elim H6; intros; apply H4 in H6; auto; repeat split; Ens.
    assert ((B1 ∪ A)⊂(B ∪ A)).
    { unfold Subclass; intros; apply Theorem4 in H11.
      apply Theorem4; destruct H11; try tauto.
      unfold Subclass in H9; apply H9 in H11; auto. }
    add (B1∪A ⊂ B∪A) H8; apply H2 in H8; auto.
  - intro B; intros; destruct H5.
    unfold En_f1; apply Axiom_Scheme; repeat split; auto.
    + apply H4; split; auto; intros; apply H6 in H7.
      unfold En_f1 in H7; apply Axiom_Scheme in H7; apply H7.
    + apply H4; split; try (apply Axiom_Union; split; Ens).
      intro A1; intros; destruct H7.
      assert ((B∩A1) ⊂ B /\ Finite (B∩A1)).
      { split.
        - unfold Subclass; intros; apply Theorem4' in H9; apply H9.
        - rewrite Theorem6'; apply Property_Finite with (A:=A1); auto.
          unfold Subclass; intros; apply Theorem4' in H9; apply H9. }
      apply H6 in H9; unfold En_f1 in H9; apply Axiom_Scheme in H9.
      destruct H9, H10; assert (A1 ⊂ (B∩A1) ∪ A).
      { unfold Subclass; intros; double H12; unfold Subclass in H7.
        apply H7 in H13; apply Theorem4 in H13; apply Theorem4.
        destruct H13; try tauto; left; apply Theorem4'; split; auto. }
      apply H2 with (A:= (B∩A1) ∪ A); auto.
Qed.

Theorem LemmaH1 : forall (f A: Class),
  Finite_Character f -> A∈f -> (exists M, MaxMember M f /\ A ⊂ M).
Proof.
  intros; double H.
  assert (A ∈ (En_f1 f A)).
  { unfold En_f1; apply Axiom_Scheme; repeat split; Ens.
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
  { unfold En_f1; apply Axiom_Scheme.
    unfold En_f1 in H1; apply Axiom_Scheme in H1; destruct H1, H5.
    unfold En_f1 in H2; apply Axiom_Scheme in H2; destruct H2, H7.
    repeat split; try (apply Axiom_Union; split); auto.
    rewrite Theorem7; rewrite Theorem5; auto. }
  apply H4 in H5; unfold ProperSubclass in H5.
  apply not_and_or in H5; destruct H5.
  - cut (M ⊂ M ∪ A); intros; try contradiction.
    unfold Subclass; intros; apply Theorem4; auto.
  - apply NNPP in H5; assert (A ⊂ M).
    { rewrite H5; unfold Subclass; intros; apply Theorem4; auto. }
    split; auto; unfold MaxMember; unfold Finite_Character in H; destruct H.
    unfold En_f1 in H1; apply Axiom_Scheme in H1; destruct H1, H8; intros.
    clear H10; repeat split; auto; intro K; intros; intro.
    unfold ProperSubclass in H11; destruct H11.
    add (M ⊂ K) H6; apply Theorem28 in H6; apply Theorem29 in H6.
    double H10; rewrite Theorem6 in H6; rewrite <- H6 in H13.
    assert (K ∈ (En_f1 f A)).
    { unfold En_f1; apply Axiom_Scheme; repeat split; Ens. }
    apply H4 in H14; unfold ProperSubclass in H14; tauto.
Qed.

Hint Resolve LemmaH1 : Axiom_of_Choice.


(* LemmaH2 *)

(* Hypothesis HH2 : forall (A1 F: Class), A1 ⊂ F /\ Finite A1. *)

Lemma LemmaH2 : forall (A: Class),
  Ensemble A -> Finite_Character \{ λ n, n ⊂ A /\ Nest n \}.
Proof.
  intros.
  unfold Finite_Character; repeat split; intros.
  - apply Theorem38 in H; auto.
    assert (\{ λ n, n ⊂ A /\ Nest n \} ⊂ pow(A)).
    { unfold Subclass at 1; intros.
      unfold PowerClass; apply Axiom_Scheme.
      apply Axiom_Scheme in H0; destruct H0, H1; split; auto. }
    apply Theorem33 in H0; auto.
  - apply Axiom_Scheme in H0; apply Axiom_Scheme; destruct H0, H1, H2.
    double H1; add (F ⊂ A) H5; apply Theorem28 in H5; double H5.
    apply Theorem33 in H6; repeat split; auto; intros; unfold Nest.
    intros; unfold Nest in H4; destruct H7; unfold Subclass in H1.
    apply H1 in H7; apply H1 in H8; add (B∈F) H7.
  - destruct H0; apply Axiom_Scheme; repeat split; auto; intros.
    + unfold Subclass; intros; assert ([z] ⊂ F /\ Finite ([z])).
      { split; try (apply Finite_Single; Ens).
        unfold Subclass; intros; apply Axiom_Scheme in H3.
        destruct H3; rewrite H4; auto; apply Theorem19; Ens. }
      apply H1 in H3; apply Axiom_Scheme in H3; destruct H3, H4.
      unfold Subclass in H4; apply H4; apply Axiom_Scheme; Ens.
    + unfold Nest; intros; destruct H2.
      assert ([A0|B] ⊂ F /\ Finite ([A0|B])).
      { split.
        - unfold Subclass; intros; unfold Unordered in H4.
          apply Theorem4 in H4; destruct H4.
          + unfold Singleton in H4; apply Axiom_Scheme in H4.
            destruct H4; rewrite H5; auto; apply Theorem19; Ens.
          + unfold Singleton in H4; apply Axiom_Scheme in H4.
            destruct H4; rewrite H5; auto; apply Theorem19; Ens.
        - unfold Unordered; apply Theorem168.
          split; apply Finite_Single; Ens. }
      apply H1 in H4; apply Axiom_Scheme in H4; destruct H4, H5.
      unfold Nest in H6; apply H6; split.
      * unfold Unordered; apply Theorem4; left.
        unfold Singleton; apply Axiom_Scheme; Ens.
      * unfold Unordered; apply Theorem4; right.
        unfold Singleton; apply Axiom_Scheme; Ens.
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
  apply Axiom_Scheme; auto.
Qed.

Hint Resolve Hausdorff : Axiom_of_Choice.

End Husdorff_Principle.
