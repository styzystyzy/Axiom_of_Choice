Require Import Basic_Definitions.


(** The proof of AC **)

Module Type AC_Proof.

Axiom WellOrderPrinciple : forall (X: Class),
  Ensemble X -> exists le0: Class, WellOrder le0 X.

Definition En_cf X le := \{\ λ x y, x ∈ (pow(X)~[Φ]) /\ y∈x /\ 
  (exists z0, MinElement z0 x le /\ y = z0) \}\.

Theorem Proof_Axiom_Choice : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros.
  generalize (classic (X = Φ)); intros; destruct H0.
  - rewrite H0; exists Φ; unfold Choice_Function; repeat split; intros.
    + unfold Relation; intros.
      generalize (Theorem16 z); contradiction.
    + destruct H1; generalize (Theorem16 ([x,y])); contradiction.
    + unfold Subclass; intros; unfold Range in H1.
      apply Axiom_Scheme in H1; destruct H1, H2.
      generalize (Theorem16 ([x,z])); contradiction.
    + apply Axiom_Extent; split; intros.
      * unfold Domain in H1; apply Axiom_Scheme in H1; destruct H1, H2.
        generalize (Theorem16 ([z,x])); contradiction.
      * unfold Setminus in H1; apply Theorem4' in H1; destruct H1.
        unfold Complement in H2; apply Axiom_Scheme in H2; destruct H2.
        unfold PowerClass in H1; apply Axiom_Scheme in H1; destruct H1.
        add (Φ ⊂ z) H4; try (apply Theorem26); apply Theorem27 in H4.
        assert (z ∈ [Φ]). { apply Axiom_Scheme; split; auto. }
        contradiction.
    + unfold Domain in H1; apply Axiom_Scheme in H1; destruct H1, H2.
      generalize (Theorem16 ([A,x])); contradiction.
  - double H; apply WellOrderPrinciple in H1.
    destruct H1 as [le H1]; unfold WellOrder in H1; destruct H1.
    exists (En_cf X le); unfold Choice_Function.
    assert (Function (En_cf X le)).
    { unfold Function; split; intros.
      - unfold Relation; intros; PP H3 x y; exists x, y; auto.
      - destruct H3; apply Axiom_SchemeP in H3; apply Axiom_SchemeP in H4.
        destruct H3, H4, H5, H6, H7, H8, H9, H10, H9, H10.
        unfold TotalOrder in H1; destruct H1.
        assert (y ∈ X /\ z ∈ X).
        { unfold Setminus in H5; apply Theorem4' in H5; destruct H5.
          apply Axiom_Scheme in H5; destruct H5; split; auto. }
        generalize (classic (y = z)); intros; destruct H15; auto.
        apply H13 in H14; auto; clear H15.
        assert (x ≠ Φ).
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
    + unfold Subclass; intros; apply Axiom_Scheme in H4.
      destruct H4, H5 as [y H5]; apply Axiom_SchemeP in H5.
      destruct H5, H6, H7; clear H8; unfold Setminus in H6.
      apply Theorem4' in H6; destruct H6; clear H8.
      apply Axiom_Scheme in H6; destruct H6; auto.
    + apply Axiom_Extent; intro A; split; intros.
      * apply Axiom_Scheme in H4; destruct H4, H5 as [y H5].
        apply Axiom_SchemeP in H5; apply H5.
      * apply Axiom_Scheme; split; Ens; double H4.
        unfold Setminus in H5; apply Theorem4' in H5; destruct H5.
        apply Axiom_Scheme in H5; destruct H5; unfold Complement in H6.
        apply Axiom_Scheme in H6; destruct H6; clear H6; unfold NotIn in H8.
        assert (A ∈ [Φ] <-> Ensemble A /\ (Φ ∈ μ -> A = Φ)).
        { split; intros.
          - unfold Singleton in H5; apply Axiom_Scheme in H6; auto.
          - unfold Singleton; apply Axiom_Scheme; auto. }
        apply definition_not in H6; auto; clear H8.
        apply not_and_or in H6; destruct H6; try contradiction.
        apply imply_to_and in H6; destruct H6; clear H6.
        assert (A ⊂ X /\ A ≠ Φ). { split; auto. }
        apply H2 in H6; destruct H6 as [z0 H6]; double H6.
        unfold MinElement in H9; apply H9 in H8; clear H9; destruct H8.
        exists z0; apply Axiom_SchemeP; repeat split; auto.
        -- apply Theorem49; split; Ens.
        -- exists z0; auto.
    + double H4; apply Property_Value in H4; auto; unfold Domain in H5.
      apply Axiom_Scheme in H5; destruct H5, H6 as [y H6]; double H6.
      apply Axiom_SchemeP in H7; destruct H7, H8, H9; clear H10.
      add ([A,y] ∈ (En_cf X le)) H4; unfold Function in H3.
      apply H3 in H4; rewrite H4; auto.
Qed.

End AC_Proof.

