Require Export Basic_Definitions.


(** The proof of AC **)

Module Type Zermelo_Proof_AC.

Axiom Zermelo : forall A, Ensemble A -> Φ ∉ A ->
  (forall x y, x ∈ A /\ y ∈ A -> x ≠ y -> x ∩ y = Φ) ->
  (exists D, Ensemble D /\ (forall B, B ∈ A -> exists x, B ∩ D = [x])).

Definition En_p X : Class :=
  \{ λ z, exists A, A ∈ (pow(X)~[Φ]) /\ z = (A × [A]) \}.

Theorem Proof_Axiom_Choice : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros.
  assert (exists D, forall p, p ∈ (En_p X) -> exists x, p ∩ D = [x]).
  { assert (Ensemble (En_p X) /\ Φ ∉ (En_p X)).
    { assert ((En_p X) ⊂ pow(X × (pow(X)~[Φ]))).
      { unfold Subclass; intros; unfold En_p in H0; apply Axiom_Scheme in H0.
        destruct H0, H1 as [A H1], H1; rewrite H2 in *; clear H2.
        apply Axiom_Scheme; split; auto; unfold Subclass; intros.
        PP H2 a b; clear H2; apply Axiom_SchemeP in H3; destruct H3, H3.
        apply Axiom_Scheme in H1; destruct H1, H5; double H5.
        unfold PowerClass in H7; apply Axiom_Scheme in H7.
        destruct H7 as [_ H7]; unfold Cartesian.
        apply Axiom_SchemeP; repeat split; auto.
        unfold Singleton in H4; apply Axiom_Scheme in H4; destruct H4.
        rewrite H8 in *; try apply Theorem19; Ens; clear H8.
        unfold Setminus; apply Theorem4'; split; auto. }
      assert (Ensemble (pow( X × (pow( X) ~ [Φ])))).
      { apply Theorem38; auto; apply Theorem74; split; auto.
        unfold Setminus; apply Theorem38 in H; auto.
        apply Theorem33 with (x:= pow(X)); auto.
        unfold Subclass; intros; apply Theorem4' in H1; apply H1. }
      apply Theorem33 in H0; auto; clear H1; split; auto.
      intro; unfold En_p in H1; apply Axiom_Scheme in H1; destruct H1.
      destruct H2 as [A H2], H2; unfold Setminus in H2.
      apply Theorem4' in H2; destruct H2; unfold Complement in H4.
      apply Axiom_Scheme in H4; destruct H4.
      generalize (classic (A = Φ)); intros; destruct H6.
      - rewrite H6 in H5; destruct H5; apply Axiom_Scheme; Ens.
      - apply Property_NotEmpty in H6; destruct H6.
        assert ([x,A] ∈ Φ).
        { rewrite H3; unfold Cartesian; apply Axiom_SchemeP.
          repeat split; try apply Theorem49; Ens; apply Axiom_Scheme; Ens. }
        generalize (Theorem16 ([x,A])); intros; contradiction. }
    destruct H0; apply Zermelo in H0; try destruct H0 as [D H0], H0; Ens.
    intros; unfold En_p in H2; destruct H2; apply Axiom_Scheme in H2.
    apply Axiom_Scheme in H4; destruct H2,H4,H5 as [A H5],H6 as [B H6], H5, H6.
    rewrite H7, H8 in *; clear H7 H8; apply Axiom_Extent; split; intros.
    - apply Theorem4' in H7; destruct H7; PP H7 a b; clear H7.
      apply Axiom_SchemeP in H8; apply Axiom_SchemeP in H9.
      destruct H8, H9, H8, H10; unfold Singleton in H11, H12.
      apply Axiom_Scheme in H11; apply Axiom_Scheme in H12.
      destruct H11 as [_ H11], H12 as [_ H12]; AssE A; AssE B.
      apply Theorem19 in H13; apply Theorem19 in H14; apply H12 in H13.
      apply H11 in H14. rewrite H13 in H14; rewrite H14 in H3; destruct H3; Ens.
    - generalize (Theorem16 z); intros; contradiction. }
  destruct H0 as [D H0].
  set (fc := \{\ λ A B, A ∈ (pow(X) ~ [Φ]) /\ B = First( ∩((A×[A]) ∩ D)) \}\).
  assert (Function (fc)).
  { unfold Function; split; intros.
    - unfold Relation; intros; PP H1 a b; Ens.
    - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
      destruct H1, H2, H3, H4; rewrite H5, H6; auto. }
  exists fc; unfold Choice_Function; repeat split; try apply H1; intros.
  - clear H1; unfold Subclass, Range; intros; apply Axiom_Scheme in H1.
    destruct H1, H2; apply Axiom_SchemeP in H2; clear H1; destruct H2, H2.
    apply Theorem49 in H1; destruct H1.
    assert ((x × [x]) ∈ (En_p X)).
    { unfold En_p; apply Axiom_Scheme; split; Ens.
      apply Theorem74; split; try apply Theorem42; auto. }
    AssE (x × [x]); apply H0 in H5; destruct H5; rewrite H5 in H3.
    assert (Ensemble x0).
    { apply Theorem42'; rewrite <- H5.
      apply Theorem33 with (x:= x × [x]); auto; unfold Subclass; intros.
      apply Theorem4' in H7; apply H7. }
    clear H6; double H7; apply Theorem44 in H7; destruct H7 as [H7 _].
    rewrite H7 in H3; clear H7.
    assert (x0 ∈ (x × [x] ∩ D)).
    { rewrite H5; unfold Singleton; apply Axiom_Scheme; Ens. }
    apply Theorem4' in H7; destruct H7 as [H7 _]; PP H7 a b; clear H6 H7.
    apply Axiom_SchemeP in H8; destruct H8, H7; apply Theorem49 in H6.
    apply Theorem54 in H6; destruct H6 as [H6 _]; rewrite H6 in H3.
    rewrite H3 in *; unfold Setminus, PowerClass in H2; apply Theorem4' in H2.
    destruct H2 as [H2 _]; apply Axiom_Scheme in H2; apply H2 in H7; auto.
  - clear H1; apply Axiom_Extent; split; intros.
    + unfold Domain in H1; apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; apply H2.
    + unfold Domain; apply Axiom_Scheme; split; Ens.
      assert ((z × [z]) ∈ (En_p X)).
      { unfold En_p; apply Axiom_Scheme; split.
        - apply Theorem74; split; try apply Theorem42; Ens.
        - exists z; split; auto. }
      AssE (z × [z]); apply H0 in H2; destruct H2.
      assert (Ensemble x).
      { apply Theorem42'; rewrite <- H2.
        apply Theorem33 with (x:= z × [z]); auto; unfold Subclass; intros.
        apply Theorem4' in H4; apply H4. }
      assert (x ∈ (z × [z] ∩ D)); clear H3.
      { rewrite H2; unfold Singleton; apply Axiom_Scheme; Ens. }
      apply Theorem4' in H5; destruct H5 as [H3 _]; PP H3 a b.
      clear H3; apply Theorem49 in H4; elim H4; intros; clear H6.
      apply Theorem54 in H4; destruct H4 as [H4 _]; apply Axiom_SchemeP in H5.
      destruct H5, H6; exists a; apply Axiom_SchemeP; repeat split; auto.
      * apply Theorem49; split; Ens.
      * rewrite H2; apply Theorem44 in H5; destruct H5 as [H5 _].
        rewrite H5, H4; auto.
  - apply Property_Value in H2; auto.
    apply Axiom_SchemeP in H2; destruct H2, H3.
    assert ((A × [A]) ∈ (En_p X)).
    { unfold En_p; apply Axiom_Scheme; split.
      - apply Theorem74; split; try apply Theorem42; Ens.
      - exists A; split; auto. }
    AssE (A × [A]); apply H0 in H5; destruct H5.
    assert (Ensemble x).
    { apply Theorem42'; rewrite <- H5.
      apply Theorem33 with (x:= A × [A]); auto; unfold Subclass; intros.
      apply Theorem4' in H7; apply H7. }
    assert (x ∈ (A × [A] ∩ D)); clear H6.
    { rewrite H5; unfold Singleton; apply Axiom_Scheme; Ens. }
    apply Theorem4' in H8; destruct H8 as [H6 _]; PP H6 a b.
    clear H6; apply Theorem49 in H7; apply Theorem54 in H7.
    destruct H7 as [H7 _]; apply Axiom_SchemeP in H8; destruct H8, H8.
    rewrite H5 in H4; apply Theorem44 in H6; destruct H6 as [H6 _].
    rewrite H6, H7 in H4; rewrite H4; auto.
Qed.

End Zermelo_Proof_AC.

