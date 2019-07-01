Require Export Maximal_Principle.


(** Zorn Lemma **)

Module Type Zorn_Lemma.

Declare Module Max : Maximal_Principle.

Definition En_Fs X le x := \{ λ u, u∈X /\ Rrelation u le x \}.

Definition En_FF X A le := \{ λ u, exists a, u = (En_Fs X le a) /\ a∈A \}.
Axiom Property_FF : forall X A le a,
  (En_Fs X le a) ∈ (En_FF X A le) ->
  (forall b, En_Fs X le a = En_Fs X le b -> a = b).

Definition En_A X A le := \{ λ u, (En_Fs X le u) ∈ A \}.

Lemma Property_Fs : forall X le u v,
  PartialOrder le X -> u∈X ->
  (En_Fs X le u ⊂ En_Fs X le v <-> Rrelation u le v).
Proof.
  intros; unfold PartialOrder in H.
  destruct H, H1, H2, H3; split; intros.
  - assert (u ∈ (En_Fs X le u)).
    { unfold En_Fs; apply Axiom_Scheme; repeat split; Ens. }
    unfold Subclass in H5; apply H5 in H6; unfold En_Fs in H6.
    apply Axiom_Scheme in H6; try apply H6.
  - unfold Subclass; intros; unfold En_Fs in H6; unfold En_Fs.
    apply Axiom_Scheme in H6; apply Axiom_Scheme; destruct H6, H7.
    repeat split; auto; unfold Transitivity in H4; apply H4 with (v:=u).
    repeat split; auto; destruct H1; unfold Subclass in H9.
    unfold Rrelation in H5; apply H9 in H5; unfold Cartesian in H5.
    apply Axiom_SchemeP in H5; apply H5.
Qed.

Lemma LemmaZ1 : forall A X le,
  PartialOrderSet X le ->
  (Chain A X le <-> (En_FF X A le)⊂(En_FF X X le) /\ Nest(En_FF X A le) /\ A≠Φ).
Proof.
  intros; split; intros.
  - double H; unfold PartialOrderSet in H1; unfold Chain in H0.
    apply H0 in H1; clear H0; destruct H1, H0; split.
    + unfold Subclass; intros; apply Axiom_Scheme in H3; apply Axiom_Scheme.
      destruct H3, H4, H4; split; auto; exists x; split; auto.
    + split; auto; unfold Nest; intros; destruct H3; apply Axiom_Scheme in H3.
      apply Axiom_Scheme in H4; destruct H3, H4, H5, H5, H6, H6.
      generalize (classic (x=x0)); intros; destruct H9.
      * rewrite H9 in H5; rewrite H5, H6.
        right; unfold Subclass; intros; auto.
      * unfold TotalOrder in H1; destruct H1; clear H1; double H7.
        add (x0∈A) H7; apply H10 in H7; auto; clear H10; clear H9.
        unfold PartialOrderSet in H; unfold PartialOrder in H.
        destruct H, H9, H10 as [H11 H10], H10 as [H12 H10]; clear H11 H12.
        unfold Transitivity in H10; rewrite H5, H6; destruct H7.
        -- left; unfold Subclass; intros; apply Axiom_Scheme in H11.
           destruct H11, H12; apply Axiom_Scheme; repeat split; auto.
           assert (Rrelation x le x0).
           { unfold Rrelation in H7; unfold Rrelation.
             apply Theorem4' in H7; apply H7. }
           unfold Subclass in H0; apply H0 in H1; apply H0 in H8.
           apply H10 with (v:= x); auto.
        -- right; unfold Subclass; intros; apply Axiom_Scheme in H11.
           destruct H11, H12; apply Axiom_Scheme; repeat split; auto.
           assert (Rrelation x0 le x).
           { unfold Rrelation in H7; unfold Rrelation.
             apply Theorem4' in H7; apply H7. }
           unfold Subclass in H0; apply H0 in H1; apply H0 in H8.
           apply H10 with (v:= x0); auto.
  - destruct H0, H1; unfold Chain; intros; clear H3.
    assert (forall z, z∈A -> (En_Fs X le z) ∈ (En_FF X A le)).
    { intros; unfold En_FF; apply Axiom_Scheme; split.
      - assert (En_Fs X le z ⊂ X).
        { unfold Subclass; intros; apply Axiom_Scheme in H4; apply H4. }
        unfold PartialOrderSet in H; destruct H; clear H5.
        apply Theorem33 in H4; auto.
      - exists z; split; auto. }
    assert (A ⊂ X); try split; auto.
    { unfold Subclass; intros; unfold Subclass in H0.
      apply H3 in H4; apply H0 in H4; double H4; unfold En_FF in H5.
      apply Axiom_Scheme in H5; destruct H5, H6, H6.
      apply Property_FF with (A:=X) in H6; auto; rewrite H6; auto. }
    unfold PartialOrderSet in H; unfold PartialOrder in H; destruct H.
    destruct H5, H6, H7; unfold TotalOrder.
    split; try (apply Theorem33 with (x:=X); auto).
    unfold PartialOrder; repeat split; auto.
    + apply Theorem33 in H4; auto.
    + destruct H5; unfold Relation in H5; unfold Relation; intros.
      apply Theorem4' in H10; destruct H10; apply H5 in H10; auto.
    + unfold Subclass; intros; apply Theorem4' in H9; apply H9.
    + unfold Reflexivity; intros; unfold Rrelation; apply Theorem4'.
      unfold Reflexivity in H6; double H9; unfold Subclass in H4.
      apply H4 in H10; apply H6 in H10; unfold Rrelation in H10.
      split; auto; unfold Cartesian; apply Axiom_SchemeP; Ens.
    + unfold Antisymmetry in H7; unfold Antisymmetry; intros.
      destruct H9, H10; apply H7; auto; unfold Rrelation in H10, H12.
      apply Theorem4' in H10; apply Theorem4' in H12; destruct H10, H12.
      unfold Rrelation; split; auto.
    + unfold Transitivity in H8; unfold Transitivity; intros.
      destruct H9, H10, H9, H12; assert ((u∈X /\ v∈X /\ w∈X) /\
      Rrelation u le v /\ Rrelation v le w).
      { unfold Subclass in H4; apply H4 in H9; apply H4 in H12.
        apply H4 in H13; repeat split; auto; unfold Rrelation.
        - unfold Rrelation in H10; apply Theorem4' in H10; apply H10.
        - unfold Rrelation in H11; apply Theorem4' in H11; apply H11. }
      apply H8 in H14; unfold Rrelation in H14; clear H8.
      unfold Rrelation; apply Theorem4'; split; auto.
      unfold Cartesian; apply Axiom_SchemeP; Ens.
    + intros; destruct H9; unfold Nest in H1.
      assert ((En_Fs X le x) ∈ (En_FF X A le) /\ (En_Fs X le y) ∈ 
      (En_FF X A le)). { apply H3 in H9; apply H3 in H11; split; auto. }
      apply H1 in H12; clear H1; clear H2; destruct H12.
      * { left; unfold Rrelation; apply Theorem4'; split.
          - apply Property_ProperSubclass in H1; destruct H1.
            + unfold ProperSubclass in H1; destruct H1; clear H2.
              apply Property_Fs in H1; unfold Rrelation in H1; auto.
              unfold PartialOrder; auto.
            + assert ((En_Fs X le x) ∈ (En_FF X A le)).
              { unfold En_FF; apply Axiom_Scheme; double H9.
                apply H3 in H11; split; Ens. }
              apply Property_FF with (A:=A) in H1; auto; contradiction.
          - unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
            apply Theorem49; split; Ens. }
      * { right; unfold Rrelation; apply Theorem4'; split.
          - apply Property_ProperSubclass in H1; destruct H1.
            + unfold ProperSubclass in H1; destruct H1; clear H2.
              apply Property_Fs in H1; unfold Rrelation in H1; auto.
              unfold PartialOrder; auto.
            + assert ((En_Fs X le y) ∈ (En_FF X A le)).
              { unfold En_FF; apply Axiom_Scheme; double H9.
                apply H3 in H11; split; Ens. }
              apply Property_FF with (A:=A) in H1; auto.
              symmetry in H1; contradiction.
          - unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
            apply Theorem49; split; Ens. }
Qed.

Lemma LemmaZ2 : forall A X le y,
  PartialOrderSet X le /\ X ≠ Φ ->
  (BoundU y A X le -> (forall x, x ∈ (En_FF X A le) -> x ⊂ (En_Fs X le y))).
Proof.
  intros; double H.
  unfold BoundU in H0; apply H0 in H2; clear H0; destruct H2, H2.
  unfold En_FF in H1; apply Axiom_Scheme in H1; destruct H1.
  destruct H4 as [a H4], H4; rewrite H4; unfold Subclass; intros.
  unfold En_Fs in H6; unfold En_Fs.
  apply Axiom_Scheme in H6; apply Axiom_Scheme.
  double H5; apply H3 in H5; destruct H6, H8, H; clear H10.
  repeat split; auto; unfold PartialOrderSet, PartialOrder in H.
  destruct H, H10, H11, H12; unfold Transitivity in H13.
  apply H13 with (v:=a); repeat split; auto.
Qed.

Lemma LemmaZ3 : forall X le y,
  PartialOrderSet X le /\ X ≠ Φ ->
  (MaxElement y X le <-> MaxMember (En_Fs X le y) (En_FF X X le)).
Proof.
  intros; destruct H; split; intros.
  - unfold MaxElement in H1; apply H1 in H0; clear H1; destruct H0.
    unfold PartialOrderSet, PartialOrder in H; destruct H.
    unfold MaxMember; intros; clear H3; repeat split; intros.
    + unfold En_FF; apply Axiom_Scheme; split.
      * assert ((En_Fs X le y) ⊂ X).
        { unfold Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
        apply Theorem33 in H3; auto.
      * exists y; split; auto.
    + apply Axiom_Scheme in H3; destruct H3, H4, H4; rewrite H4; intro.
      apply H1 in H5; apply not_and_or in H5; destruct H5.
      * unfold ProperSubclass in H6; destruct H6; clear H7.
        apply Property_Fs in H6; unfold Rrelation in H6; try apply H2; auto.
        unfold PartialOrder; auto.
      * apply NNPP in H5; rewrite H5 in H6; unfold ProperSubclass in H6.
        destruct H6; contradiction.
  - unfold PartialOrderSet, PartialOrder in H; destruct H.
    unfold MaxElement; intros; clear H3.
    unfold MaxMember in H1; assert (En_FF X X le ≠ Φ).
    { apply Property_NotEmpty in H0; destruct H0.
      apply Property_NotEmpty; exists (En_Fs X le x).
      unfold En_FF; apply Axiom_Scheme; split.
      - apply Theorem33 with (x:= X); auto; unfold Subclass; intros.
        unfold En_Fs in H3; apply Axiom_Scheme in H3; apply H3.
      - exists x; split; auto. }
    apply H1 in H3; clear H1; clear H0; destruct H3; double H0.
    unfold En_FF in H3; apply Axiom_Scheme in H3; destruct H3, H4, H4.
    apply Property_FF with (A:= X) in H4; auto; rewrite <- H4 in H5.
    split; intros; auto; assert (En_Fs X le y0 ∈ (En_FF X X le)).
    { unfold En_FF; apply Axiom_Scheme; split.
      - assert (En_Fs X le y0 ⊂ X).
        { unfold Subclass; intros; apply Axiom_Scheme in H7; apply H7. }
        apply Theorem33 in H7; auto.
      - exists y0; split; auto. }
    apply H1 in H7; intro; elim H7; destruct H8.
    unfold ProperSubclass; split.
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
      { unfold Subclass; intros; unfold En_FF in H2.
        apply Axiom_Scheme in H2; destruct H2, H3, H3.
        unfold PowerClass; apply Axiom_Scheme; split; auto.
        rewrite H3; unfold Subclass; intros.
        unfold En_Fs in H5; apply Axiom_Scheme in H5; apply H5. }
      apply Theorem38 in H; auto; apply Theorem33 in H2; auto. }
    apply Max.MaxPrinciple in H2.
    + destruct H2 as [M H2]; double H2; unfold MaxMember in H3.
      assert (En_FF X X le ≠ Φ).
      { apply Property_NotEmpty in H1; destruct H1.
        apply Property_NotEmpty; exists (En_Fs X le x).
        unfold En_FF; apply Axiom_Scheme; split.
        - destruct H; apply Theorem33 with (x:= X); auto.
          unfold Subclass; intros; apply Axiom_Scheme in H5; apply H5.
        - exists x; split; auto. }
      apply H3 in H4; clear H3; destruct H4.
      unfold En_FF in H3; apply Axiom_Scheme in H3; destruct H3.
      destruct H5 as [v H5], H5; rewrite H5 in H2; add (X ≠ Φ) H.
      exists v; apply LemmaZ3 with (y:=v) in H; auto; apply H; auto.
    + intro B; intros; destruct H3.
      generalize (classic (B = Φ)); intros; destruct H5.
      { rewrite H5; apply Property_NotEmpty in H1.
        destruct H1 as [z H1]; exists (En_Fs X le z); split.
        - unfold En_FF; apply Axiom_Scheme; split.
          + destruct H; apply Theorem33 with (x:=X); auto.
            unfold Subclass; intros; apply Axiom_Scheme in H7; apply H7.
          + exists z; split; auto.
        - intros; generalize (Theorem16 u); contradiction. }
      assert ( (En_FF X (En_A X B le) le) ⊂ (En_FF X X le) /\
      Nest (En_FF X (En_A X B le) le) /\ (En_A X B le) ≠ Φ).
      { assert ((En_FF X (En_A X B le) le) ⊂ (En_FF X X le)).
        { intros; unfold Subclass; intros.
          apply Axiom_Scheme in H6; destruct H6, H7 as [a H7], H7.
          apply Axiom_Scheme in H8; destruct H8.
          apply Axiom_Scheme; split; auto.
          unfold Subclass in H3; apply H3 in H9; unfold En_FF in H8.
          double H9; apply Axiom_Scheme in H10; destruct H10, H11 as [a1 H11].
          destruct H11; apply Property_FF with (b:= a1) in H9; auto.
          rewrite H9 in H7; exists a1; auto. }
        repeat split; auto; unfold Nest; intros.
        - destruct H7; apply Axiom_Scheme in H7; apply Axiom_Scheme in H8.
          destruct H7, H8, H9 as [a H9], H10 as [b H10], H9, H10.
          apply Axiom_Scheme in H11; apply Axiom_Scheme in H12.
          destruct H11, H12; rewrite H9, H10.
          unfold Nest in H4; add ((En_Fs X le b) ∈ B) H13.
        - apply Property_NotEmpty in H5; destruct H5; double H5.
          apply H3 in H7; apply Axiom_Scheme in H7; destruct H7, H8, H8.
          rewrite H8 in H5; apply Property_NotEmpty; exists x0.
          apply Axiom_Scheme; split; Ens. }
      double H; apply LemmaZ1 with (A:= (En_A X B le)) in H7.
      apply H7 in H6; clear H7; double H6; apply H0 in H6; clear H0.
      destruct H6 as [y H0]; unfold Chain in H7; double H.
      unfold PartialOrderSet in H6; apply H7 in H6; clear H7.
      destruct H6; exists (En_Fs X le y); split; intros.
      * unfold BoundU in H0; double H; add (X≠Φ) H8; apply H0 in H8.
        clear H0; destruct H8, H8 as [H9 H8]; clear H9.
        unfold En_FF; apply Axiom_Scheme; split.
        -- assert (En_Fs X le y ⊂ X).
           { unfold Subclass; intros; apply Axiom_Scheme in H9; apply H9. }
           destruct H; apply Theorem33 in H9; auto.
        -- exists y; split; auto.
      * double H8; unfold Subclass in H3; apply H3 in H9.
        apply Axiom_Scheme in H9; destruct H9, H10, H10; add (X≠Φ) H.
        apply LemmaZ2 with (A:=En_A X B le)(y:=y)(x:=u) in H; auto.
        apply Axiom_Scheme; split; auto; exists x; split; auto.
        apply Axiom_Scheme; split; Ens; rewrite <- H10; auto.
Qed.

Hint Resolve Zorn : Axiom_of_Choice.

End Zorn_Lemma.
