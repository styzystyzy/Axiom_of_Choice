Require Export Zorn_Lemma.


(** Well-Ordering Principle **)

Module Type WellOrdering_Theorem.

Declare Module Zorn : Zorn_Lemma.

Definition En_L X := \{\ λ Y le, Y ⊂ X /\ Y ≠ Φ /\ WellOrder le Y\}\.

Definition lee X: Class :=
  \{\ λ L1 L2, (L1 ∈ (En_L X) /\ L2 ∈ (En_L X)) /\
  (forall x y, x∈(First L1) /\ y∈(First L1) ->
  (Rrelation x (Second L1) y <-> Rrelation x (Second L2) y)) /\
  Initial_Segment (First L1) (First L2) (Second L2) \}\.

Definition En_Z K := \{ λ x, exists Y le, [Y,le] ∈ K /\ x∈Y \}.

Definition leeq K : Class :=
  \{\ λ u v, exists Y le, [Y,le] ∈ K /\ u∈Y /\ v∈Y /\ Rrelation u le v \}\.

Definition leep Y le x :=
  \{\ λ y1 y2, (y1∈Y /\ y2∈Y /\ Rrelation y1 le y2)\/(y1∈(Y∪[x])/\ y2=x) \}\.

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

Lemma LemmaW1 : forall X, Ensemble X -> PartialOrder (lee X) (En_L X).
Proof.
  intros.
  unfold PartialOrder; repeat split.
  - assert (Ensemble (pow(X)× pow(X×X))).
    { double H; apply Theorem38 in H0; auto; apply Theorem74.
      split; auto; apply Theorem38; auto; apply Theorem74; auto. }
    apply Theorem33 with (x:= pow(X)× pow(X×X)); auto.
    unfold Subclass; intros; PP H1 Y0 le0; apply Axiom_SchemeP in H2.
    destruct H2, H3, H4; unfold WellOrder in H5; destruct H5; clear H6.
    unfold TotalOrder in H5; destruct H5; clear H6.
    unfold PartialOrder in H5; destruct H5, H6, H6.
    unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
    + unfold PowerClass; apply Axiom_Scheme; split; auto.
    + unfold PowerClass; apply Axiom_Scheme; split; auto.
      * apply Theorem33 in H8; auto; apply Theorem74; auto.
      * unfold Subclass; intros; apply H8 in H9; PP H9 u v.
        apply Axiom_SchemeP in H10; destruct H10, H11.
        apply Axiom_SchemeP; repeat split; auto.
  - unfold Relation; intros; PP H0 x y; Ens.
  - unfold Subclass; intros; PP H0 u v; apply Axiom_SchemeP in H1.
    destruct H1, H2, H2; apply Axiom_SchemeP; auto.
  - unfold Reflexivity; intros; double H0; unfold En_L in H1.
    PP H1 u v; unfold Rrelation, lee; apply Axiom_SchemeP.
    assert (Ensemble ([u,v])). { Ens. }
    split; try apply Theorem49; auto; apply Theorem49 in H3.
    apply Theorem54 in H3; destruct H3; rewrite H3, H4; clear H3 H4.
    split; Ens; split; intros.
    + split; intros; auto.
    + unfold Initial_Segment; split; try (unfold Subclass; auto).
      apply Axiom_SchemeP in H2; destruct H2, H3, H4.
      split; try apply H5; intros; apply H6.
  - unfold Antisymmetry; intros; destruct H1.
    unfold Rrelation, lee in H1, H2; apply Axiom_SchemeP in H1.
    apply Axiom_SchemeP in H2; destruct H1, H2, H3, H4; clear H2 H3 H4.
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
    clear x y; apply Axiom_Extent; split; intros.
    + double H9; unfold Subclass in H8; apply H8 in H10.
      PP H10 x y; apply Axiom_SchemeP in H11; destruct H11.
      apply H1 in H12; unfold Rrelation in H12; apply H12; auto.
    + double H9; unfold Subclass in H8; apply H6 in H10.
      PP H10 x y; apply Axiom_SchemeP in H11; destruct H11.
      apply H3 in H12; unfold Rrelation in H12; apply H12; auto.
  - clear H; unfold Transitivity; intros; destruct H, H0.
    elim H; intros; destruct H3; unfold En_L in H2, H3, H4.
    PP H2 Y1 le1; PP H3 Y2 le2; PP H4 Y3 le3; clear H H2 H3 H4 H5 H6 H7.
    unfold Rrelation; unfold lee; apply Axiom_SchemeP.
    unfold Rrelation in H0, H1; unfold lee in H0, H1.
    apply Axiom_SchemeP in H0; apply Axiom_SchemeP in H1; destruct H0,H1; split.
    + apply Theorem49 in H; apply Theorem49 in H1; destruct H, H1.
      apply Theorem49; split; auto.
    + apply Property_lee in H; apply Property_lee in H1.
      destruct H, H1, H3, H4, H5, H6; clear H1 H4.
      rewrite H, H3, H5, H7 in H0; rewrite H5, H6, H7, H8 in H2.
      rewrite H, H3, H6, H8; clear H H3 H5 H7 H6 H8; destruct H0, H2.
      destruct H, H1; split; auto; clear H H1 H3 H4; destruct H0, H2.
      unfold Initial_Segment in H0, H2; destruct H0, H2, H3, H4; split; intros.
      * elim H7; intros; unfold Subclass in H0; apply H0 in H8.
        apply H0 in H9; add (y ∈ Y2) H8; clear H9; apply H1 in H8.
        apply H in H7; split; intros; tauto.
      * double H0; add (Y2 ⊂ Y3) H7; apply Theorem28 in H7.
        unfold Initial_Segment; repeat split; try apply H4; auto; intros.
        apply H5 with (v:=v0); destruct H8, H9; assert (u0 ∈ Y2).
        { apply H6 with (v:=v0); unfold Subclass in H0.
          apply H0 in H9; repeat split; auto. }
        repeat split; auto; unfold Subclass in H0; apply H0 in H9.
        add (v0 ∈ Y2) H11; apply H1 in H11; apply H11; auto.
Qed.

Lemma LemmaW2 : forall (X K : Class),
  Ensemble X -> Chain K (En_L X) (lee X) -> WellOrder (leeq K) (En_Z K).
Proof.
  intros; double H.
  unfold Chain in H0; apply (LemmaW1 X) in H1; apply H0 in H1.
  clear H0; destruct H1; unfold WellOrder; split.
  - unfold TotalOrder; split; intros.
    { unfold PartialOrder; repeat split.
      - assert ((En_Z K) ⊂ X).
        { unfold Subclass; intros; unfold En_Z in H2.
          apply Axiom_Scheme in H2; destruct H2, H3 as [Y [le H3]], H3.
          destruct H0; unfold Subclass in H0; apply H0 in H3.
          unfold En_L in H3; apply Axiom_SchemeP in H3; destruct H3, H6.
          unfold Subclass in H6; apply H6 in H4; auto. }
        apply Theorem33 in H2; auto.
      - unfold Relation; intros; PP H2 Y0 le0; Ens.
      - unfold Subclass; intros; PP H2 Y0 le0; apply Axiom_SchemeP in H3.
        destruct H3, H4 as [Y1 [le1 H4]], H4, H5, H6; apply Axiom_SchemeP.
        repeat split; try (apply Axiom_Scheme; split); Ens.
      - unfold Reflexivity; intros; unfold En_Z in H2; apply Axiom_Scheme in H2.
        unfold Rrelation, leeq; apply Axiom_SchemeP; destruct H2.
        destruct H3 as [Y [le H3]], H3; split; try apply Theorem49; auto.
        exists Y, le; repeat split; auto; unfold Subclass in H0.
        apply H0 in H3; unfold En_L in H3; apply Axiom_SchemeP in H3.
        destruct H3, H5; unfold WellOrder in H6; destruct H6; clear H6.
        destruct H7; clear H7; unfold TotalOrder in H6; destruct H6; clear H7.
        unfold PartialOrder in H6; destruct H6, H7, H8; clear H9.
        unfold Reflexivity in H8; apply H8; auto.
      - unfold Antisymmetry; intros; destruct H3; apply Axiom_SchemeP in H3.
        apply Axiom_SchemeP in H4; destruct H3, H4; clear H4.
        destruct H5 as [Y1 [le1 H5]], H6 as [Y2 [le2 H6]].
        destruct H5, H6, H5, H7, H8, H9.
        generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H12.
        + assert (Ensemble ([Y1,le1])). { Ens. }
          apply Theorem49 in H13; apply Theorem55 in H12; auto.
          clear H13; destruct H12; rewrite H13 in H10; clear H12.
          clear H13; destruct H0; clear H12; unfold Subclass in H0.
          apply H0 in H6; apply Axiom_SchemeP in H6; destruct H6, H12, H13.
          unfold WellOrder in H14; destruct H14; clear H15.
          unfold TotalOrder in H14; destruct H14; clear H15.
          unfold PartialOrder in H14; destruct H14, H15, H16, H17.
          unfold Antisymmetry in H17; apply H17; auto.
        + assert ([Y1, le1] ∈ K /\ [Y2, le2] ∈ K). { Ens. }
          clear H2; unfold TotalOrder in H1; destruct H1.
          apply H2 in H13; auto; clear H2 H12; destruct H13.
          * unfold Rrelation in H2; apply Theorem4' in H2; destruct H2.
            clear H12; unfold lee in H2; apply Axiom_SchemeP in H2; destruct H2.
            apply Property_lee in H2; destruct H2, H13, H14.
            rewrite H2, H13, H14, H15 in H12; clear H2 H13 H14 H15.
            destruct H12, H12; apply H12 in H10; auto; clear H2 H12 H13.
            destruct H0; unfold Subclass in H0; apply H0 in H6.
            apply Axiom_SchemeP in H6; destruct H6, H12, H13.
            unfold WellOrder in H14; destruct H14; clear H15.
            unfold TotalOrder in H14; destruct H14; clear H15.
            unfold PartialOrder in H14; destruct H14, H15, H16, H17.
            unfold Antisymmetry in H17; apply H17; auto.
          * unfold Rrelation in H2; apply Theorem4' in H2; destruct H2.
            clear H12; unfold lee in H2; apply Axiom_SchemeP in H2; destruct H2.
            apply Property_lee in H2; destruct H2, H13, H14.
            rewrite H2, H13, H14, H15 in H12; clear H2 H13 H14 H15.
            destruct H12, H12; apply H12 in H10; auto; clear H2 H12 H13.
            destruct H0; unfold Subclass in H0; apply H0 in H6.
            apply Axiom_SchemeP in H6; destruct H6, H12, H13.
            unfold WellOrder in H14; destruct H14; clear H15.
            unfold TotalOrder in H14; destruct H14; clear H15.
            unfold PartialOrder in H14; destruct H14, H15, H16, H17.
            unfold Antisymmetry in H17; apply H17; auto.
      - unfold Transitivity; intros; destruct H2; clear H2; destruct H3.
        unfold Rrelation, leeq in H2, H3; apply Axiom_SchemeP in H2.
        apply Axiom_SchemeP in H3; destruct H2, H3; destruct H4 as [Y1[le1 H4]].
        destruct H5 as [Y2 [le2 H5]], H4, H5, H6, H7, H8, H9.
        generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H12.
        + assert (Ensemble ([Y1, le1])); Ens.
          apply Theorem49 in H13; apply Theorem55 in H12; auto.
          clear H13; destruct H12; rewrite H12 in H6; rewrite H13 in H10.
          unfold Rrelation, leeq; apply Axiom_SchemeP; split.
          * apply Theorem49; Ens.
          * exists Y2, le2; repeat split; auto.
            unfold Subclass in H0; apply H0 in H5; unfold En_L in H5.
            apply Axiom_SchemeP in H5; destruct H5, H14, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitivity in H19; apply H19 with (v:=v); auto.
        + unfold TotalOrder in H1; destruct H1; apply H13 in H12; auto.
          clear H13; destruct H12.
          * unfold Rrelation, lee in H12; apply Theorem4' in H12; destruct H12.
            clear H13; apply Axiom_SchemeP in H12; destruct H12.
            apply Property_lee in H12; destruct H12, H14, H15.
            rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
            destruct H13, H13, H14; clear H15; unfold Rrelation, leeq.
            apply Axiom_SchemeP; split; try (apply Theorem49; Ens).
            exists Y2, le2; repeat split; auto; double H6.
            add (v∈Y1) H15; apply H13 in H15; apply H15 in H10; clear H13 H15.
            unfold Subclass in H0; apply H0 in H5; unfold En_L in H5.
            apply Axiom_SchemeP in H5; destruct H5, H13, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitivity in H19; apply H19 with (v:=v); auto.
          * unfold Rrelation, lee in H12; apply Theorem4' in H12; destruct H12.
            clear H13; apply Axiom_SchemeP in H12; destruct H12.
            apply Property_lee in H12; destruct H12, H14, H15.
            rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
            destruct H13, H13, H14; clear H15; unfold Rrelation, leeq.
            apply Axiom_SchemeP; split; try (apply Theorem49; Ens).
            exists Y1, le1; repeat split; auto; double H7.
            add (w∈Y2) H15; apply H13 in H15; apply H15 in H11; clear H13 H15.
            unfold Subclass in H0; apply H0 in H4; unfold En_L in H4.
            apply Axiom_SchemeP in H4; destruct H4, H13, H15 as [H16 H15].
            clear H16; unfold WellOrder in H15; destruct H15; clear H16.
            unfold TotalOrder in H15; destruct H15; clear H16.
            unfold PartialOrder in H15; destruct H15, H16, H17, H18.
            unfold Transitivity in H19; apply H19 with (v:=v); auto. }
    { unfold En_Z in H2; destruct H2.
      apply Axiom_Scheme in H2; apply Axiom_Scheme in H4.
      destruct H2, H4, H5 as [Y1 [le1 H5]], H6 as [Y2 [le2 H6]], H5, H6.
      generalize (classic ([Y1, le1] = [Y2, le2])); intros; destruct H9.
      - assert (Ensemble ([Y1, le1])). { Ens. }
        apply Theorem49 in H10; apply Theorem55 in H9; auto.
        clear H10; destruct H9; rewrite H9 in H7; clear H9 H10; double H6.
        unfold Subclass in H0; apply H0 in H9; unfold En_L in H9.
        apply Axiom_SchemeP in H9; destruct H9, H10; clear H9; clear H10.
        destruct H11 as [H12 H11]; clear H12; unfold WellOrder in H11.
        destruct H11; clear H10; unfold TotalOrder in H9; destruct H9.
        clear H9; double H7; add (y∈Y2) H9; apply H10 in H9; auto.
        clear H10 H3; destruct H9.
        + left; unfold Rrelation, leeq; apply Axiom_SchemeP.
          split; try apply Theorem49; Ens.
          exists Y2, le2; repeat split; auto.
        + right; unfold Rrelation, leeq; apply Axiom_SchemeP.
          split; try apply Theorem49; Ens.
          exists Y2, le2; repeat split; auto.
      - unfold TotalOrder in H1; destruct H1; apply H10 in H9; auto.
        clear H10; destruct H9.
        + unfold Rrelation, lee in H9; apply Theorem4' in H9; destruct H9.
          clear H10; apply Axiom_SchemeP in H9; destruct H9.
          apply Property_lee in H9; destruct H9, H11, H12.
          rewrite H9, H11, H12, H13 in H10; clear H9 H11 H12 H13.
          destruct H10; clear H9; destruct H10, H10, H11.
          clear H12; unfold WellOrder in H11; destruct H11.
          clear H12; unfold TotalOrder in H11; destruct H11.
          unfold Subclass in H10; apply H10 in H7; double H7.
          add (y∈Y2) H13; apply H12 in H13; auto; clear H12; destruct H13.
          * left; unfold Rrelation, leeq; apply Axiom_SchemeP.
            split; try apply Theorem49; Ens.
            exists Y2, le2; repeat split; auto.
          * right; unfold Rrelation, leeq; apply Axiom_SchemeP.
            split; try apply Theorem49; Ens.
            exists Y2, le2; repeat split; auto.
        + unfold Rrelation, lee in H9; apply Theorem4' in H9; destruct H9.
          clear H10; apply Axiom_SchemeP in H9; destruct H9.
          apply Property_lee in H9; destruct H9, H11, H12.
          rewrite H9, H11, H12, H13 in H10; clear H9 H11 H12 H13.
          destruct H10; clear H9; destruct H10, H10, H11.
          clear H12; unfold WellOrder in H11; destruct H11.
          clear H12; unfold TotalOrder in H11; destruct H11.
          unfold Subclass in H10; apply H10 in H8; double H7.
          add (y∈Y1) H13; apply H12 in H13; auto; clear H12; destruct H13.
          * left; unfold Rrelation, leeq; apply Axiom_SchemeP.
            split; try apply Theorem49; Ens.
            exists Y1, le1; repeat split; auto.
          * right; unfold Rrelation, leeq; apply Axiom_SchemeP.
            split; try apply Theorem49; Ens.
            exists Y1, le1; repeat split; auto. }
  - intro P; intros; destruct H2; apply Property_NotEmpty in H3.
    destruct H3 as [p H3]; double H3; unfold Subclass in H2.
    apply H2 in H4; clear H2; unfold En_Z in H4; apply Axiom_Scheme in H4.
    destruct H4, H4 as [Y [le H4]], H4; clear H2; double H4.
    apply H0 in H4; unfold En_L in H4; apply Axiom_SchemeP in H4.
    destruct H4, H6; clear H4; clear H6; unfold WellOrder in H7.
    destruct H7; clear H4; assert ((Y ∩ P) ⊂ Y /\ (Y ∩ P) ≠ Φ).
    { split.
      - unfold Subclass; intros; apply Theorem4' in H4; apply H4.
      - apply Property_NotEmpty; exists p; apply Theorem4'; auto. }
    clear H3; clear H5; elim H4; intros; apply H6 in H4; clear H6.
    clear H3; destruct H4 as [q H3]; unfold MinElement in H3.
    apply H3 in H5; clear H3; destruct H5; apply Theorem4' in H3.
    destruct H3; exists q; unfold MinElement; split; auto; clear H6.
    intro r; intros; intro; unfold Rrelation in H7; destruct H7.
    unfold leeq in H7; apply Axiom_SchemeP in H7; destruct H7.
    clear H7; destruct H9 as [Y1 [le1 H7]], H7, H9, H10.
    unfold TotalOrder in H1; destruct H1; unfold Connect in H11.
    generalize (classic ([Y,le] = [Y1,le1])); intros; destruct H13.
    + assert (Ensemble ([Y, le])). { Ens. }
      apply Theorem49 in H14; apply Theorem55 in H13; auto.
      clear H14; destruct H13; rewrite <- H13 in H9; rewrite H14 in H4.
      apply H4 with (y:=r); try apply Theorem4'; auto.
    + apply H12 in H13; auto; clear H12; destruct H13.
      * unfold Rrelation in H12; apply Theorem4' in H12; destruct H12.
        clear H13; unfold lee in H12; apply Axiom_SchemeP in H12.
        destruct H12; apply Property_lee in H12; destruct H12, H14, H15.
        rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
        destruct H13; unfold Initial_Segment in H13; destruct H13, H14.
        assert (r∈Y1 /\ q∈Y /\ Rrelation r le1 q).
        { repeat split; auto. } apply H15 in H16; clear H15.
        apply H4 with (y:=r); try apply Theorem4'; auto.
        split; auto; apply H13; auto.
      * unfold Rrelation in H12; apply Theorem4' in H12; destruct H12.
        clear H13; unfold lee in H12; apply Axiom_SchemeP in H12.
        destruct H12; apply Property_lee in H12; destruct H12, H14, H15.
        rewrite H12, H14, H15, H16 in H13; clear H12 H14 H15 H16.
        destruct H13; unfold Initial_Segment in H13; destruct H13, H14.
        clear H15; double H9; unfold Subclass in H14; apply H14 in H15.
        apply H4 with (y:=r); try apply Theorem4'; auto.
        split; auto; apply H13; auto.
Qed.

Lemma LemmaW3 : forall (K X: Class),
  Ensemble X -> Chain K (En_L X) (lee X) -> exists y, BoundU y K (En_L X) (lee X).
Proof.
  intros; double H; double H0.
  apply LemmaW2 in H0; auto; exists ([(En_Z K),(leeq K)]).
  unfold Chain in H2; apply (LemmaW1 X) in H1; apply H2 in H1.
  clear H2; destruct H1; unfold BoundU; intros; destruct H3.
  assert ([En_Z K, leeq K] ∈ (En_L X)).
  { unfold En_L; apply Axiom_SchemeP; split.
    - apply Theorem49; split.
      + assert ((En_Z K) ⊂ X).
        { unfold Subclass; intros; unfold En_Z in H5.
          apply Axiom_Scheme in H5; destruct H5, H6 as [Y [le H6]], H6.
          unfold Subclass in H1; apply H1 in H6; unfold En_L in H6.
          apply Axiom_SchemeP in H6; destruct H6, H8; auto. }
        apply Theorem33 in H5; auto.
      + assert ((leeq K) ⊂ X × X ).
        { unfold Subclass; intros; unfold leeq in H5.
          PP H5 u v; apply Axiom_SchemeP in H6; destruct H6.
          destruct H7 as [Y [le H7]], H7, H8, H9.
          unfold Subclass in H1; apply H1 in H7; unfold En_L in H7.
          apply Axiom_SchemeP in H7; destruct H7, H11; unfold Subclass in H11.
          apply H11 in H8; apply H11 in H9; unfold Cartesian.
          apply Axiom_SchemeP; repeat split; auto. }
        assert (Ensemble X /\ Ensemble X). { auto. }
        apply Theorem74 in H6; apply Theorem33 in H5; auto.
    - split.
      + unfold Subclass; intros; unfold En_Z in H5.
        apply Axiom_Scheme in H5; destruct H5, H6 as [Y [le H6]], H6.
        unfold Subclass in H1; apply H1 in H6; unfold En_L in H6.
        apply Axiom_SchemeP in H6; destruct H6, H8; auto.
      + split; try apply H0; destruct H1; apply Property_NotEmpty in H5.
        destruct H5; apply Property_NotEmpty; double H5.
        unfold Subclass in H1; apply H1 in H6; PP H6 Y0 le0.
        apply Axiom_SchemeP in H7; destruct H7, H8, H9.
        apply Property_NotEmpty in H9; destruct H9.
        exists x0; unfold En_Z; apply Axiom_Scheme; split; Ens. }
  repeat split; auto; try apply H1; intros.
  double H6; unfold Subclass in H1; apply H1 in H7.
  double H7; unfold En_L in H8; PP H8 Y1 le1; clear H9.
  unfold Rrelation; unfold lee; apply Axiom_SchemeP.
  assert (Ensemble ([Y1,le1]) /\ Ensemble ([En_Z K,leeq K])). { Ens. }
  split; try apply Theorem49; auto; destruct H9.
  apply Theorem49 in H9; apply Theorem54 in H9; destruct H9.
  apply Theorem49 in H10; apply Theorem54 in H10; destruct H10.
  rewrite H9, H10, H11, H12; clear H9; clear H10; clear H11; clear H12.
  clear H3; clear H4; split; auto; split; intros.
  - destruct H3; split; intros.
    + unfold Rrelation, leeq; apply Axiom_SchemeP.
      split; try apply Theorem49; Ens.
      exists Y1, le1; repeat split; auto.
    + unfold Rrelation, leeq in H9; apply Axiom_SchemeP in H9.
      destruct H9, H10 as [Y2 [le2 H10]], H10, H11, H12, H2.
      generalize (classic ([Y1,le1] = [Y2,le2])); intros; destruct H15.
      * assert (Ensemble ([Y1, le1])). { Ens. }
        apply Theorem49 in H16; apply Theorem55 in H15; auto.
        clear H16; destruct H15; rewrite H16; auto.
      * apply H14 in H15; auto; clear H14; destruct H15.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply Axiom_SchemeP in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14; clear H16.
           clear H17; clear H18; destruct H15, H15; apply H15; auto.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply Axiom_SchemeP in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14; clear H16.
           clear H17; clear H18; destruct H15, H15; apply H15; auto.
  - unfold Initial_Segment; split.
    + unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
    + split; try apply H0; intros; destruct H3, H4.
      unfold Rrelation, leeq in H9; apply Axiom_SchemeP in H9.
      destruct H9, H10 as [Y2 [le2 H10]], H10, H11, H12, H2.
      generalize (classic ([Y1,le1] = [Y2,le2])); intros; destruct H15.
      * assert (Ensemble ([Y1, le1])). { Ens. }
        apply Theorem49 in H16; apply Theorem55 in H15; auto.
        clear H16; destruct H15; rewrite H15; auto.
      * apply H14 in H15; auto; clear H14; destruct H15.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply Axiom_SchemeP in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14 H16 H17 H18.
           destruct H15; clear H14; unfold Initial_Segment in H15.
           destruct H15, H15, H16; apply H17 with (v:=v); auto.
        -- unfold Rrelation in H14; apply Theorem4' in H14; destruct H14.
           clear H15; unfold lee in H14; apply Axiom_SchemeP in H14.
           destruct H14; apply Property_lee in H14; destruct H14, H16, H17.
           rewrite H14, H16, H17, H18 in H15; clear H14 H16 H17 H18.
           destruct H15; clear H14; unfold Initial_Segment in H15.
           destruct H15, H15; auto.
Qed.

Theorem WellOrdering : forall (X: Class),
  Ensemble X -> exists le: Class, WellOrder le X.
Proof.
  intros.
  assert (PartialOrderSet (En_L X) (lee X)).
  { unfold PartialOrderSet; try apply LemmaW1; auto. }
  double H0; apply Zorn.Zorn in H1; intros; try apply LemmaW3; auto.
  destruct H1 as [Y H1]; unfold MaxElement in H1.
  generalize (classic (X = Φ)); intros; destruct H2.
  { rewrite H2; exists Φ; unfold WellOrder; split; intros.
    - unfold TotalOrder; split; intros.
      + unfold PartialOrder; repeat split; intros.
        * apply Theorem33 with (x:=X); auto; unfold Subclass; intros.
          generalize (Theorem16 z); intros; contradiction.
        * unfold Relation; intros.
          generalize (Theorem16 z); intros; contradiction.
        * unfold Subclass; intros.
          generalize (Theorem16 z); intros; contradiction.
        * unfold Reflexivity; intros.
          generalize (Theorem16 a); intros; contradiction.
        * unfold Antisymmetry; intros; destruct H3.
          generalize (Theorem16 x); intros; contradiction.
        * unfold Transitivity; intros; destruct H3, H3.
          generalize (Theorem16 u); intros; contradiction.
      + destruct H3; generalize (Theorem16 x); contradiction.
    - destruct H3; generalize (Theorem26 A); intros.
      absurd (A = Φ); auto; apply Theorem27; auto. }
  assert (En_L X ≠ Φ).
  { apply Property_NotEmpty in H2; destruct H2.
    apply Property_NotEmpty; exists ([[x],leq ([x])]).
    unfold En_L; apply Axiom_SchemeP; repeat split; intros.
    - assert (Ensemble ([x])). { apply Theorem42; Ens. }
      apply Theorem49; split; auto.
      apply Theorem33 with (x:= ([x])×([x])); auto.
      + apply Theorem74; auto.
      + unfold Subclass; intros; PP H4 a b; unfold leq in H5.
        apply Axiom_SchemeP in H5; destruct H5, H6, H7.
        unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
    - unfold Subclass; intros; unfold Singleton in H3.
      apply Axiom_Scheme in H3; destruct H3; rewrite H4; auto.
      apply Theorem19; Ens.
    - apply Property_NotEmpty; exists x; apply Axiom_Scheme; Ens.
    - apply Theorem33 with (x:=X); auto; unfold Subclass; intros.
      unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
      rewrite H4; auto; apply Theorem19; Ens.
    - unfold Relation; intros; PP H3 a b; exists a, b; auto.
    - unfold Subclass; intros; PP H3 a b; unfold leq in H4.
      apply Axiom_SchemeP in H4; destruct H4, H5, H6.
      unfold Cartesian; apply Axiom_SchemeP; repeat split; auto.
    - unfold Reflexivity; intros; unfold Rrelation, leq.
      apply Axiom_SchemeP; repeat split; auto; apply Theorem49; Ens.
    - unfold Antisymmetry; intros; destruct H3.
      unfold Singleton in H3, H5; apply Axiom_Scheme in H3.
      apply Axiom_Scheme in H5; destruct H3, H5.
      rewrite H6, H7; try apply Theorem19; Ens.
    - unfold Transitivity; intros; destruct H3, H3, H5.
      apply Axiom_Scheme in H3; apply Axiom_Scheme in H6; destruct H3, H6.
      rewrite H7, H8; try apply Theorem19; Ens.
      unfold Rrelation, leq; apply Axiom_SchemeP; repeat split; auto.
      + apply Theorem49; split; Ens.
      + unfold Singleton; apply Axiom_Scheme; Ens.
      + unfold Singleton; apply Axiom_Scheme; Ens.
    - destruct H3; apply Axiom_Scheme in H3; apply Axiom_Scheme in H5.
      destruct H3, H5; rewrite H6, H7 in H4; try apply Theorem19; Ens.
      contradiction.
    - destruct H3; apply Property_NotEmpty in H4; destruct H4.
      exists x0; unfold MinElement; intros; split; auto; intros.
      intro; destruct H7; unfold Rrelation, leq in H7.
      apply Axiom_SchemeP in H7; destruct H7, H9, H10.
      rewrite H11 in H8; contradiction. }
  apply H1 in H3; clear H1 H2; destruct H3.
  unfold En_L in H1; PP H1 Y0 le0; apply Axiom_SchemeP in H3.
  destruct H3, H4, H5; apply Property_ProperSubclass in H4; destruct H4.
  - double H4; unfold ProperSubclass in H7; destruct H7; clear H8.
    apply Property_ProperSubclass' in H4; destruct H4, H4.
    assert (([Y0∪[x],(leep Y0 le0 x)]) ∈ (En_L X)).
    { unfold WellOrder in H6; destruct H6; unfold TotalOrder in H6; destruct H6.
      double H6; unfold PartialOrder in H11; destruct H11 as [H12 H11].
      clear H12; destruct H11; apply Axiom_SchemeP; repeat split; intros.
      - apply Theorem49 in H3; destruct H3; apply Theorem49; split.
        + apply Axiom_Union; split; auto; apply Theorem42; Ens.
        + assert ((leep Y0 le0 x) ⊂ le0∪(X×X)).
          { unfold Subclass; intros; PP H14 y1 y2; apply Axiom_SchemeP in H15.
            destruct H15; apply Theorem4; destruct H16.
            - left; destruct H16, H17; auto.
            - right; unfold Cartesian; apply Axiom_SchemeP; destruct H16.
              rewrite H17; repeat split; try apply Theorem49; Ens.
              apply Theorem4 in H16; destruct H16; auto.
              unfold Singleton in H16; apply Axiom_Scheme in H16; destruct H16.
              rewrite H18; auto; apply Theorem19; Ens. }
          apply Theorem33 in H14; auto; apply Axiom_Union; split; auto.
          apply Theorem74; auto.
      - unfold Subclass; intros; apply Theorem4 in H13; destruct H13.
        + unfold Subclass in H7; apply H7 in H13; auto.
        + unfold Singleton in H13; apply Axiom_Scheme in H13; destruct H13.
          rewrite H14; auto; apply Theorem19; Ens.
      - apply Property_NotEmpty in H5; destruct H5.
        apply Property_NotEmpty; exists x0; apply Theorem4; tauto.
      - apply Theorem33 with (x:=X); auto; unfold Subclass; intros.
        apply Theorem4 in H13; destruct H13; auto; unfold Singleton in H13.
        apply Axiom_Scheme in H13; destruct H13; rewrite H14; auto.
        apply Theorem19; Ens.
      - unfold Relation; intros; unfold leep in H13; PP H13 y1 y2; Ens.
      - unfold Subclass; intros; PP H13 y1 y2; apply Axiom_SchemeP in H14.
        destruct H14; apply Axiom_SchemeP; split; auto; destruct H15.
        + destruct H15, H16; split; try apply Theorem4; auto.
        + destruct H15; split; auto; rewrite H16; apply Theorem4.
          right; unfold Singleton; apply Axiom_Scheme; Ens.
      - unfold Reflexivity; intros; unfold Rrelation, leep; apply Axiom_SchemeP.
        split; try apply Theorem49; Ens; apply Theorem4 in H13; destruct H13.
        + left; repeat split; auto; destruct H12.
          unfold Reflexivity in H12; auto.
        + right; unfold Singleton in H13.
          apply Axiom_Scheme in H13; destruct H13.
          rewrite H14; try apply Theorem19; Ens; split; auto.
          apply Theorem4; right; apply Axiom_Scheme; Ens.
      - unfold Antisymmetry; intros; clear H13; destruct H14.
        unfold Rrelation, leep in H13, H14; apply Axiom_SchemeP in H13.
        apply Axiom_SchemeP in H14; destruct H13, H14, H15, H16.
        + destruct H15, H16, H17, H18, H12, H21; clear H22.
          unfold Antisymmetry in H21; apply H21; auto.
        + destruct H15, H16; rewrite H18 in H15; contradiction.
        + destruct H15, H16; rewrite H17 in H16; contradiction.
        + destruct H15, H16; rewrite H17, H18; auto.
      - clear H11; destruct H12; clear H11; destruct H12; unfold Transitivity.
        intros; unfold Transitivity in H12; destruct H13, H14, H13, H16.
        unfold Rrelation; apply Axiom_SchemeP; split; try apply Theorem49; Ens.
        unfold Rrelation, leep in H14, H15; apply Axiom_SchemeP in H14.
        apply Axiom_SchemeP in H15; destruct H14, H15, H18, H19.
        + left; destruct H18, H19, H20, H21; repeat split; auto.
          apply H12 with (v:=v); auto.
        + right; destruct H19; split; auto.
        + destruct H18, H19; rewrite H20 in H19; contradiction.
        + right; destruct H19; split; auto.
      - destruct H13; apply Theorem4 in H13.
        apply Theorem4 in H15; destruct H13, H15.
        + double H13; add (y∈Y0) H16; apply H10 in H16; auto.
          clear H10; destruct H16.
          * left; unfold Rrelation, leep; apply Axiom_SchemeP.
            repeat split; try apply Theorem49; Ens.
          * right; unfold Rrelation, leep; apply Axiom_SchemeP.
            repeat split; try apply Theorem49; Ens.
        + left; unfold Rrelation, leep; apply Axiom_SchemeP.
          split; try apply Theorem49; Ens; right; split.
          * apply Theorem4; tauto.
          * apply Axiom_Scheme in H15; destruct H15; apply H16.
            apply Theorem19; Ens.
        + right; unfold Rrelation, leep; apply Axiom_SchemeP.
          split; try apply Theorem49; Ens; right; split.
          * apply Theorem4; tauto.
          * apply Axiom_Scheme in H13; destruct H13; apply H16.
            apply Theorem19; Ens.
        + left; unfold Rrelation, leep; apply Axiom_SchemeP.
          split; try apply Theorem49; Ens; right; split.
          * apply Theorem4; tauto.
          * apply Axiom_Scheme in H15; destruct H15; apply H16.
            apply Theorem19; Ens.
      - destruct H13; assert (A ⊂ Y0 \/ (exists B, B⊂Y0 /\ A = B∪[x])).
        { generalize (classic (x ∈ A)); intros; destruct H15.
          - right; exists (A ~ [x]); split.
            + unfold Subclass; intros; unfold Setminus in H16.
              apply Axiom_Scheme in H16; destruct H16, H17.
              unfold Complement in H18; apply Axiom_Scheme in H18; destruct H18.
              unfold NotIn in H19; unfold Subclass in H13; apply H13 in H17.
              apply Theorem4 in H17; tauto.
            + unfold Setminus; apply Axiom_Extent; split; intros.
              * unfold Subclass in H13; double H16; apply H13 in H17.
                apply Theorem4; apply Theorem4 in H17; destruct H17; try tauto.
                left; apply Theorem4'; split; auto; unfold Complement.
                apply Axiom_Scheme; split; Ens; unfold NotIn; intro.
                apply Axiom_Scheme in H18; destruct H18.
                rewrite H19 in H17; try contradiction; try apply Theorem19; Ens.
              * apply Theorem4 in H16; destruct H16.
                -- apply Theorem4' in H16; apply H16.
                -- apply Axiom_Scheme in H16; destruct H16; rewrite H17; auto.
                   apply Theorem19; Ens.
          - left; unfold Subclass; intros; unfold Subclass in H13.
            double H16; apply H13 in H17; apply Theorem4 in H17.
            destruct H17; auto; apply Axiom_Scheme in H17; destruct H17.
            rewrite H18 in H16; try contradiction; apply Theorem19; Ens. }
        destruct H15.
        + double H15; add (A≠Φ) H16; apply H9 in H16; clear H9.
          destruct H16; exists x0; unfold MinElement in H9.
          apply H9 in H14; clear H9; destruct H14; unfold MinElement; intros.
          split; auto; intros; apply H14 in H17; intro; elim H17; clear H17.
          destruct H18; split; auto; unfold Rrelation, leep in H17.
          apply Axiom_SchemeP in H17; destruct H17, H19; try apply H19.
          destruct H19; rewrite H20 in H9; apply H15 in H9; contradiction.
        + destruct H15 as [B H15], H15.
          generalize (classic (B = Φ)); intros; destruct H17.
          * rewrite H17 in H16; rewrite Theorem17 in H16; clear H17.
            rewrite H16; exists x; unfold MinElement; intros; split; intros.
            -- unfold Singleton; apply Axiom_Scheme; split; Ens.
            -- unfold Singleton in H18; apply Axiom_Scheme in H18; destruct H18.
               intro; destruct H20; rewrite H19 in H21; try contradiction.
               apply Theorem19; Ens.
          * rewrite H16; double H15; add (B≠Φ) H18; clear H16; apply H9 in H18.
            clear H9; destruct H18; exists x0; unfold MinElement in H9.
            apply H9 in H17; clear H9; destruct H17; unfold MinElement; intros.
            clear H17; split; try (apply Theorem4; tauto); intros.
            apply Theorem4 in H17; destruct H17.
            -- apply H16 in H17; intro; elim H17; clear H17.
               destruct H18; split; auto; unfold Rrelation, leep in H17.
               apply Axiom_SchemeP in H17; destruct H17, H19; try apply H19.
               destruct H19; rewrite H20 in H9; apply H15 in H9; contradiction.
            -- intro; destruct H18; apply Axiom_Scheme in H17; destruct H17.
               rewrite H20 in H18, H19; try apply Theorem19; Ens.
               apply Axiom_SchemeP in H18; destruct H18, H21, H21.
               ++ destruct H22; contradiction.
               ++ contradiction. }
    double H9; apply H2 in H10; elim H10; clear H10; split.
    + unfold Rrelation, lee; apply Axiom_SchemeP.
      assert (Ensemble ([[Y0,le0],[Y0∪[x],leep Y0 le0 x]])).
      { apply Theorem49; Ens. } split; auto.
      apply Property_lee in H10; destruct H10, H11, H12.
      rewrite H10, H11, H12, H13; clear H10 H11 H12 H13.
      split; try (split; auto; apply Axiom_SchemeP; Ens); split; intros.
      * split; intros.
        -- destruct H10; unfold Rrelation, leep; apply Axiom_SchemeP.
           split; try apply Theorem49; Ens; try tauto.
        -- unfold Rrelation, leep in H11; apply Axiom_SchemeP in H11.
           destruct H11; destruct H12, H12; try apply H13.
           destruct H10; rewrite H13 in H14; contradiction.
      * unfold Initial_Segment; split.
        -- unfold Subclass; intros; apply Theorem4; tauto.
        -- unfold En_L in H9; apply Axiom_SchemeP in H9; destruct H9, H10, H11.
           split; try apply H12; intros; destruct H13, H14.
           unfold Rrelation, leep; apply Axiom_SchemeP in H15; destruct H15.
           destruct H16; try apply H16; destruct H16.
           rewrite H17 in H14; contradiction.
    + intro; apply Theorem49 in H3; apply Theorem55 in H10; auto.
      destruct H10; elim H8; rewrite H10; apply Theorem4; right.
      apply Axiom_Scheme; split; Ens.
  - rewrite H4 in H6; exists le0; auto.
Qed.

Hint Resolve WellOrdering : Axiom_of_Choice.

End WellOrdering_Theorem.
