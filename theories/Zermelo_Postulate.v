Require Export Maximal_Principle.


(** Zermelo Postulate **)

Module Type Zermelo_Postulate.

Declare Module Max : Maximal_Principle.

Definition En_TB B A : Class :=
  \{ λ k, k ⊂ ∪A /\ (forall a, a ∈ (A ~ B) -> a ∩ k = Φ) /\
  (forall a, a ∈ B -> exists x, a ∩ k = [x]) \}.

Definition En_T A : Class :=
  \{ λ k, exists B, B ⊂ A /\ k ∈ (En_TB B A) \}.

Theorem Zermelo : forall A,
  Ensemble A -> Φ ∉ A ->
  (forall x y, x ∈ A /\ y ∈ A -> x ≠ y -> x ∩ y = Φ) ->
  (exists D, Ensemble D /\ (forall B, B ∈ A -> exists x, B ∩ D = [x])).
Proof.
  intros.
  generalize (classic (A = Φ)); intros; destruct H2.
  - rewrite H2 in *; clear H2; exists Φ; split; intros; auto.
    generalize (Theorem16 B); intros; contradiction.
  - assert (Ensemble (En_T A)).
    { apply Axiom_Amalgamation in H; apply Theorem38 in H; auto.
      assert (En_T A ⊂ pow(∪A)).
      { unfold Subclass; intros; apply Axiom_Scheme in H3; destruct H3.
        destruct H4 as [B H4], H4; unfold En_TB in H5.
        apply Axiom_Scheme in H5; destruct H5, H6.
        unfold PowerClass; apply Axiom_Scheme; split; auto. }
      apply Theorem33 in H3; auto. }
    assert (En_T A ≠ Φ).
    { apply Property_NotEmpty in H2; destruct H2.
      generalize (classic (x = Φ)); intros; destruct H4.
      - rewrite H4 in H2; contradiction.
      - apply Property_NotEmpty in H4; destruct H4.
        apply Property_NotEmpty; exists [x0]; unfold En_T.
        AssE x0; apply Theorem42 in H5; auto.
        apply Axiom_Scheme; split; auto; exists [x]; repeat split.
        + unfold Subclass, Singleton; intros; apply Axiom_Scheme in H6.
          destruct H6; rewrite H7; try apply Theorem19; Ens.
        + unfold En_TB; apply Axiom_Scheme; repeat split; auto; intros.
          * unfold Subclass; intros; apply Axiom_Scheme in H6; destruct H6.
            rewrite H7; try apply Theorem19; Ens; apply Axiom_Scheme; Ens.
          * unfold Setminus in H6; apply Theorem4' in H6; destruct H6.
            assert (x ∈ A /\ a ∈ A); auto; apply H1 in H8.
            { generalize (classic (a ∩ [x0] = Φ)); intros; destruct H9; auto.
              apply Property_NotEmpty in H9; destruct H9.
              apply Theorem4' in H9; destruct H9; apply Axiom_Scheme in H10.
              destruct H10; rewrite H11 in *; try apply Theorem19; Ens.
              assert (x0 ∈ (x ∩ a)); try apply Theorem4'; auto.
              rewrite H8 in H12; generalize (Theorem16 x0); contradiction. }
            { intro; rewrite H9 in H7; unfold Complement in H7.
              apply Axiom_Scheme in H7; destruct H7, H10; unfold Singleton.
              apply Axiom_Scheme; split; auto. }
          * exists x0; apply Axiom_Scheme in H6; destruct H6.
            rewrite H7 in *; try apply Theorem19; Ens.
            apply Axiom_Extent; split; intros.
            -- apply Theorem4' in H8; apply H8.
            -- apply Theorem4'; split; auto; apply Axiom_Scheme in H8.
               destruct H8; rewrite H9; try apply Theorem19; Ens. }
    apply Max.MaxPrinciple in H3.
    + destruct H3 as [C H3]; unfold MaxMember in H3.
      apply H3 in H4; clear H3; destruct H4; exists C; split; Ens.
      unfold En_T in H3; apply Axiom_Scheme in H3; destruct H3.
      destruct H5 as [B H5], H5.
      generalize (classic (B = A)); intro; destruct H7.
      * rewrite H7 in H6; apply Axiom_Scheme in H6; apply H6.
      * double H5; apply Property_Φ in H8; assert (A ~ B <> Φ).
        { intro; apply H8 in H9; symmetry in H9; tauto. }
        clear H7 H8; apply Property_NotEmpty in H9; destruct H9.
        unfold Setminus in H7; apply Theorem4' in H7; destruct H7.
        generalize (classic (x = Φ)); intro; destruct H9;
        try (rewrite H9 in H7; contradiction).
        apply Property_NotEmpty in H9; destruct H9.
        assert ((C ∪ [x0]) ∈ (En_T A)).
        { unfold En_T; apply Axiom_Scheme; split.
          - apply Axiom_Union; split; try apply Theorem42; Ens.
          - exists (B ∪ [x]); repeat split.
            + unfold Subclass; intros; apply Theorem4 in H10.
              destruct H10; auto; apply Axiom_Scheme in H10; destruct H10.
              rewrite H11; try apply Theorem19; Ens.
            + apply Axiom_Scheme; repeat split; intros.
              * apply Axiom_Union; split; try apply Theorem42; Ens.
              * unfold Subclass; intros; apply Theorem4 in H10; destruct H10.
                { apply Axiom_Scheme in H6; apply H6 in H10; auto. }
                { apply Axiom_Scheme in H10; destruct H10.
                  rewrite H11; try apply Theorem19; Ens; unfold Element_U.
                  apply Axiom_Scheme; split; Ens. }
              * apply Axiom_Scheme in H6; unfold Setminus in H10.
                apply Theorem4' in H10; destruct H10; rewrite Theorem8.
                apply Axiom_Scheme in H11; destruct H11.
                assert (a ∈ (B ∪ [x]) <-> a ∈ B \/ a ∈ [x]).
                { split; try apply Theorem4. }
                apply definition_not in H13; auto; clear H12.
                apply not_or_and in H13; destruct H13.
                assert (a ∈ (A ~ B)).
                { unfold Setminus; apply Theorem4'; split; auto.
                  unfold Complement; apply Axiom_Scheme; auto. }
                apply H6 in H14; rewrite H14; clear H14.
                assert (x ∈ A /\ a ∈ A); auto; apply H1 in H14.
                { generalize (classic (a ∩ [x0] = Φ)); intros; destruct H15.
                  - rewrite H15; apply Theorem5.
                  - apply Property_NotEmpty in H15; destruct H15.
                    apply Theorem4' in H15; destruct H15.
                    apply Axiom_Scheme in H16; destruct H16.
                    rewrite H17 in *; try apply Theorem19; Ens.
                    assert (x0 ∈ (x ∩ a)); try apply Theorem4'; auto.
                    rewrite H14 in H18; destruct (Theorem16 _ H18). }
                { intro; rewrite H15 in H13; destruct H13; unfold Singleton.
                  apply Axiom_Scheme; split; auto. }
              * apply Axiom_Scheme in H6; rewrite Theorem8.
                apply Theorem4 in H10; destruct H10.
                { double H10; apply H6 in H11; destruct H11; rewrite H11.
                  clear H11; assert (x ∈ A /\ a ∈ A); auto; apply H1 in H11.
                  - generalize (classic (a ∩ [x0] = Φ)); intros; destruct H12.
                    + rewrite H12; rewrite Theorem6, Theorem17; Ens.
                    + apply Property_NotEmpty in H12; destruct H12.
                      apply Theorem4' in H12; destruct H12.
                      apply Axiom_Scheme in H13; destruct H13.
                      rewrite H14 in *; try apply Theorem19; Ens.
                      assert (x0 ∈ (x ∩ a)); try apply Theorem4'; auto.
                      rewrite H11 in H15; destruct (Theorem16 _ H15).
                  - intro; rewrite <- H12 in H10; unfold Complement in H8.
                    apply Axiom_Scheme in H8; destruct H8; contradiction. }
                { apply Axiom_Scheme in H10; destruct H10.
                  rewrite H11; try apply Theorem19; Ens; clear H10 H11 a.
                  assert (x ∈ (A ~ B)); try apply Theorem4'; auto.
                  apply H6 in H10; rewrite H10, Theorem17; exists x0.
                  apply Axiom_Extent; split; intros.
                  - apply Theorem4' in H11; apply H11.
                  - apply Theorem4'; split; auto; apply Axiom_Scheme in H11.
                    destruct H11; rewrite H12; try apply Theorem19; Ens. } }
        apply H4 in H10; destruct H10; unfold ProperSubclass.
        split; unfold Subclass; intros; try (apply Theorem4; auto).
        apply Axiom_Scheme in H6.
        assert (x ∈ (A ~ B)); try apply Theorem4'; auto.
        apply H6 in H10; intro; assert (x0 ∈ Φ).
        { rewrite <- H10; apply Theorem4'; split; auto; rewrite H11.
          apply Theorem4; right; apply Axiom_Scheme; split; Ens. }
        generalize (Theorem16 x0); intros; contradiction.
    + intros; exists (∪n); split; intros.
      * apply Property_FinChar in H5; auto; split; auto; clear H6.
        destruct H5; unfold Finite_Character; repeat split; auto.
        { intros F H7 F1 H8; destruct H8; unfold En_T in H7.
          apply Axiom_Scheme in H7; destruct H7, H10 as [B H10], H10.
          unfold En_T; apply Axiom_Scheme; assert (Ensemble F1).
          { apply Theorem33 in H8; auto. }
          split; auto; unfold En_TB in H11; apply Axiom_Scheme in H11.
          destruct H11 as [_ H11], H11.
          exists \{ λ a, a ∈ B /\ exists x, a ∩ F1 = [x] \}; repeat split.
          - red; intros; apply Axiom_Scheme in H14; destruct H14, H15.
            apply H10 in H15; auto.
          - apply Axiom_Scheme; repeat split; auto; intros.
            + apply Theorem28 with (y:= F); split; auto.
            + apply Theorem4' in H14; destruct H14; apply Axiom_Scheme in H15.
              destruct H15 as [_ H15]; unfold NotIn in H15.
              apply definition_not with (B:= Ensemble a /\ a∈B /\
              (exists x, a ∩ F1 = [x])) in H15.
              * apply not_and_or in H15; destruct H15.
                { destruct H15; Ens. }
                { apply not_and_or in H15; destruct H15.
                  - assert (a ∈ (A ~ B)).
                    { unfold Setminus; apply Theorem4'; split; auto.
                      unfold Complement; apply Axiom_Scheme; split; Ens. }
                    apply H13 in H16; apply Theorem27;split;try apply Theorem26.
                    rewrite <- H16; unfold Subclass; intros.
                    apply Theorem4' in H17; apply Theorem4'; destruct H17; Ens.
                  - generalize (classic (a ∈ B)); intros; destruct H16.
                    + apply H13 in H16; destruct H16.
                      apply not_ex_all_not with (n:= x) in H15.
                      generalize (classic (a∩F1=Φ)); intros; destruct H17; auto.
                      apply Property_NotEmpty in H17; destruct H17 as [z H17].
                      assert ((a ∩ F1) ⊂ [x]).
                      { unfold Subclass; intros; rewrite <- H16.
                        apply Theorem4' in H18; apply Theorem4'; destruct H18.
                        split; auto. }
                      double H17; apply H18 in H19; unfold Singleton in H19.
                      apply Axiom_Scheme in H19; destruct H19.
                      assert ([x] ⊂ (a ∩ F1)).
                      { unfold Subclass; intros; unfold Singleton in H21.
                        apply Axiom_Scheme in H21; destruct H21.
                        assert (Ensemble x).
                        { apply Theorem42'; rewrite <- H16.
                          apply Theorem33 with (x:= a); Ens; unfold Subclass.
                          intros; apply Theorem4' in H23; apply H23. }
                        rewrite H22, <- H20; try apply Theorem19; Ens. }
                      assert ((a ∩ F1) ⊂ [x] /\ [x] ⊂ (a ∩ F1)); auto.
                      apply Theorem27 in H22; rewrite H22 in H15; tauto.
                    + assert (a ∈ (A ~ B)).
                      { unfold Setminus; apply Theorem4'; split; auto.
                        unfold Complement; apply Axiom_Scheme; split; Ens. }
                      apply H13 in H17; apply Theorem27.
                      split; try apply Theorem26; rewrite <- H17.
                      unfold Subclass; intros; apply Theorem4' in H18.
                      apply Theorem4'; destruct H18; Ens. }
              * split; intros; try apply Axiom_Scheme in H16; try apply Axiom_Scheme; Ens.
            + apply Axiom_Scheme in H14; apply H14. }
        { intros; destruct H7.
          generalize (classic (F ∈ (En_T A))); intros; destruct H9; auto.
          assert (forall B, B ⊂ A -> ~ F ∈ (En_TB B A)).
          { intros; unfold En_T in H9.
            apply definition_not with (B:= Ensemble F /\ exists B, B ⊂ A /\
            F ∈ (En_TB B A)) in H9.
            - apply not_and_or in H9; destruct H9; try tauto.
              apply not_ex_all_not with (n:= B) in H9.
              apply not_and_or in H9; tauto.
            - split; intros; try apply Axiom_Scheme; auto.
              apply Axiom_Scheme in H11; apply H11. }
          set (B:= \{ λ a, a ∈ A /\ a ∩ F <> Φ /\ ~ (exists x, a ∩ F = [x]) \}
            ∪ \{ λ a, a ∈ A /\ a ∩ F <> Φ /\ (exists x, a ∩ F = [x]) \}).
          assert (B ⊂ A).
          { unfold Subclass; intros; apply Theorem4 in H11.
            destruct H11; apply Axiom_Scheme in H11; apply H11. }
          apply H10 in H11; unfold En_TB in H11.
          apply definition_not with (B:= Ensemble F /\ F ⊂ ∪ A /\ (forall a, 
          a ∈ (A ~ B) -> a ∩ F = Φ) /\ (forall a, a ∈ B -> exists x,
          a ∩ F = [x])) in H11.
          - apply not_and_or in H11; destruct H11; try tauto.
            apply not_and_or in H11; destruct H11.
            + assert (forall z, z ⊂ F /\ Finite z -> z ⊂ ∪ A).
              { intros; apply H8 in H12; unfold En_T in H12.
                apply Axiom_Scheme in H12; destruct H12, H13, H13.
                unfold En_TB in H14; apply Axiom_Scheme in H14; apply H14. }
              destruct H11; unfold Subclass; intros.
              assert ([z] ⊂ F /\ Finite ([z])).
              { split; try apply Finite_Single; Ens; unfold Subclass; intros.
                unfold Singleton in H13; apply Axiom_Scheme in H13; destruct H13.
                rewrite H14; try apply Theorem19; Ens. }
              apply H12 in H13; apply H13; unfold Singleton.
              apply Axiom_Scheme; split; Ens.
            + apply not_and_or in H11; destruct H11.
              * apply not_all_ex_not in H11; destruct H11 as [a H11].
                apply imply_to_and in H11; destruct H11.
                unfold Setminus in H11; apply Theorem4' in H11; destruct H11.
                apply Axiom_Scheme in H13; destruct H13.
                unfold NotIn in H14; apply definition_not with (B:= a ∈ 
                \{λ a, a∈A /\ a ∩ F <> Φ /\ ~ (exists x, a ∩ F = [x])\} \/
                a ∈ \{ λ a, a ∈ A /\ a ∩ F <> Φ /\ (exists x, a ∩ F = [x]) \})
                in H14.
                { apply not_or_and in H14; destruct H14.
                  apply definition_not with (B:= Ensemble a /\ a ∈ A /\
                  a ∩ F <> Φ /\ ~ (exists x, a ∩ F = [x])) in H14.
                  - apply definition_not with (B:= Ensemble a /\ a ∈ A /\
                    a ∩ F <> Φ /\ (exists x, a ∩ F = [x])) in H15; try tauto.
                    split; intros; try apply Axiom_Scheme; auto.
                    apply Axiom_Scheme in H16; auto.
                  - split; intros; try apply Axiom_Scheme; auto.
                    apply Axiom_Scheme in H16; auto. }
                { split; intros; try apply Theorem4; auto. }
              * apply not_all_ex_not in H11; destruct H11 as [a H11].
                apply imply_to_and in H11; destruct H11.
                apply Theorem4 in H11; destruct H11.
                { apply Axiom_Scheme in H11; clear B H12; destruct H11,H12,H13.
                  assert (~ (forall x y, x ∈ (a ∩ F) /\ y ∈ (a ∩ F) -> x = y)).
                  { intro; apply Property_NotEmpty in H13; destruct H13, H14.
                    exists x; apply Axiom_Extent; split; intros.
                    - add (x ∈ (a ∩ F)) H14; apply H15 in H14; rewrite H14.
                      unfold Singleton; apply Axiom_Scheme; Ens.
                    - unfold Singleton in H14; apply Axiom_Scheme in H14.
                      destruct H14; rewrite H16; try apply Theorem19; Ens. }
                  destruct H15; intros; destruct H15.
                  generalize (classic (x = y)); intros; destruct H17; auto.
                  apply Theorem4' in H15; apply Theorem4' in H16.
                  destruct H15, H16.
                  assert ([x|y] ⊂ F /\ Finite ([x|y])).
                  { split.
                    - unfold Subclass; intros; apply Theorem46 in H20; Ens.
                      destruct H20; rewrite H20; auto.
                    - unfold Unordered; apply Theorem168.
                      split; apply Finite_Single; Ens. }
                  apply H8 in H20; apply Axiom_Scheme in H20.
                  destruct H20, H21 as [B H21], H21; unfold En_TB in H22.
                  apply Axiom_Scheme in H22; destruct H22, H23.
                  generalize (classic (a ∈ B)); intros; destruct H25.
                  - apply H24 in H25; destruct H25.
                    assert ([x | y] ⊂ a).
                    { unfold Subclass; intros; apply Theorem46 in H26; Ens.
                      destruct H26; rewrite H26; auto. }
                    apply Theorem30 in H26; rewrite Theorem6' in H26.
                    rewrite H26 in H25; clear H26; destruct H17.
                    assert (x ∈ [x0] /\ y ∈ [x0]).
                    { rewrite <- H25; split; apply Theorem46; Ens. }
                    destruct H17; apply Axiom_Scheme in H17.
                    apply Axiom_Scheme in H26; destruct H17, H26.
                    assert (x0 ∈ μ).
                    { apply Theorem19; apply Theorem42'; rewrite <- H25.
                      apply Theorem46; Ens. }
                    rewrite H27, H28; auto.
                  - assert (a ∈ (A ~ B)).
                    { unfold Setminus; apply Theorem4'; split; auto.
                      unfold Complement; apply Axiom_Scheme; split; Ens. }
                    apply H24 in H26. clear H24.
                    assert ([x | y] ⊂ a).
                    { unfold Subclass; intros; apply Theorem46 in H24; Ens.
                      destruct H24; rewrite H24; auto. }
                    apply Theorem30 in H24; rewrite Theorem6' in H24.
                    rewrite H24 in H26; clear H24.
                    assert (x ∈ Φ). { rewrite <- H26; apply Theorem46; Ens. }
                    generalize (Theorem16 x); intros; contradiction. }
                { apply Axiom_Scheme in H11; destruct H11, H13, H14; tauto. }
          - split; intros; try apply Axiom_Scheme;
            try apply Axiom_Scheme in H12; auto. }
      * unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
Qed.

Hint Resolve Zermelo : Axiom_of_Choice.

End Zermelo_Postulate.

