Require Export Hausdorff_Maximal_Principle.


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
  (forall n, n⊂A /\ Nest n -> exists N, N∈A /\ (forall u, u∈n -> u⊂N))  ->
  exists M, MaxMember M A.
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
  apply not_and_or in H11; destruct H11.
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