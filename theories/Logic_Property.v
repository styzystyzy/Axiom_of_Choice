Require Export Classical.

(** Some basic logic properties **)

Module Property.

Lemma Lemma_xy : forall (x y: Prop), x -> y -> x /\ y.
Proof. intros; split; auto. Qed.

Lemma Lemma_x : forall x: Prop, x -> x /\ x.
Proof. intros; split; auto. Qed.

Ltac double H := apply Lemma_x in H; destruct H.

Ltac add y H:= apply (Lemma_xy _ y) in H; auto.

Lemma definition_not : forall (A B: Prop), (A<->B) -> (~ A) -> (~ B).
Proof. unfold not; intros; apply H in H1; apply H0 in H1; auto. Qed.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Hint Resolve Lemma_xy Lemma_x definition_not : set.

End Property.

Export Property.
