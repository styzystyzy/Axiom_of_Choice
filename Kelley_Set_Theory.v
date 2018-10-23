(* This document only provides the definition and theorem that we needed in the Axiom_of_Choice.v, and the complete Coq proof of Kelley axiomatic set theory can contact with stycyj@bupt.edu.cn. *)

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

Axiom property_not : forall (x y: Prop),
  (~ (x /\ y) <-> (~x) \/ (~y)) /\ (~ (x \/ y) <-> (~x) /\ (~y)).

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Hint Resolve Lemma_xy Lemma_x definition_not property_not : set.

End Property.

Export Property.


(** The foramlization of axiomatic set theory **)


Module AxiomaticSetTheory.

Parameter Class : Type.


(* ∈：belongs to. x∈y : In x y. *)

Parameter In : Class -> Class -> Prop.

Notation "x ∈ y" := (In x y) (at level 10).


(* I Axiom of extent : For each x and each y it is true that
x = y if and only if for each z, z∈x when and only when z∈y. *)

Axiom AxiomI : forall x y, x = y <-> (forall z, z∈x <-> z∈y).

Hint Resolve AxiomI : set.


(* Definition1 : x is a set iff for some y, x∈y. *)

Definition Ensemble x : Prop := exists y, x∈y.

Ltac Ens := unfold Ensemble; eauto.

Ltac AssE x := assert (Ensemble x); Ens.

Hint Unfold Ensemble : set.


(* II Classiferification axiom-scheme : For each b, b ∈ {a : P A} if and only if b is a set and P b. *)

(* {...:...} *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).

Axiom AxiomII : forall b P,
  b ∈ \{ P \} <-> Ensemble b /\ (P b).

Hint Resolve AxiomII : set.


(* Definition2 : x∪y = {z:z∈x or z∈y}. *)

Definition Union x y : Class := \{ λ z, z∈x \/ z∈y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

Hint Unfold Union : set.


(* Definition3 :  x∩y = {z:z∈x and z∈y}. *)

Definition Intersection x y : Class := \{ λ z, z∈x /\ z∈y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60).

Hint Unfold Intersection : set.


(* Theorem4 :  z∈x∪y iff z∈x or z∈y, z∈x∩y iff z∈x and z∈y. *)

Theorem Theorem4 : forall (x y: Class) (z: Class),
  z∈x \/ z∈y <-> z∈(x ∪ y).
Proof.
  intros; split; intros.
  - unfold Union; apply AxiomII; split; auto.
    destruct H; Ens.
  - unfold Union in H; apply AxiomII in H; apply H.
Qed.

Theorem Theorem4' : forall (x y: Class) (z: Class),
  z∈x /\ z∈y <-> z∈(x ∩ y).
Proof.
  intros; unfold Intersection; split; intros.
  - apply AxiomII; split; auto; destruct H; Ens.
  - apply AxiomII in H; apply H.
Qed.

Hint Resolve Theorem4 Theorem4' : set.


(* Theorem5 : x∪x=x and x∩x=x. *)

Theorem Theorem5 : forall (x: Class), x ∪ x = x.
Proof.
  intros.
  apply AxiomI; split; intros.
  - apply Theorem4 in H; destruct H; auto.
  - apply Theorem4; left; apply H.
Qed.

Theorem Theorem5' : forall (x: Class), x ∩ x = x.
Proof.
  intros.
  apply AxiomI; split; intros.
  - apply Theorem4' in H; apply H.
  - apply Theorem4'; split; apply H.
Qed.

Hint Rewrite Theorem5 Theorem5' : set.


(* Theorem6 : x∪y=y∪x and x∩y=y∩x. *)

Theorem Theorem6 : forall (x y: Class), x ∪ y = y ∪ x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4 in H; apply Theorem4; tauto.
  - apply Theorem4 in H; apply Theorem4; tauto.
Qed.

Theorem Theorem6' : forall (x y: Class), x ∩ y = y ∩ x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4' in H; apply Theorem4'; tauto.
  - apply Theorem4' in H; apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem6 Theorem6' : set.


(* Theorem7 : (x∪y)∪z=x∪(y∪z) and (x∩y)∩z=x∩(y∩z). *)

Theorem Theorem7 : forall (x y z: Class),
  (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros.
  apply AxiomI; split; intro.
  - apply Theorem4 in H; apply Theorem4; destruct H.
    + apply Theorem4 in H; destruct H; try tauto.
      right; apply Theorem4; auto.
    + right; apply Theorem4; auto.
  - apply Theorem4 in H; apply Theorem4; destruct H.
    + left; apply Theorem4; auto.
    + apply Theorem4 in H; destruct H; try tauto.
      left; apply Theorem4; auto.
Qed.

Theorem Theorem7' : forall (x y z: Class),
  (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros.
  apply AxiomI; split; intro.
  - apply Theorem4' in H; destruct H.
    apply Theorem4' in H; destruct H.
    apply Theorem4'; split; auto.
    apply Theorem4'; split; auto.
  - apply Theorem4' in H; destruct H.
    apply Theorem4' in H0; destruct H0.
    apply Theorem4'; split; auto.
    apply Theorem4'; split; auto.
Qed.

Hint Rewrite Theorem7 Theorem7' : set.


(* Theorem8 : x∩(y∪z)=(x∩y)∪(x∩z) and x∪(y∩z)=(x∪y)∩(x∪z). *)

Theorem Theorem8 : forall (x y z: Class),
  x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4; apply Theorem4' in H; destruct H.
    apply Theorem4 in H0; destruct H0.
    + left; apply Theorem4'; split; auto.
    + right; apply Theorem4'; split; auto.
  - apply Theorem4 in H; apply Theorem4'; destruct H.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; left; auto.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; right; auto.
Qed.

Hint Rewrite Theorem8 : set.


(* Definition9 : x∉y iff it is false that x∈y. *)

Definition NotIn x y : Prop := ~ x∈y.

Notation "x ∉ y" := (NotIn x y) (at level 10).

Hint Unfold NotIn : set.


(* Definition10 : ~x={y:y∉x}. *)

Definition Complement x : Class := \{ λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

Hint Unfold Complement : set.


(* Definition13 : x~y=x∩(~y). *)

Definition Setminus x y : Class := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

Hint Unfold Setminus : set.


(* Definition15 : 0={x:x≠x}. *)

Notation "x ≠ y" := (x <> y) (at level 70).

Definition Φ : Class := \{ λ x, x ≠ x \}.

Hint Unfold Φ : set.


(* Theorem16 : x∉0. *)

Theorem Theorem16 : forall (x: Class), x ∉ Φ.
Proof.
  intros; unfold NotIn; intro.
  unfold Φ in H; apply AxiomII in H.
  destruct H; apply H0; auto.
Qed.

Hint Resolve Theorem16 : set.


(* 定理17  Φ∪x=x同时Φ∩x=Φ *)

Theorem Theorem17 : forall x, Φ ∪ x = x.
Proof.
  intros; apply AxiomI; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    generalize (Theorem16 z); contradiction.
  - apply Theorem4; tauto.
Qed.

Hint Rewrite Theorem17 : set.


(* Definition18 : u={x:x=x}, the class u is the universe. *)

Definition μ : Class := \{ λ x, x = x \}.

Lemma Property_μ : forall (x y: Class),
  x ∪ (¬ x) = μ.
Proof.
  intros.
  apply AxiomI; split; intros.
  - unfold μ; apply AxiomII; split; auto.
    unfold Ensemble; exists (x ∪ ¬ x); auto.
  - unfold μ in H; apply AxiomII in H; destruct H.
    generalize (classic (z∈x)); intros.
    destruct H1; apply Theorem4; try tauto.
    right; apply AxiomII; split; auto.
Qed.

Hint Unfold μ : set.
Hint Resolve Property_μ : set.


(* Theorem19 : x∈u iff x is a set. *)

Theorem Theorem19 : forall (x: Class),
  x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intro.
  - unfold μ in H; apply AxiomII in H; apply H.
  - unfold μ; apply AxiomII; split; auto.
Qed.

Hint Resolve Theorem19 : set.


(* Theorem20 : x∪μ=μ and x∩μ=x. *)

Theorem Theorem20 : forall (x: Class), x ∪ μ = μ.
Proof.
  intros.
  apply AxiomI; split; intro.
  - apply Theorem4 in H; destruct H; auto.
    apply Theorem19; Ens.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem20' : forall (x: Class), x ∩ μ = x.
Proof.
  intros.
  apply AxiomI; split; intro.
  - apply Theorem4' in H; apply H.
  - apply Theorem4'; split; auto.
    apply Theorem19; Ens.
Qed.

Hint Resolve Theorem20 Theorem20' : set.


(* Definition22 : ∩x={z:for each y, if y∈x, then z∈y}. *) 

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

Hint Unfold Element_I : set.


(* Definition23 : ∪x={z:for some y, z∈y and y∈x}. *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

Hint Unfold Element_U : set.


(* 定理24  ∩Φ=μ同时∪Φ=Φ *)

Theorem Theorem24 : ∩ Φ = μ.
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem19; Ens.
  - apply AxiomII; apply Theorem19 in H; split; auto.
    intros; generalize (Theorem16 y); contradiction.
Qed.

Theorem Theorem24' : ∪ Φ = Φ.
Proof.
  intros; apply AxiomI; split; intro.
  - apply AxiomII in H; destruct H, H0, H0.
    generalize (Theorem16 x); contradiction.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem24 Theorem24' : set. 


(* Definition25 : x⊂y iff for each z, if z∈x, then z∈y. *)

Definition Included x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Included x y) (at level 70).

Hint Unfold Included : set.


(* Theorem26 : Φ⊂x and x⊂μ. *)

Theorem Theorem26 : forall (x: Class), Φ ⊂ x.
Proof.
  intros.
  unfold Included; intros.
  generalize (Theorem16 z); intro; contradiction.
Qed.

Theorem Theorem26' : forall x, x ⊂ μ.
Proof.
  intros; unfold Included; intros; apply Theorem19; Ens.
Qed.

Hint Resolve Theorem26 Theorem26' : set.


(* Theorem27 : x=y iff x⊂y and y⊂x. *)

Theorem Theorem27 : forall (x y: Class),
  (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  intros; split; intros.
  - unfold Included in H; destruct H.
    apply AxiomI; split; auto.
  - rewrite <- H; unfold Included; split; auto.
Qed.

Hint Resolve Theorem27 : set.


(* Theorem28 : If x⊂y and y⊂z, then x⊂z. *)

Theorem Theorem28 : forall (x y z: Class),
  x ⊂ y /\ y ⊂ z -> x ⊂ z.
Proof.
  intros; destruct H; unfold Included; intros.
  unfold Included in H1; auto.
Qed.

Hint Resolve Theorem28 : set.


(* Theorem29 : x⊂y iff x∪y=y. *)

Theorem Theorem29 : forall (x y: Class),
  x ∪ y = y <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Included; intros.
    apply AxiomI with (z:=z) in H; apply H.
    apply Theorem4; left; auto.
  - apply AxiomI; split; intros.
    + apply Theorem4 in H0; elim H0; intros; auto.
    + apply Theorem4; tauto.
Qed.

Hint Resolve Theorem29 : set.


(* Theorem32 : If x∈y, x⊂∪y and ∩y⊂x. *)

Theorem Theorem32 : forall (x y: Class),
  x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros; split.
  - unfold Included; intros.
    apply AxiomII; split; Ens.
  - unfold Included; intros.
    apply AxiomII in H0; destruct H0.
    apply H1 in H; auto.
Qed.

Hint Resolve Theorem32 : set.


(* III Axiom of subsets : If x is a set there is a set y such that for each z, if z⊂x, then z∈y. *)

Axiom AxiomIII : forall (x: Class),
  Ensemble x -> exists y, Ensemble y /\ (forall z, z⊂x -> z∈y).

Hint Resolve AxiomIII : set.


(* Theorem33 : If x is a set and z⊂x, then z is a set. *)

Theorem Theorem33 : forall (x z: Class),
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros.
  apply AxiomIII in H; destruct H.
  apply H in H0; Ens.
Qed.

Hint Resolve Theorem33 : set.


(* 定理35  如果x≠0，则∩x是一个集 *)

Lemma Property_NotEmpty : forall x, x ≠ Φ <-> exists z, z∈x.
Proof.
  intros; assert (x = Φ <-> ~ (exists y, y∈x)).
  { split; intros.
    - intro; destruct H0; rewrite H in H0.
      apply AxiomII in H0; destruct H0; case H1; auto.
    - apply AxiomI; split; intros.
      + elim H; exists z; auto.
      + generalize (Theorem16 z); contradiction. }
  split; intros.
  - apply definition_not with (B:= ~(exists y, y∈x)) in H0; auto.
    apply NNPP in H0; destruct H0; exists x0; auto.
  - apply definition_not with (A:=(~ (exists y, y∈x))); auto.
    destruct H; split; auto.
Qed.

Theorem Theorem35 : forall x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros; apply Property_NotEmpty in H; destruct H; AssE x0.
  generalize (Theorem32 x0 x H); intros.
  destruct H1; apply Theorem33 in H2; auto.
Qed.

Hint Resolve Property_NotEmpty Theorem35 : set.


(* Definition36 : 2*x = {y:y⊂x}. *)

Definition PowerSet x : Class := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerSet x) (at level 0, right associativity).

Hint Unfold PowerSet : set.


(* Theorem38 : If x is a set, pow(x) is a set. *)

Theorem Theorem38 : forall (x y: Class),
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros; split.
  - apply AxiomIII in H; destruct H, H.
    assert (pow(x) ⊂ x0).
    { unfold Included; intros.
      unfold PowerSet in H1; apply AxiomII in H1.
      destruct H1; apply H0 in H2; auto. }
    apply Theorem33 in H1; auto.
  - split; intros.
    + apply Theorem33 with (z:=y) in H; auto.
      apply AxiomII; split; auto.
    + apply AxiomII in H0; apply H0.
Qed.

Hint Resolve Theorem38 : set.


(* Theorem39 : μ is not a set. *)

Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  generalize (classic (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \})).
  intros; destruct H.
  - double H; apply AxiomII in H; destruct H; contradiction.
  - intro; elim H; apply AxiomII; split; auto.
Qed.

Theorem Theorem39 : ~ Ensemble μ.
Proof.
  unfold not; generalize Lemma_N; intros.
  generalize (Theorem26' \{ λ x, x ∉ x \}); intros.
  apply Theorem33 in H1; auto.
Qed.

Hint Resolve Lemma_N Theorem39 : set.

Hint Resolve Theorem39 : set.


(* Definition40 : {x}={z : if x∈u, then z=x}. *)

Definition Singleton x : Class := \{ λ z, x∈μ -> z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Hint Unfold Singleton : set.


(* Theorem42 : If x is a set, then, for each y, y∈{x} iff y=x. *)

Theorem Theorem42 : forall (x: Class),
  Ensemble x -> Ensemble [x].
Proof.
  intros.
  apply Lemma_x in H; elim H; intros.
  apply Theorem33 with (x:= pow(x)); auto.
  - apply Theorem38 in H0; auto.
  - unfold Included; intros.
    apply Theorem38 with (y:= z) in H0; auto.
    elim H0; intros; apply H4.
    unfold Singleton in H2.
    apply AxiomII in H2; elim H2; intros.
    rewrite H6; unfold Included; auto.
    apply Theorem19; auto.
Qed.

Hint Resolve Theorem42 : set.


(* Theorem43 : {x}=μ iff x is not a set. *)

Theorem Theorem43 : forall (x: Class),
  [x] = μ <-> ~Ensemble x.
Proof.
  intros; split; intros.
  - unfold not; intros.
    apply Theorem42 in H0; auto.
    rewrite H in H0; generalize Theorem39; intros.
    absurd (Ensemble μ); auto.
  - generalize (Theorem19 x); intros; unfold Singleton.
    apply definition_not with (B:= x∈μ) in H; try tauto.
    apply AxiomI; split; intros.
    + apply AxiomII in H1; elim H1; intros.
      apply Theorem19; auto.
    + apply AxiomII; split; intros.
      apply Theorem19 in H1; auto.
      absurd (x∈μ); auto.
Qed.

Hint Rewrite Theorem43 : set.


(* Theorem42' : If {x} is a set, x is a set. *)

Theorem Theorem42' : forall x, Ensemble [x] -> Ensemble x.
Proof.
  intros.
  generalize (classic (Ensemble x)); intros.
  destruct H0; auto; generalize (Theorem39); intros.
  apply Theorem43 in H0; auto.
  rewrite H0 in H; contradiction.
Qed.

Hint Resolve Theorem42' : set.


(* IV Axiom of union : If x is a set and y is a set so is x∪y. *)

Axiom AxiomIV : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble (x∪y).

Lemma AxiomIV': forall (x y: Class),
  Ensemble (x∪y) -> Ensemble x /\ Ensemble y.
Proof.
  intros; split.
  - assert (x ⊂ (x∪y)).
    { unfold Included; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
  - assert (y ⊂ (x∪y)).
    { unfold Included; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
Qed.

Hint Resolve AxiomIV AxiomIV' : set.


(* Definition45 : {xy}={x}∪{y}. *)

Definition Unordered x y : Class := [x]∪[y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

Hint Unfold Unordered : set.


(* Theorem46 : If x is a set and y is a set, then {xy} is a set and z∈{xy} iff z=x or z=y; {xy}=μ if and only if x is not a set or y is not a set. *)

Theorem Theorem46 : forall (x y: Class) (z: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x|y] /\ (z∈[x|y] <-> (z=x \/ z=y)).
Proof.
  intros.
  unfold Unordered; split.
  - apply AxiomIV; elim H; intros; split.
    + apply Theorem42 in H0; auto.
    + apply Theorem42 in H1; auto.
  - split; intros.
    + apply Theorem4 in H0; elim H0; intros.
      * unfold Singleton in H1; apply AxiomII in H1.
        elim H1; intros; left; apply H3.
        apply Theorem19; apply H.
      * unfold Singleton in H1; apply AxiomII in H1.
        elim H1; intros; right; apply H3.
        apply Theorem19; apply H.
    + apply Theorem4; elim H0; intros.
      * left; unfold Singleton; apply AxiomII.
        split; try (rewrite H1; apply H); intro; apply H1.
      * right; unfold Singleton; apply AxiomII.
        split; try (rewrite H1; apply H); intro; apply H1.
Qed.

Hint Resolve Theorem46 : set.


(* Theorem47 : If x and y are sets, then ∩{xy}=x∩y and ∪{xy}=x∪y. *)

Theorem Theorem47 : forall x y,
  Ensemble x /\ Ensemble y -> (∩[x|y] = x ∩ y) /\ (∪[x|y] = x ∪ y).
Proof.
  intros; split; apply AxiomI; intros.
  - split; intros.
    + apply Theorem4'.
      split; apply AxiomII in H0; destruct H0; apply H1; apply Theorem4.
      * left; apply AxiomII; split; try apply H; auto.
      * right; apply AxiomII; split; try apply H; auto.
    + apply Theorem4' in H0; destruct H0.
      apply AxiomII; split; intros; try AssE z.
      apply Theorem4 in H2; destruct H2.
      * apply AxiomII in H2; destruct H2; destruct H.
        apply Theorem19 in H; apply H4 in H; rewrite H; auto.
      * apply AxiomII in H2; destruct H2; destruct H.
        apply Theorem19 in H5; apply H4 in H5; rewrite H5; auto.
  - split; intros.
    + apply AxiomII in H0; destruct H0; destruct H1; destruct H1.
      apply Theorem4 in H2; apply Theorem4.
      destruct H2; apply AxiomII in H2; destruct H2.
      * left; destruct H; apply Theorem19 in H.
        apply H3 in H; rewrite H in H1; auto.
      * right; destruct H; apply Theorem19 in H4.
        apply H3 in H4; rewrite H4 in H1; auto.
    + apply Theorem4 in H0; apply AxiomII.
      split; destruct H0; try AssE z.
      * exists x; split; auto; apply Theorem4; left.
        apply AxiomII; split; try apply H; trivial.
      * exists y; split; auto; apply Theorem4; right.
        apply AxiomII; split; try apply H; trivial.
Qed.

Hint Resolve Theorem47 : set.


(* Definition48 : (x,y)={{x}{y}}. *)

Definition Ordered x y : Class := [ [x] | [x|y] ].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

Hint Unfold Ordered : set.


(* Theorem49 : (x,y) is a set if and only if x is a set and y is a set. *)

Theorem Theorem49 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble x /\ Ensemble y.
Proof.
  intros; split; intro.
  - unfold Ordered in H; unfold Unordered in H.
    apply AxiomIV' in H; elim H; intros.
    apply Theorem42' in H0; auto.
    apply Theorem42' in H0; auto.
    apply Theorem42' in H1; auto; split; auto.
    unfold Unordered in H1; apply AxiomIV' in H1.
    elim H1; intros; apply Theorem42' in H3; auto.
  - elim H; intros; unfold Ordered; unfold Unordered.
    apply AxiomIV; split.
    + apply Theorem42; auto; apply Theorem42; auto.
    + apply Theorem42; auto; apply Theorem46; auto.
Qed.

Hint Resolve Theorem49 : set.


(* Theorem50 : If x and y are sets, then ∪(x,y)={xy}, ∩(x,y)={x}, ∪∩(x,y)=x, ∩∩(x,y)=x, ∪∪(x,y)=x∪y, ∩∪(x,y)=x∩y. *)

Lemma Lemma50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x] /\ Ensemble [x | y].
Proof.
  intros.
  apply Theorem49 in H; auto.
  unfold Ordered in H; unfold Unordered in H.
  apply AxiomIV' in H; elim H; intros.
  apply Theorem42' in H0; auto.
  apply Theorem42' in H1; auto.
Qed.

Theorem Theorem50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\
  (∪(∩[x,y]) = x) /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\
  (∩(∪[x,y]) = x∩y).
Proof.
  intros; elim H; intros.
  repeat unfold Ordered; apply Lemma50 in H.
  apply Theorem47 in H; auto; elim H; intros; repeat split.
  - rewrite H3; apply AxiomI; split; intros.
    + apply Theorem4 in H4; elim H4; intros.
      * unfold Unordered; apply Theorem4; left; apply H5.
      * apply H5.
    + apply Theorem4; right; apply H4.
  - rewrite H2; apply AxiomI; split; intros.
    + apply Theorem4' in H4; apply H4.
    + apply Theorem4'; split; auto.
      unfold Unordered; apply Theorem4; left; apply H4.
  - rewrite H2; apply AxiomI; split; intros.
    + apply AxiomII in H4; elim H4; intros.
      elim H6; intros; elim H7; intros.
      apply Theorem4' in H9; elim H9; intros.
      unfold Singleton in H10; apply AxiomII in H10.
      elim H10; intros; rewrite <- H13. apply H8.
      apply Theorem19; apply H0.
    + apply AxiomII; split.
      * unfold Ensemble; exists x; apply H4.
      * exists x; split. apply H4.
        apply Theorem4'; split.
        -- unfold Singleton; apply AxiomII; split; auto.
        -- unfold Unordered; apply Theorem4.
           left; unfold Singleton; apply AxiomII.
           split; try apply H0; trivial.
  - rewrite H2; apply AxiomI; split; intros.
    + apply AxiomII in H4; elim H4; intros.
      apply H6; apply Theorem4'; split.
      * unfold Singleton; apply AxiomII; split; auto.
      * unfold Unordered; apply Theorem4.
        left; unfold Singleton; apply AxiomII; split; auto.
    + apply AxiomII; split.
      * unfold Ensemble; exists x; apply H4.
      * intros; apply Theorem4' in H5; elim H5; intros.
        unfold Singleton in H6; apply AxiomII in H6.
        elim H6; intros;  rewrite H9. 
        apply H4. apply Theorem19; apply H0.
  - rewrite H3; apply AxiomI; split; intros.
    + apply Theorem4; apply AxiomII in H4; elim H4; intros.
      elim H6; intros; elim H7; intros.
      apply Theorem4 in H9; elim H9; intros.
      * unfold Singleton in H10; apply AxiomII in H10.
        elim H10; intros; left; rewrite <- H12; try apply H8.
        apply Theorem19; apply H0.
      * unfold Unordered in H10; apply Theorem4 in H10; elim H10; intros.
        -- unfold Singleton in H11; apply AxiomII in H11.
           elim H11; intros; left; rewrite <- H13.
           apply H8. apply Theorem19; apply H0.
        -- unfold Singleton in H11; apply AxiomII in H11.
           elim H11; intros; right; rewrite <- H13.
           apply H8. apply Theorem19; apply H1.
    + apply AxiomII; apply Theorem4 in H4; split.
      * unfold Ensemble; elim H4; intros.
        -- exists x; apply H5.
        -- exists y; apply H5.
      * elim H4; intros.
        -- exists x; split; auto.
           apply Theorem4; left.
           unfold Singleton; apply AxiomII; split; auto.
        -- exists y; split; auto.
           apply Theorem4; right.
           unfold Unordered; apply Theorem4; right.
           unfold Singleton; apply AxiomII; split; auto.
  - rewrite H3; apply AxiomI; split; intros.
    + apply Lemma_x in H4; elim H4; intros.
      apply AxiomII in H5; apply AxiomII in H6.
      elim H4; intros; apply Theorem4'; split; auto.
      * apply H5; apply Theorem4; left.
        unfold Singleton; apply AxiomII; split; auto.
      * apply H6; apply Theorem4; right.
        unfold Unordered; apply Theorem4; right.
        unfold Singleton; apply AxiomII; split; auto.
    + apply Theorem4' in H4; elim H4; intros.
      apply AxiomII; split.
      unfold Ensemble; exists x; apply H5.
      intros; apply Theorem4 in H7; destruct H7.
      * unfold Singleton in H7; apply AxiomII in H7.
        destruct H7; rewrite H8; auto.
        apply Theorem19; apply H0.
      * unfold Unordered in H7; apply AxiomII in H7; destruct H7, H8.
        -- unfold Singleton in H8; apply AxiomII in H8.
           destruct H8; rewrite H9; auto.
           apply Theorem19; apply H0.
        -- unfold Singleton in H8; apply AxiomII in H8.
           destruct H8; rewrite H9; auto.
           apply Theorem19; apply H1.
Qed.

Hint Resolve Theorem50 : set.


(* Definition51 : 1st coord z = ∩∩z. *)

Definition First (z: Class) := ∩∩z.

Hint Unfold First : set.


(* Definition52 : 2nd coord z = (∩∪z)∪(∪∪z)~(∪∩z). *)

Definition Second (z: Class) := (∩∪z)∪(∪∪z)~(∪∩z).

Hint Unfold Second : set.


(* Theorem54 : If x and y are sets, 1st coord (x,y) = x and 2nd coord (x,y) = y. *)

Lemma Lemma54 : forall (x y: Class),
  (x ∪ y) ~ x = y ~ x.
Proof.
  intros.
  apply AxiomI; split; intros.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; apply Theorem4 in H; split; auto.
    destruct H; auto.
    unfold Complement in H0; apply AxiomII in H0.
    destruct H0; unfold NotIn in H1; elim H1; auto.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; split; auto.
    apply Theorem4; right; auto.
Qed.

Theorem Theorem54 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> First [x,y] = x /\ Second [x,y] = y.
Proof.
  intros.
  apply Theorem50 in H; auto; split.
  - unfold First; apply H.
  - elim H; intros; elim H1; intros.
    elim H3; intros; elim H5; intros.
    elim H7; intros; unfold Second.
    rewrite H9; rewrite H8; rewrite H4.
    rewrite Lemma54; auto; unfold Setminus.
    rewrite Theorem6'; auto; rewrite <- Theorem8; auto.
    rewrite Property_μ; auto; rewrite Theorem20'; auto.
Qed.

Hint Resolve Theorem54 : set.


(* Theorem55 : If x and y are sets and (x,y) = (u,v), then x = u and y = v. *)

Theorem Theorem55 : forall (x y u v: Class),
  Ensemble x /\ Ensemble y -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  intros.
  apply Lemma_x in H; elim H; intros.
  apply Theorem49 in H0; auto; apply Theorem54 in H1; auto.
  elim H1; intros; split; intros.
  - rewrite H4 in H0.
    apply Theorem49 in H0; auto; apply Theorem54 in H0; auto.
    elim H0; intros; split.
    + rewrite <- H4 in H5; rewrite <- H2; rewrite H5; auto.
    + rewrite <- H4 in H6; rewrite H3 in H6; apply H6.
  - elim H4; intros; rewrite H5; rewrite H6; trivial.
Qed.

Hint Resolve Theorem55 : set.


(* Definition56 : r is a relation iff for each member z of r there is x and y such that z=(x,y). *)

Definition Relation r : Prop := forall z, z∈r -> exists x y, z = [x,y].

Hint Unfold Relation: set.


(* { (x,y) : ... } *)

Parameter Classifier_P : (Class -> Class -> Prop) -> Class.

Notation "\{\ P \}\" := (Classifier_P P) (at level 0).

Axiom AxiomII_P : forall (a b: Class) (P: Class -> Class -> Prop),
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).

Axiom Property_P : forall (z: Class) (P: Class -> Class -> Prop),
  z ∈ \{\ P \}\ -> (exists a b, z = [a,b]) /\ z ∈ \{\ P \}\.

Axiom Property_P' : forall (z: Class) (P: Class -> Class -> Prop),
  (forall a b, z = [a,b] -> z ∈ \{\ P \}\) -> z ∈ \{\ P \}\.

Ltac PP H a b:= apply Property_P in H; destruct H as [[a [b H]]];
rewrite H in *.

Ltac PP' H := apply Property_P'; intros a b H; rewrite H in *.

Hint Resolve AxiomII_P Property_P Property_P': set.


(* 定义60  r ⁻¹={[x,y]:[y,x]∈r} *)

Definition Inverse r : Class := \{\ λ x y, [y,x]∈r \}\.

Notation "r ⁻¹" := (Inverse r)(at level 5).

Hint Unfold Inverse : set.


(* Definition63 : f is a function iff f is a relation and for each x, each y, each z, if (x,y)∈f and (x,z)∈f, then y = z. *)

Definition Function f : Prop :=
  Relation f /\ (forall x y z, [x,y] ∈ f /\ [x,z] ∈ f -> y=z).

Hint Unfold Function : set.


(* Definition65 : domain f = {x:for some y, (x,y)∈f}. *)

Definition Domain f : Class := \{ λ x, exists y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

Lemma Property_dom : forall x y f,
  [x,y] ∈ f -> x ∈ dom( f ).
Proof.
  intros; apply AxiomII.
  split; eauto; AssE [x, y].
  apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Domain : set.


(* Definition66 : range f = {y:for some x, (x,y)∈f}. *)

Definition Range f : Class := \{ λ y, exists x, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

Lemma Property_ran : forall x y f,
  [x,y] ∈ f -> y ∈ ran( f ).
Proof.
  intros; apply AxiomII.
  split; eauto; AssE [x,y].
  apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Range : set.


(* Definition68 : f(x) = ∩{y:(x,y)∈f}. *)

Definition Value f x : Class := ∩ \{ λ y, [x,y] ∈ f \}.

Notation "f [ x ]" := (Value f x)(at level 5).

Lemma Property_Value : forall f x,
  Function f -> x ∈ (dom( f )) -> [x,f[x]] ∈ f.
Proof.
  intros; unfold Function in H;destruct H as [_ H].
  apply AxiomII in H0; destruct H0, H1.
  assert (x0=f[x]).
  - apply AxiomI; split; intros.
    + apply AxiomII; split; intros; try Ens.
      apply AxiomII in H3; destruct H3.
      assert (x0=y). { apply H with x; split; auto. }
      rewrite <- H5; auto.
    + apply AxiomII in H2; destruct H2 as [_ H2].
      apply H2; apply AxiomII; split; auto.
      AssE [x, x0]; apply Theorem49 in H3; apply H3.
  - rewrite <- H2; auto.
Qed.

Hint Unfold Value : set.


(* 定理69 如果x∉f的定义域，则f[x]=μ;如果x∈f的定义域，则f[x]∈μ*)

Lemma Lemma69 : forall (x y f:Class),
  Function f -> ( x ∉ dom( f ) -> \{ λ y, [x,y] ∈ f \} = Φ ) /\
  ( x ∈ dom( f ) -> \{ λ y, [x,y] ∈ f \} <> Φ ).
Proof.
  intros; split; intros.
  - generalize (classic (\{ λ y0, [x, y0] ∈ f \} = Φ)); intro. 
    destruct H1; auto; apply Property_NotEmpty in H1; auto.
    elim H1; intro z; intros; apply AxiomII in H2.
    destruct H2 as [H2 H3]; apply Property_dom in H3; contradiction.
  - apply Property_NotEmpty; auto; exists f[x].
    apply AxiomII;eapply Property_Value in H0; auto.
    split; auto; apply Property_ran in H0; Ens.
Qed.

Theorem Theorem69 : forall (x f:Class),
  Function f -> ( x ∉ (dom( f )) -> f[x] = μ ) /\
  ( x ∈ dom( f ) -> (f[x]) ∈  μ ).
Proof.
  intros; split; intros.
  - apply Lemma69 in H0; auto.
    unfold Value.
    rewrite H0; apply Theorem24.
  - apply Lemma69 in H0; auto.
    apply Theorem35 in H0; auto.
  apply Theorem19; auto.
Qed.

Hint Resolve Theorem69 : set.


(* Theorem70 : If f is a function, then f = {(x,y) : y = f(x)}. *)

Theorem Theorem70 : forall (f: Class),
  Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; apply AxiomI; split; intros.
  - PP' H1; apply AxiomII_P; split; try Ens.
    apply AxiomI; split; intros.
    + apply AxiomII; split; intros; try Ens.
      apply AxiomII in H3; destruct H3.
      apply Lemma_xy with (y:=[a,y] ∈ f) in H0; auto.
      unfold Function in H; apply H in H0.
      rewrite <- H0; auto.
    + unfold Element_I in H1; apply AxiomII in H2; destruct H2.
      apply H3; apply AxiomII; split; auto; AssE [a,b].
      apply Theorem49 in H4; try apply H4.
  - PP H0 a b; apply AxiomII_P in H1; destruct H1.
    generalize (classic (a ∈ dom(f))); intros; destruct H3.
    + apply Property_Value in H3; auto; rewrite H2; auto.
    + apply Theorem69 in H3; auto.
      rewrite H3 in H2; rewrite H2 in H1.
      apply Theorem49 in H1; destruct H1 as [_ H1].
      generalize Theorem39; intro; contradiction.
Qed.

Hint Resolve Theorem70 : set.


(* 代换公理 V 如果f是一个函数同时f的定义域是一个集，则f的值域是一个集 *)

Axiom AxiomV : forall (f: Class),
  Function f -> Ensemble dom(f) -> Ensemble ran(f).

Hint Resolve AxiomV : set.


(* VI Axiom of amalgamation : If x is a set so is ∪x. *)

Axiom AxiomVI : forall (x: Class), Ensemble x -> Ensemble (∪ x).

Hint Resolve AxiomVI : set.


(* Definition72 : x × y = {(u,v) : u∈x and v∈y}. *)

Definition Cartesian x y : Class := \{\ λ u v, u∈x /\ v∈y \}\.

Notation "x × y" := (Cartesian x y)(at level 0, right associativity).

Hint Unfold Cartesian : set.


(* 定理73 如果u与y均为集，则[u]×y也是集*)

Lemma Ex_Lemma73 : forall u y: Class, 
  Ensemble u /\ Ensemble y -> 
  exists f, Function f /\ dom(f) = y /\ ran(f) = [u] × y.
Proof.
  intros; destruct H.
  exists (\{\ λ w z, (w∈y /\ z = [u,w]) \}\).
  repeat split; intros.
  - red; intros; PP H1 a b.
    exists a; exists b; auto.
  - destruct H1.
    apply AxiomII_P in H1; apply AxiomII_P in H2.
    destruct H1 as [_ [_ H1]]; destruct H2 as [_ [_ H2]].
    rewrite H2; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1 as [_ [t H1]].
      apply AxiomII_P in H1; tauto.
    + apply AxiomII; split; try Ens.
      exists [u,z]; apply AxiomII_P; split; auto.
      AssE z; apply Theorem49; split; auto.
      apply Theorem49; tauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1, H1, H2.
      apply AxiomII_P in H2; destruct H2, H3.
      rewrite H4; apply AxiomII_P; repeat split; auto.
      * apply Theorem49; split; auto; AssE x0.
      * apply AxiomII; split; auto.
    + PP H1 a b; apply AxiomII_P in H2; destruct H2, H3.
      apply AxiomII; split; auto; exists b.
      apply AxiomII_P; repeat split; auto.
      * apply Theorem49; split; auto; AssE b.
      * apply Theorem19 in H; apply AxiomII in H3.
        destruct H3; rewrite H5; auto.
Qed.

Theorem Theorem73 : forall (u y:Class),
  Ensemble u /\ Ensemble y -> Ensemble ([u] × y).
Proof.
  intros; elim H; intros; apply Ex_Lemma73 in H; auto.
  destruct H,H,H2; rewrite <- H3; apply AxiomV; auto.
  rewrite H2; auto.
Qed.

Hint Resolve Theorem73 : set.


(* 定理74 如果x与y均为集，则 x×y 也是集 *)

Lemma Ex_Lemma74 : forall x y:Class, Ensemble x /\ Ensemble y -> 
  exists f:Class, Function f /\ dom( f ) = x /\ 
  ran( f ) = \{ λ z, (exists u, u∈x /\ z = [u] × y) \}.
Proof.
  intros; destruct H.
  exists (\{\ λ u z, (u∈x /\ z = [u] × y) \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; exists a; exists b; auto.
  - destruct H1; apply AxiomII_P in H1; apply AxiomII_P in H2.
    destruct H1, H2, H3, H4; subst z; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1, H2.
      apply AxiomII_P in H2; tauto.
    + apply AxiomII; split; try AssE z.
      exists (([z]) × y); apply AxiomII_P.
      repeat split; auto; apply Theorem49; split; auto.
      apply Theorem73; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H1; destruct H1, H2.
      apply AxiomII_P in H2; apply AxiomII.
      split; auto; exists x0; tauto.
    + apply AxiomII in H1; destruct H1, H2, H2.
      apply AxiomII; split; auto.
      exists x0; apply AxiomII_P; repeat split; auto.
      apply Theorem49; split; auto; AssE x0.
Qed.

Lemma Lemma74 : forall (x y:Class),Ensemble x /\ Ensemble y -> 
  ∪ \{ λ z, (exists u, u∈x /\ z = [u] × y) \} = x × y.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H0; destruct H0, H1, H1.
    apply AxiomII in H2; destruct H2, H3, H3.
    rewrite H4 in H1; PP H1 a b.
    apply AxiomII_P in H5; destruct H5, H6.
    apply AxiomII_P; repeat split; auto.
    apply AxiomII in H6; destruct H6 as [_ H6].
    AssE x1; apply Theorem19 in H8.
    rewrite <- H6 in H3; auto.
  - PP H0 a b; apply AxiomII_P in H1; destruct H1, H2.
    apply AxiomII; split; auto.
    exists (([a]) × y); split; AssE a.
    + apply AxiomII_P; repeat split; auto.
      apply AxiomII; intros; auto.
    + apply AxiomII; split.
      * apply Theorem73; split; try apply H; auto.
      * exists a; split; auto.
Qed.

Theorem Theorem74 : forall (x y:Class), 
  Ensemble x /\ Ensemble y -> Ensemble x × y.
Proof.
  intros; double H; double H0; destruct H0.
  apply Ex_Lemma74 in H; destruct H, H, H3.
  rewrite <- H3 in H0; apply AxiomV in H0; auto.
  rewrite H4 in H0; apply AxiomVI in H0.
  rewrite Lemma74 in H0; auto.
Qed.

Hint Resolve Theorem74 : set.


(* Definition81 *)

Definition Rrelation x r y : Prop := [x,y] ∈ r.

Hint Unfold Rrelation : set.


(* Definition82 *)

Definition Connect r x : Prop :=
  forall u v, u∈x /\ v∈x -> (Rrelation u r v) \/ (Rrelation v r u) \/ u=v.

Hint Unfold Connect : set.


(* Definition83 *)

Definition Transitive r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x) /\ (Rrelation u r v /\ 
  Rrelation v r w) -> Rrelation u r w.

Hint Unfold Transitive: set.


(* 定义86 *)

Definition FirstMember z r x : Prop :=
  z∈x /\ (forall y, y∈x -> ~ Rrelation y r z).

Hint Unfold FirstMember : set.


(* 定义84 有修改，非严格偏序中，为Antisymmetry，严格偏序中，为Asymmetry。
   \\本系统中采用严格偏序。\\ *)

Definition Asymmetry r x : Prop :=
  forall u v, (u∈x /\ v∈x) /\ Rrelation u r v -> ~ Rrelation v r u.

Hint Unfold Asymmetry : set.


(* 定义87 *)

Definition WellOrdered r x : Prop :=
  Connect r x /\ (forall y, y⊂x /\ y≠Φ -> exists z, FirstMember z r y).

Hint Unfold WellOrdered : set.


(* 定义95 *)

Definition Function1_1 f : Prop := Function f /\ Function (f ⁻¹).

Hint Unfold Function1_1 : set.


(* 正则公理 VII *)

Axiom AxiomVII : forall x, x ≠ Φ -> exists y, y∈x /\ x ∩ y = Φ.

Hint Resolve AxiomVII : set.


(* 定理101 *)

Theorem Theorem101 : forall x, x ∉ x.
Proof.
  intros.
  generalize (classic (x∈x)); intros.
  destruct H; auto; assert ([x] ≠ Φ).
  { apply Property_NotEmpty; exists x.
    unfold Singleton; apply AxiomII; Ens. }
  apply AxiomVII in H0; destruct H0 as [y H0], H0.
  unfold Singleton in H0; apply AxiomII in H0; destruct H0.
  rewrite H2 in H1; try (apply Theorem19); Ens.
  assert (x ∈ ([x] ∩ x)).
  { apply Theorem4'; split; auto.
    unfold Singleton; apply AxiomII; Ens. }
  rewrite H1 in H3; generalize (Theorem16 x); contradiction.
Qed.

Hint Resolve Theorem101 : set.


(* 定义103 *)

Definition E : Class := \{\ λ x y, x∈y \}\.

Hint Unfold E : set.


(* 定义105 *)

Definition full x : Prop := forall m, m∈x -> m⊂x.

Hint Unfold full : set.


(* 定义106 *)

Definition Ordinal x : Prop := Connect E x /\ full x.

Hint Unfold Ordinal : set.


(* 定义112 *)

Definition R : Class := \{ λ x, Ordinal x \}.

Hint Unfold R : set.


(* 定义116 *)

Definition Less x y : Prop := x∈y.

Notation "x ≺ y" := (Less x y)(at level 67, left associativity).

Hint Unfold Less : set.


(* 定义129 *)

Definition Integer x : Prop := Ordinal x /\ WellOrdered (E ⁻¹) x.

Hint Unfold Integer : set.


(* 定义131 *)

Definition W : Class := \{ λ x, Integer x \}.

Hint Unfold W : set.


(* A.11 基数 *)


(* 定义144 x≈y当且仅当存在一个1-1函数f，f的定义域=x而f的值域=y *)

Definition Equivalent x y : Prop :=
  exists f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.

Notation "x ≈ y" := (Equivalent x y) (at level 70).

Hint Unfold Equivalent : set.


(* 定义148 x是一个基数就是说x是一个序数，并且如果y∈R和y≺x，则x≈y不真 *)

Definition Cardinal x : Prop :=
  Ordinal x /\ (forall y, y∈R -> y ≺ x -> ~ (x ≈ y)).

Hint Unfold Cardinal : set.


(* 定义149 C={x:x是基数} *)

Definition C : Class := \{ λ x, Cardinal x \}.

Hint Unfold C : set.


(* 定义151 P={[x,y]:x≈y且y∈C} *)

Definition P : Class := \{\ λ x y, x ≈ y /\ y∈C \}\.

Hint Unfold P : set.


(* 定理153 如果x是一个集，则P[x]≈x *)

Theorem Theorem153 : forall x, Ensemble x -> P[x] ≈ x.
Admitted.

Hint Resolve Theorem153 : set.


(* 定义166 x是有限的当且仅当P[x]∈w *)

Definition Finite x : Prop := P[x] ∈ W.

Hint Unfold Finite : set.


(* 定理167 x是有限的当且仅当存在r使得r良序x，并且r⁻¹也良序x *)

Theorem Theorem167 : forall (x: Class),
  Finite x <-> exists r, WellOrdered r x /\ WellOrdered (r⁻¹) x.
Admitted.

Hint Resolve Theorem167 : set.


(* 定理168 如果x与y均有限，则x∪y也有限 *)

Theorem Theorem168 : forall (x y: Class),
  Finite x /\ Finite y -> Finite (x ∪ y).
Admitted.

Hint Resolve Theorem168 : set.


Lemma Property_Finite : forall (A B: Class),
  Finite A -> B ⊂ A -> Finite B.
Proof.
  intros.
  apply Theorem167 in H; destruct H as [r H], H.
  apply Theorem167; exists r; split.
  - unfold WellOrdered, Connect in H; destruct H.
    unfold WellOrdered, Connect; split; intros.
    + destruct H3; apply H; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
  - unfold WellOrdered, Connect in H1; destruct H1.
    unfold WellOrdered, Connect; split; intros.
    + destruct H3; apply H1; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
Qed.


Lemma Finite_Single : forall z, Ensemble z -> Finite ([z]).
Proof.
  intros.
  apply Theorem167; exists E; split.
  - unfold WellOrdered; split; intros.
    + unfold Connect; intros; destruct H0.
      unfold Singleton in H0, H1.
      apply AxiomII in H0; apply AxiomII in H1.
      destruct H0, H1; double H.
      apply Theorem19 in H; apply Theorem19 in H4.
      apply H2 in H; apply H3 in H4.
      rewrite <- H4 in H; tauto.
    + destruct H0; apply Property_NotEmpty in H1.
      destruct H1; exists x; unfold FirstMember.
      split; auto; intros; unfold Included in H0.
      apply H0 in H1; apply H0 in H2.
      unfold Singleton in H1, H2; double H.
      apply AxiomII in H1; apply AxiomII in H2; destruct H1, H2.
      apply Theorem19 in H; apply Theorem19 in H3.
      apply H4 in H; apply H5 in H3.
      rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation in H6; unfold E in H6.
      apply AxiomII_P in H6; destruct H6.
      generalize (Theorem101 y0); intros; contradiction.
  - unfold WellOrdered; split; intros.
    + unfold Connect; intros; destruct H0.
      unfold Singleton in H0, H1.
      apply AxiomII in H0; apply AxiomII in H1.
      destruct H0, H1; double H.
      apply Theorem19 in H; apply Theorem19 in H4.
      apply H2 in H; apply H3 in H4.
      rewrite <- H4 in H; tauto.
    + destruct H0; apply Property_NotEmpty in H1; auto.
      destruct H1; exists x; unfold FirstMember.
      split; auto; intros; unfold Included in H0.
      apply H0 in H1; apply H0 in H2.
      unfold Singleton in H1, H2; double H.
      apply AxiomII in H1; apply AxiomII in H2; destruct H1, H2.
      apply Theorem19 in H; apply Theorem19 in H3.
      apply H4 in H; apply H5 in H3.
      rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation in H6; unfold Inverse in H6.
      apply AxiomII_P in H6; destruct H6; unfold E in H7.
      apply AxiomII_P in H7; destruct H7.
      generalize (Theorem101 y0); intros; contradiction.
Qed.


End AxiomaticSetTheory.

Export AxiomaticSetTheory.
