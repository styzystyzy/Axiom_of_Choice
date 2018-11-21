(* This document only provides the definition and theorem that we needed in the Axiom_of_Choice.v, and the complete Coq proof of Kelley axiomatic set theory can contact with stycyj@bupt.edu.cn. *)

Require Export Logic_Property.

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


(* 定义  x≠y 当且仅当 x=y 不真 *)

Definition Inequality (x y: Class) : Prop := ~ (x = y).

Notation "x ≠ y" := (Inequality x y) (at level 70).

Corollary Property_Ineq : forall x y, (x ≠ y) <-> (y ≠ x).
Proof.
 intros; split; intros; intro; apply H; auto.
Qed.

Hint Unfold Inequality: set.
Hint Resolve Property_Ineq: set.


(* Definition15 : 0={x:x≠x}. *)

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


(* 定理30  x⊂y当且仅当x∩y=x *)

Theorem Theorem30 : forall x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Included; intros; apply AxiomI with (z:=z) in H.
    apply H in H0; apply Theorem4' in H0; tauto.
  - apply AxiomI; split; intros.
    + apply Theorem4' in H0; tauto.
    + apply Theorem4'; split; auto.
Qed.

Hint Resolve Theorem30 : set.


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


(* Proper Subset *)

Definition ProperSubset x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperSubset x y) (at level 70).

Lemma Property_ProperSubset : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperSubset; auto.
Qed.

Lemma Property_ProperSubset' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperSubset in H; destruct H.
  generalize (Theorem27 x y); intros.
  apply definition_not with (B:= (x ⊂ y /\ y ⊂ x)) in H0; try tauto.
  apply property_not in H0; destruct H0; try tauto.
  unfold Included in H0.
  apply not_all_ex_not in H0; destruct H0.
  apply imply_to_and in H0.
  exists x0; auto.
Qed.

Lemma Property_ProperSubset'' : forall (x y: Class),
  x ⊂ y \/ y ⊂ x -> ~ (x ⊂ y) -> y ⊊ x.
Proof.
  intros; destruct H.
  - elim H0; auto.
  - unfold ProperSubset; split; auto.
    intro; rewrite H1 in H.
    pattern x at 2 in H; rewrite <- H1 in H.
    contradiction.
Qed.

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperSubset in H; destruct H; auto.
    apply Property_ProperSubset' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Setminus; apply Theorem4'; split; auto.
      unfold Complement; apply AxiomII; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply AxiomI; split; intros.
    + unfold Setminus in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply AxiomII in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.

Hint Unfold ProperSubset : Axiom_of_Choice.
Hint Resolve Property_ProperSubset Property_ProperSubset'
             Property_ProperSubset'' Property_Φ: Axiom_of_Chioce.


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


(* 定理61  (r ⁻¹)⁻¹=r *)

Lemma Lemma61 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble [y,x].
Proof.
  intros; split; intros.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
Qed.

Theorem Theorem61 : forall (r: Class),
  (r ⁻¹)⁻¹ = r.
Proof.
  intros; apply AxiomI; split; intros.
  - PP H a b; apply AxiomII_P in H0; destruct H0.
    apply AxiomII_P in H1; apply H1.
  - PP' H0; apply AxiomII_P; split; Ens.
    apply AxiomII_P; split; auto.
    apply Lemma61; auto; Ens.
Qed.

Hint Rewrite Theorem61 : set.


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


(* 定义78 f在x上，当且仅当f为一函数同时x=f的定义域 *)

Definition On f x : Prop :=  (Function f /\ dom( f ) = x).

Hint Unfold On : set.


(* Definition81 *)

Definition Rrelation x r y : Prop := [x,y] ∈ r.

Hint Unfold Rrelation : set.


(* Definition82 *)

Definition Connect r x : Prop :=
  forall u v, u∈x /\ v∈x -> (Rrelation u r v) \/ (Rrelation v r u) \/ u=v.

Hint Unfold Connect : set.


(* Definition83 *)

Definition Transitive r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x /\ Rrelation u r v /\ Rrelation v r w) -> Rrelation u r w.

Hint Unfold Transitive: set.


(* 定义84 *)

Definition Asymmetry r x : Prop :=
  forall u v, (u ∈ x /\ v ∈ x /\ Rrelation u r v) -> ~ Rrelation v r u.

Corollary Property_Asy : forall r x u, Asymmetry r x -> u ∈ x -> ~ Rrelation u r u.
Proof.
  intros; intro.
  unfold Asymmetry in H; specialize H with u u.
  apply H; repeat split; auto.
Qed.

Hint Unfold Asymmetry: set.

(* 定义86 *)

Definition FirstMember z r x : Prop :=
  z∈x /\ (forall y, y∈x -> ~ Rrelation y r z).

Hint Unfold FirstMember : set.


(* 定义87 *)

Definition WellOrder r x : Prop :=
  Connect r x /\ (forall y, y⊂x /\ y≠Φ -> exists z, FirstMember z r y).

Hint Unfold WellOrder : set.


(* 定理88 *)

Lemma Lemma88 : forall x u v w,
  Ensemble u -> Ensemble v -> Ensemble w -> x ∈ ([u] ∪ [v] ∪ [w]) -> x = u \/ x= v \/ x = w.
Proof.
  intros; apply Theorem19 in H; apply Theorem19 in H0; apply Theorem19 in H1.
  apply AxiomII in H2; destruct H2, H3.
  - left; apply AxiomII in H3; destruct H3; auto.
  - apply AxiomII in H3; destruct H3, H4.
    + right; left; apply AxiomII in H4; destruct H4; auto.
    + right; right; apply AxiomII in H4; destruct H4; auto.
Qed.

Theorem Theorem88 : forall r x, WellOrder r x -> Transitive r x /\ Asymmetry r x .
Proof.
  intros; generalize H; intro.
  unfold WellOrder in H0; destruct H0.
  assert (Asymmetry r x).
  { unfold Asymmetry; intros.
     destruct H2, H3; AssE u; AssE v.
     assert (([u | v] ⊂ x) /\ ([u | v] ≠ Φ)).
     { split.
        - unfold Included; intros; apply AxiomII in H7; destruct H7, H8.
          + apply Theorem19 in H5; apply AxiomII in H8; destruct H8; rewrite H9; auto.
          + apply Theorem19 in H6; apply AxiomII in H8; destruct H8; rewrite H9; auto.
        - apply Property_NotEmpty; exists u; apply AxiomII.
         split; auto;  left; apply AxiomII; split; auto. }
  apply H1 in H7; destruct H7; unfold FirstMember in H7; destruct H7.
  apply Theorem46 in H7; auto; destruct H7; subst x0.
  - assert (v ∈ [u | v]).
    { apply AxiomII; split; auto; right; apply AxiomII; split; auto. }
    apply H8; auto.
  - assert (u ∈ [u | v]).
    { apply AxiomII; split; auto; left; apply AxiomII; split; auto. }
    apply H8 in H7; auto. }
  split; auto; unfold Transitive; intros.
  - destruct H3, H4, H5, H6; unfold Connect in H0; specialize H0 with w u.
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    * assert (([u] ∪ [v] ∪ [w] ⊂ x) /\ ([u] ∪ [v] ∪ [w] ≠ Φ)).
      { split.
        - unfold Included; intros; apply AxiomII in H8; destruct H8 as [_ H8]; destruct H8.
         + AssE u; apply Theorem19 in H9; apply AxiomII in H8; destruct H8; rewrite H10; auto.
         + apply AxiomII in H8; destruct H8 as [_ H8]; destruct H8.
            * AssE v; apply Theorem19 in H9; apply AxiomII in H8; destruct H8; rewrite H10; auto.
            * AssE w; apply Theorem19 in H9; apply AxiomII in H8; destruct H8; rewrite H10; auto.
        - intro; generalize (Theorem16 u); intro.
           apply H9; rewrite <- H8; apply AxiomII; split; Ens.
           left; apply AxiomII; split; intros; auto; Ens. }
      apply H1 in H8; destruct H8.
      unfold FirstMember in H8; destruct H8.
      assert (u ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; left; apply AxiomII; split; Ens. }
      assert (v ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply AxiomII; split; Ens; left; apply AxiomII; split; Ens. }
      assert (w ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply AxiomII; split; Ens; right; apply AxiomII; split; Ens. }
      apply Lemma88 in H8; Ens.
      destruct H8 as [H8 | [H8 | H8]]; subst x0.
      + apply H9 in H12; contradiction.
      + apply H9 in H10; contradiction.
      + apply H9 in H11; contradiction.
  * subst w; unfold Asymmetry in H2.
     absurd (Rrelation u r v); auto.
Qed.

Hint Resolve Theorem88: set.


(* 定义89 *)

Definition Section y r x : Prop :=
  y ⊂ x /\ WellOrder r x /\
  (forall u v, (u ∈ x /\ v ∈ y /\ Rrelation u r v) -> u ∈ y).

Hint Unfold Section : set.


(* 定理91 *)

Theorem Theorem91 : forall x y r,
  Section y r x /\ y ≠ x ->
  (exists v, v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \}).
Proof.
  intros; destruct H.
  assert (exists v, FirstMember v r (x ~ y)).
  { unfold Section, WellOrder in H; destruct H, H1, H1.
    assert ((x ~ y) ⊂ x).
    { red; intros; apply AxiomII in H4; tauto. }
    generalize (classic (x ~ y = Φ)); intro; destruct H5.
    - apply Property_Φ in H; apply H in H5.
      apply Property_Ineq in H0; contradiction.
    - apply H3; split; auto. }
  destruct H1; unfold FirstMember in H1; destruct H1.
  exists x0; apply AxiomII in H1; destruct H1, H3.
  split; auto; apply AxiomI; split; intros.
  unfold Section in H; destruct H, H6.
  - apply AxiomII; repeat split; Ens.
    assert (z ∈ x); auto.
    unfold WellOrder, Connect in H6; destruct H6 as [H6 _].
    specialize H6 with x0 z; destruct H6 as [H6|[H6|H6]]; auto.
    + assert (x0 ∈ y).
      { apply H7 with z; repeat split; auto. }
      apply AxiomII in H4; destruct H4; contradiction.
    + apply AxiomII in H4; destruct H4; subst x0; contradiction.
  - apply AxiomII in H5; destruct H5, H6.
    generalize (classic (z ∈ (x ~ y))); intro; destruct H8.
    + apply H2 in H8; contradiction.
    + generalize (classic (z ∈ y)); intro; destruct H9; auto.
      elim H8; apply AxiomII; repeat split; auto; apply AxiomII; tauto.
Qed.

Hint Resolve Theorem91 : set.


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


(* 定理107 *)

Theorem Theorem107 : forall x, Ordinal x -> WellOrder E x.
Proof.
  intros.
  unfold Ordinal in H; destruct H.
  unfold WellOrder; intros.
  split; auto; intros; destruct H1.
  apply AxiomVII in H2; destruct H2, H2.
  exists x0; unfold FirstMember; intros.
  split; auto; intros; intro.
  unfold Rrelation in H5; apply AxiomII_P in H5; destruct H5.
  assert (y0 ∈ (y ∩ x0)). { apply AxiomII; split; Ens. }
  rewrite H3 in H7; generalize (Theorem16 y0); contradiction.
Qed.

Hint Resolve Theorem107 : set.


(* 定理108 *)

Theorem Theorem108 : forall x y,
  Ordinal x -> y ⊂ x -> y ≠ x -> full y -> y ∈ x.
Proof.
  intros.
  assert (Section y E x).
  { apply Theorem107 in H; unfold Section; intros.
    split; auto; split; auto; intros; destruct H3, H4.
    unfold Rrelation in H5; apply AxiomII_P in H5; destruct H5.
    unfold full in H2; apply H2 in H4; auto. }
  generalize (Lemma_xy _ _ H3 H1); intro.
  apply Theorem91 in H4; destruct H4 as [v H4], H4.
  assert (v = \{ λ u, u ∈ x /\ Rrelation u E v \}).
  { apply AxiomI; split; intros; AssE z.
    - apply AxiomII; split; auto.
      unfold Ordinal in H; destruct H.
      double H4; unfold full in H8; apply H8 in H4.
      split; auto; apply AxiomII_P; split; auto.
      apply Theorem49; split; Ens.
    - apply AxiomII in H6; destruct H6, H8.
      unfold Rrelation in H9; apply AxiomII_P in H9; tauto. }
  rewrite <- H6 in H5; subst v; auto.
Qed.

Hint Resolve Theorem108 : set.


(* 定理109 *)

Lemma Lemma109 : forall x y, Ordinal x /\ Ordinal y -> full (x ∩ y).
Proof.
  intros; destruct H.
  unfold Ordinal in H, H0; destruct H, H0.
  unfold full in *; intros.
  apply AxiomII in H3; destruct H3, H4.
  apply H1 in H4; apply H2 in H5.
  unfold Included; intros.
  apply AxiomII; repeat split; Ens.
Qed.

Lemma Lemma109' : forall x y,
  Ordinal x /\ Ordinal y -> ((x ∩ y) = x) \/ ((x ∩ y) ∈ x).
Proof.
  intros; generalize (classic ((x ∩ y) = x)); intro.
  destruct H0; try tauto. assert ((x ∩ y) ⊂ x).
  { unfold Included; intros; apply Theorem4' in H1; tauto. }
  elim H; intros; apply Lemma109 in H.
  eapply Theorem108 in H2; eauto.
Qed.

Theorem Theorem109 : forall x y,
  Ordinal x /\ Ordinal y -> x ⊂ y \/ y ⊂ x.
Proof.
  intros; elim H; intros.
  generalize (Lemma_xy _ _ H1 H0); intro.
  apply Lemma109' in H; apply Lemma109' in H2; destruct H.
  - apply Theorem30 in H; tauto.
  - destruct H2.
    + apply Theorem30 in H2; tauto.
    + assert ((x ∩ y) ∈ (x ∩ y)).
      { rewrite Theorem6' in H2; apply AxiomII; Ens. }
      apply Theorem101 in H3; elim H3.
Qed.

Hint Resolve Theorem109 : set.


(* 定理110 *)

Theorem Theorem110 : forall x y,
  Ordinal x /\ Ordinal y -> x ∈ y \/ y ∈ x \/ x = y.
Proof.
  intros; generalize (classic (x = y)); intro; destruct H0; try tauto.
  elim H; intros; apply Theorem109 in H; destruct H.
  - left; unfold Ordinal in H1; destruct H1; eapply Theorem108; eauto.
  - right; left; unfold Ordinal in H2; destruct H2.
    eapply Theorem108; eauto; intro; auto.
Qed.

Hint Resolve Theorem110 : set.


(* 定义112 *)

Definition R : Class := \{ λ x, Ordinal x \}.

Hint Unfold R : set.


(* 定义116 *)

Definition Less x y : Prop := x∈y.

Notation "x ≺ y" := (Less x y)(at level 67, left associativity).

Hint Unfold Less : set.


(* 定义129 *)

Definition Integer x : Prop := Ordinal x /\ WellOrder (E ⁻¹) x.

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


(* 定理146 如果x≈y，则y≈x *)

Theorem Theorem146 : forall x y, x ≈ y -> y ≈ x.
Proof.
  intros.
  unfold Equivalent in H; destruct H as [f H], H, H0.
  unfold Equivalent; exists f⁻¹; split.
  - unfold Function1_1 in H; destruct H.
    unfold Function1_1; split; try rewrite Theorem61; auto.
  - unfold Inverse; split.
    + unfold Domain; apply AxiomI; split; intros.
      * apply AxiomII in H2; destruct H2, H3.
        apply AxiomII_P in H3; destruct H3.
        apply Property_ran in H4; rewrite H1 in H4; auto.
      * apply AxiomII; split; Ens.
        rewrite <- H1 in H2; unfold Range in H2.
        apply AxiomII in H2; destruct H2, H3.
        exists (x0); apply AxiomII_P; split; auto.
        apply Theorem49; AssE ([x0,z]).
        apply Theorem49 in H4; destruct H4; Ens.
    + unfold Range; apply AxiomI; split; intros.
      * apply AxiomII in H2; destruct H2, H3.
        apply AxiomII_P in H3; destruct H3.
        apply Property_dom in H4; rewrite H0 in H4; auto.
      * apply AxiomII; split; Ens.
        rewrite <- H0 in H2; unfold Domain in H2.
        apply AxiomII in H2; destruct H2, H3.
        exists (x0); apply AxiomII_P; split; auto.
        apply Theorem49; AssE ([z,x0]).
        apply Theorem49 in H4; destruct H4; Ens.
Qed.

Hint Resolve Theorem146 : set.


(* 定理147 如果x≈y同时y≈z，则x≈z *)

Theorem Theorem147 : forall x y z,
  x ≈ y -> y ≈ z -> x ≈ z.
Proof.
  intros.
  unfold Equivalent in H, H0; unfold Equivalent.
  destruct H as [f1 H], H0 as [f2 H0], H, H0, H1, H2.
  exists (\{\λ u v, exists w, [u,w] ∈ f1 /\ [w,v] ∈ f2\}\); split.
  - unfold Function1_1; unfold Function1_1 in H, H0.
    destruct H, H0; split.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H7 a b; Ens.
      * destruct H7; apply AxiomII_P in H7; destruct H7, H9.
        apply AxiomII_P in H8; destruct H8, H10; clear H7 H8.
        unfold Function in H, H0; destruct H9, H10, H, H0.
        add ([x0,x2] ∈ f1) H7; apply H11 in H7; rewrite H7 in H8.
        add ([x2,z0] ∈ f2) H8; apply H12 in H8; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H7 a b; Ens.
      * unfold Inverse in H7; destruct H7; apply AxiomII_P in H7.
        apply AxiomII_P in H8; destruct H7, H8; clear H7 H8.
        apply AxiomII_P in H9; destruct H9, H8.
        apply AxiomII_P in H10; destruct H10, H10; clear H7 H9.
        unfold Function in H5, H6; destruct H8, H10, H5, H6.
        assert ([x0,x1] ∈ f2⁻¹ /\ [x0,x2] ∈ f2⁻¹).
        { unfold Inverse; split.
          - apply AxiomII_P; split; auto; AssE [x1,x0].
            apply Theorem49 in H13; destruct H13.
            apply Theorem49; split; auto.
          - apply AxiomII_P; split; auto; AssE [x2,x0].
            apply Theorem49 in H13; destruct H13.
            apply Theorem49; split; auto. }
        apply H12 in H13; rewrite H13 in H7; clear H8 H10 H12 H13.
        assert ([x2,y0] ∈ f1⁻¹ /\ [x2,z0] ∈ f1⁻¹).
        { unfold Inverse; split.
          - apply AxiomII_P; split; auto; AssE [y0,x2].
            apply Theorem49 in H8; destruct H8.
            apply Theorem49; split; auto.
          - apply AxiomII_P; split; auto; AssE [z0,x2].
            apply Theorem49 in H8; destruct H8.
            apply Theorem49; split; auto. }
        apply H11 in H8; auto.
  - rewrite <- H1, <- H4; split.
    + apply AxiomI; split; intros.
      * apply AxiomII in H5; destruct H5, H6.
        apply AxiomII_P in H6; destruct H6, H7, H7.
        apply Property_dom in H7; auto.
      * apply AxiomII; split; Ens; apply AxiomII in H5.
        destruct H5, H6; double H6; apply Property_ran in H7.
        rewrite H3 in H7; rewrite <- H2 in H7; apply AxiomII in H7.
        destruct H7, H8; exists x1; apply AxiomII_P; split; Ens.
        AssE [z0,x0]; AssE [x0,x1]; apply Theorem49 in H9.
        apply Theorem49 in H10; destruct H9, H10.
        apply Theorem49; split; auto.
    + apply AxiomI; split; intros.
      * apply AxiomII in H5; destruct H5, H6.
        apply AxiomII_P in H6; destruct H6, H7, H7.
        apply Property_ran in H8; auto.
      * apply AxiomII; split; Ens; apply AxiomII in H5.
        destruct H5, H6; double H6; apply Property_dom in H7.
        rewrite H2 in H7; rewrite <- H3 in H7; apply AxiomII in H7.
        destruct H7, H8; exists x1; apply AxiomII_P; split; Ens.
        AssE [x0,z0]; AssE [x1,x0]; apply Theorem49 in H9.
        apply Theorem49 in H10; destruct H9, H10.
        apply Theorem49; split; auto.
Qed.

Hint Resolve Theorem147 : set.


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


(* 定理152 P是一个函数，P的定义域的=μ且P的值域=C *)

Theorem Theorem152 : Function P /\ dom(P) = μ /\ ran(P) = C.
Proof.
  unfold P; repeat split; intros.
  - unfold Relation; intros; PP H a b; Ens.
  - destruct H; apply AxiomII_P in H; apply AxiomII_P in H0.
    destruct H, H0, H1, H2; apply Theorem146 in H1.
    apply (Theorem147 _ _ z) in H1; auto; clear H H0 H2.
    unfold C in H3, H4; apply AxiomII in H3; destruct H3.
    apply AxiomII in H4; destruct H4.
    unfold Cardinal in H0, H3; destruct H0, H3.
    assert (Ordinal y /\ Ordinal z). { split; auto. }
    apply Theorem110 in H6; destruct H6.
    + apply Theorem146 in H1. (* apply H5 in H0; auto; try contradiction.
    + destruct H6; auto; apply H4 in H3; auto; try contradiction.
  - apply AxiomI; split; intros; try apply Theorem19; Ens.
    apply Theorem19 in H; double H; apply Theorem140 in H0.
    destruct H0 as [f H0], H0, H1; apply AxiomII; split; auto.
    assert (WellOrder E \{ λ x, x ≈ z /\ Ordinal x \}).
    { assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ R).
      { unfold Included; intros; apply AxiomII in H3.
        destruct H3, H4; apply AxiomII; split; auto. }
      apply (Lemma97 _ E _) in H3; auto.
      apply Theorem107; apply Theorem113. }
    unfold WellOrder in H3; destruct H3 as [H4 H3]; clear H4.
    assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ \{ λ x, x ≈ z /\ Ordinal x \}
            /\ \{ λ x, x ≈ z /\ Ordinal x \} ≠ Φ).
    { split; try unfold Included; auto.
      apply Lemma35; exists dom(f); apply AxiomII.
      unfold Ordinal_Number, R in H2; apply AxiomII in H2; destruct H2.
      split; auto; split; auto; unfold Equivalent; exists f; auto. }
    apply H3 in H4; destruct H4; unfold FirstMember in H4; destruct H4.
    apply AxiomII in H4; destruct H4, H6.
    exists x; apply AxiomII_P.
    repeat split; try apply Theorem49; auto.
    + apply Theorem146; unfold Equivalent; Ens.
    + unfold C; apply AxiomII; split; auto.
      unfold Cardinal_Number; split; intros.
      { unfold Ordinal_Number, R; apply AxiomII; auto. }
      { unfold Less in H9; unfold R in H8.
        apply AxiomII in H8; destruct H8; intro.
        assert (y ∈ \{ λ x,x ≈ z /\ Ordinal x \}).
        { apply AxiomII; split; auto; split; auto.
          apply Theorem146 in H11; apply (Theorem147 _ x _); auto. }
        apply H5 in H12; apply H12; unfold Rrelation, E.
        apply AxiomII_P; split; try apply Theorem49; auto. }
  - unfold Range; apply AxiomI; split; intros.
    + apply AxiomII in H; destruct H, H0.
      apply AxiomII_P in H0; apply H0.
    + apply AxiomII; split; Ens; exists z; apply AxiomII_P.
      repeat split; try apply Theorem49; Ens.
      apply Theorem145. *)
Admitted.

Hint Resolve Theorem152 : set.

(* 定理153 如果x是一个集，则P[x]≈x *)

Theorem Theorem153 : forall x, Ensemble x -> P[x] ≈ x.
Proof.
  intros.
  generalize Theorem152; intros; destruct H0, H1.
  apply Theorem19 in H; rewrite <- H1 in H.
  apply Property_Value in H; auto.
  unfold P at 2 in H; apply AxiomII_P in H.
  apply Theorem146; apply H.
Qed.

Hint Resolve Theorem153 : set.


(* 定义166 x是有限的当且仅当P[x]∈w *)

Definition Finite x : Prop := P[x] ∈ W.

Hint Unfold Finite : set.


(* 定理167 x是有限的当且仅当存在r使得r良序x，并且r⁻¹也良序x *)

Theorem Theorem167 : forall (x: Class),
  Finite x <-> exists r, WellOrder r x /\ WellOrder (r⁻¹) x.
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
  - unfold WellOrder, Connect in H; destruct H.
    unfold WellOrder, Connect; split; intros.
    + destruct H3; apply H; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
  - unfold WellOrder, Connect in H1; destruct H1.
    unfold WellOrder, Connect; split; intros.
    + destruct H3; apply H1; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
Qed.


Lemma Finite_Single : forall z, Ensemble z -> Finite ([z]).
Proof.
  intros.
  apply Theorem167; exists E; split.
  - unfold WellOrder; split; intros.
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
  - unfold WellOrder; split; intros.
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
