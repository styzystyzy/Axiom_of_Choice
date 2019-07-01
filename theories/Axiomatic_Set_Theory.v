(* This document only provides definitions and theorems that we needed in the
   paper "Formalization of the Axiom of Choice and its Equivalent Theorems",
   and the complete formalization of Kelley axiomatic set theory can be seen in
   https://github.com/styzystyzy/Axiomatic_Set_Theory/ . *)

(* In this work, set theory is divided into two parts. One part is basic set
   theory (Axiomatic_Set_Theory.v), including some basic definitions and
   theorems of sets. The other part is related to the finite cardinals, 
   including integers, cardinal numbers and so on. According to the first part,
   we can independently prove AC by Zermelo's postulate or the well-ordering
   theorem. On the basis of the second part, we define the set of finite 
   character and prove some properties of it. *)


Require Export Logic_Property.

(** The foramlization of axiomatic set theory **)


Module AxiomaticSetTheory.

Parameter Class : Type.


(* ∈: belongs to. x∈y : In x y. *)

Parameter In : Class -> Class -> Prop.

Notation "x ∈ y" := (In x y) (at level 10).


(* I Axiom of extent : For each x and each y it is true that x = y
   if and only if for each z, z∈x when and only when z∈y. *)

Axiom Axiom_Extent : forall x y, x = y <-> (forall z, z∈x <-> z∈y).

Hint Resolve Axiom_Extent : set.


(* Definition1 : x is a set iff for some y, x∈y. *)

Definition Ensemble x : Prop := exists y, x∈y.

Ltac Ens := unfold Ensemble; eauto.

Ltac AssE x := assert (Ensemble x); Ens.

Hint Unfold Ensemble : set.


(* II Classiferification axiom-scheme : For each b, b ∈ {a : P A} if and only
   if b is a set and P b. *)

(* {...:...} *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).

Axiom Axiom_Scheme : forall b P,
  b ∈ \{ P \} <-> Ensemble b /\ (P b).

Hint Resolve Axiom_Scheme : set.


(* Definition2 : x∪y = {z : z∈x or z∈y}. *)

Definition Union x y : Class := \{ λ z, z∈x \/ z∈y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

Hint Unfold Union : set.


(* Definition3 :  x∩y = {z : z∈x and z∈y}. *)

Definition Intersection x y : Class := \{ λ z, z∈x /\ z∈y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60).

Hint Unfold Intersection : set.


(* Theorem4 :  z∈x∪y iff z∈x or z∈y, z∈x∩y iff z∈x and z∈y. *)

Theorem Theorem4 : forall (x y: Class) (z: Class),
  z∈x \/ z∈y <-> z∈(x ∪ y).
Proof.
  intros; split; intros.
  - unfold Union; apply Axiom_Scheme; split; auto.
    destruct H; Ens.
  - unfold Union in H; apply Axiom_Scheme in H; apply H.
Qed.

Theorem Theorem4' : forall (x y: Class) (z: Class),
  z∈x /\ z∈y <-> z∈(x ∩ y).
Proof.
  intros; unfold Intersection; split; intros.
  - apply Axiom_Scheme; split; auto; destruct H; Ens.
  - apply Axiom_Scheme in H; apply H.
Qed.

Hint Resolve Theorem4 Theorem4' : set.


(* Theorem5 : x∪x = x and x∩x = x. *)

Theorem Theorem5 : forall (x: Class), x ∪ x = x.
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - apply Theorem4 in H; destruct H; auto.
  - apply Theorem4; left; apply H.
Qed.

Theorem Theorem5' : forall (x: Class), x ∩ x = x.
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; apply H.
  - apply Theorem4'; split; apply H.
Qed.

Hint Rewrite Theorem5 Theorem5' : set.


(* Theorem6 : x∪y = y∪x and x∩y = y∩x. *)

Theorem Theorem6 : forall (x y: Class), x ∪ y = y ∪ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; apply Theorem4; tauto.
  - apply Theorem4 in H; apply Theorem4; tauto.
Qed.

Theorem Theorem6' : forall (x y: Class), x ∩ y = y ∩ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; apply Theorem4'; tauto.
  - apply Theorem4' in H; apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem6 Theorem6' : set.


(* Theorem7 : (x∪y)∪z = x∪(y∪z) and (x∩y)∩z = x∩(y∩z). *)

Theorem Theorem7 : forall (x y z: Class),
  (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros.
  apply Axiom_Extent; split; intro.
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
  apply Axiom_Extent; split; intro.
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


(* Theorem8 : x∩(y∪z)= (x∩y)∪(x∩z) and x∪(y∩z) = (x∪y)∩(x∪z). *)

Theorem Theorem8 : forall (x y z: Class),
  x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply Axiom_Extent; split; intros.
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


(* Definition10 : ~x = {y : y∉x}. *)

Definition Complement x : Class := \{ λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

Hint Unfold Complement : set.


(* Definition13 : x~y = x∩(~y). *)

Definition Setminus x y : Class := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

Hint Unfold Setminus : set.


(* Definition Inequality : x≠y iff x=y is not true. *)

Definition Inequality (x y: Class) : Prop := ~ (x = y).

Notation "x ≠ y" := (Inequality x y) (at level 70).

Corollary Property_Ineq : forall x y, (x ≠ y) <-> (y ≠ x).
Proof.
 intros; split; intros; intro; apply H; auto.
Qed.

Hint Unfold Inequality: set.
Hint Resolve Property_Ineq: set.


(* Definition15 : Φ = {x : x ≠ x}. *)

Definition Φ : Class := \{ λ x, x ≠ x \}.

Hint Unfold Φ : set.


(* Theorem16 : x∉Φ. *)

Theorem Theorem16 : forall (x: Class), x ∉ Φ.
Proof.
  intros; unfold NotIn; intro.
  unfold Φ in H; apply Axiom_Scheme in H.
  destruct H; apply H0; auto.
Qed.

Hint Resolve Theorem16 : set.


(* Theorem17 : Φ∪x = x and Φ∩x = Φ *)

Theorem Theorem17 : forall x, Φ ∪ x = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    generalize (Theorem16 z); contradiction.
  - apply Theorem4; tauto.
Qed.

Hint Rewrite Theorem17 : set.


(* Definition18 : μ = {x : x=x}, the class μ is the universe. *)

Definition μ : Class := \{ λ x, x = x \}.

Lemma Property_μ : forall (x y: Class),
  x ∪ (¬ x) = μ.
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - unfold μ; apply Axiom_Scheme; split; auto.
    unfold Ensemble; exists (x ∪ ¬ x); auto.
  - unfold μ in H; apply Axiom_Scheme in H; destruct H.
    generalize (classic (z∈x)); intros.
    destruct H1; apply Theorem4; try tauto.
    right; apply Axiom_Scheme; split; auto.
Qed.

Hint Unfold μ : set.
Hint Resolve Property_μ : set.


(* Theorem19 : x∈μ iff x is a set. *)

Theorem Theorem19 : forall (x: Class),
  x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intro.
  - unfold μ in H; apply Axiom_Scheme in H; apply H.
  - unfold μ; apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem19 : set.


(* Theorem20 : x∪μ = μ and x∩μ = x. *)

Theorem Theorem20 : forall (x: Class), x ∪ μ = μ.
Proof.
  intros.
  apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; destruct H; auto.
    apply Theorem19; Ens.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem20' : forall (x: Class), x ∩ μ = x.
Proof.
  intros.
  apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; apply H.
  - apply Theorem4'; split; auto.
    apply Theorem19; Ens.
Qed.

Hint Resolve Theorem20 Theorem20' : set.


(* Definition22 : ∩x = {z : for each y, if y∈x, then z∈y}. *) 

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

Hint Unfold Element_I : set.


(* Definition23 : ∪x = {z : for some y, z∈y and y∈x}. *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

Hint Unfold Element_U : set.


(* Theorem24 : ∩Φ = μ and ∪Φ = Φ. *)

Theorem Theorem24 : ∩ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem19; Ens.
  - apply Axiom_Scheme; apply Theorem19 in H; split; auto.
    intros; generalize (Theorem16 y); contradiction.
Qed.

Theorem Theorem24' : ∪ Φ = Φ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H; destruct H, H0, H0.
    generalize (Theorem16 x); contradiction.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem24 Theorem24' : set. 


(* Definition25 : x⊂y iff for each z, if z∈x, then z∈y. *)

Definition Subclass x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Subclass x y) (at level 70).

Hint Unfold Subclass : set.


(* Theorem26 : Φ⊂x and x⊂μ. *)

Theorem Theorem26 : forall (x: Class), Φ ⊂ x.
Proof.
  intros.
  unfold Subclass; intros.
  generalize (Theorem16 z); intro; contradiction.
Qed.

Theorem Theorem26' : forall x, x ⊂ μ.
Proof.
  intros; unfold Subclass; intros; apply Theorem19; Ens.
Qed.

Hint Resolve Theorem26 Theorem26' : set.


(* Theorem27 : x=y iff x⊂y and y⊂x. *)

Theorem Theorem27 : forall (x y: Class),
  (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  intros; split; intros.
  - unfold Subclass in H; destruct H.
    apply Axiom_Extent; split; auto.
  - rewrite <- H; unfold Subclass; split; auto.
Qed.

Hint Resolve Theorem27 : set.


(* Theorem28 : If x⊂y and y⊂z, then x⊂z. *)

Theorem Theorem28 : forall (x y z: Class),
  x ⊂ y /\ y ⊂ z -> x ⊂ z.
Proof.
  intros; destruct H; unfold Subclass; intros.
  unfold Subclass in H1; auto.
Qed.

Hint Resolve Theorem28 : set.


(* Theorem29 : x⊂y iff x∪y=y. *)

Theorem Theorem29 : forall (x y: Class),
  x ∪ y = y <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros.
    apply Axiom_Extent with (z:=z) in H; apply H.
    apply Theorem4; left; auto.
  - apply Axiom_Extent; split; intros.
    + apply Theorem4 in H0; elim H0; intros; auto.
    + apply Theorem4; tauto.
Qed.

Hint Resolve Theorem29 : set.


(* Theorem30 : x⊂y iff x∩y=x. *)

Theorem Theorem30 : forall x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros; apply Axiom_Extent with (z:=z) in H.
    apply H in H0; apply Theorem4' in H0; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Theorem4' in H0; tauto.
    + apply Theorem4'; split; auto.
Qed.

Hint Resolve Theorem30 : set.


(* Theorem32 : If x∈y, x⊂∪y and ∩y⊂x. *)

Theorem Theorem32 : forall (x y: Class),
  x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros; split.
  - unfold Subclass; intros.
    apply Axiom_Scheme; split; Ens.
  - unfold Subclass; intros.
    apply Axiom_Scheme in H0; destruct H0.
    apply H1 in H; auto.
Qed.

Hint Resolve Theorem32 : set.


(* Proper Subset *)

Definition ProperSubclass x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperSubclass x y) (at level 70).

Lemma Property_ProperSubclass : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperSubclass; auto.
Qed.

Lemma Property_ProperSubclass' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperSubclass in H; destruct H.
  generalize (Theorem27 x y); intros.
  apply definition_not with (B:= (x ⊂ y /\ y ⊂ x)) in H0; try tauto.
  apply not_and_or in H0; destruct H0; try tauto.
  unfold Subclass in H0.
  apply not_all_ex_not in H0; destruct H0.
  apply imply_to_and in H0.
  exists x0; auto.
Qed.

Lemma Property_ProperSubclass'' : forall (x y: Class),
  x ⊂ y \/ y ⊂ x -> ~ (x ⊂ y) -> y ⊊ x.
Proof.
  intros; destruct H.
  - elim H0; auto.
  - unfold ProperSubclass; split; auto.
    intro; rewrite H1 in H.
    pattern x at 2 in H; rewrite <- H1 in H.
    contradiction.
Qed.

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperSubclass in H; destruct H; auto.
    apply Property_ProperSubclass' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Setminus; apply Theorem4'; split; auto.
      unfold Complement; apply Axiom_Scheme; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply Axiom_Extent; split; intros.
    + unfold Setminus in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply Axiom_Scheme in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.

Hint Unfold ProperSubclass : set.
Hint Resolve Property_ProperSubclass Property_ProperSubclass'
             Property_ProperSubclass'' Property_Φ: set.


(* III Axiom of subsets : If x is a set there is a set y such that for
   each z, if z⊂x, then z∈y. *)

Axiom Axiom_Subsets : forall (x: Class),
  Ensemble x -> exists y, Ensemble y /\ (forall z, z⊂x -> z∈y).

Hint Resolve Axiom_Subsets : set.


(* Theorem33 : If x is a set and z⊂x, then z is a set. *)

Theorem Theorem33 : forall (x z: Class),
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros.
  apply Axiom_Subsets in H; destruct H.
  apply H in H0; Ens.
Qed.

Hint Resolve Theorem33 : set.


(* Theorem35 : If x≠Φ, then ∩x is a set. *)

Lemma Property_NotEmpty : forall x, x ≠ Φ <-> exists z, z∈x.
Proof.
  intros; assert (x = Φ <-> ~ (exists y, y∈x)).
  { split; intros.
    - intro; destruct H0; rewrite H in H0.
      apply Axiom_Scheme in H0; destruct H0; case H1; auto.
    - apply Axiom_Extent; split; intros.
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


(* Definition36 : 2*x = {y : y⊂x}. *)

Definition PowerClass x : Class := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerClass x) (at level 0, right associativity).

Hint Unfold PowerClass : set.


(* Theorem38 : If x is a set, then 2*x is a set, and for each y,
   y⊂x iff y∈2*x. *)

Theorem Theorem38 : forall (x y: Class),
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros; split.
  - apply Axiom_Subsets in H; destruct H, H.
    assert (pow(x) ⊂ x0).
    { unfold Subclass; intros.
      unfold PowerClass in H1; apply Axiom_Scheme in H1.
      destruct H1; apply H0 in H2; auto. }
    apply Theorem33 in H1; auto.
  - split; intros.
    + apply Theorem33 with (z:=y) in H; auto.
      apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme in H0; apply H0.
Qed.

Hint Resolve Theorem38 : set.


(* Theorem39 : μ is not a set. *)

Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  generalize (classic (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \})).
  intros; destruct H.
  - double H; apply Axiom_Scheme in H; destruct H; contradiction.
  - intro; elim H; apply Axiom_Scheme; split; auto.
Qed.

Theorem Theorem39 : ~ Ensemble μ.
Proof.
  unfold not; generalize Lemma_N; intros.
  generalize (Theorem26' \{ λ x, x ∉ x \}); intros.
  apply Theorem33 in H1; auto.
Qed.

Hint Resolve Lemma_N Theorem39 : set.

Hint Resolve Theorem39 : set.


(* Definition40 : {x} = {z : if x∈u, then z=x}. *)

Definition Singleton x : Class := \{ λ z, x∈μ -> z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Hint Unfold Singleton : set.


(* Theorem41 : If x is a set, for each y, y∈[x] iff y=x. *)

Theorem Theorem41 : forall x, Ensemble x -> (forall y, y∈[x] <-> y=x).
Proof.
  intros; split; intros.
  - apply Axiom_Scheme in H0; destruct H0; apply H1.
    apply Theorem19 in H; auto.
  - apply Axiom_Scheme; split; intros; auto.
    rewrite <- H0 in H; auto.
Qed.

Hint Resolve Theorem41 : set.


(* Theorem42 : If x is a set, then {x} is a set. *)

Theorem Theorem42 : forall (x: Class),
  Ensemble x -> Ensemble [x].
Proof.
  intros.
  apply Lemma_x in H; elim H; intros.
  apply Theorem33 with (x:= pow(x)); auto.
  - apply Theorem38 in H0; auto.
  - unfold Subclass; intros.
    apply Theorem38 with (y:= z) in H0; auto.
    elim H0; intros; apply H4.
    unfold Singleton in H2.
    apply Axiom_Scheme in H2; elim H2; intros.
    rewrite H6; unfold Subclass; auto.
    apply Theorem19; auto.
Qed.

Hint Resolve Theorem42 : set.


(* Theorem43 : {x} = μ iff x is not a set. *)

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
    apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; elim H1; intros.
      apply Theorem19; auto.
    + apply Axiom_Scheme; split; intros.
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


(* Theorem44 : If x is a set, then ∩[x] = x and ∪[x] = x. *)

Theorem Theorem44 : forall x, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  intros; generalize (Theorem41 x H); intros.
  split; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H1; destruct H1; apply H2; apply H0; auto.
  - apply Axiom_Scheme; split; Ens; intros.
    apply H0 in H2; rewrite H2; auto.
  - apply Axiom_Scheme in H1; destruct H1, H2, H2.
    unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
    rewrite H4 in H2; auto; apply Theorem19; auto.
  - apply Axiom_Scheme; split; Ens; exists x; split; auto.
    unfold Singleton; apply Axiom_Scheme; auto.
Qed.

Hint Resolve Theorem44 : set.


(* IV Axiom of union : If x is a set and y is a set so is x∪y. *)

Axiom Axiom_Union : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble (x∪y).

Lemma Axiom_Union': forall (x y: Class),
  Ensemble (x∪y) -> Ensemble x /\ Ensemble y.
Proof.
  intros; split.
  - assert (x ⊂ (x∪y)).
    { unfold Subclass; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
  - assert (y ⊂ (x∪y)).
    { unfold Subclass; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
Qed.

Hint Resolve Axiom_Union Axiom_Union' : set.


(* Definition45 : {xy} = {x}∪{y}. *)

Definition Unordered x y : Class := [x]∪[y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

Hint Unfold Unordered : set.


(* Theorem46 : If x is a set and y is a set, then {xy} is a set and z∈{xy}
   iff z=x or z=y; {xy}=μ if and only if x is not a set or y is not a set. *)

Theorem Theorem46 : forall (x y: Class) (z: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x|y] /\ (z∈[x|y] <-> (z=x \/ z=y)).
Proof.
  intros.
  unfold Unordered; split.
  - apply Axiom_Union; elim H; intros; split.
    + apply Theorem42 in H0; auto.
    + apply Theorem42 in H1; auto.
  - split; intros.
    + apply Theorem4 in H0; elim H0; intros.
      * unfold Singleton in H1; apply Axiom_Scheme in H1.
        elim H1; intros; left; apply H3.
        apply Theorem19; apply H.
      * unfold Singleton in H1; apply Axiom_Scheme in H1.
        elim H1; intros; right; apply H3.
        apply Theorem19; apply H.
    + apply Theorem4; elim H0; intros.
      * left; unfold Singleton; apply Axiom_Scheme.
        split; try (rewrite H1; apply H); intro; apply H1.
      * right; unfold Singleton; apply Axiom_Scheme.
        split; try (rewrite H1; apply H); intro; apply H1.
Qed.

Hint Resolve Theorem46 : set.


(* Theorem47 : If x and y are sets, then ∩{xy} = x∩y and ∪{xy} = x∪y. *)

Theorem Theorem47 : forall x y,
  Ensemble x /\ Ensemble y -> (∩[x|y] = x ∩ y) /\ (∪[x|y] = x ∪ y).
Proof.
  intros; split; apply Axiom_Extent; intros.
  - split; intros.
    + apply Theorem4'.
      split; apply Axiom_Scheme in H0; destruct H0; apply H1; apply Theorem4.
      * left; apply Axiom_Scheme; split; try apply H; auto.
      * right; apply Axiom_Scheme; split; try apply H; auto.
    + apply Theorem4' in H0; destruct H0.
      apply Axiom_Scheme; split; intros; try AssE z.
      apply Theorem4 in H2; destruct H2.
      * apply Axiom_Scheme in H2; destruct H2; destruct H.
        apply Theorem19 in H; apply H4 in H; rewrite H; auto.
      * apply Axiom_Scheme in H2; destruct H2; destruct H.
        apply Theorem19 in H5; apply H4 in H5; rewrite H5; auto.
  - split; intros.
    + apply Axiom_Scheme in H0; destruct H0; destruct H1; destruct H1.
      apply Theorem4 in H2; apply Theorem4.
      destruct H2; apply Axiom_Scheme in H2; destruct H2.
      * left; destruct H; apply Theorem19 in H.
        apply H3 in H; rewrite H in H1; auto.
      * right; destruct H; apply Theorem19 in H4.
        apply H3 in H4; rewrite H4 in H1; auto.
    + apply Theorem4 in H0; apply Axiom_Scheme.
      split; destruct H0; try AssE z.
      * exists x; split; auto; apply Theorem4; left.
        apply Axiom_Scheme; split; try apply H; trivial.
      * exists y; split; auto; apply Theorem4; right.
        apply Axiom_Scheme; split; try apply H; trivial.
Qed.

Hint Resolve Theorem47 : set.


(* Definition48 : (x,y) = {{x}{y}}. *)

Definition Ordered x y : Class := [ [x] | [x|y] ].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

Hint Unfold Ordered : set.


(* Theorem49 : (x,y) is a set if and only if x is a set and y is a set. *)

Theorem Theorem49 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble x /\ Ensemble y.
Proof.
  intros; split; intro.
  - unfold Ordered in H; unfold Unordered in H.
    apply Axiom_Union' in H; elim H; intros.
    apply Theorem42' in H0; auto.
    apply Theorem42' in H0; auto.
    apply Theorem42' in H1; auto; split; auto.
    unfold Unordered in H1; apply Axiom_Union' in H1.
    elim H1; intros; apply Theorem42' in H3; auto.
  - elim H; intros; unfold Ordered; unfold Unordered.
    apply Axiom_Union; split.
    + apply Theorem42; auto; apply Theorem42; auto.
    + apply Theorem42; auto; apply Theorem46; auto.
Qed.

Hint Resolve Theorem49 : set.


(* Theorem50 : If x and y are sets, then ∪(x,y) = {xy}, ∩(x,y) = {x},
   ∪∩(x,y) = x, ∩∩(x,y) = x, ∪∪(x,y) = x∪y, ∩∪(x,y) = x∩y. *)

Lemma Lemma50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x] /\ Ensemble [x | y].
Proof.
  intros.
  apply Theorem49 in H; auto.
  unfold Ordered in H; unfold Unordered in H.
  apply Axiom_Union' in H; elim H; intros.
  apply Theorem42' in H0; auto.
  apply Theorem42' in H1; auto.
Qed.

Theorem Theorem50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\
  (∪(∩[x,y]) = x) /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y])=x∪y) /\ (∩(∪[x,y])=x∩y).
Proof.
  intros; elim H; intros.
  repeat unfold Ordered; apply Lemma50 in H.
  apply Theorem47 in H; auto; elim H; intros; repeat split.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Theorem4 in H4; elim H4; intros.
      * unfold Unordered; apply Theorem4; left; apply H5.
      * apply H5.
    + apply Theorem4; right; apply H4.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Theorem4' in H4; apply H4.
    + apply Theorem4'; split; auto.
      unfold Unordered; apply Theorem4; left; apply H4.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; elim H4; intros.
      elim H6; intros; elim H7; intros.
      apply Theorem4' in H9; elim H9; intros.
      unfold Singleton in H10; apply Axiom_Scheme in H10.
      elim H10; intros; rewrite <- H13. apply H8.
      apply Theorem19; apply H0.
    + apply Axiom_Scheme; split.
      * unfold Ensemble; exists x; apply H4.
      * exists x; split. apply H4.
        apply Theorem4'; split.
        -- unfold Singleton; apply Axiom_Scheme; split; auto.
        -- unfold Unordered; apply Theorem4.
           left; unfold Singleton; apply Axiom_Scheme.
           split; try apply H0; trivial.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; elim H4; intros.
      apply H6; apply Theorem4'; split.
      * unfold Singleton; apply Axiom_Scheme; split; auto.
      * unfold Unordered; apply Theorem4.
        left; unfold Singleton; apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme; split.
      * unfold Ensemble; exists x; apply H4.
      * intros; apply Theorem4' in H5; elim H5; intros.
        unfold Singleton in H6; apply Axiom_Scheme in H6.
        elim H6; intros;  rewrite H9. 
        apply H4. apply Theorem19; apply H0.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Theorem4; apply Axiom_Scheme in H4; elim H4; intros.
      elim H6; intros; elim H7; intros.
      apply Theorem4 in H9; elim H9; intros.
      * unfold Singleton in H10; apply Axiom_Scheme in H10.
        elim H10; intros; left; rewrite <- H12; try apply H8.
        apply Theorem19; apply H0.
      * unfold Unordered in H10; apply Theorem4 in H10; elim H10; intros.
        -- unfold Singleton in H11; apply Axiom_Scheme in H11.
           elim H11; intros; left; rewrite <- H13.
           apply H8. apply Theorem19; apply H0.
        -- unfold Singleton in H11; apply Axiom_Scheme in H11.
           elim H11; intros; right; rewrite <- H13.
           apply H8. apply Theorem19; apply H1.
    + apply Axiom_Scheme; apply Theorem4 in H4; split.
      * unfold Ensemble; elim H4; intros.
        -- exists x; apply H5.
        -- exists y; apply H5.
      * elim H4; intros.
        -- exists x; split; auto.
           apply Theorem4; left.
           unfold Singleton; apply Axiom_Scheme; split; auto.
        -- exists y; split; auto.
           apply Theorem4; right.
           unfold Unordered; apply Theorem4; right.
           unfold Singleton; apply Axiom_Scheme; split; auto.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Lemma_x in H4; elim H4; intros.
      apply Axiom_Scheme in H5; apply Axiom_Scheme in H6.
      elim H4; intros; apply Theorem4'; split; auto.
      * apply H5; apply Theorem4; left.
        unfold Singleton; apply Axiom_Scheme; split; auto.
      * apply H6; apply Theorem4; right.
        unfold Unordered; apply Theorem4; right.
        unfold Singleton; apply Axiom_Scheme; split; auto.
    + apply Theorem4' in H4; elim H4; intros.
      apply Axiom_Scheme; split.
      unfold Ensemble; exists x; apply H5.
      intros; apply Theorem4 in H7; destruct H7.
      * unfold Singleton in H7; apply Axiom_Scheme in H7.
        destruct H7; rewrite H8; auto.
        apply Theorem19; apply H0.
      * unfold Unordered in H7; apply Axiom_Scheme in H7; destruct H7, H8.
        -- unfold Singleton in H8; apply Axiom_Scheme in H8.
           destruct H8; rewrite H9; auto.
           apply Theorem19; apply H0.
        -- unfold Singleton in H8; apply Axiom_Scheme in H8.
           destruct H8; rewrite H9; auto.
           apply Theorem19; apply H1.
Qed.

Hint Resolve Theorem50 : set.


(* Definition51 : 1st coord z = ∩∩z. *)

Definition First (z: Class) := ∩∩z.

Notation " fst( z ) " := (First z) (at level 0).

Hint Unfold First : set.


(* Definition52 : 2nd coord z = (∩∪z)∪(∪∪z)~(∪∩z). *)

Definition Second (z: Class) := (∩∪z)∪(∪∪z)~(∪∩z).

Notation " snd( z ) " := (Second z) (at level 0).

Hint Unfold Second : set.


(* Theorem54 : If x and y are sets, 1st coord (x,y)=x and 2nd coord (x,y)=y. *)

Proposition Lemma54 : forall (x y: Class),
  (x ∪ y) ~ x = y ~ x.
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; apply Theorem4 in H; split; auto.
    destruct H; auto.
    unfold Complement in H0; apply Axiom_Scheme in H0.
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


(* Definition56 : r is a relation iff for each member z of r there is x and y
   such that z = (x,y). *)

Definition Relation r : Prop := forall z, z∈r -> exists x y, z = [x,y].

Hint Unfold Relation: set.


(* { (x,y) : ... } *)

Parameter Classifier_P : (Class -> Class -> Prop) -> Class.

Notation "\{\ P \}\" := (Classifier_P P) (at level 0).

Axiom Axiom_SchemeP : forall (a b: Class) (P: Class -> Class -> Prop),
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).

Axiom Property_P : forall (z: Class) (P: Class -> Class -> Prop),
  z ∈ \{\ P \}\ -> (exists a b, z = [a,b]) /\ z ∈ \{\ P \}\.

Ltac PP H a b:= apply Property_P in H; destruct H as [[a [b H]]];
rewrite H in *.

Hint Resolve Axiom_SchemeP Property_P: set.


(* Definition60 : r ⁻¹ = {[x,y] : [y,x]∈r} *)

Definition Inverse r : Class := \{\ λ x y, [y,x]∈r \}\.

Notation "r ⁻¹" := (Inverse r)(at level 5).

Hint Unfold Inverse : set.


(* Theorem61 : (r ⁻¹)⁻¹ = r *)

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
  Relation r -> (r ⁻¹)⁻¹ = r.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
    apply Axiom_SchemeP in H2; apply H2.
  - unfold Relation in H; double H0; apply H in H1.
    destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply Axiom_SchemeP; split; Ens; apply Axiom_SchemeP; split; auto.
    apply Lemma61; auto; Ens.
Qed.

Hint Rewrite Theorem61 : set.


(* Definition63 : f is a function iff f is a relation and for each x,
   each y, each z, if (x,y)∈f and (x,z)∈f, then y = z. *)

Definition Function f : Prop :=
  Relation f /\ (forall x y z, [x,y] ∈ f /\ [x,z] ∈ f -> y=z).

Hint Unfold Function : set.


(* Definition65 : domain f = {x : for some y, (x,y)∈f}. *)

Definition Domain f : Class := \{ λ x, exists y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

Lemma Property_dom : forall x y f,
  [x,y] ∈ f -> x ∈ dom( f ).
Proof.
  intros; apply Axiom_Scheme.
  split; eauto; AssE [x, y].
  apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Domain : set.


(* Definition66 : range f = {y : for some x, (x,y)∈f}. *)

Definition Range f : Class := \{ λ y, exists x, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

Lemma Property_ran : forall x y f,
  [x,y] ∈ f -> y ∈ ran( f ).
Proof.
  intros; apply Axiom_Scheme.
  split; eauto; AssE [x,y].
  apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Range : set.


(* Definition68 : f(x) = ∩{y : (x,y)∈f}. *)

Definition Value f x : Class := ∩ \{ λ y, [x,y] ∈ f \}.

Notation "f [ x ]" := (Value f x)(at level 5).

Lemma Property_Value : forall f x,
  Function f -> x ∈ (dom( f )) -> [x,f[x]] ∈ f.
Proof.
  intros; unfold Function in H;destruct H as [_ H].
  apply Axiom_Scheme in H0; destruct H0, H1.
  assert (x0=f[x]).
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme; split; intros; try Ens.
      apply Axiom_Scheme in H3; destruct H3.
      assert (x0=y). { apply H with x; split; auto. }
      rewrite <- H5; auto.
    + apply Axiom_Scheme in H2; destruct H2 as [_ H2].
      apply H2; apply Axiom_Scheme; split; auto.
      AssE [x, x0]; apply Theorem49 in H3; apply H3.
  - rewrite <- H2; auto.
Qed.

Hint Unfold Value : set.


(* Theorem69 : If x ∉ domain f, then f(x)=μ; If x ∈ domain f, then f[x]∈μ. *)

Lemma Lemma69 : forall x f,
  Function f -> ( x ∉ dom( f ) -> \{ λ y, [x,y] ∈ f \} = Φ ) /\
  ( x ∈ dom( f ) -> \{ λ y, [x,y] ∈ f \} <> Φ ).
Proof.
  intros; split; intros.
  - generalize (classic (\{ λ y0, [x, y0] ∈ f \} = Φ)); intro.
    destruct H1; auto; apply Property_NotEmpty in H1; auto.
    elim H1; intro z; intros; apply Axiom_Scheme in H2.
    destruct H2 as [H2 H3]; apply Property_dom in H3; contradiction.
  - apply Property_NotEmpty; auto; exists f[x].
    apply Axiom_Scheme;eapply Property_Value in H0; auto.
    split; auto; apply Property_ran in H0; Ens.
Qed.

Theorem Theorem69 : forall x f,
  ( x ∉ (dom( f )) -> f[x] = μ ) /\ ( x ∈ dom( f ) -> (f[x]) ∈  μ ).
Proof.
  intros; split; intros.
  - assert (\{ λ y, [x,y] ∈ f \} = Φ).
    { apply Axiom_Extent; split; intros.
       apply Axiom_Scheme in H0; destruct H0.
       apply Property_dom in H1; contradiction.
       generalize (Theorem16 z); intro; contradiction. }
    unfold Value; rewrite H0; apply Theorem24.
  - assert (\{ λ y, [x,y] ∈ f \} <> Φ).
    { intro.
       apply Axiom_Scheme in H; destruct H, H1.
       generalize (Axiom_Extent \{ λ y : Class,[x, y] ∈ f \} Φ); intro; destruct H2.
       apply H2 with x0 in H0; destruct H0.
       assert (x0 ∈ Φ).
       { apply H0; apply Axiom_Scheme; split; auto.
          AssE [x, x0];  apply Theorem49 in H5; tauto. }
       eapply Theorem16; eauto. }
     apply Theorem35 in H0; apply Theorem19; auto.
Qed.

Hint Resolve Theorem69 : set.


(* Property Value *)

Corollary Property_Value' : forall f x,
  Function f -> f[x] ∈ ran(f) -> [x,f[x]] ∈ f.
Proof.
  intros; apply Property_Value; auto.
  apply Axiom_Scheme in H0; destruct H0, H1.
  generalize (classic (x ∈ dom( f))); intros.
  destruct H2; auto; apply Theorem69 in H2; auto.
  rewrite H2 in H0; generalize (Theorem39); intro; contradiction.
Qed.


(* Theorem70 : If f is a function, then f = {(x,y) : y = f(x)}. *)

Theorem Theorem70 : forall f,
  Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - double H0; unfold Function, Relation in H; destruct H.
    apply H in H1; destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply Axiom_SchemeP; split; try Ens; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme; split; intros; try Ens.
      apply Axiom_Scheme in H3; destruct H3.
      apply Lemma_xy with (y:=[a, y] ∈ f) in H0; auto.
      apply H2 in H0; rewrite <- H0; auto.
    + unfold Value, Element_I in H1; apply Axiom_Scheme in H1; destruct H1.
      apply H3; apply Axiom_Scheme; split; auto; AssE [a,b].
      apply Theorem49 in H4; try apply H4.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
    generalize (classic (a ∈ dom( f ))); intros; destruct H3.
    + apply Property_Value in H3; auto; rewrite H2; auto.
    + apply Theorem69 in H3; auto.
      rewrite H3 in H2; rewrite H2 in H1.
      apply Theorem49 in H1; destruct H1 as [_ H1].
      generalize Theorem39; intro; contradiction.
Qed.

Hint Resolve Theorem70 : set.


(* V Axiom of substitution : If f is a function and domain f is a set,
   then range f is a set. *)

Axiom Axiom_Substitution : forall (f: Class),
  Function f -> Ensemble dom(f) -> Ensemble ran(f).

Hint Resolve Axiom_Substitution : set.


(* VI Axiom of amalgamation : If x is a set so is ∪x. *)

Axiom Axiom_Amalgamation : forall (x: Class), Ensemble x -> Ensemble (∪ x).

Hint Resolve Axiom_Amalgamation : set.


(* Definition72 : x × y = {(u,v) : u∈x and v∈y}. *)

Definition Cartesian x y : Class := \{\ λ u v, u∈x /\ v∈y \}\.

Notation "x × y" := (Cartesian x y)(at level 0, right associativity).

Hint Unfold Cartesian : set.


(* Theorem73 : If u and y are sets of is {u}×y. *)

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
    apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1 as [_ [_ H1]]; destruct H2 as [_ [_ H2]].
    rewrite H2; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1 as [_ [t H1]].
      apply Axiom_SchemeP in H1; tauto.
    + apply Axiom_Scheme; split; try Ens.
      exists [u,z]; apply Axiom_SchemeP; split; auto.
      AssE z; apply Theorem49; split; auto.
      apply Theorem49; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H1, H2.
      apply Axiom_SchemeP in H2; destruct H2, H3.
      rewrite H4; apply Axiom_SchemeP; repeat split; auto.
      * apply Theorem49; split; auto; AssE x0.
      * apply Axiom_Scheme; split; auto.
    + PP H1 a b; apply Axiom_SchemeP in H2; destruct H2, H3.
      apply Axiom_Scheme; split; auto; exists b.
      apply Axiom_SchemeP; repeat split; auto.
      * apply Theorem49; split; auto; AssE b.
      * apply Theorem19 in H; apply Axiom_Scheme in H3.
        destruct H3; rewrite H5; auto.
Qed.

Theorem Theorem73 : forall (u y:Class),
  Ensemble u /\ Ensemble y -> Ensemble ([u] × y).
Proof.
  intros; elim H; intros; apply Ex_Lemma73 in H; auto.
  destruct H,H,H2; rewrite <- H3; apply Axiom_Substitution; auto.
  rewrite H2; auto.
Qed.

Hint Resolve Theorem73 : set.


(* Theorem74 : If x and y are sets so is x×y. *)

Lemma Ex_Lemma74 : forall x y:Class, Ensemble x /\ Ensemble y -> 
  exists f:Class, Function f /\ dom( f ) = x /\ 
  ran( f ) = \{ λ z, (exists u, u∈x /\ z = [u] × y) \}.
Proof.
  intros; destruct H.
  exists (\{\ λ u z, (u∈x /\ z = [u] × y) \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; exists a; exists b; auto.
  - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1, H2, H3, H4; subst z; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; tauto.
    + apply Axiom_Scheme; split; try AssE z.
      exists (([z]) × y); apply Axiom_SchemeP.
      repeat split; auto; apply Theorem49; split; auto.
      apply Theorem73; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; apply Axiom_Scheme.
      split; auto; exists x0; tauto.
    + apply Axiom_Scheme in H1; destruct H1, H2, H2.
      apply Axiom_Scheme; split; auto.
      exists x0; apply Axiom_SchemeP; repeat split; auto.
      apply Theorem49; split; auto; AssE x0.
Qed.

Lemma Lemma74 : forall (x y:Class),Ensemble x /\ Ensemble y -> 
  ∪ \{ λ z, (exists u, u∈x /\ z = [u] × y) \} = x × y.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0, H1, H1.
    apply Axiom_Scheme in H2; destruct H2, H3, H3.
    rewrite H4 in H1; PP H1 a b.
    apply Axiom_SchemeP in H5; destruct H5, H6.
    apply Axiom_SchemeP; repeat split; auto.
    apply Axiom_Scheme in H6; destruct H6 as [_ H6].
    AssE x1; apply Theorem19 in H8.
    rewrite <- H6 in H3; auto.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1, H2.
    apply Axiom_Scheme; split; auto.
    exists (([a]) × y); split; AssE a.
    + apply Axiom_SchemeP; repeat split; auto.
      apply Axiom_Scheme; intros; auto.
    + apply Axiom_Scheme; split.
      * apply Theorem73; split; try apply H; auto.
      * exists a; split; auto.
Qed.

Theorem Theorem74 : forall (x y:Class), 
  Ensemble x /\ Ensemble y -> Ensemble x × y.
Proof.
  intros; double H; double H0; destruct H0.
  apply Ex_Lemma74 in H; destruct H, H, H3.
  rewrite <- H3 in H0; apply Axiom_Substitution in H0; auto.
  rewrite H4 in H0; apply Axiom_Amalgamation in H0.
  rewrite Lemma74 in H0; auto.
Qed.

Hint Resolve Theorem74 : set.


(* Theorem75 : If f is a function and domain f is a set,
   then f is a set. *)

Theorem Theorem75 : forall f, 
  Function f /\ Ensemble dom( f ) -> Ensemble f.
Proof.
  intros; destruct H.
  assert (Ensemble ran(f)); try apply Axiom_Substitution; auto.
  assert (Ensemble (dom( f)) × (ran( f))).
  { apply Theorem74; split; auto. }
  apply Theorem33 with (x:=(dom( f ) × ran( f ))); auto.
  unfold Subclass; intros; rewrite Theorem70 in H3; auto.
  PP H3 a b; rewrite <- Theorem70 in H4; auto; AssE [a,b].
  repeat split; auto; apply Axiom_SchemeP; split; auto.
  generalize (Property_dom a b f H4); intro.
  generalize (Property_ran a b f H4); intro; tauto.
Qed.

Hint Resolve Theorem75 : set.


(* Definition81 : x r y if and only if (x,y)∈r. *)

Definition Rrelation x r y : Prop := [x,y] ∈ r.

Hint Unfold Rrelation : set.


(* Definition82 : r connects x if and only if when u and v belong to x
   either u r v or v r u or v = u. *)

Definition Connect r x : Prop :=
  forall u v, u∈x /\ v∈x -> (Rrelation u r v) \/ (Rrelation v r u) \/ u=v.

Hint Unfold Connect : set.


(* Definition83 : r is transitive in x if and only if, when u, v, and w
   are members of x and u r v and v r w, then u r w. *)

Definition Transitive r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x /\ Rrelation u r v /\ Rrelation v r w)
  -> Rrelation u r w.

Hint Unfold Transitive: set.


(* Definition84 : r is asymmetric in x if and only if, when u and v are
   members of x and u r v, then it is not true that v r u. *)

Definition Asymmetric r x : Prop :=
  forall u v, (u ∈ x /\ v ∈ x /\ Rrelation u r v) -> ~ Rrelation v r u.

Corollary Property_Asy : forall r x u,
  Asymmetric r x -> u ∈ x -> ~ Rrelation u r u.
Proof.
  intros; intro.
  unfold Asymmetric in H; specialize H with u u.
  apply H; repeat split; auto.
Qed.

Hint Unfold Asymmetric: set.


(* Theorem86 : z is an r-first member of x if and only if z∈x and if y∈x,
   then it is false that y r z. *)

Definition FirstMember z r x : Prop :=
  z∈x /\ (forall y, y∈x -> ~ Rrelation y r z).

Hint Unfold FirstMember : set.


(* Strict and non-strict well orders are closely related. A non-strict well 
order may be converted to a strict partial order by removing all relationships
of the form a ≤ a. Conversely, a strict well order may be converted to a non-
strict well order by adjoining all relationships of that form. Thus, if "≤" is
a non-strict well order, then the corresponding strict partial order "<" is
the irreflexive kernel given by:

  a < b if a ≤ b and a ≠ b

Conversely, if "<" is a strict well order, then the corresponding non-strict
well order "≤" is the reflexive closure given by:

  a ≤ b if a < b or a = b.  *)

(* Definition87 : r well-orders x if and only if r connects x and if y⊂x and
   y≠Φ, then there is an r-first member of y. It is a strict well order. *)

Definition KWellOrder r x : Prop :=
  Connect r x /\ (forall y, y⊂x /\ y≠Φ -> exists z, FirstMember z r y).

Hint Unfold KWellOrder : set.


(* Theorem88 : If r well-orders x, then r is transitive in x and r is
   asymmetric in x. *)

Lemma Lemma88 : forall x u v w,
  Ensemble u -> Ensemble v -> Ensemble w -> x ∈ ([u] ∪ [v] ∪ [w]) ->
  x = u \/ x= v \/ x = w.
Proof.
  intros; apply Theorem19 in H; apply Theorem19 in H0; apply Theorem19 in H1.
  apply Axiom_Scheme in H2; destruct H2, H3.
  - left; apply Axiom_Scheme in H3; destruct H3; auto.
  - apply Axiom_Scheme in H3; destruct H3, H4.
    + right; left; apply Axiom_Scheme in H4; destruct H4; auto.
    + right; right; apply Axiom_Scheme in H4; destruct H4; auto.
Qed.

Theorem Theorem88 : forall r x,
  KWellOrder r x -> Transitive r x /\ Asymmetric r x .
Proof.
  intros; generalize H; intro; unfold KWellOrder in H0; destruct H0.
  assert (Asymmetric r x).
  { unfold Asymmetric; intros; destruct H2, H3; AssE u; AssE v.
    assert (([u | v] ⊂ x) /\ ([u | v] ≠ Φ)).
    { split.
      - unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
        + apply Theorem19 in H5; apply Axiom_Scheme in H8; destruct H8.
          rewrite H9; auto.
        + apply Theorem19 in H6; apply Axiom_Scheme in H8; destruct H8.
          rewrite H9; auto.
        - apply Property_NotEmpty; exists u; apply Axiom_Scheme; split; auto.
          left; apply Axiom_Scheme; split; auto. }
    apply H1 in H7; destruct H7; unfold FirstMember in H7; destruct H7.
    apply Theorem46 in H7; auto; destruct H7; subst x0.
    - apply H8; auto; apply Axiom_Scheme; split; auto; right; apply Axiom_Scheme; auto.
    - assert (u ∈ [u | v]).
      { apply Axiom_Scheme; split; auto; left; apply Axiom_Scheme; split; auto. }
      apply H8 in H7; auto. }
  split; auto; unfold Transitive; intros.
  - destruct H3, H4, H5, H6; unfold Connect in H0; specialize H0 with w u.
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    + assert (([u] ∪ [v] ∪ [w] ⊂ x) /\ ([u] ∪ [v] ∪ [w] ≠ Φ)).
      { split; unfold Subclass; intros.
        - apply Axiom_Scheme in H8; destruct H8 as [_ H8], H8.
          + AssE u; apply Theorem19 in H9; apply Axiom_Scheme in H8; destruct H8.
            rewrite H10; auto.
          + apply Axiom_Scheme in H8; destruct H8 as [_ H8]; destruct H8.
            * AssE v; apply Theorem19 in H9; apply Axiom_Scheme in H8.
              destruct H8; rewrite H10; auto.
            * AssE w; apply Theorem19 in H9; apply Axiom_Scheme in H8.
              destruct H8; rewrite H10; auto.
        - intro; generalize (Theorem16 u); intro.
          apply H9; rewrite <- H8; apply Axiom_Scheme; split; Ens.
          left; apply Axiom_Scheme; split; intros; auto; Ens. }
      apply H1 in H8; destruct H8; unfold FirstMember in H8; destruct H8.
      assert (u ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; left; apply Axiom_Scheme; split; Ens. }
      assert (v ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply Axiom_Scheme; split; Ens.
        left; apply Axiom_Scheme; split; Ens. }
      assert (w ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply Axiom_Scheme; split; Ens.
        right; apply Axiom_Scheme; split; Ens. }
      apply Lemma88 in H8; Ens; destruct H8 as [H8 | [H8 | H8]]; subst x0.
      * apply H9 in H12; contradiction.
      * apply H9 in H10; contradiction.
      * apply H9 in H11; contradiction.
    + subst w; unfold Asymmetric in H2; absurd (Rrelation u r v); auto.
Qed.

Hint Resolve Theorem88: set.


(* Definition89 : y is an r-section of x if and only if y⊂x, r well-orders x,
   and for each u and v such that u∈x, v∈y, and u r v it is true that u∈y. *)

Definition Section y r x : Prop :=
  y ⊂ x /\ KWellOrder r x /\
  (forall u v, (u ∈ x /\ v ∈ y /\ Rrelation u r v) -> u ∈ y).

Hint Unfold Section : set.


(* Theorem91 : If y is an r-section of x an y≠x, then y = {u : u∈x and u r v}
   for some v in x. *)

Theorem Theorem91 : forall x y r,
  Section y r x /\ y ≠ x ->
  (exists v, v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \}).
Proof.
  intros; destruct H.
  assert (exists v, FirstMember v r (x ~ y)).
  { unfold Section, KWellOrder in H; destruct H, H1, H1.
    assert ((x ~ y) ⊂ x).
    { red; intros; apply Axiom_Scheme in H4; tauto. }
    generalize (classic (x ~ y = Φ)); intro; destruct H5.
    - apply Property_Φ in H; apply H in H5.
      apply Property_Ineq in H0; contradiction.
    - apply H3; split; auto. }
  destruct H1; unfold FirstMember in H1; destruct H1; exists x0.
  apply Axiom_Scheme in H1; destruct H1, H3; split; auto.
  apply Axiom_Extent; split; intros.
  - unfold Section in H; destruct H, H6; apply Axiom_Scheme.
    repeat split; Ens; assert (z ∈ x); auto.
    unfold KWellOrder, Connect in H6; destruct H6 as [H6 _].
    specialize H6 with x0 z; destruct H6 as [H6|[H6|H6]]; auto.
    + assert (x0 ∈ y).
      { apply H7 with z; repeat split; auto. }
      apply Axiom_Scheme in H4; destruct H4; contradiction.
    + apply Axiom_Scheme in H4; destruct H4; subst x0; contradiction.
  - apply Axiom_Scheme in H5; destruct H5, H6.
    generalize (classic (z ∈ (x ~ y))); intro; destruct H8.
    + apply H2 in H8; contradiction.
    + generalize (classic (z ∈ y)); intro; destruct H9; auto.
      elim H8; apply Axiom_Scheme; repeat split; auto; apply Axiom_Scheme; tauto.
Qed.

Hint Resolve Theorem91 : set.


(* Theorem92 : If x and y are r-sections of z, then x⊂y or y⊂x. *)

Theorem Theorem92 : forall x y z r,
  Section x r z /\ Section y r z -> x ⊂ y \/ y ⊂ x.
Proof.
  intros; destruct  H.
  generalize (classic (x = z)); intro; destruct H1.
  - right; red in H0; subst z; tauto.
  - generalize (classic (y = z)); intro; destruct H2.
    + left; red in H; subst z; tauto.
    + apply Lemma_xy with (x:=(Section x r z)) in H1; auto.
      apply Lemma_xy with (x:=(Section y r z)) in H2; auto.
      apply Theorem91 in H1; destruct H1, H1; apply Theorem91 in H2.
      destruct H2, H2; unfold Section in H; destruct H as [_ [H _]].
      unfold KWellOrder in H; destruct H as [H _]; unfold Section in H0.
      destruct H0, H5; apply Theorem88 in H5; destruct H5.
      assert ((x0 ∈ z) /\ (x1 ∈ z)); try split; auto.
      unfold Connect in H; generalize (H _ _ H8); intros.
      destruct H9 as [H9 | [H9 | H9]].
      * left; unfold Subclass; intros; rewrite H3 in H10.
        apply Axiom_Scheme in H10; destruct H10, H11; rewrite H4; apply Axiom_Scheme.
        repeat split; auto; apply H5 with x0; auto.
      * right; unfold Subclass; intros; rewrite H4 in H10.
        apply Axiom_Scheme in H10; destruct H10, H11; rewrite H3; apply Axiom_Scheme.
        repeat split; auto; apply H5 with x1; auto.
      * right; subst x0; rewrite H3, H4; unfold Subclass; intros; auto.
Qed.

Hint Resolve Theorem92 : set.


(* Definition93 : f is r-s order preserving if and only if f is a function,
   r well-orders domain f, s well-orders range f, and f(u) s f(v) whenever u
   and v are members of domain f such that u r v. *)

Definition Order_Pr f r s : Prop := 
  Function f /\ KWellOrder r dom(f) /\ KWellOrder s ran(f) /\
  (forall u v, u ∈ dom(f) /\ v ∈ dom(f) /\ Rrelation u r v ->
  Rrelation f[u] s f[v]).

Hint Unfold Order_Pr : set.


(* Definition95 : f is a 1_1 function iff both f and f ⁻¹ are functions.*)

Definition Function1_1 f : Prop := Function f /\ Function (f ⁻¹).

Corollary Property_F11 : forall f,
  dom(f⁻¹) = ran(f) /\ ran(f⁻¹) = dom(f).
Proof.
  intros; unfold Domain, Range; split.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H; destruct H, H0; apply Axiom_SchemeP in H0.
      destruct H0; apply Axiom_Scheme; split; Ens.
    + apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
      exists x; apply Axiom_SchemeP; split; auto; apply Theorem49.
      AssE [x,z]; apply Theorem49 in H1; destruct H1; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H; destruct H, H0; apply Axiom_SchemeP in H0.
      destruct H0; apply Axiom_Scheme; split; Ens.
    + apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
      exists x; apply Axiom_SchemeP; split; auto; apply Theorem49.
      AssE [z,x]; apply Theorem49 in H1; destruct H1; auto.
Qed.

Hint Unfold Function1_1 : set.


(* Theorem96 : If f is r-s order preserving, then f is a 1_1 function and
   f ⁻¹ is s-r order preserving. *)

Lemma Lemma96 : forall f, dom( f) = ran( f ⁻¹).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
    exists x; apply Axiom_SchemeP; split; auto; apply Lemma61; Ens.
  - apply Axiom_Scheme in H; destruct H, H0.
    apply Axiom_Scheme; split; auto; exists x; apply Axiom_SchemeP in H0; tauto.
Qed.

Lemma Lemma96' : forall f, ran( f) = dom( f ⁻¹).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
    exists x; apply Axiom_SchemeP; split; auto; apply Lemma61; Ens.
  - apply Axiom_Scheme in H; destruct H, H0.
    apply Axiom_Scheme; split; auto; exists x; apply Axiom_SchemeP in H0; tauto.
Qed.

Lemma Lemma96'' : forall f u,
  Function f -> Function f ⁻¹ -> u ∈ ran(f) ->  (f⁻¹)[u] ∈ dom(f).
Proof.
  intros; rewrite Lemma96' in H1;  apply Property_Value in H1; auto.
  apply Axiom_SchemeP in H1; destruct H1; apply Property_dom in H2; auto.
Qed.

Lemma Lemma96''' : forall f u,
  Function f -> Function f ⁻¹ -> u ∈ ran(f) -> u = f  [(f ⁻¹) [u]].
Proof.
  intros; generalize (Lemma96'' _ _ H H0 H1); intro.
  apply Property_Value in H2; auto; rewrite Lemma96' in H1.
  apply Property_Value in H1; auto; apply Axiom_SchemeP in H1; destruct H1.
  red in H; destruct H; eapply H4; eauto.
Qed.

Theorem Theorem96 : forall f r s,
  Order_Pr f r s -> Function1_1 f /\ Order_Pr (f ⁻¹) s r.
Proof.
  intros; unfold Order_Pr in H; destruct H, H0, H1.
  assert (Function1_1 f).
  { unfold Function1_1; split; auto; unfold Function; split; intros.
    - red; intros; PP H3 a b; Ens.
    - destruct H3; rename y into u; rename z into v.
      apply Axiom_SchemeP in H3; destruct H3; apply Axiom_SchemeP in H4; destruct H4.
      double H5; double H6; apply Property_dom in H5; apply Property_dom in H6.
      double H7; double H8; apply Property_dom in H7; apply Property_dom in H8.
      rewrite Theorem70 in H9; auto; apply Axiom_SchemeP in H9.
      destruct H9 as [_ H9]; rewrite Theorem70 in H10; auto.
      apply Axiom_SchemeP in H10; destruct H10 as [_ H10]; rewrite H10 in H9.
      symmetry in H9; clear H10; apply Property_Value in H7; auto.
      apply Property_Value in H8; auto; apply Property_ran in H7.
      apply Property_ran in H8; double H0; double H1; apply Theorem88 in H11.
      destruct H11; unfold KWellOrder in H1; destruct H1 as [H1 _].
      unfold Connect in H1; specialize H1 with f [u] f [v]; destruct H0.
      unfold Connect in H0; specialize H0 with u v.
      destruct H0 as [H0 | [H0 | H0]]; try split; auto.
      + assert (Rrelation f [u] s f [v]); try apply H2; try tauto.
        rewrite H9 in H14; generalize (Property_Asy _ _ _ H12 H8); tauto.
      + assert (Rrelation f [v] s f [u]); try apply H2; try tauto.
        rewrite H9 in H14; generalize (Property_Asy _ _ _ H12 H8); tauto. }
  split; auto.
  - unfold Function1_1 in H3; destruct H3 as [_ H3]; unfold Order_Pr; intros.
    repeat rewrite <- Lemma96; repeat rewrite <- Lemma96'; split; auto.
    split; auto; split; intros; auto; destruct H4, H5.
    assert ((f ⁻¹) [u] ∈ dom(f)); try apply Lemma96''; auto.
    assert ((f ⁻¹) [v] ∈ dom(f)); try apply Lemma96''; auto.
    unfold KWellOrder in H0; destruct H0 as [H0 _]; unfold Connect in H0.
    specialize H0 with (f ⁻¹) [u] (f ⁻¹) [v].
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    + assert (Rrelation f  [(f ⁻¹) [v]] s f [(f ⁻¹) [u]] ); auto.
      rewrite <- Lemma96''' in H9; rewrite <- Lemma96''' in H9; auto.
      apply Theorem88 in H1; destruct H1; unfold Asymmetric in H10.
      generalize (Lemma_xy _ _ H5 (Lemma_xy _ _ H4 H9)); intro.
      generalize (H10 _ _ H11); intro; contradiction.
    + assert (f [(f ⁻¹) [u]] = f [(f ⁻¹) [v]]); rewrite H0; auto.
      rewrite <- Lemma96''' in H9; rewrite <- Lemma96''' in H9; auto.
      apply Theorem88 in H1; destruct H1.
      rewrite H9 in H6; apply Property_Asy with (r:=s) in H5; tauto.
Qed.

Hint Resolve Theorem96 : set.


(* Theorem97 : If f and g are r-s order preserving, domain f and domain g are r-
   sections of x and range f and range g are s-sections of y, then f⊂g or g⊂f. *)

Lemma Lemma97 : forall y r x,
  KWellOrder r x -> y ⊂ x -> KWellOrder r y.
Proof.
  intros; unfold KWellOrder in H; destruct H.
  unfold KWellOrder; intros; split; intros.
  - red; intros; apply H; destruct H2; split; auto.
  - specialize H1 with y0; apply H1; destruct H2.
    split; auto; eapply Theorem28; eauto.
Qed.

Lemma Lemma97' :  forall f g u r s v x y, 
  Order_Pr f r s /\ Order_Pr g r s ->
  FirstMember u r (\{ λ a ,a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}) ->
  g[v] ∈ ran( g) -> Section ran( f) s y -> Section dom( f) r x ->
  Section dom( g) r x -> Rrelation g [v] s g [u] -> f[u] = g[v] ->
  f ⊂ g \/ g ⊂ f.
Proof.
  intros.
  unfold FirstMember in H0; destruct H0; apply Axiom_Scheme in H0; destruct H0, H8.
  apply Axiom_Scheme in H8; destruct H8 as [_ [H8 H10]].
  destruct H; unfold Order_Pr in H, H11.
  apply Property_Value in H8; apply Property_Value in H10; try tauto.
  apply Property_ran in H8; apply Property_ran in H10; auto.
  assert (Rrelation v r u).
  { elim H11; intros; clear H13.
    apply Theorem96 in H11; destruct H11 as [_ H11].
    red in H11; destruct H11 as [H11 [_ [_ H13]]].
    double H1; double H10; rewrite Lemma96' in H14, H15.
    apply Property_Value' in H10; auto; apply Property_dom in H10.
    rewrite Lemma96 in H10; apply Property_Value' in H1; auto.
    apply Property_dom in H1; rewrite Lemma96 in H1.
    rewrite Lemma96''' with (f:=g⁻¹); try (rewrite Theorem61; apply H12); auto.
    pattern v; rewrite Lemma96''' with (f:=(g⁻¹));
    try rewrite Theorem61; try apply H11; try apply H12; auto. }
  assert (v ∈ \{ λ a, a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}).
  { apply Property_Value' in H1; try tauto; apply Property_dom in H1.
    apply Property_Value' in H8; try tauto; apply Property_dom in H8.
    apply Axiom_Scheme; repeat split; try Ens; try intro.
    - apply Axiom_Scheme; repeat split; try Ens; apply H3 with u; repeat split; auto.
      unfold Section in H4; apply H4; auto.
    - assert (v ∈ dom(f)).
      { apply H3 with u; repeat split; auto; apply H4 in H1; auto. }
      assert (Rrelation f [v] s f [u]). { apply H; repeat split; auto. }
      rewrite H13 in H15; unfold Section in H2; destruct H2, H16.
      generalize (Lemma97 _ _ _ H16 H2); intro; apply Theorem88 in H18.
      destruct H18; rewrite <- H13 in H15; rewrite H6 in H15.
      rewrite <- H13 in H15; apply Property_Value in H14; try tauto.
      apply Property_ran in H14; generalize (Property_Asy _ _ _ H19 H14).
      intro; contradiction. }
  apply H7 in H13; contradiction.
Qed.

Theorem Theorem97 : forall f g r s x y,
  Order_Pr f r s /\ Order_Pr g r s -> Section dom(f) r x /\ Section dom(g) r x
  -> Section ran(f) s y /\ Section ran(g) s y -> f ⊂ g \/ g ⊂ f.
Proof.
  intros; destruct H, H0, H1.
  assert (Order_Pr (g ⁻¹) s r). { apply Theorem96 in H2; tauto. }
  generalize (classic (\{ λ a, a ∈ (dom(f)∩dom(g)) /\ f[a]≠g[a]\} = Φ)); intro.
  destruct H6.
  - generalize (Lemma_xy _ _ H0 H3); intro.
    unfold Order_Pr in H; destruct H; unfold Order_Pr in H2; destruct H2.
    generalize (Theorem92 _ _ _ _ H7); intro; destruct H10.
    + left; unfold Subclass; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply Axiom_SchemeP in H13; destruct H13; rewrite Theorem70; auto.
      apply Axiom_SchemeP; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a]\}).
      { apply Axiom_Scheme; split; Ens; split; auto; apply Theorem30 in H10.
        rewrite H10; auto. }
      eapply Axiom_Extent in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
    + right; unfold Subclass; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply Axiom_SchemeP in H13; destruct H13; rewrite Theorem70; auto.
      apply Axiom_SchemeP; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a]\}).
      { apply Axiom_Scheme; split; Ens; split; auto; apply Theorem30 in H10.
        rewrite Theorem6' in H10; rewrite H10; auto. }
      eapply Axiom_Extent in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
  - assert (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a] \} ⊂ dom(f)).
    { unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
      apply Theorem4' in H8; tauto. }
    double H2; double H; unfold Order_Pr in H9; destruct H9, H10, H11.
    unfold KWellOrder in H10; destruct H10.
    generalize (Lemma_xy _ _ H7 H6); intro; apply H13 in H14.
    destruct H14 as [u H14]; double H14; unfold FirstMember in H15.
    destruct H15; apply Axiom_Scheme in H15; destruct H15, H17.
    unfold Order_Pr in H2; destruct H2 as [H19 [_ [H2 _]]].
    apply Axiom_Scheme in H17; destruct H17 as [_ [H17 H20]]; double H17; double H20.
    apply Property_Value in H17; apply Property_Value in H20; auto.
    apply Property_ran in H17; apply Property_ran in H20.
    generalize (Lemma_xy _ _ H1 H4); intro.
    apply Theorem92 in H23; auto; destruct H23.
    + apply H23 in H17; double H17; apply Axiom_Scheme in H17.
      destruct H17 as [_ [v H17]]; rewrite Theorem70 in H17; auto.
      apply Axiom_SchemeP in H17; destruct H17; rewrite H25 in H24.
      generalize (Lemma_xy _ _ H24 H20); intro; unfold KWellOrder in H2.
      destruct H2 as [H2 _]; unfold Connect in H2; apply H2 in H26.
      destruct H26 as [H26 | [H26 | H26]].
      * apply (Lemma97' f g u r s v x y); auto.
      * red in H1; destruct H1 as [_ [_ H1]]; rewrite <- H25 in H26.
        assert (g [u] ∈ ran( f)).
        { apply H1 with f [u]; repeat split; auto; unfold Section in H4.
          apply H4; apply Property_ran with u; apply Property_Value; auto.
          apply Property_ran with u; apply Property_Value; auto. }
        apply Axiom_Scheme in H27; destruct H27 as [_ [v1 H27]]; double H27.
        apply Property_dom in H28; apply Property_Value in H28; auto.
        rewrite Theorem70 in H27; auto; apply Axiom_SchemeP in H27.
        destruct H27 as [_ H27]; rewrite H27 in H26.
        assert (g ⊂ f \/ f ⊂ g).
        { apply (Lemma97' g f u r s v1 x y); try tauto; try rewrite Theorem6'.
          assert (\{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a]\} =
                  \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ g[a] ≠ f[a] \}).
          { apply Axiom_Extent; split; intros; apply Axiom_Scheme in H29; apply Axiom_Scheme.
            - repeat split; try tauto; apply Property_Ineq; tauto.
            - repeat split; try tauto; apply Property_Ineq; tauto. }
          rewrite <- H29; auto. apply Property_ran in H28; auto. }
        tauto.
      * rewrite <- H25 in H26; contradiction.
    + apply H23 in H20; double H18.
      apply Axiom_Scheme in H20; destruct H20 as [_ [v H20]]; double H20.
      apply Property_dom in H25; apply Property_Value in H25; auto.
      assert (f [v] = g [u]). { eapply H9; eauto. }
      apply Property_ran in H20; generalize (Lemma_xy _ _ H17 H20); intro.
      unfold KWellOrder in H11; destruct H11 as [H11 _]; apply H11 in H27.
      destruct H27 as [H27 | [H27 | H27]]; try contradiction.
      * unfold Section in H4; destruct H4 as [_ [_ H4]].
        assert (f[u] ∈ ran( g)).
        { apply H4 with g[u]; repeat split; auto. red in H1; apply H1.
          apply Property_ran with u; apply Property_Value; auto.
          apply Property_ran with u; apply Property_Value; auto. }
        apply Axiom_Scheme in H28; destruct H28 as [_ [v1 H28]]; double H28.
        apply Property_dom in H29; apply Property_Value in H29; auto.
        rewrite Theorem70 in H28; auto; apply Axiom_SchemeP in H28; destruct H28.
        rewrite H30 in H27; apply (Lemma97' f g u r s v1 x y); try tauto; auto.
        apply Property_ran with v1; auto.
      * assert (g ⊂ f \/ f ⊂ g).
        { rewrite <- H26 in H27, H20.
          apply (Lemma97' g f u r s v x y); try tauto; auto; rewrite Theorem6'.
          assert (\{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a]\} =
                  \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ g[a] ≠ f[a]\}).
          { apply Axiom_Extent; split; intros; apply Axiom_Scheme in H28; apply Axiom_Scheme.
            - repeat split; try tauto; apply Property_Ineq; tauto.
            - repeat split; try tauto; apply Property_Ineq; tauto. }
          rewrite <- H28; auto. }
        tauto.
Qed.

Hint Resolve Theorem97 : set.


(* Definition98 : f is r-s order preserving in x and y if and only if r
   well-orders x, s well-orders y, f is r-s order preserving, domain f is an
   r-section of x, and range f is an s-section of y. *)

Definition Order_PXY  f x y r s : Prop :=
  KWellOrder r x /\ KWellOrder s y /\ Order_Pr f r s /\
  Section dom(f) r x /\ Section ran(f) s y.

Hint Unfold Order_PXY : set.


(* Theorem99 : If r well-orders x and s well-orders y, then there is a function
   f which is r-s order preserving in x and y such that either domain f = x or
   range f = y.  *)

Definition En_f x y r s :=
  \{\ λ u v, u ∈ x /\ (exists g, Function g /\ Order_PXY g x y r s /\
      u ∈ dom(g) /\ [u,v] ∈ g ) \}\.

Lemma Lemma99 : forall y r x,
  KWellOrder r x -> Section y r x -> KWellOrder r y.
Proof.
  intros; red in H0; eapply Lemma97; eauto; tauto.
Qed.

Lemma Lemma99' : forall a b f z,
  ~ a ∈ dom(f) -> Ensemble a -> Ensemble b -> (z ∈ dom(f) -> 
  (f ∪ [[a,b]]) [z] = f [z]).
Proof.
  intros.
  apply Axiom_Extent; split; intros; apply Axiom_Scheme in H3; destruct H3;
  apply Axiom_Scheme; split; intros; auto.
  - apply H4; apply Axiom_Scheme in H5; destruct H5.
    apply Axiom_Scheme; split; auto; apply Axiom_Scheme; split; Ens.
  - apply H4; apply Axiom_Scheme in H5; destruct H5; apply Axiom_Scheme; split; auto.
    apply Axiom_Scheme in H6; destruct H6, H7; auto; apply Axiom_Scheme in H7.
    destruct H7; assert([a,b]∈μ). { apply Theorem19; apply Theorem49; tauto. }
    generalize (H8 H9); intro; apply Theorem49 in H6.
    apply Theorem55 in H10; auto; destruct H10.
    rewrite H10 in H2; contradiction.
Qed.

Lemma Lemma99'' : forall a b f z,
  ~ a ∈ dom(f) -> Ensemble a -> Ensemble b -> (z=a -> (f ∪ [[a,b]]) [z] = b).
Proof.
  intros; apply Axiom_Extent; split; intros; subst z.
  - apply Axiom_Scheme in H3; destruct H3; apply H3; apply Axiom_Scheme; split; auto.
    apply Axiom_Scheme; split; try apply Theorem49; try tauto.
    right; apply Axiom_Scheme; split; try apply Theorem49; try tauto.
  - apply Axiom_Scheme; split; intros; Ens; apply Axiom_Scheme in H2; destruct H2;
    apply Axiom_Scheme in H4; destruct H4, H5.
    + apply Property_dom in H5; contradiction.
    + apply Axiom_Scheme in H5; destruct H5.
      assert ([a, b] ∈ μ). { apply Theorem19; apply Theorem49; tauto. }
      generalize (H6 H7); intro; apply Theorem49 in H4.
      apply Theorem55 in H8; auto; destruct H8; rewrite H9; auto.
Qed.

Lemma Lemma99''' : forall y r x a b,
  Section y r x -> a ∈ y -> ~ b ∈ y -> b ∈ x -> Rrelation a r b.
Proof.
  intros; unfold Section in H; destruct H, H3.
  unfold KWellOrder in H3; destruct H3; unfold Connect in H3.
  assert (a ∈ x); auto; generalize (Lemma_xy _ _ H2 H6); intro.
  apply H3 in H7; destruct H7 as [H7 | [H7 | H7]]; auto.
  - assert (b ∈ y). { eapply H4; eauto. } contradiction.
  - rewrite H7 in H1; contradiction.
Qed.

Theorem Theorem99 : forall r s x y,
  KWellOrder r x /\ KWellOrder s y -> exists f, Function f /\
  Order_PXY f x y r s /\ (dom(f) = x \/ ran(f) = y).
Proof.
  intros.
  assert (Function (En_f x y r s)).
  { unfold Function; split; intros.
    - unfold Relation; intros; PP H0 a b; eauto.
    - destruct H0; apply Axiom_SchemeP in H0; destruct H0, H2, H3, H3, H4, H5.
      unfold Order_PXY in H4; destruct H4 as [_ [_ [H4 [H7 H8]]]].
      apply Axiom_SchemeP in H1; destruct H1, H9, H10, H10, H11, H12.
      unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H14 H15]]]].
      assert (x1 ⊂ x2 \/ x2 ⊂ x1). { apply (Theorem97 x1 x2 r s x y); tauto. }
      destruct H16.
      + apply H16 in H6; eapply H10; eauto.
      + apply H16 in H13; eapply H3; eauto. }
  exists (En_f x y r s); split; auto.
  assert (Section (dom(En_f x y r s)) r x).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; tauto.
    - split; try tauto; intros; destruct H1, H2; apply Axiom_Scheme in H2.
      destruct H2, H4; apply Axiom_SchemeP in H4; destruct H4, H5, H6.
      apply Axiom_Scheme; split; Ens; exists ((En_f x y r s)[u]).
      apply Property_Value; auto; apply Axiom_Scheme; split; Ens.
      assert (u ∈ dom( x1)).
      { destruct H6, H7; unfold Order_PXY in H7; destruct H7, H9, H10, H11.
        unfold Section in H11; destruct H11, H13; apply H14 with v.
        destruct H8; tauto. }
      exists (x1[u]); apply Axiom_SchemeP; repeat split; auto.
      + apply Theorem49; split; Ens.
        apply Theorem19; apply Theorem69; try tauto.
      + exists x1; split; try tauto; split; try tauto.
        split; auto; apply Property_Value; try tauto. }
  assert (Section (ran(En_f x y r s)) s y).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H2; destruct H2, H3.
      apply Axiom_SchemeP in H3; destruct H3, H4, H5, H5, H6, H7.
      unfold Order_PXY in H6; destruct H6 as [_ [_ [_ [_ H6]]]].
      destruct H6 as [H6 _]; apply Property_ran in H8; auto.
    - split; try tauto; intros; destruct H2, H3; apply Axiom_Scheme in H3.
      destruct H3, H5; apply Axiom_SchemeP in H5; destruct H5, H6, H7.
      apply Axiom_Scheme; split; Ens; exists (x1⁻¹[u]); apply Axiom_SchemeP.
      destruct H7 as [H7 [H8 [H9 H10]]]; double H8; unfold Order_PXY in H8.
      destruct H8 as [_ [_ [H12 [H13 H8]]]]; generalize H11 as H20; intro.
      unfold Order_PXY in H11; destruct H11 as [H11 [_ H19]].
      unfold Section in H8; destruct H8 as [H8 [_ H15]].
      assert (u ∈ ran( x1)).
      { apply Property_ran in H10; apply H15 with v; tauto. }
      generalize H14 as H21; intro; apply Theorem96 in H12; destruct H12.
      unfold Function1_1 in H12; destruct H12; apply Lemma96'' in H14; auto.
      repeat split; auto.
      + apply Theorem49; split; Ens.
      + apply Property_Value in H14; auto; rewrite <- Lemma96''' in H14; auto.
        apply Property_dom in H14; destruct H19 as [_ [[H19 _] _]]; auto.
      + exists x1; split; try tauto; split; try tauto; split; auto.
        apply Property_Value in H14; auto; rewrite <- Lemma96''' in H14; auto. }
  assert (Order_PXY (En_f x y r s) x y r s).
  { unfold Order_PXY; split; try tauto; split; try tauto; split; [idtac|tauto].
    unfold Order_Pr; split; auto; destruct H; split; try eapply Lemma99; eauto.
    split; intros; try eapply Lemma99; eauto; destruct H4, H5; double H4.
    double H5; apply Property_Value in H4; apply Property_Value in H5; auto.
    apply Axiom_SchemeP in H4; destruct H4 as [H4 [H9 [g1 [H10 [H11 [H12 H13]]]]]].
    apply Axiom_SchemeP in H5; destruct H5 as [H5 [H14 [g2 [H15 [H16 [H17 H18]]]]]].
    rewrite Theorem70 in H13; auto; apply Axiom_SchemeP in H13.
    destruct H13 as [_ H13]; rewrite Theorem70 in H18; auto.
    apply Axiom_SchemeP in H18; destruct H18 as [_ H18].
    rewrite H13, H18; clear H13 H18.
    unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H13 H18]]]].
    unfold Order_PXY in H16; destruct H16 as [_ [_ [H16 [H19 H20]]]].
    generalize (Lemma_xy _ _ H11 H16); intro.
    apply (Theorem97 g1 g2 r s x y) in H21; apply Property_Value in H12; auto.
    apply Property_Value in H17; auto; destruct H21.
    - apply H21 in H12; double H12; rewrite Theorem70 in H12; auto.
      apply Axiom_SchemeP in H12; destruct H12 as [_ H12]; rewrite H12.
      apply Property_dom in H22; apply Property_dom in H17; apply H16; tauto.
    - apply H21 in H17; double H17; rewrite Theorem70 in H17; auto.
      apply Axiom_SchemeP in H17; destruct H17 as [_ H17]; rewrite H17.
      apply Property_dom in H12; apply Property_dom in H22; apply H11; tauto. }
  split; auto; apply NNPP; intro; apply not_or_and in H4; destruct H4.
  assert (exists u, FirstMember u r (x ~ dom( En_f x y r s))).
  { unfold Section in H1; destruct H1, H6.
    assert ((x ~ dom( En_f x y r s)) ⊂ x).
    { red; intros; apply Axiom_Scheme in H8; tauto. }
    assert ((x ~ dom( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H1; apply H1 in H9; apply H4; auto. }
    generalize (Lemma97 _ _ _ H6 H8); intro; apply H10.
    repeat split; auto; red; auto. }
  assert (exists v, FirstMember v s (y ~ ran( En_f x y r s))).
  { unfold Section in H2; destruct H2, H7.
    assert ((y ~ ran( En_f x y r s)) ⊂ y).
    { red; intros; apply Axiom_Scheme in H9; tauto. }
    assert ((y ~ ran( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H2; apply H2 in H10; apply H5; auto. }
    generalize (Lemma97 _ _ _ H7 H9); intro; apply H11.
    repeat split; auto; red; auto. }
  destruct H6 as [u H6]; destruct H7 as [v H7].
  unfold FirstMember in H6; unfold FirstMember in H7; destruct H6, H7.
  apply Axiom_Scheme in H6; destruct H6 as [_ [H6 H10]]; apply Axiom_Scheme in H10.
  destruct H10 as [_ H10]; apply H10; apply Axiom_Scheme; split; Ens.
  exists v; apply Axiom_SchemeP; split; try apply Theorem49; split; try Ens.
  exists ((En_f x y r s) ∪ [[u,v]]).
  assert (Function (En_f x y r s ∪ [[u, v]])).
  { assert ([u, v] ∈ μ) as H18.
    { apply Theorem19; apply Theorem49; split; try Ens. }
    unfold Function; split; intros.
    - unfold Relation; intros.
      apply Axiom_Scheme in H11; destruct H11 as [H11 [H12 | H12]].
      + PP H12 a b; eauto.
      + apply Axiom_Scheme in H12; exists u,v; apply H12; auto.
    - destruct H11; apply Axiom_Scheme in H11; apply Axiom_Scheme in H12.
      destruct H11 as [H11 [H13 | H13]], H12 as [H12 [H14 | H14]].
      + unfold Function in H0; eapply H0; eauto.
      + apply Property_dom in H13; apply Axiom_Scheme in H14; destruct H14.
        apply Theorem55 in H15; apply Theorem49 in H12; auto.
        destruct H15; rewrite H15 in H13; contradiction.
      + apply Property_dom in H14; apply Axiom_Scheme in H13; destruct H13.
        apply Theorem55 in H15; apply Theorem49 in H11; auto.
        destruct H15; rewrite H15 in H14; contradiction.
      + apply Axiom_Scheme in H13; destruct H13; apply Theorem49 in H13.
        apply Theorem55 in H15; auto; apply Axiom_Scheme in H14; destruct H14.
        apply Theorem55 in H16; apply Theorem49 in H12; auto.
        destruct H15, H16; rewrite H17; auto. }
  split; auto.
  assert (Section (dom(En_f x y r s ∪ [[u, v]])) r x).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H12; destruct H12, H13.
      apply Axiom_Scheme in H13; destruct H13, H14.
      + apply Property_dom in H14; unfold Section in H1; apply H1; auto.
      + apply Axiom_Scheme in H14; destruct H14.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H15 in H16; apply Theorem49 in H13; apply Theorem55 in H16; auto.
        destruct H16; rewrite H16; auto.
    - split; try tauto; intros; destruct H12, H13; apply Axiom_Scheme in H13.
      destruct H13, H15; apply Axiom_Scheme in H15; destruct H15, H16.
      + apply Axiom_Scheme; split; Ens.
        assert ([u0,(En_f x y r s)[u0]] ∈ (En_f x y r s)).
        { apply Property_dom in H16; apply Property_Value; auto.
          apply H1 with v0; repeat split; auto. }
        exists (En_f x y r s)[u0]; apply Axiom_Scheme; split; Ens.
      + apply Axiom_Scheme in H16; destruct H16.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H17 in H18; apply Theorem49 in H16; apply Theorem55 in H18; auto.
        destruct H18; subst v0.
        assert ([u0,(En_f x y r s)[u0]] ∈ (En_f x y r s)).
        { apply Property_Value; auto.
          generalize (classic (u0 ∈ dom( En_f x y r s))); intro.
          destruct H18; auto; absurd (Rrelation u0 r u); auto.
          apply H8; apply Axiom_Scheme; repeat split; Ens.
          apply Axiom_Scheme; split; Ens. }
        apply Axiom_Scheme; split; Ens; exists ((En_f x y r s)[u0]).
        apply Axiom_Scheme; split; Ens. }
  assert (Section (ran(En_f x y r s ∪ [[u, v]])) s y).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H13; destruct H13, H14.
      apply Axiom_Scheme in H7; destruct H7 as [_ [H7 _]] .
      apply Axiom_Scheme in H14; destruct H14, H15.
      + apply Property_ran in H15; unfold Section in H2; apply H2; auto.
      + apply Axiom_Scheme in H15; destruct H15.
        assert ([u, v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H16 in H17; apply Theorem55 in H17; apply Theorem49 in H14; auto.
        destruct H17; rewrite H18; auto.
    - split; try tauto; intros; destruct H13, H14; apply Axiom_Scheme in H14.
      destruct H14, H16; unfold Order_PXY in H3; destruct H3 as [_ [_ [H3 _]]].
      apply Theorem96 in H3; destruct H3 as [[_ H3] _].
      apply Axiom_Scheme in H16; destruct H16, H17.
      + apply Axiom_Scheme; split; Ens.
        assert ([((En_f x y r s) ⁻¹) [u0], u0] ∈ (En_f x y r s)).
        { assert (u0 ∈ ran( En_f x y r s)). 
          { apply Property_ran in H17; apply H2 with v0; repeat split; auto. }
          pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
          apply Property_Value'; auto; rewrite <- Lemma96'''; auto. }
        exists ((En_f x y r s) ⁻¹) [u0]; apply Axiom_Scheme; split; Ens.
      + apply Axiom_Scheme in H17; destruct H17.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H18 in H19; apply Theorem55 in H19; apply Theorem49 in H16; auto.
        destruct H19; subst v0.
        assert ([((En_f x y r s) ⁻¹)[u0], u0] ∈ (En_f x y r s)).
        { generalize (classic (u0 ∈ ran( En_f x y r s))); intro; destruct H20.
          - pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
            apply Property_Value'; auto; rewrite <- Lemma96'''; auto.
          - absurd (Rrelation u0 s v); auto; apply H9; apply Axiom_Scheme.
            repeat split; Ens; apply Axiom_Scheme; split; Ens. }
        apply Axiom_Scheme; split; Ens; exists ((En_f x y r s) ⁻¹)[u0].
        apply Axiom_Scheme; split; Ens. }
  split.
  - unfold Order_PXY; split; try tauto; split; try tauto; split; [idtac|tauto].
    unfold Order_Pr; intros; split; auto.
    split; try eapply Lemma99; eauto; try apply H.
    split; try eapply Lemma99; eauto; try apply H; intros; destruct H14, H15.
    apply Axiom_Scheme in H14; destruct H14, H17; apply Axiom_Scheme in H17.
    destruct H17 as [_ H17]; apply Axiom_Scheme in H15; destruct H15, H18.
    apply Axiom_Scheme in H18; destruct H18 as [_ H18].
    assert ([u,v]∈μ) as H20. { apply Theorem19; apply Theorem49; split; Ens. }
    destruct H17, H18.
    + apply Property_dom in H17; apply Property_dom in H18.
      repeat rewrite Lemma99'; auto; Ens; unfold Order_PXY in H3.
      destruct H3 as [_ [_ [H3 _]]]; unfold Order_Pr in H3; eapply H3; eauto.
    + apply Property_dom in H17; rewrite Lemma99'; auto; Ens.
      apply Axiom_Scheme in H18; destruct H18; apply H19 in H20.
      apply Theorem55 in H20; destruct H20; apply Theorem49 in H18; auto.
      rewrite Lemma99''; auto; Ens.
      apply Lemma99''' with (y:=(ran( En_f x y r s))) (x:=y); auto.
      * apply Property_Value in H17; auto; double H17.
        apply Property_ran in H17; apply Axiom_Scheme; split; Ens.
      * apply Axiom_Scheme in H7; destruct H7, H22; apply Axiom_Scheme in H23; tauto.
      * apply Axiom_Scheme in H7; tauto.
    + apply Property_dom in H18; pattern ((En_f x y r s ∪ [[u,v]])[v0]).
      rewrite Lemma99'; Ens.
      assert (u0 ∈ dom( En_f x y r s)).
      { unfold Section in H1; apply H1 with v0; split; auto.
        apply Axiom_Scheme in H17; destruct H17; apply H19 in H20.
        apply Theorem55 in H20; apply Theorem49 in H17; auto.
        destruct H20; rewrite H20; auto. }
      rewrite Lemma99'; Ens; unfold Order_PXY in H3.
      destruct H3 as [_ [_ [H3 _]]]; unfold Order_Pr in H3; eapply H3; eauto.
    + double H20; apply Axiom_Scheme in H17; destruct H17; apply H21 in H19.
      apply Axiom_Scheme in H18; destruct H18; apply H22 in H20.
      apply Theorem55 in H20; destruct H20; apply Theorem49 in H18; auto.
      apply Theorem55 in H19; destruct H19; apply Theorem49 in H17; auto.
      subst u0 v0; destruct H as [H _]; apply Theorem88 in H.
      destruct H as [_ H]; apply Property_Asy with (u:=u) in H; tauto.
  - assert (Ensemble ([u,v])). { apply Theorem49; split; Ens. } split.
    + apply Axiom_Scheme; split; Ens; exists v; apply Axiom_Scheme; split; Ens.
      right; apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem99 : set.


(* VII Axiom of regularity : If x ≠ Φ there is a member y of x such x∩y = Φ. *)

Axiom Axiom_Regularity : forall x, x ≠ Φ -> exists y, y∈x /\ x ∩ y = Φ.

Hint Resolve Axiom_Regularity : set.


(* Theorem101 : x ∉ x. *)

Theorem Theorem101 : forall x, x ∉ x.
Proof.
  intros.
  generalize (classic (x∈x)); intros.
  destruct H; auto; assert ([x] ≠ Φ).
  { apply Property_NotEmpty; exists x.
    unfold Singleton; apply Axiom_Scheme; Ens. }
  apply Axiom_Regularity in H0; destruct H0 as [y H0], H0.
  unfold Singleton in H0; apply Axiom_Scheme in H0; destruct H0.
  rewrite H2 in H1; try (apply Theorem19); Ens.
  assert (x ∈ ([x] ∩ x)).
  { apply Theorem4'; split; auto.
    unfold Singleton; apply Axiom_Scheme; Ens. }
  rewrite H1 in H3; generalize (Theorem16 x); contradiction.
Qed.

Hint Resolve Theorem101 : set.


(* Theorem102 : It is false that x∈y and y∈x. *)

Theorem Theorem102 : forall x y, ~ (x ∈ y /\ y ∈ x).
Proof.
  intros; intro; destruct H.
  assert (\{ λ z, z = x \/ z =y \} ≠ Φ).
  { apply Property_NotEmpty; exists x; apply Axiom_Scheme; split; Ens. }
  apply Axiom_Regularity in H1; destruct H1, H1; apply Axiom_Scheme in H1; destruct H1.
  destruct H3; subst x0.
  - assert (y ∈ (\{ λ z, z = x \/ z = y \} ∩ x)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H3; generalize (Theorem16 y); intro; contradiction.
  - assert (x ∈ (\{ λ z, z = x \/ z = y \} ∩ y)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H3; generalize (Theorem16 x); intro; contradiction.
Qed.

Hint Resolve Theorem102 : set.


(* Definition103 : E = {(x,y) : x∈y}. *)

Definition E : Class := \{\ λ x y, x∈y \}\.

Hint Unfold E : set.


(* Definition105 : x is full iff each member of x is a subset of x. *)

Definition full x : Prop := forall m, m∈x -> m⊂x.

Corollary Property_Full : forall x,
  full x <-> (forall u v : Class, v ∈ x /\ u ∈ v -> u ∈ x).
Proof.
  intros; split; intros.
  - unfold full in H; destruct H0; apply H in H0; auto.
  - unfold full; intros; unfold Subclass; intros; apply H with m; tauto.
Qed.

Hint Unfold full : set.


(* Definition106 : x is an ordinal iff E connects x and x is full.  *)

Definition Ordinal x : Prop := Connect E x /\ full x.

Hint Unfold Ordinal : set.


(* Theorem107 : If x is an ordinal E well-orders x. *)

Theorem Theorem107 : forall x, Ordinal x -> KWellOrder E x.
Proof.
  intros.
  unfold Ordinal in H; destruct H.
  unfold KWellOrder; intros.
  split; auto; intros; destruct H1.
  apply Axiom_Regularity in H2; destruct H2, H2.
  exists x0; unfold FirstMember; intros.
  split; auto; intros; intro.
  unfold Rrelation in H5; apply Axiom_SchemeP in H5; destruct H5.
  assert (y0 ∈ (y ∩ x0)). { apply Axiom_Scheme; split; Ens. }
  rewrite H3 in H7; generalize (Theorem16 y0); contradiction.
Qed.

Hint Resolve Theorem107 : set.


(* Theorem108 : If x is an ordinal, y⊂x, y≠x, and y is full, then y∈x. *)

Theorem Theorem108 : forall x y,
  Ordinal x -> y ⊂ x -> y ≠ x -> full y -> y ∈ x.
Proof.
  intros.
  assert (Section y E x).
  { apply Theorem107 in H; unfold Section; intros.
    split; auto; split; auto; intros; destruct H3, H4.
    unfold Rrelation in H5; apply Axiom_SchemeP in H5; destruct H5.
    unfold full in H2; apply H2 in H4; auto. }
  generalize (Lemma_xy _ _ H3 H1); intro.
  apply Theorem91 in H4; destruct H4 as [v H4], H4.
  assert (v = \{ λ u, u ∈ x /\ Rrelation u E v \}).
  { apply Axiom_Extent; split; intros; AssE z.
    - apply Axiom_Scheme; split; auto; unfold Ordinal in H; destruct H.
      double H4; unfold full in H8; apply H8 in H4.
      split; auto; apply Axiom_SchemeP; split; auto; apply Theorem49; split; Ens.
    - apply Axiom_Scheme in H6; destruct H6, H8.
      unfold Rrelation in H9; apply Axiom_SchemeP in H9; tauto. }
  rewrite <- H6 in H5; subst v; auto.
Qed.

Hint Resolve Theorem108 : set.


(* Theorem109 : If x is an ordinal an y is an ordinal, then x⊂y or y⊂x. *)

Lemma Lemma109 : forall x y, Ordinal x /\ Ordinal y -> full (x ∩ y).
Proof.
  intros; destruct H.
  unfold Ordinal in H, H0; destruct H, H0.
  unfold full in *; intros.
  apply Axiom_Scheme in H3; destruct H3, H4.
  apply H1 in H4; apply H2 in H5.
  unfold Subclass; intros.
  apply Axiom_Scheme; repeat split; Ens.
Qed.

Lemma Lemma109' : forall x y,
  Ordinal x /\ Ordinal y -> ((x ∩ y) = x) \/ ((x ∩ y) ∈ x).
Proof.
  intros; generalize (classic ((x ∩ y) = x)); intro.
  destruct H0; try tauto. assert ((x ∩ y) ⊂ x).
  { unfold Subclass; intros; apply Theorem4' in H1; tauto. }
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
      { rewrite Theorem6' in H2; apply Axiom_Scheme; Ens. }
      apply Theorem101 in H3; elim H3.
Qed.

Hint Resolve Theorem109 : set.


(* Theorem110 : If x is an ordinal an y is an ordinal, then x∈y or y∈x or
   x = y. *)

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


(* Theorem111 : If x is an ordinal and y∈x, then y is an ordinal. *)

Theorem Theorem111 : forall x y, Ordinal x /\ y ∈ x -> Ordinal y.
Proof.
  intros.
  destruct H; double H; unfold Ordinal in H; destruct H.
  assert (Connect E y).
  { unfold Connect; intros; unfold Ordinal in H1; apply H1 in H0.
    assert (u ∈ x /\ v ∈ x). { destruct H3; split; auto. }
    apply H; auto. }
  unfold Ordinal; split; auto; unfold full; intros; unfold Subclass; intros.
  apply Theorem107 in H1; unfold Ordinal in H1; assert (y ⊂ x); auto.
  assert (m ∈ x); auto; assert (m⊂ x); auto; assert (z ∈ x); auto.
  apply Theorem88 in H1; destruct H1; unfold Transitive in H1.
  specialize H1 with z m y; assert (Rrelation z E y).
  { apply H1; repeat split; Ens.
    - unfold Rrelation; apply Axiom_SchemeP; split; auto.
      apply Theorem49; split; Ens.
    - unfold Rrelation; apply Axiom_SchemeP; split; auto.
      apply Theorem49; split; Ens. }
  unfold Rrelation in H11; apply Axiom_SchemeP in H11; tauto.
Qed.

Hint Resolve Theorem111 : set.


(* Definition112 : R = {x : x is an ordinal}. *)

Definition R : Class := \{ λ x, Ordinal x \}.

Hint Unfold R : set.


(* Theorem113 : R is an ordinal and R is not a set. *)

Lemma Lemma113 :forall u v,
  Ensemble u -> Ensemble v -> Ordinal u /\ Ordinal v ->
  (Rrelation u E v \/ Rrelation v E u \/ u = v) .
Proof.
  intros; apply Theorem110 in H1.
  destruct H1 as [H1 | [H1 | H1]].
  - left; unfold Rrelation; apply Axiom_SchemeP; split; Ens; apply Theorem49; auto.
  - right; left; apply Axiom_SchemeP; split; Ens; apply Theorem49; auto.
  - right; right; auto.
Qed.

Theorem Theorem113 : Ordinal R /\ ~ Ensemble R.
Proof.
  intros.
  assert (Ordinal R).
  { unfold Ordinal; intros; split.
    - unfold Connect; intros; destruct H.
      apply Axiom_Scheme in H; destruct H; apply Axiom_Scheme in H0; destruct H0.
      generalize (Lemma_xy _ _ H1 H2); intro; apply Lemma113; auto.
    - unfold full; intros; apply Axiom_Scheme in H; destruct H.
      unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
      eapply Theorem111; eauto. }
  split; auto; intro; assert (R ∈ R). { apply Axiom_Scheme; split; auto. }
  apply Theorem101 in H1; auto.
Qed.

Hint Resolve Theorem113 : set.


(* Theorem114 : Each E-section of R is an ordinal. *)

Theorem Theorem114 : forall x, Section x E R -> Ordinal x.
Proof.
  intros.
  generalize (classic (x = R)); intro; destruct H0.
  - rewrite H0; apply Theorem113.
  - generalize (Lemma_xy _ _ H H0); intro.
    apply Theorem91 in H1; destruct H1, H1.
    assert (x0 = \{ λ u, u ∈ R /\ Rrelation u E x0 \}).
    { apply Axiom_Extent; split; intros.
      - apply Axiom_Scheme; repeat split; Ens.
        + apply Axiom_Scheme in H1; destruct H1.
          apply Axiom_Scheme; split; Ens; eapply Theorem111; eauto.
        + red; apply Axiom_SchemeP; split; auto; apply Theorem49; Ens.
      - apply Axiom_Scheme in H3; destruct H3, H4.
        unfold Rrelation in H5; apply Axiom_SchemeP in H5; tauto. }
    subst x; rewrite H3 in H1; apply Axiom_Scheme in H1; tauto.
Qed.

Corollary Lemma114 : forall x, Ordinal x -> Section x E R.
Proof.
  intros; unfold Section; split.
  - unfold Subclass; intros; apply Axiom_Scheme; split; try Ens.
    eapply Theorem111; eauto.
  - split; intros; try (apply Theorem107; apply Theorem113).
    destruct H0, H1; unfold Ordinal in H2; apply Axiom_SchemeP in H2; destruct H2.
    unfold Ordinal in H; destruct H; apply H4 in H1; auto.
Qed.

Hint Resolve Theorem114 : set.


(* Definition115 : x is an ordinal number iff x ∈ R. *)

Definition Ordinal_Number x : Prop := x ∈ R.

Hint Unfold Ordinal_Number : set.


(* Definition116 : x ≺ y if and only if x ∈ y. *)

Definition Less x y : Prop := x ∈ y.

Notation "x ≺ y" := (Less x y)(at level 67, left associativity).

Hint Unfold Less : set.


(* Definition117 : x ≼ y if and only if x ∈ y or x = y. *)

Definition LessEqual x y := x ∈ y \/ x = y.

Notation "x ≼ y" := (LessEqual x y)(at level 67, left associativity).

Hint Unfold LessEqual : set.


(* Definition122 : x + 1 = x ∪ {x}. *)

Definition PlusOne x := x ∪ [x].

Hint Unfold PlusOne : set.


(* Theorem123 : If x∈R, then x+1 is the E-first member of {y : y∈R and x≺y}. *)

Lemma Lemma123 : forall x, x ∈ R -> (PlusOne x) ∈ R.
Proof.
  intros; apply Axiom_Scheme; split.
  - apply Axiom_Union; split; Ens; apply Theorem42; Ens.
  - unfold Connect; split.
    + unfold Connect; intros; destruct H0; apply Axiom_Scheme in H0; destruct H0.
      apply Axiom_Scheme in H1; destruct H1, H2, H3.
      *  apply Axiom_Scheme in H; destruct H as [_ H].
         assert (Ordinal u). { eapply Theorem111; eauto. }
         assert (Ordinal v). { eapply Theorem111; eauto. }
         generalize (Lemma_xy _ _ H4 H5); intro; apply Lemma113; auto.
      * apply Axiom_Scheme in H3; destruct H3; AssE x; apply Theorem19 in H5.
        apply H4 in H5; subst v; left; unfold Rrelation; apply Axiom_SchemeP.
        split; auto; apply Theorem49; tauto.
      * apply Axiom_Scheme in H2; destruct H2; AssE x; apply Theorem19 in H5.
        apply H4 in H5; subst u; right; left; unfold Subclass.
        apply Axiom_SchemeP; split; auto; apply Theorem49; tauto.
      * AssE x; apply Theorem19 in H4; double H4; apply Axiom_Scheme in H2.
        destruct H2; apply H6 in H4; apply Axiom_Scheme in H3; destruct H3.
        apply H7 in H5; subst u; subst v; tauto.
    + unfold full; intros; unfold Subclass; intros; apply Axiom_Scheme in H0.
      destruct H0; apply Axiom_Scheme in H; destruct H.
      apply Axiom_Scheme; split; Ens; destruct H2.
      * unfold Ordinal in H3; destruct H3; generalize (Property_Full x); intro.
        destruct H5; apply H5 with (u:=z) (v:=m) in H4; tauto.
      * apply Axiom_Scheme in H2; destruct H2.
        apply Theorem19 in H; apply H4 in H; subst m; tauto.
Qed.

Theorem Theorem123 : forall x,
  x ∈ R -> FirstMember (PlusOne x) E (\{ λ y, (In y R /\ Less x y) \}).
Proof.
  intros; unfold FirstMember; split; intros.
  - apply Axiom_Scheme; repeat split.
    + unfold Ensemble; exists R; apply Lemma123; auto.
    + apply Lemma123; auto.
    + unfold Less; intros; apply Axiom_Scheme; split; Ens.
      right; apply Axiom_Scheme; split; Ens.
  - intro; apply Axiom_Scheme in H0; destruct H0, H2.
    unfold Rrelation in H1; apply Axiom_SchemeP in H1; destruct H1.
    apply Axiom_Scheme in H4; destruct H4; unfold Less in H3; destruct H5.
    + eapply Theorem102; eauto.
    + AssE x; apply Theorem19 in H6; apply Axiom_Scheme in H5; destruct H5.
      apply H7 in H6; subst y; eapply Theorem101; eauto.
Qed.

Hint Resolve Theorem123 : set.


(* Definition125 : f|x = f ∩ (x × μ). *)

Definition Restriction f x : Class := f ∩ (x) × μ.

Notation "f | ( x )" := (Restriction f x)(at level 40).

Hint Unfold Restriction : set.


(* Theorem127 : Let f be a function such that domain f is an ordinal and
   f(u) = g(f|u) for u in domain f. If h is also a function such that domain h
   is an ordinal and h(u) = g(h|u) for u in domain h, then h ⊂ f or f ⊂ h. *)

Theorem Theorem127 : forall f h g,
  Function f -> Ordinal dom(f) ->
  (forall u0, u0 ∈ dom(f) -> f[u0] = g[f | (u0)]) ->
  Function h -> Ordinal dom(h) ->
  (forall u1, u1 ∈ dom(h) -> h[u1] = g[h | (u1)]) -> h ⊂ f \/ f ⊂ h.
Proof.
  intros; generalize (Lemma_xy _ _ H0 H3); intro; apply Theorem109 in H5.
  generalize (classic (\{λ a, a∈(dom(f)∩dom(h))/\f[a]≠h[a]\}=Φ)); intro.
  destruct H6.
  - destruct H5.
    + right; unfold Subclass; intros; rewrite Theorem70 in H7; auto; PP H7 a b.
      double H8; rewrite <- Theorem70 in H8; auto; apply Property_dom in H8.
      apply Axiom_SchemeP in H9; destruct H9; rewrite Theorem70; auto.
      apply Axiom_SchemeP; split; auto; rewrite H10.
      generalize (classic (f[a] = h[a])); intro; destruct H11; auto.
      assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
      { apply Axiom_Scheme; split; Ens; split; auto.
        apply Theorem30 in H5; rewrite H5; auto. }
      eapply Axiom_Extent in H6; apply H6 in H12.
      generalize (Theorem16 a); intros; contradiction.
    + left; unfold Subclass; intros; rewrite Theorem70 in H7; auto; PP H7 a b.
      double H8; rewrite <- Theorem70 in H8; auto; apply Property_dom in H8.
      apply Axiom_SchemeP in H9; destruct H9; rewrite Theorem70; auto.
      apply Axiom_SchemeP; split; auto; rewrite H10.
      generalize (classic (f[a] = h[a])); intro; destruct H11; auto.
      assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
      { apply Axiom_Scheme; split; Ens; split; auto.
        apply Theorem30 in H5; rewrite Theorem6'; rewrite H5; auto. }
      eapply Axiom_Extent in H6; apply H6 in H12.
      generalize (Theorem16 a); intros; contradiction.
  - assert (exists u, FirstMember u E \{λ a, a∈(dom(f)∩dom(h))/\f[a]≠h[a]\}).
    { apply Theorem107 in H0; unfold KWellOrder in H0; apply H0; split; auto.
      unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
      apply Axiom_Scheme in H8; tauto. }
    destruct H7 as [u H7]; unfold FirstMember in H7; destruct H7.
    apply Axiom_Scheme in H7; destruct H7, H9; apply Axiom_Scheme in H9.
    destruct H9 as [_ [H9 H11]]; generalize (H1 _ H9).
    generalize (H4 _ H11); intros.
    assert ((h | (u)) = (f | (u))).
    { apply Axiom_Extent; intros; split; intros.
      - apply Axiom_Scheme in H14; destruct H14, H15; apply Axiom_Scheme.
        repeat split; auto; PP H16 a b; apply Axiom_SchemeP in H17.
        destruct H17 ,H18; generalize H15 as H22; intro.
        apply Property_dom in H22; rewrite Theorem70 in H15; auto.
        rewrite Theorem70; auto; apply Axiom_SchemeP in H15; destruct H15.
        apply Axiom_SchemeP; split; auto; rewrite H20; symmetry.
        generalize (classic (f[a] = h[a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply Axiom_Scheme; repeat split; auto; try Ens; apply Axiom_Scheme.
          repeat split; auto; try Ens; unfold Ordinal in H0; destruct H0.
          unfold full in H23; apply H23 in H9; auto. }
        apply H8 in H23; elim H23; red; apply Axiom_SchemeP; split; auto.
        apply Theorem49; split; try Ens.
      - apply Axiom_Scheme in H14; destruct H14, H15; apply Axiom_Scheme.
        repeat split; auto; PP H16 a b; apply Axiom_SchemeP in H17.
        destruct H17 ,H18; generalize H15 as H22; intro.
        apply Property_dom in H22; rewrite Theorem70 in H15; auto.
        rewrite Theorem70; auto; apply Axiom_SchemeP in H15; destruct H15.
        apply Axiom_SchemeP; split; auto; rewrite H20; symmetry.
        generalize (classic (f[a] = h[a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply Axiom_Scheme; repeat split; auto; try Ens; apply Axiom_Scheme.
          repeat split; auto; try Ens; unfold Ordinal in H3; destruct H3.
          unfold full in H23; apply H23 in H11; auto. }
        apply H8 in H23; elim H23; red; apply Axiom_SchemeP; split; auto.
        apply Theorem49; split; try Ens. }
    rewrite <- H14 in H13; rewrite <- H12 in H13; contradiction.
Qed.

Hint Resolve Theorem127 : set.


(* Theorem128 : For each g there is a unique function f such that domain f is
   an ordinal and f(x) = g(f|x) for each ordinal number x. *)

Definition En_f' g :=
  \{\ λ u v, u ∈ R /\ (exists h, Function h /\ Ordinal dom(h) /\
  (forall z, z ∈ dom(h) -> h[z] = g [h | (z)] ) /\ [u,v] ∈ h ) \}\.

Lemma Lemma128 : forall u v w, Ordinal u -> v ∈ u -> w ∈ v -> w ∈ u.
Proof.
  intros; unfold Ordinal in H; destruct H.
  generalize (Property_Full u); intro; destruct H3.
  eapply H3; eauto.
Qed.

Lemma Lemma128' : forall f x,
  Function f -> Ordinal dom(f) -> Ordinal_Number x ->
  ~ x ∈ dom(f) -> f | (x) = f .
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H3; tauto.
  - apply Axiom_Scheme; split; Ens; split; auto.
    unfold Function, Relation in H; destruct H as [H _].
    double H3; apply H in H4; destruct H4 as [a [b H4]]; rewrite H4 in *.
    clear H H4; apply Axiom_SchemeP; split; Ens; split.
    + unfold Ordinal in H1; apply Axiom_Scheme in H1; destruct H1.
      assert (Ordinal dom(f) /\ Ordinal x); auto.
      apply Theorem110 in H4; apply Property_dom in H3; auto.
      destruct H4 as [H4 | [H4 | H4]]; try contradiction.
      * eapply Lemma128; eauto.
      * rewrite H4 in H3; auto.
    + apply Property_ran in H3; apply Theorem19; Ens.
Qed.

Theorem Theorem128 :  forall g,
  exists f, Function f /\ Ordinal dom(f) /\
  (forall x, Ordinal_Number x -> f [x] = g [f | (x)]).
Proof.
  intros; exists (En_f' g).
  assert (Function (En_f' g)).
  { unfold Function; intros; split; intros.
    - unfold Relation; intros; PP H a b; eauto.
    - destruct H; apply Axiom_SchemeP in H; apply Axiom_SchemeP in H0.
      destruct H, H1, H2, H2, H3, H4, H0, H6, H7, H7, H8, H9.
      generalize (Theorem127 _ _ _ H2 H3 H4 H7 H8 H9); intro; destruct H11.
      + apply H11 in H10; eapply H2; eauto.
      + apply H11 in H5; eapply H7; eauto. }
  split; auto.
  - assert (Ordinal dom( En_f' g)).
    { apply Theorem114; unfold Section; intros; split.
      - unfold Subclass; intros; apply Axiom_Scheme in H0; destruct H0, H1.
        apply Axiom_SchemeP in H1; tauto.
      - split; intros.
        + apply Theorem107; apply Theorem113.
        + destruct H0, H1; apply Axiom_Scheme in H1; destruct H1, H3.
          apply Axiom_SchemeP in H3; destruct H3, H4, H5, H5, H6, H7.
          apply Axiom_SchemeP in H2; destruct H2; apply Theorem49 in H2.
          destruct H2; apply Axiom_Scheme; split; auto; apply Property_dom in H8.
          assert (u ∈ dom( x0)). { eapply Lemma128; eauto. } exists (x0[u]).
          apply Axiom_SchemeP; split; try apply Theorem49; split; auto.
          * apply Theorem19; apply Theorem69; auto.
          * exists x0; split; auto; split; auto; split; auto.
            apply Property_Value; auto. }
    split; intros; auto.
    generalize (classic (x ∈ dom(En_f' g))); intro; destruct H2.
    + apply Axiom_Scheme in H2; destruct H2, H3; apply Axiom_SchemeP in H3.
       destruct H2, H3, H4; destruct H5 as [h [H5 [H6 [H7 H8]]]].
       assert (h ⊂ En_f' g).
       { double H5; unfold Subclass; intros; unfold Function, Relation in H9.
         destruct H9 as [H9 _]; double H10; apply H9 in H11.
         destruct H11 as [a [b H11]]; rewrite H11 in *; clear H9 H11 z.
         apply Axiom_SchemeP; split; try Ens; double H10; apply Property_dom in H9.
         split; try apply Axiom_Scheme; Ens; split; Ens.
         eapply Theorem111; eauto. }
      generalize H8; intro; apply H9 in H10; generalize H8; intro.
      apply Property_dom in H11; apply H7 in H11; generalize H8; intro.
      apply Property_dom in H12; apply Property_dom in H8.
      apply Property_Value in H8; auto; apply Property_dom in H10.
      apply Property_Value in H10; auto; apply H9 in H8.
      assert (h [x] = (En_f' g) [x]). { eapply H; eauto. }
      rewrite <- H13; clear H13.
      assert (h | (x) = En_f' g | (x)).
      { apply Axiom_Extent; split; intros; apply Axiom_Scheme in H13; destruct H13, H14.
        - apply Axiom_Scheme; repeat split; auto.
        - apply Axiom_Scheme; repeat split; auto; rewrite Theorem70; auto.
          PP H15 a b; apply Axiom_SchemeP in H16; apply Axiom_SchemeP; split; auto.
          destruct H16, H17. assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
         apply Property_Value in H19; auto; apply H9 in H19; eapply H; eauto. }
      rewrite <- H13; auto.
    + generalize H2; intro; apply Theorem69 in H2; auto.
      rewrite (Lemma128' _ _ H H0 H1 H3).
      generalize (classic (En_f' g ∈ dom(g))); intro; destruct H4.
      * generalize Theorem113; intro; destruct H5 as [H5 _].
        apply Theorem107 in H5; unfold KWellOrder  in H5; destruct H5.
        assert ((R ~ dom(En_f' g)) ⊂ R /\ (R ~ dom(En_f' g)) ≠ Φ).
        { split; try (red; intros; apply Axiom_Scheme in H7; tauto).
          intro; generalize (Lemma114 _ H0); intro; unfold Section in H8.
          destruct H8; apply Property_Φ in H8; apply H8 in H7.
          rewrite <- H7 in H3; contradiction. }
        apply H6 in H7; destruct H7 as [y H7].
        assert (((En_f' g) ∪ [[y,g[En_f' g]]]) ⊂ (En_f' g)).
        { unfold Subclass; intros; apply Axiom_Scheme in H8; destruct H8, H9; auto.
          assert (Ensemble ([y, g [En_f' g]])).
          { unfold FirstMember in H7; destruct H7; AssE y.
            apply Theorem69 in H4; apply Theorem19 in H4.
            apply Theorem49; tauto. }
          apply Axiom_Scheme in H9; destruct H9.
          rewrite H11; try apply Theorem19; auto.
          apply Axiom_SchemeP; split; auto; split.
          - unfold FirstMember in H7; destruct H7; apply Axiom_Scheme in H7; tauto.
          - exists ((En_f' g) ∪ [[y,g[En_f' g]]]).
            assert (Function (En_f' g ∪ [[y, g [En_f' g]]])).
            { unfold Function; split; intros.
              - unfold Relation; intros; apply Axiom_Scheme in H12.
                destruct H12, H13.
                + PP H13 a b; eauto.
                + apply Axiom_Scheme in H13; destruct H13; apply Theorem19 in H10.
                  apply H14 in H10; eauto.
              - destruct H12; apply Axiom_Scheme in H12; destruct H12 as [_ H12].
                apply Axiom_Scheme in H13; destruct H13 as [_ H13].
                unfold FirstMember in H7; destruct H7.
                apply Axiom_Scheme in H7; destruct H7 as [_ [_ H7]].
                apply Axiom_Scheme in H7; destruct H7; destruct H12, H13.
                + eapply H; eauto.
                + apply Axiom_Scheme in H13; destruct H13; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; rewrite H10 in H12.
                  apply Property_dom in H12; contradiction.
                + apply Axiom_Scheme in H12; destruct H12; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; rewrite H10 in H13.
                  apply Property_dom in H13; contradiction.
                + double H12; apply Axiom_Scheme in H12; apply Axiom_Scheme in H13.
                  destruct H12, H13; double H10; apply Theorem19 in H10.
                  apply H17 in H10; apply Theorem19 in H19; apply H18 in H19.
                  apply Theorem55 in H10; destruct H10; apply Theorem49 in H12;
                  auto; apply Theorem55 in H19; destruct H19;
                  apply Theorem49 in H13; auto; rewrite H20, H21; auto. }
            split; auto; split.
            + apply Theorem114; unfold Section; intros; split.
              * unfold Subclass; intros; apply Axiom_Scheme in H13.
                destruct H13, H14; apply Axiom_Scheme in H14; destruct H14, H15.
                { apply Property_dom in H15; apply Axiom_Scheme.
                  split; Ens; eapply Theorem111; eauto. }
                { apply Axiom_Scheme in H15; destruct H15; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; unfold FirstMember in H7.
                  destruct H7; apply Axiom_Scheme in H7; rewrite H10; tauto. }
              * split; try (apply Theorem107; apply Theorem113); intros.
                destruct H13, H14; apply Axiom_Scheme in H14; destruct H14, H16.
                apply Axiom_Scheme in H16; destruct H16, H17.
                { apply Axiom_Scheme; split; Ens.
                  assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                  { apply Property_Value; auto; apply Property_dom in H17.
                    unfold Rrelation in H15; apply Axiom_SchemeP in H15.
                    destruct H15; eapply Lemma128; eauto. }
                  exists ((En_f' g) [u]); apply Axiom_Scheme; split; Ens. }
                { assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                  { apply Property_Value; auto; apply Axiom_Scheme in H17.
                    destruct H17; apply Theorem19 in H10; apply H18 in H10.
                    apply Theorem55 in H10; destruct H10; try apply Theorem49;
                    auto; subst v; unfold FirstMember in H7; destruct H7.
                    generalize (classic (u ∈ dom( En_f' g))); intro.
                    destruct H20; auto; absurd (Rrelation u E y); auto;
                    try apply H10; apply Axiom_Scheme; repeat split; Ens.
                    apply Axiom_Scheme; split; Ens. }
                  apply Axiom_Scheme; split; Ens; exists ((En_f' g)[u]).
                  apply Axiom_Scheme; split; Ens. }
            + split; intros.
              * apply Property_Value in H13; auto.
                apply Axiom_Scheme in H13; destruct H13, H14.
                { apply Axiom_SchemeP in H14; destruct H14, H15.
                  destruct H16 as [h [H16 [H17 [H18 H19]]]]; double H19.
                  apply Property_dom in H20; rewrite Theorem70 in H19; auto.
                  apply Axiom_SchemeP in H19; destruct H19.
                  assert (h ⊂ En_f' g).
                  { unfold Subclass; intros; double H16.
                    unfold Function, Relation in H23; destruct H23 as [H23 _].
                    double H22; apply H23 in H24; destruct H24 as [a [b H24]].
                    rewrite H24 in *; clear H23 H24; apply Axiom_SchemeP.
                    split; try Ens; double H22; apply Property_dom in H23.
                    split; try apply Axiom_Scheme; Ens.
                    split; try Ens; eapply Theorem111; eauto. }
                  assert ((En_f' g ∪ [[y, g[En_f' g]]]) |
                           (z0) = En_f' g | (z0)).
                  { unfold Restriction; rewrite Theorem6'; rewrite Theorem8.
                    assert ((z0) × μ ∩ [[y, g [En_f' g]]] = Φ).
                    { apply Axiom_Extent; split; intros; apply Axiom_Scheme in H23;
                      destruct H23, H24; auto.
                      PP H24 a b; apply Axiom_SchemeP in H26; destruct H26, H27.
                      apply Axiom_Scheme in H25; destruct H25.
                      apply Theorem19 in H10; apply H29 in H10.
                      apply Theorem55 in H10; apply Theorem49 in H25; auto.
                      destruct H10; rewrite H10 in H27.
                      assert (y ∈ dom( h)). { eapply Lemma128; eauto. }
                      apply Property_Value in H31; auto; apply H22 in H31.
                      apply Property_dom in H31; unfold FirstMember in H7.
                      destruct H7; apply Axiom_Scheme in H7; destruct H7, H33.
                      apply Axiom_Scheme in H34; destruct H34; contradiction. }
                    rewrite H23; rewrite Theorem6; rewrite Theorem17.
                    apply Theorem6'. }
                  rewrite H21; rewrite H23.
                  assert (h | (z0) = En_f' g | (z0)).
                  { apply Axiom_Extent; split; intros.
                    - apply Axiom_Scheme in H24; destruct H24, H25.
                      apply Axiom_Scheme; repeat split; auto.
                    - apply Axiom_Scheme in H24; destruct H24, H25; apply Axiom_Scheme.
                      repeat split; auto; rewrite Theorem70; auto.
                      PP H26 a b; apply Axiom_SchemeP in H27.
                      apply Axiom_SchemeP; split; auto; destruct H27 as [_ [H27 _]].
                      assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
                      apply Property_Value in H28; auto; apply H22 in H28.
                      eapply H; eauto. }
                  rewrite <- H24; auto. }
                { apply Axiom_Scheme in H14; destruct H14; double H10.
                  apply Theorem19 in H10; apply H15 in H10.
                  apply Theorem55 in H10; apply Theorem49 in H13; auto.
                  destruct H10; subst z0; rewrite H17.
                  assert ((En_f' g ∪ [[y, g[En_f' g]]]) | (y) = En_f' g | (y)).
                  { apply Axiom_Extent; split; intros.
                    - apply Axiom_Scheme in H10; destruct H10, H18.
                      apply Axiom_Scheme in H18; destruct H18, H20.
                      + apply Axiom_Scheme; tauto.
                      + PP H19 a b; apply Axiom_SchemeP in H21; destruct H21, H22.
                        apply Axiom_Scheme in H20; destruct H20.
                        apply Theorem19 in H16; apply H24 in H16.
                        apply Theorem55 in H16; apply Theorem49 in H21; auto.
                        destruct H16; rewrite H16 in H22.
                        generalize (Theorem101 y); intro; contradiction. 
                    - unfold Restriction; rewrite Theorem6'; rewrite Theorem8.
                      apply Axiom_Scheme; split; Ens; left; rewrite Theorem6'; Ens. }
                  rewrite H10; unfold FirstMember in H7; destruct H7.
                  apply Axiom_Scheme in H7; destruct H7, H19; apply Axiom_Scheme in H20.
                  destruct H20; rewrite Lemma128'; auto. }
              * apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; split; Ens. }
        unfold FirstMember in H7; destruct H7.
        assert (y ∈ dom(En_f' g ∪ [[y, g [En_f' g]]])).
        { apply Axiom_Scheme; split; Ens; exists g [En_f' g].
          assert (Ensemble ([y, g [En_f' g]])).
          { apply Theorem49; split; Ens; apply Theorem69 in H4.
            apply Theorem19; auto. }
          apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; auto. }
        apply Axiom_Scheme in H7; destruct H7, H11; apply Axiom_Scheme in H12.
        destruct H12; elim H13; apply Axiom_Scheme in H10; destruct H10, H14.
        apply H8 in H14; apply Property_dom in H14; auto.
      * apply Theorem69 in H4; rewrite H2, H4; auto.
Qed.

Hint Resolve Theorem128 : set.


End AxiomaticSetTheory.

Export AxiomaticSetTheory.
