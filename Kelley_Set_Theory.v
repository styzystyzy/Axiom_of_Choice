(* This document only provides the definition and theorem that we needed in the
   paper "Formalization of the Axiom of Choice and its Equivalent Theorems",
   and the complete Coq proof of Kelley axiomatic set theory can contact with
   stycyj@bupt.edu.cn. *)

Require Export Logic_Property.

(** The foramlization of axiomatic set theory **)


Module AxiomaticSetTheory.

Parameter Class : Type.


(* ∈: belongs to. x∈y : In x y. *)

Parameter In : Class -> Class -> Prop.

Notation "x ∈ y" := (In x y) (at level 10).


(* I Axiom of extent : For each x and each y it is true that x = y
   if and only if for each z, z∈x when and only when z∈y. *)

Axiom AxiomI : forall x y, x = y <-> (forall z, z∈x <-> z∈y).

Hint Resolve AxiomI : set.


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

Axiom AxiomII : forall b P,
  b ∈ \{ P \} <-> Ensemble b /\ (P b).

Hint Resolve AxiomII : set.


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


(* Theorem5 : x∪x = x and x∩x = x. *)

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


(* Theorem6 : x∪y = y∪x and x∩y = y∩x. *)

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


(* Theorem7 : (x∪y)∪z = x∪(y∪z) and (x∩y)∩z = x∩(y∩z). *)

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


(* Theorem8 : x∩(y∪z)= (x∩y)∪(x∩z) and x∪(y∩z) = (x∪y)∩(x∪z). *)

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
  unfold Φ in H; apply AxiomII in H.
  destruct H; apply H0; auto.
Qed.

Hint Resolve Theorem16 : set.


(* Theorem17 : Φ∪x = x and Φ∩x = Φ *)

Theorem Theorem17 : forall x, Φ ∪ x = x.
Proof.
  intros; apply AxiomI; split; intro.
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


(* Theorem19 : x∈μ iff x is a set. *)

Theorem Theorem19 : forall (x: Class),
  x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intro.
  - unfold μ in H; apply AxiomII in H; apply H.
  - unfold μ; apply AxiomII; split; auto.
Qed.

Hint Resolve Theorem19 : set.


(* Theorem20 : x∪μ = μ and x∩μ = x. *)

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


(* Theorem30 : x⊂y iff x∩y=x. *)

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
  apply not_and_or in H0; destruct H0; try tauto.
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


(* III Axiom of subsets : If x is a set there is a set y such that for
   each z, if z⊂x, then z∈y. *)

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


(* Theorem35 : If x≠Φ, then ∩x is a set. *)

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


(* Definition36 : 2*x = {y : y⊂x}. *)

Definition PowerSet x : Class := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerSet x) (at level 0, right associativity).

Hint Unfold PowerSet : set.


(* Theorem38 : If x is a set, then 2*x is a set, and for each y,
   y⊂x iff y∈2*x. *)

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


(* Definition40 : {x} = {z : if x∈u, then z=x}. *)

Definition Singleton x : Class := \{ λ z, x∈μ -> z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Hint Unfold Singleton : set.


(* Theorem42 : If x is a set, then {x} is a set. *)

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


(* Theorem47 : If x and y are sets, then ∩{xy} = x∩y and ∪{xy} = x∪y. *)

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


(* Theorem50 : If x and y are sets, then ∪(x,y) = {xy}, ∩(x,y) = {x},
   ∪∩(x,y) = x, ∩∩(x,y) = x, ∪∪(x,y) = x∪y, ∩∪(x,y) = x∩y. *)

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
  (∪(∩[x,y]) = x) /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y])=x∪y) /\ (∩(∪[x,y])=x∩y).
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


(* Theorem54 : If x and y are sets, 1st coord (x,y)=x and 2nd coord (x,y)=y. *)

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


(* Definition56 : r is a relation iff for each member z of r there is x and y
   such that z = (x,y). *)

Definition Relation r : Prop := forall z, z∈r -> exists x y, z = [x,y].

Hint Unfold Relation: set.


(* { (x,y) : ... } *)

Parameter Classifier_P : (Class -> Class -> Prop) -> Class.

Notation "\{\ P \}\" := (Classifier_P P) (at level 0).

Axiom AxiomII_P : forall (a b: Class) (P: Class -> Class -> Prop),
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).

Axiom Property_P : forall (z: Class) (P: Class -> Class -> Prop),
  z ∈ \{\ P \}\ -> (exists a b, z = [a,b]) /\ z ∈ \{\ P \}\.

Ltac PP H a b:= apply Property_P in H; destruct H as [[a [b H]]];
rewrite H in *.

Hint Resolve AxiomII_P Property_P: set.


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
  intros; apply AxiomI; split; intros.
  - PP H0 a b; apply AxiomII_P in H1; destruct H1.
    apply AxiomII_P in H2; apply H2.
  - unfold Relation in H; double H0; apply H in H1.
    destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply AxiomII_P; split; Ens; apply AxiomII_P; split; auto.
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
  intros; apply AxiomII.
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
  intros; apply AxiomII.
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


(* Theorem69 : If x ∉ domain f, then f(x)=μ; If x ∈ domain f, then f[x]∈μ. *)

Lemma Lemma69 : forall x f,
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

Theorem Theorem69 : forall x f,
  ( x ∉ (dom( f )) -> f[x] = μ ) /\ ( x ∈ dom( f ) -> (f[x]) ∈  μ ).
Proof.
  intros; split; intros.
  - assert (\{ λ y, [x,y] ∈ f \} = Φ).
    { apply AxiomI; split; intros.
       apply AxiomII in H0; destruct H0.
       apply Property_dom in H1; contradiction.
       generalize (Theorem16 z); intro; contradiction. }
    unfold Value; rewrite H0; apply Theorem24.
  - assert (\{ λ y, [x,y] ∈ f \} <> Φ).
    { intro.
       apply AxiomII in H; destruct H, H1.
       generalize (AxiomI \{ λ y : Class,[x, y] ∈ f \} Φ); intro; destruct H2.
       apply H2 with x0 in H0; destruct H0.
       assert (x0 ∈ Φ).
       { apply H0; apply AxiomII; split; auto.
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
  apply AxiomII in H0; destruct H0, H1.
  generalize (classic (x ∈ dom( f))); intros.
  destruct H2; auto; apply Theorem69 in H2; auto.
  rewrite H2 in H0; generalize (Theorem39); intro; contradiction.
Qed.


(* Theorem70 : If f is a function, then f = {(x,y) : y = f(x)}. *)

Theorem Theorem70 : forall f,
  Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; apply AxiomI; split; intros.
  - double H0; unfold Function, Relation in H; destruct H.
    apply H in H1; destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply AxiomII_P; split; try Ens; apply AxiomI; split; intros.
    + apply AxiomII; split; intros; try Ens.
      apply AxiomII in H3; destruct H3.
      apply Lemma_xy with (y:=[a, y] ∈ f) in H0; auto.
      apply H2 in H0; rewrite <- H0; auto.
    + unfold Value, Element_I in H1; apply AxiomII in H1; destruct H1.
      apply H3; apply AxiomII; split; auto; AssE [a,b].
      apply Theorem49 in H4; try apply H4.
  - PP H0 a b; apply AxiomII_P in H1; destruct H1.
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


(* Theorem74 : If x and y are sets so is x×y. *)

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


(* Theorem75 : If f is a function and domain f is a set,
   then f is a set. *)

Theorem Theorem75 : forall f, 
  Function f /\ Ensemble dom( f ) -> Ensemble f.
Proof.
  intros; destruct H.
  assert (Ensemble ran(f)); try apply AxiomV; auto.
  assert (Ensemble (dom( f)) × (ran( f))).
  { apply Theorem74; split; auto. }
  apply Theorem33 with (x:=(dom( f ) × ran( f ))); auto.
  unfold Included; intros; rewrite Theorem70 in H3; auto.
  PP H3 a b; rewrite <- Theorem70 in H4; auto; AssE [a,b].
  repeat split; auto; apply AxiomII_P; split; auto.
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
  apply AxiomII in H2; destruct H2, H3.
  - left; apply AxiomII in H3; destruct H3; auto.
  - apply AxiomII in H3; destruct H3, H4.
    + right; left; apply AxiomII in H4; destruct H4; auto.
    + right; right; apply AxiomII in H4; destruct H4; auto.
Qed.

Theorem Theorem88 : forall r x,
  KWellOrder r x -> Transitive r x /\ Asymmetric r x .
Proof.
  intros; generalize H; intro; unfold KWellOrder in H0; destruct H0.
  assert (Asymmetric r x).
  { unfold Asymmetric; intros; destruct H2, H3; AssE u; AssE v.
    assert (([u | v] ⊂ x) /\ ([u | v] ≠ Φ)).
    { split.
      - unfold Included; intros; apply AxiomII in H7; destruct H7, H8.
        + apply Theorem19 in H5; apply AxiomII in H8; destruct H8.
          rewrite H9; auto.
        + apply Theorem19 in H6; apply AxiomII in H8; destruct H8.
          rewrite H9; auto.
        - apply Property_NotEmpty; exists u; apply AxiomII; split; auto.
          left; apply AxiomII; split; auto. }
    apply H1 in H7; destruct H7; unfold FirstMember in H7; destruct H7.
    apply Theorem46 in H7; auto; destruct H7; subst x0.
    - apply H8; auto; apply AxiomII; split; auto; right; apply AxiomII; auto.
    - assert (u ∈ [u | v]).
      { apply AxiomII; split; auto; left; apply AxiomII; split; auto. }
      apply H8 in H7; auto. }
  split; auto; unfold Transitive; intros.
  - destruct H3, H4, H5, H6; unfold Connect in H0; specialize H0 with w u.
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    + assert (([u] ∪ [v] ∪ [w] ⊂ x) /\ ([u] ∪ [v] ∪ [w] ≠ Φ)).
      { split; unfold Included; intros.
        - apply AxiomII in H8; destruct H8 as [_ H8], H8.
          + AssE u; apply Theorem19 in H9; apply AxiomII in H8; destruct H8.
            rewrite H10; auto.
          + apply AxiomII in H8; destruct H8 as [_ H8]; destruct H8.
            * AssE v; apply Theorem19 in H9; apply AxiomII in H8.
              destruct H8; rewrite H10; auto.
            * AssE w; apply Theorem19 in H9; apply AxiomII in H8.
              destruct H8; rewrite H10; auto.
        - intro; generalize (Theorem16 u); intro.
          apply H9; rewrite <- H8; apply AxiomII; split; Ens.
          left; apply AxiomII; split; intros; auto; Ens. }
      apply H1 in H8; destruct H8; unfold FirstMember in H8; destruct H8.
      assert (u ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; left; apply AxiomII; split; Ens. }
      assert (v ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply AxiomII; split; Ens.
        left; apply AxiomII; split; Ens. }
      assert (w ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply AxiomII; split; Ens.
        right; apply AxiomII; split; Ens. }
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
    { red; intros; apply AxiomII in H4; tauto. }
    generalize (classic (x ~ y = Φ)); intro; destruct H5.
    - apply Property_Φ in H; apply H in H5.
      apply Property_Ineq in H0; contradiction.
    - apply H3; split; auto. }
  destruct H1; unfold FirstMember in H1; destruct H1; exists x0.
  apply AxiomII in H1; destruct H1, H3; split; auto.
  apply AxiomI; split; intros.
  - unfold Section in H; destruct H, H6; apply AxiomII.
    repeat split; Ens; assert (z ∈ x); auto.
    unfold KWellOrder, Connect in H6; destruct H6 as [H6 _].
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
      * left; unfold Included; intros; rewrite H3 in H10.
        apply AxiomII in H10; destruct H10, H11; rewrite H4; apply AxiomII.
        repeat split; auto; apply H5 with x0; auto.
      * right; unfold Included; intros; rewrite H4 in H10.
        apply AxiomII in H10; destruct H10, H11; rewrite H3; apply AxiomII.
        repeat split; auto; apply H5 with x1; auto.
      * right; subst x0; rewrite H3, H4; unfold Included; intros; auto.
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
  - apply AxiomI; split; intros.
    + apply AxiomII in H; destruct H, H0; apply AxiomII_P in H0.
      destruct H0; apply AxiomII; split; Ens.
    + apply AxiomII in H; destruct H, H0; apply AxiomII; split; auto.
      exists x; apply AxiomII_P; split; auto; apply Theorem49.
      AssE [x,z]; apply Theorem49 in H1; destruct H1; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H; destruct H, H0; apply AxiomII_P in H0.
      destruct H0; apply AxiomII; split; Ens.
    + apply AxiomII in H; destruct H, H0; apply AxiomII; split; auto.
      exists x; apply AxiomII_P; split; auto; apply Theorem49.
      AssE [z,x]; apply Theorem49 in H1; destruct H1; auto.
Qed.

Hint Unfold Function1_1 : set.


(* Theorem96 : If f is r-s order preserving, then f is a 1_1 function and
   f ⁻¹ is s-r order preserving. *)

Lemma Lemma96 : forall f, dom( f) = ran( f ⁻¹).
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H; destruct H, H0; apply AxiomII; split; auto.
    exists x; apply AxiomII_P; split; auto; apply Lemma61; Ens.
  - apply AxiomII in H; destruct H, H0.
    apply AxiomII; split; auto; exists x; apply AxiomII_P in H0; tauto.
Qed.

Lemma Lemma96' : forall f, ran( f) = dom( f ⁻¹).
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H; destruct H, H0; apply AxiomII; split; auto.
    exists x; apply AxiomII_P; split; auto; apply Lemma61; Ens.
  - apply AxiomII in H; destruct H, H0.
    apply AxiomII; split; auto; exists x; apply AxiomII_P in H0; tauto.
Qed.

Lemma Lemma96'' : forall f u,
  Function f -> Function f ⁻¹ -> u ∈ ran(f) ->  (f⁻¹)[u] ∈ dom(f).
Proof.
  intros; rewrite Lemma96' in H1;  apply Property_Value in H1; auto.
  apply AxiomII_P in H1; destruct H1; apply Property_dom in H2; auto.
Qed.

Lemma Lemma96''' : forall f u,
  Function f -> Function f ⁻¹ -> u ∈ ran(f) -> u = f  [(f ⁻¹) [u]].
Proof.
  intros; generalize (Lemma96'' _ _ H H0 H1); intro.
  apply Property_Value in H2; auto; rewrite Lemma96' in H1.
  apply Property_Value in H1; auto; apply AxiomII_P in H1; destruct H1.
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
      apply AxiomII_P in H3; destruct H3; apply AxiomII_P in H4; destruct H4.
      double H5; double H6; apply Property_dom in H5; apply Property_dom in H6.
      double H7; double H8; apply Property_dom in H7; apply Property_dom in H8.
      rewrite Theorem70 in H9; auto; apply AxiomII_P in H9.
      destruct H9 as [_ H9]; rewrite Theorem70 in H10; auto.
      apply AxiomII_P in H10; destruct H10 as [_ H10]; rewrite H10 in H9.
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
  unfold FirstMember in H0; destruct H0; apply AxiomII in H0; destruct H0, H8.
  apply AxiomII in H8; destruct H8 as [_ [H8 H10]].
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
    apply AxiomII; repeat split; try Ens; try intro.
    - apply AxiomII; repeat split; try Ens; apply H3 with u; repeat split; auto.
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
    + left; unfold Included; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply AxiomII_P in H13; destruct H13; rewrite Theorem70; auto.
      apply AxiomII_P; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a]\}).
      { apply AxiomII; split; Ens; split; auto; apply Theorem30 in H10.
        rewrite H10; auto. }
      eapply AxiomI in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
    + right; unfold Included; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply AxiomII_P in H13; destruct H13; rewrite Theorem70; auto.
      apply AxiomII_P; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a]\}).
      { apply AxiomII; split; Ens; split; auto; apply Theorem30 in H10.
        rewrite Theorem6' in H10; rewrite H10; auto. }
      eapply AxiomI in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
  - assert (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a] \} ⊂ dom(f)).
    { unfold Included; intros; apply AxiomII in H7; destruct H7, H8.
      apply Theorem4' in H8; tauto. }
    double H2; double H; unfold Order_Pr in H9; destruct H9, H10, H11.
    unfold KWellOrder in H10; destruct H10.
    generalize (Lemma_xy _ _ H7 H6); intro; apply H13 in H14.
    destruct H14 as [u H14]; double H14; unfold FirstMember in H15.
    destruct H15; apply AxiomII in H15; destruct H15, H17.
    unfold Order_Pr in H2; destruct H2 as [H19 [_ [H2 _]]].
    apply AxiomII in H17; destruct H17 as [_ [H17 H20]]; double H17; double H20.
    apply Property_Value in H17; apply Property_Value in H20; auto.
    apply Property_ran in H17; apply Property_ran in H20.
    generalize (Lemma_xy _ _ H1 H4); intro.
    apply Theorem92 in H23; auto; destruct H23.
    + apply H23 in H17; double H17; apply AxiomII in H17.
      destruct H17 as [_ [v H17]]; rewrite Theorem70 in H17; auto.
      apply AxiomII_P in H17; destruct H17; rewrite H25 in H24.
      generalize (Lemma_xy _ _ H24 H20); intro; unfold KWellOrder in H2.
      destruct H2 as [H2 _]; unfold Connect in H2; apply H2 in H26.
      destruct H26 as [H26 | [H26 | H26]].
      * apply (Lemma97' f g u r s v x y); auto.
      * red in H1; destruct H1 as [_ [_ H1]]; rewrite <- H25 in H26.
        assert (g [u] ∈ ran( f)).
        { apply H1 with f [u]; repeat split; auto; unfold Section in H4.
          apply H4; apply Property_ran with u; apply Property_Value; auto.
          apply Property_ran with u; apply Property_Value; auto. }
        apply AxiomII in H27; destruct H27 as [_ [v1 H27]]; double H27.
        apply Property_dom in H28; apply Property_Value in H28; auto.
        rewrite Theorem70 in H27; auto; apply AxiomII_P in H27.
        destruct H27 as [_ H27]; rewrite H27 in H26.
        assert (g ⊂ f \/ f ⊂ g).
        { apply (Lemma97' g f u r s v1 x y); try tauto; try rewrite Theorem6'.
          assert (\{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a]\} =
                  \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ g[a] ≠ f[a] \}).
          { apply AxiomI; split; intros; apply AxiomII in H29; apply AxiomII.
            - repeat split; try tauto; apply Property_Ineq; tauto.
            - repeat split; try tauto; apply Property_Ineq; tauto. }
          rewrite <- H29; auto. apply Property_ran in H28; auto. }
        tauto.
      * rewrite <- H25 in H26; contradiction.
    + apply H23 in H20; double H18.
      apply AxiomII in H20; destruct H20 as [_ [v H20]]; double H20.
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
        apply AxiomII in H28; destruct H28 as [_ [v1 H28]]; double H28.
        apply Property_dom in H29; apply Property_Value in H29; auto.
        rewrite Theorem70 in H28; auto; apply AxiomII_P in H28; destruct H28.
        rewrite H30 in H27; apply (Lemma97' f g u r s v1 x y); try tauto; auto.
        apply Property_ran with v1; auto.
      * assert (g ⊂ f \/ f ⊂ g).
        { rewrite <- H26 in H27, H20.
          apply (Lemma97' g f u r s v x y); try tauto; auto; rewrite Theorem6'.
          assert (\{λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a]\} =
                  \{λ a, a ∈ (dom(f) ∩ dom(g)) /\ g[a] ≠ f[a]\}).
          { apply AxiomI; split; intros; apply AxiomII in H28; apply AxiomII.
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
  apply AxiomI; split; intros; apply AxiomII in H3; destruct H3;
  apply AxiomII; split; intros; auto.
  - apply H4; apply AxiomII in H5; destruct H5.
    apply AxiomII; split; auto; apply AxiomII; split; Ens.
  - apply H4; apply AxiomII in H5; destruct H5; apply AxiomII; split; auto.
    apply AxiomII in H6; destruct H6, H7; auto; apply AxiomII in H7.
    destruct H7; assert([a,b]∈μ). { apply Theorem19; apply Theorem49; tauto. }
    generalize (H8 H9); intro; apply Theorem49 in H6.
    apply Theorem55 in H10; auto; destruct H10.
    rewrite H10 in H2; contradiction.
Qed.

Lemma Lemma99'' : forall a b f z,
  ~ a ∈ dom(f) -> Ensemble a -> Ensemble b -> (z=a -> (f ∪ [[a,b]]) [z] = b).
Proof.
  intros; apply AxiomI; split; intros; subst z.
  - apply AxiomII in H3; destruct H3; apply H3; apply AxiomII; split; auto.
    apply AxiomII; split; try apply Theorem49; try tauto.
    right; apply AxiomII; split; try apply Theorem49; try tauto.
  - apply AxiomII; split; intros; Ens; apply AxiomII in H2; destruct H2;
    apply AxiomII in H4; destruct H4, H5.
    + apply Property_dom in H5; contradiction.
    + apply AxiomII in H5; destruct H5.
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
    - destruct H0; apply AxiomII_P in H0; destruct H0, H2, H3, H3, H4, H5.
      unfold Order_PXY in H4; destruct H4 as [_ [_ [H4 [H7 H8]]]].
      apply AxiomII_P in H1; destruct H1, H9, H10, H10, H11, H12.
      unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H14 H15]]]].
      assert (x1 ⊂ x2 \/ x2 ⊂ x1). { apply (Theorem97 x1 x2 r s x y); tauto. }
      destruct H16.
      + apply H16 in H6; eapply H10; eauto.
      + apply H16 in H13; eapply H3; eauto. }
  exists (En_f x y r s); split; auto.
  assert (Section (dom(En_f x y r s)) r x).
  { unfold Section; split.
    - unfold Included; intros; apply AxiomII in H1; destruct H1, H2.
      apply AxiomII_P in H2; tauto.
    - split; try tauto; intros; destruct H1, H2; apply AxiomII in H2.
      destruct H2, H4; apply AxiomII_P in H4; destruct H4, H5, H6.
      apply AxiomII; split; Ens; exists ((En_f x y r s)[u]).
      apply Property_Value; auto; apply AxiomII; split; Ens.
      assert (u ∈ dom( x1)).
      { destruct H6, H7; unfold Order_PXY in H7; destruct H7, H9, H10, H11.
        unfold Section in H11; destruct H11, H13; apply H14 with v.
        destruct H8; tauto. }
      exists (x1[u]); apply AxiomII_P; repeat split; auto.
      + apply Theorem49; split; Ens.
        apply Theorem19; apply Theorem69; try tauto.
      + exists x1; split; try tauto; split; try tauto.
        split; auto; apply Property_Value; try tauto. }
  assert (Section (ran(En_f x y r s)) s y).
  { unfold Section; split.
    - unfold Included; intros; apply AxiomII in H2; destruct H2, H3.
      apply AxiomII_P in H3; destruct H3, H4, H5, H5, H6, H7.
      unfold Order_PXY in H6; destruct H6 as [_ [_ [_ [_ H6]]]].
      destruct H6 as [H6 _]; apply Property_ran in H8; auto.
    - split; try tauto; intros; destruct H2, H3; apply AxiomII in H3.
      destruct H3, H5; apply AxiomII_P in H5; destruct H5, H6, H7.
      apply AxiomII; split; Ens; exists (x1⁻¹[u]); apply AxiomII_P.
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
    apply AxiomII_P in H4; destruct H4 as [H4 [H9 [g1 [H10 [H11 [H12 H13]]]]]].
    apply AxiomII_P in H5; destruct H5 as [H5 [H14 [g2 [H15 [H16 [H17 H18]]]]]].
    rewrite Theorem70 in H13; auto; apply AxiomII_P in H13.
    destruct H13 as [_ H13]; rewrite Theorem70 in H18; auto.
    apply AxiomII_P in H18; destruct H18 as [_ H18].
    rewrite H13, H18; clear H13 H18.
    unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H13 H18]]]].
    unfold Order_PXY in H16; destruct H16 as [_ [_ [H16 [H19 H20]]]].
    generalize (Lemma_xy _ _ H11 H16); intro.
    apply (Theorem97 g1 g2 r s x y) in H21; apply Property_Value in H12; auto.
    apply Property_Value in H17; auto; destruct H21.
    - apply H21 in H12; double H12; rewrite Theorem70 in H12; auto.
      apply AxiomII_P in H12; destruct H12 as [_ H12]; rewrite H12.
      apply Property_dom in H22; apply Property_dom in H17; apply H16; tauto.
    - apply H21 in H17; double H17; rewrite Theorem70 in H17; auto.
      apply AxiomII_P in H17; destruct H17 as [_ H17]; rewrite H17.
      apply Property_dom in H12; apply Property_dom in H22; apply H11; tauto. }
  split; auto; apply NNPP; intro; apply not_or_and in H4; destruct H4.
  assert (exists u, FirstMember u r (x ~ dom( En_f x y r s))).
  { unfold Section in H1; destruct H1, H6.
    assert ((x ~ dom( En_f x y r s)) ⊂ x).
    { red; intros; apply AxiomII in H8; tauto. }
    assert ((x ~ dom( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H1; apply H1 in H9; apply H4; auto. }
    generalize (Lemma97 _ _ _ H6 H8); intro; apply H10.
    repeat split; auto; red; auto. }
  assert (exists v, FirstMember v s (y ~ ran( En_f x y r s))).
  { unfold Section in H2; destruct H2, H7.
    assert ((y ~ ran( En_f x y r s)) ⊂ y).
    { red; intros; apply AxiomII in H9; tauto. }
    assert ((y ~ ran( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H2; apply H2 in H10; apply H5; auto. }
    generalize (Lemma97 _ _ _ H7 H9); intro; apply H11.
    repeat split; auto; red; auto. }
  destruct H6 as [u H6]; destruct H7 as [v H7].
  unfold FirstMember in H6; unfold FirstMember in H7; destruct H6, H7.
  apply AxiomII in H6; destruct H6 as [_ [H6 H10]]; apply AxiomII in H10.
  destruct H10 as [_ H10]; apply H10; apply AxiomII; split; Ens.
  exists v; apply AxiomII_P; split; try apply Theorem49; split; try Ens.
  exists ((En_f x y r s) ∪ [[u,v]]).
  assert (Function (En_f x y r s ∪ [[u, v]])).
  { assert ([u, v] ∈ μ) as H18.
    { apply Theorem19; apply Theorem49; split; try Ens. }
    unfold Function; split; intros.
    - unfold Relation; intros.
      apply AxiomII in H11; destruct H11 as [H11 [H12 | H12]].
      + PP H12 a b; eauto.
      + apply AxiomII in H12; exists u,v; apply H12; auto.
    - destruct H11; apply AxiomII in H11; apply AxiomII in H12.
      destruct H11 as [H11 [H13 | H13]], H12 as [H12 [H14 | H14]].
      + unfold Function in H0; eapply H0; eauto.
      + apply Property_dom in H13; apply AxiomII in H14; destruct H14.
        apply Theorem55 in H15; apply Theorem49 in H12; auto.
        destruct H15; rewrite H15 in H13; contradiction.
      + apply Property_dom in H14; apply AxiomII in H13; destruct H13.
        apply Theorem55 in H15; apply Theorem49 in H11; auto.
        destruct H15; rewrite H15 in H14; contradiction.
      + apply AxiomII in H13; destruct H13; apply Theorem49 in H13.
        apply Theorem55 in H15; auto; apply AxiomII in H14; destruct H14.
        apply Theorem55 in H16; apply Theorem49 in H12; auto.
        destruct H15, H16; rewrite H17; auto. }
  split; auto.
  assert (Section (dom(En_f x y r s ∪ [[u, v]])) r x).
  { unfold Section; split.
    - unfold Included; intros; apply AxiomII in H12; destruct H12, H13.
      apply AxiomII in H13; destruct H13, H14.
      + apply Property_dom in H14; unfold Section in H1; apply H1; auto.
      + apply AxiomII in H14; destruct H14.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H15 in H16; apply Theorem49 in H13; apply Theorem55 in H16; auto.
        destruct H16; rewrite H16; auto.
    - split; try tauto; intros; destruct H12, H13; apply AxiomII in H13.
      destruct H13, H15; apply AxiomII in H15; destruct H15, H16.
      + apply AxiomII; split; Ens.
        assert ([u0,(En_f x y r s)[u0]] ∈ (En_f x y r s)).
        { apply Property_dom in H16; apply Property_Value; auto.
          apply H1 with v0; repeat split; auto. }
        exists (En_f x y r s)[u0]; apply AxiomII; split; Ens.
      + apply AxiomII in H16; destruct H16.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H17 in H18; apply Theorem49 in H16; apply Theorem55 in H18; auto.
        destruct H18; subst v0.
        assert ([u0,(En_f x y r s)[u0]] ∈ (En_f x y r s)).
        { apply Property_Value; auto.
          generalize (classic (u0 ∈ dom( En_f x y r s))); intro.
          destruct H18; auto; absurd (Rrelation u0 r u); auto.
          apply H8; apply AxiomII; repeat split; Ens.
          apply AxiomII; split; Ens. }
        apply AxiomII; split; Ens; exists ((En_f x y r s)[u0]).
        apply AxiomII; split; Ens. }
  assert (Section (ran(En_f x y r s ∪ [[u, v]])) s y).
  { unfold Section; split.
    - unfold Included; intros; apply AxiomII in H13; destruct H13, H14.
      apply AxiomII in H7; destruct H7 as [_ [H7 _]] .
      apply AxiomII in H14; destruct H14, H15.
      + apply Property_ran in H15; unfold Section in H2; apply H2; auto.
      + apply AxiomII in H15; destruct H15.
        assert ([u, v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H16 in H17; apply Theorem55 in H17; apply Theorem49 in H14; auto.
        destruct H17; rewrite H18; auto.
    - split; try tauto; intros; destruct H13, H14; apply AxiomII in H14.
      destruct H14, H16; unfold Order_PXY in H3; destruct H3 as [_ [_ [H3 _]]].
      apply Theorem96 in H3; destruct H3 as [[_ H3] _].
      apply AxiomII in H16; destruct H16, H17.
      + apply AxiomII; split; Ens.
        assert ([((En_f x y r s) ⁻¹) [u0], u0] ∈ (En_f x y r s)).
        { assert (u0 ∈ ran( En_f x y r s)). 
          { apply Property_ran in H17; apply H2 with v0; repeat split; auto. }
          pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
          apply Property_Value'; auto; rewrite <- Lemma96'''; auto. }
        exists ((En_f x y r s) ⁻¹) [u0]; apply AxiomII; split; Ens.
      + apply AxiomII in H17; destruct H17.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H18 in H19; apply Theorem55 in H19; apply Theorem49 in H16; auto.
        destruct H19; subst v0.
        assert ([((En_f x y r s) ⁻¹)[u0], u0] ∈ (En_f x y r s)).
        { generalize (classic (u0 ∈ ran( En_f x y r s))); intro; destruct H20.
          - pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
            apply Property_Value'; auto; rewrite <- Lemma96'''; auto.
          - absurd (Rrelation u0 s v); auto; apply H9; apply AxiomII.
            repeat split; Ens; apply AxiomII; split; Ens. }
        apply AxiomII; split; Ens; exists ((En_f x y r s) ⁻¹)[u0].
        apply AxiomII; split; Ens. }
  split.
  - unfold Order_PXY; split; try tauto; split; try tauto; split; [idtac|tauto].
    unfold Order_Pr; intros; split; auto.
    split; try eapply Lemma99; eauto; try apply H.
    split; try eapply Lemma99; eauto; try apply H; intros; destruct H14, H15.
    apply AxiomII in H14; destruct H14, H17; apply AxiomII in H17.
    destruct H17 as [_ H17]; apply AxiomII in H15; destruct H15, H18.
    apply AxiomII in H18; destruct H18 as [_ H18].
    assert ([u,v]∈μ) as H20. { apply Theorem19; apply Theorem49; split; Ens. }
    destruct H17, H18.
    + apply Property_dom in H17; apply Property_dom in H18.
      repeat rewrite Lemma99'; auto; Ens; unfold Order_PXY in H3.
      destruct H3 as [_ [_ [H3 _]]]; unfold Order_Pr in H3; eapply H3; eauto.
    + apply Property_dom in H17; rewrite Lemma99'; auto; Ens.
      apply AxiomII in H18; destruct H18; apply H19 in H20.
      apply Theorem55 in H20; destruct H20; apply Theorem49 in H18; auto.
      rewrite Lemma99''; auto; Ens.
      apply Lemma99''' with (y:=(ran( En_f x y r s))) (x:=y); auto.
      * apply Property_Value in H17; auto; double H17.
        apply Property_ran in H17; apply AxiomII; split; Ens.
      * apply AxiomII in H7; destruct H7, H22; apply AxiomII in H23; tauto.
      * apply AxiomII in H7; tauto.
    + apply Property_dom in H18; pattern ((En_f x y r s ∪ [[u,v]])[v0]).
      rewrite Lemma99'; Ens.
      assert (u0 ∈ dom( En_f x y r s)).
      { unfold Section in H1; apply H1 with v0; split; auto.
        apply AxiomII in H17; destruct H17; apply H19 in H20.
        apply Theorem55 in H20; apply Theorem49 in H17; auto.
        destruct H20; rewrite H20; auto. }
      rewrite Lemma99'; Ens; unfold Order_PXY in H3.
      destruct H3 as [_ [_ [H3 _]]]; unfold Order_Pr in H3; eapply H3; eauto.
    + double H20; apply AxiomII in H17; destruct H17; apply H21 in H19.
      apply AxiomII in H18; destruct H18; apply H22 in H20.
      apply Theorem55 in H20; destruct H20; apply Theorem49 in H18; auto.
      apply Theorem55 in H19; destruct H19; apply Theorem49 in H17; auto.
      subst u0 v0; destruct H as [H _]; apply Theorem88 in H.
      destruct H as [_ H]; apply Property_Asy with (u:=u) in H; tauto.
  - assert (Ensemble ([u,v])). { apply Theorem49; split; Ens. } split.
    + apply AxiomII; split; Ens; exists v; apply AxiomII; split; Ens.
      right; apply AxiomII; split; auto.
    + apply AxiomII; split; Ens; right; apply AxiomII; split; auto.
Qed.

Hint Resolve Theorem99 : set.


(* VII Axiom of regularity : If x ≠ Φ there is a member y of x such x∩y = Φ. *)

Axiom AxiomVII : forall x, x ≠ Φ -> exists y, y∈x /\ x ∩ y = Φ.

Hint Resolve AxiomVII : set.


(* Theorem101 : x ∉ x. *)

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


(* Theorem102 : It is false that x∈y and y∈x. *)

Theorem Theorem102 : forall x y, ~ (x ∈ y /\ y ∈ x).
Proof.
  intros; intro; destruct H.
  assert (\{ λ z, z = x \/ z =y \} ≠ Φ).
  { apply Property_NotEmpty; exists x; apply AxiomII; split; Ens. }
  apply AxiomVII in H1; destruct H1, H1; apply AxiomII in H1; destruct H1.
  destruct H3; subst x0.
  - assert (y ∈ (\{ λ z, z = x \/ z = y \} ∩ x)).
    { apply AxiomII; repeat split; Ens; apply AxiomII; split; Ens. }
    rewrite H2 in H3; generalize (Theorem16 y); intro; contradiction.
  - assert (x ∈ (\{ λ z, z = x \/ z = y \} ∩ y)).
    { apply AxiomII; repeat split; Ens; apply AxiomII; split; Ens. }
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
  - unfold full; intros; unfold Included; intros; apply H with m; tauto.
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
  apply AxiomVII in H2; destruct H2, H2.
  exists x0; unfold FirstMember; intros.
  split; auto; intros; intro.
  unfold Rrelation in H5; apply AxiomII_P in H5; destruct H5.
  assert (y0 ∈ (y ∩ x0)). { apply AxiomII; split; Ens. }
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
    unfold Rrelation in H5; apply AxiomII_P in H5; destruct H5.
    unfold full in H2; apply H2 in H4; auto. }
  generalize (Lemma_xy _ _ H3 H1); intro.
  apply Theorem91 in H4; destruct H4 as [v H4], H4.
  assert (v = \{ λ u, u ∈ x /\ Rrelation u E v \}).
  { apply AxiomI; split; intros; AssE z.
    - apply AxiomII; split; auto; unfold Ordinal in H; destruct H.
      double H4; unfold full in H8; apply H8 in H4.
      split; auto; apply AxiomII_P; split; auto; apply Theorem49; split; Ens.
    - apply AxiomII in H6; destruct H6, H8.
      unfold Rrelation in H9; apply AxiomII_P in H9; tauto. }
  rewrite <- H6 in H5; subst v; auto.
Qed.

Hint Resolve Theorem108 : set.


(* Theorem109 : If x is an ordinal an y is an ordinal, then x⊂y or y⊂x. *)

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
  unfold Ordinal; split; auto; unfold full; intros; unfold Included; intros.
  apply Theorem107 in H1; unfold Ordinal in H1; assert (y ⊂ x); auto.
  assert (m ∈ x); auto; assert (m⊂ x); auto; assert (z ∈ x); auto.
  apply Theorem88 in H1; destruct H1; unfold Transitive in H1.
  specialize H1 with z m y; assert (Rrelation z E y).
  { apply H1; repeat split; Ens.
    - unfold Rrelation; apply AxiomII_P; split; auto.
      apply Theorem49; split; Ens.
    - unfold Rrelation; apply AxiomII_P; split; auto.
      apply Theorem49; split; Ens. }
  unfold Rrelation in H11; apply AxiomII_P in H11; tauto.
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
  - left; unfold Rrelation; apply AxiomII_P; split; Ens; apply Theorem49; auto.
  - right; left; apply AxiomII_P; split; Ens; apply Theorem49; auto.
  - right; right; auto.
Qed.

Theorem Theorem113 : Ordinal R /\ ~ Ensemble R.
Proof.
  intros.
  assert (Ordinal R).
  { unfold Ordinal; intros; split.
    - unfold Connect; intros; destruct H.
      apply AxiomII in H; destruct H; apply AxiomII in H0; destruct H0.
      generalize (Lemma_xy _ _ H1 H2); intro; apply Lemma113; auto.
    - unfold full; intros; apply AxiomII in H; destruct H.
      unfold Included; intros; apply AxiomII; split; Ens.
      eapply Theorem111; eauto. }
  split; auto; intro; assert (R ∈ R). { apply AxiomII; split; auto. }
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
    { apply AxiomI; split; intros.
      - apply AxiomII; repeat split; Ens.
        + apply AxiomII in H1; destruct H1.
          apply AxiomII; split; Ens; eapply Theorem111; eauto.
        + red; apply AxiomII_P; split; auto; apply Theorem49; Ens.
      - apply AxiomII in H3; destruct H3, H4.
        unfold Rrelation in H5; apply AxiomII_P in H5; tauto. }
    subst x; rewrite H3 in H1; apply AxiomII in H1; tauto.
Qed.

Corollary Lemma114 : forall x, Ordinal x -> Section x E R.
Proof.
  intros; unfold Section; split.
  - unfold Included; intros; apply AxiomII; split; try Ens.
    eapply Theorem111; eauto.
  - split; intros; try (apply Theorem107; apply Theorem113).
    destruct H0, H1; unfold Ordinal in H2; apply AxiomII_P in H2; destruct H2.
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
  intros; apply AxiomII; split.
  - apply AxiomIV; split; Ens; apply Theorem42; Ens.
  - unfold Connect; split.
    + unfold Connect; intros; destruct H0; apply AxiomII in H0; destruct H0.
      apply AxiomII in H1; destruct H1, H2, H3.
      *  apply AxiomII in H; destruct H as [_ H].
         assert (Ordinal u). { eapply Theorem111; eauto. }
         assert (Ordinal v). { eapply Theorem111; eauto. }
         generalize (Lemma_xy _ _ H4 H5); intro; apply Lemma113; auto.
      * apply AxiomII in H3; destruct H3; AssE x; apply Theorem19 in H5.
        apply H4 in H5; subst v; left; unfold Rrelation; apply AxiomII_P.
        split; auto; apply Theorem49; tauto.
      * apply AxiomII in H2; destruct H2; AssE x; apply Theorem19 in H5.
        apply H4 in H5; subst u; right; left; unfold Included.
        apply AxiomII_P; split; auto; apply Theorem49; tauto.
      * AssE x; apply Theorem19 in H4; double H4; apply AxiomII in H2.
        destruct H2; apply H6 in H4; apply AxiomII in H3; destruct H3.
        apply H7 in H5; subst u; subst v; tauto.
    + unfold full; intros; unfold Included; intros; apply AxiomII in H0.
      destruct H0; apply AxiomII in H; destruct H.
      apply AxiomII; split; Ens; destruct H2.
      * unfold Ordinal in H3; destruct H3; generalize (Property_Full x); intro.
        destruct H5; apply H5 with (u:=z) (v:=m) in H4; tauto.
      * apply AxiomII in H2; destruct H2.
        apply Theorem19 in H; apply H4 in H; subst m; tauto.
Qed.

Theorem Theorem123 : forall x,
  x ∈ R -> FirstMember (PlusOne x) E (\{ λ y, (In y R /\ Less x y) \}).
Proof.
  intros; unfold FirstMember; split; intros.
  - apply AxiomII; repeat split.
    + unfold Ensemble; exists R; apply Lemma123; auto.
    + apply Lemma123; auto.
    + unfold Less; intros; apply AxiomII; split; Ens.
      right; apply AxiomII; split; Ens.
  - intro; apply AxiomII in H0; destruct H0, H2.
    unfold Rrelation in H1; apply AxiomII_P in H1; destruct H1.
    apply AxiomII in H4; destruct H4; unfold Less in H3; destruct H5.
    + eapply Theorem102; eauto.
    + AssE x; apply Theorem19 in H6; apply AxiomII in H5; destruct H5.
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
    + right; unfold Included; intros; rewrite Theorem70 in H7; auto; PP H7 a b.
      double H8; rewrite <- Theorem70 in H8; auto; apply Property_dom in H8.
      apply AxiomII_P in H9; destruct H9; rewrite Theorem70; auto.
      apply AxiomII_P; split; auto; rewrite H10.
      generalize (classic (f[a] = h[a])); intro; destruct H11; auto.
      assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
      { apply AxiomII; split; Ens; split; auto.
        apply Theorem30 in H5; rewrite H5; auto. }
      eapply AxiomI in H6; apply H6 in H12.
      generalize (Theorem16 a); intros; contradiction.
    + left; unfold Included; intros; rewrite Theorem70 in H7; auto; PP H7 a b.
      double H8; rewrite <- Theorem70 in H8; auto; apply Property_dom in H8.
      apply AxiomII_P in H9; destruct H9; rewrite Theorem70; auto.
      apply AxiomII_P; split; auto; rewrite H10.
      generalize (classic (f[a] = h[a])); intro; destruct H11; auto.
      assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
      { apply AxiomII; split; Ens; split; auto.
        apply Theorem30 in H5; rewrite Theorem6'; rewrite H5; auto. }
      eapply AxiomI in H6; apply H6 in H12.
      generalize (Theorem16 a); intros; contradiction.
  - assert (exists u, FirstMember u E \{λ a, a∈(dom(f)∩dom(h))/\f[a]≠h[a]\}).
    { apply Theorem107 in H0; unfold KWellOrder in H0; apply H0; split; auto.
      unfold Included; intros; apply AxiomII in H7; destruct H7, H8.
      apply AxiomII in H8; tauto. }
    destruct H7 as [u H7]; unfold FirstMember in H7; destruct H7.
    apply AxiomII in H7; destruct H7, H9; apply AxiomII in H9.
    destruct H9 as [_ [H9 H11]]; generalize (H1 _ H9).
    generalize (H4 _ H11); intros.
    assert ((h | (u)) = (f | (u))).
    { apply AxiomI; intros; split; intros.
      - apply AxiomII in H14; destruct H14, H15; apply AxiomII.
        repeat split; auto; PP H16 a b; apply AxiomII_P in H17.
        destruct H17 ,H18; generalize H15 as H22; intro.
        apply Property_dom in H22; rewrite Theorem70 in H15; auto.
        rewrite Theorem70; auto; apply AxiomII_P in H15; destruct H15.
        apply AxiomII_P; split; auto; rewrite H20; symmetry.
        generalize (classic (f[a] = h[a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply AxiomII; repeat split; auto; try Ens; apply AxiomII.
          repeat split; auto; try Ens; unfold Ordinal in H0; destruct H0.
          unfold full in H23; apply H23 in H9; auto. }
        apply H8 in H23; elim H23; red; apply AxiomII_P; split; auto.
        apply Theorem49; split; try Ens.
      - apply AxiomII in H14; destruct H14, H15; apply AxiomII.
        repeat split; auto; PP H16 a b; apply AxiomII_P in H17.
        destruct H17 ,H18; generalize H15 as H22; intro.
        apply Property_dom in H22; rewrite Theorem70 in H15; auto.
        rewrite Theorem70; auto; apply AxiomII_P in H15; destruct H15.
        apply AxiomII_P; split; auto; rewrite H20; symmetry.
        generalize (classic (f[a] = h[a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply AxiomII; repeat split; auto; try Ens; apply AxiomII.
          repeat split; auto; try Ens; unfold Ordinal in H3; destruct H3.
          unfold full in H23; apply H23 in H11; auto. }
        apply H8 in H23; elim H23; red; apply AxiomII_P; split; auto.
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
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H3; tauto.
  - apply AxiomII; split; Ens; split; auto.
    unfold Function, Relation in H; destruct H as [H _].
    double H3; apply H in H4; destruct H4 as [a [b H4]]; rewrite H4 in *.
    clear H H4; apply AxiomII_P; split; Ens; split.
    + unfold Ordinal in H1; apply AxiomII in H1; destruct H1.
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
    - destruct H; apply AxiomII_P in H; apply AxiomII_P in H0.
      destruct H, H1, H2, H2, H3, H4, H0, H6, H7, H7, H8, H9.
      generalize (Theorem127 _ _ _ H2 H3 H4 H7 H8 H9); intro; destruct H11.
      + apply H11 in H10; eapply H2; eauto.
      + apply H11 in H5; eapply H7; eauto. }
  split; auto.
  - assert (Ordinal dom( En_f' g)).
    { apply Theorem114; unfold Section; intros; split.
      - unfold Included; intros; apply AxiomII in H0; destruct H0, H1.
        apply AxiomII_P in H1; tauto.
      - split; intros.
        + apply Theorem107; apply Theorem113.
        + destruct H0, H1; apply AxiomII in H1; destruct H1, H3.
          apply AxiomII_P in H3; destruct H3, H4, H5, H5, H6, H7.
          apply AxiomII_P in H2; destruct H2; apply Theorem49 in H2.
          destruct H2; apply AxiomII; split; auto; apply Property_dom in H8.
          assert (u ∈ dom( x0)). { eapply Lemma128; eauto. } exists (x0[u]).
          apply AxiomII_P; split; try apply Theorem49; split; auto.
          * apply Theorem19; apply Theorem69; auto.
          * exists x0; split; auto; split; auto; split; auto.
            apply Property_Value; auto. }
    split; intros; auto.
    generalize (classic (x ∈ dom(En_f' g))); intro; destruct H2.
    + apply AxiomII in H2; destruct H2, H3; apply AxiomII_P in H3.
       destruct H2, H3, H4; destruct H5 as [h [H5 [H6 [H7 H8]]]].
       assert (h ⊂ En_f' g).
       { double H5; unfold Included; intros; unfold Function, Relation in H9.
         destruct H9 as [H9 _]; double H10; apply H9 in H11.
         destruct H11 as [a [b H11]]; rewrite H11 in *; clear H9 H11 z.
         apply AxiomII_P; split; try Ens; double H10; apply Property_dom in H9.
         split; try apply AxiomII; Ens; split; Ens.
         eapply Theorem111; eauto. }
      generalize H8; intro; apply H9 in H10; generalize H8; intro.
      apply Property_dom in H11; apply H7 in H11; generalize H8; intro.
      apply Property_dom in H12; apply Property_dom in H8.
      apply Property_Value in H8; auto; apply Property_dom in H10.
      apply Property_Value in H10; auto; apply H9 in H8.
      assert (h [x] = (En_f' g) [x]). { eapply H; eauto. }
      rewrite <- H13; clear H13.
      assert (h | (x) = En_f' g | (x)).
      { apply AxiomI; split; intros; apply AxiomII in H13; destruct H13, H14.
        - apply AxiomII; repeat split; auto.
        - apply AxiomII; repeat split; auto; rewrite Theorem70; auto.
          PP H15 a b; apply AxiomII_P in H16; apply AxiomII_P; split; auto.
          destruct H16, H17. assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
         apply Property_Value in H19; auto; apply H9 in H19; eapply H; eauto. }
      rewrite <- H13; auto.
    + generalize H2; intro; apply Theorem69 in H2; auto.
      rewrite (Lemma128' _ _ H H0 H1 H3).
      generalize (classic (En_f' g ∈ dom(g))); intro; destruct H4.
      * generalize Theorem113; intro; destruct H5 as [H5 _].
        apply Theorem107 in H5; unfold KWellOrder  in H5; destruct H5.
        assert ((R ~ dom(En_f' g)) ⊂ R /\ (R ~ dom(En_f' g)) ≠ Φ).
        { split; try (red; intros; apply AxiomII in H7; tauto).
          intro; generalize (Lemma114 _ H0); intro; unfold Section in H8.
          destruct H8; apply Property_Φ in H8; apply H8 in H7.
          rewrite <- H7 in H3; contradiction. }
        apply H6 in H7; destruct H7 as [y H7].
        assert (((En_f' g) ∪ [[y,g[En_f' g]]]) ⊂ (En_f' g)).
        { unfold Included; intros; apply AxiomII in H8; destruct H8, H9; auto.
          assert (Ensemble ([y, g [En_f' g]])).
          { unfold FirstMember in H7; destruct H7; AssE y.
            apply Theorem69 in H4; apply Theorem19 in H4.
            apply Theorem49; tauto. }
          apply AxiomII in H9; destruct H9.
          rewrite H11; try apply Theorem19; auto.
          apply AxiomII_P; split; auto; split.
          - unfold FirstMember in H7; destruct H7; apply AxiomII in H7; tauto.
          - exists ((En_f' g) ∪ [[y,g[En_f' g]]]).
            assert (Function (En_f' g ∪ [[y, g [En_f' g]]])).
            { unfold Function; split; intros.
              - unfold Relation; intros; apply AxiomII in H12.
                destruct H12, H13.
                + PP H13 a b; eauto.
                + apply AxiomII in H13; destruct H13; apply Theorem19 in H10.
                  apply H14 in H10; eauto.
              - destruct H12; apply AxiomII in H12; destruct H12 as [_ H12].
                apply AxiomII in H13; destruct H13 as [_ H13].
                unfold FirstMember in H7; destruct H7.
                apply AxiomII in H7; destruct H7 as [_ [_ H7]].
                apply AxiomII in H7; destruct H7; destruct H12, H13.
                + eapply H; eauto.
                + apply AxiomII in H13; destruct H13; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; rewrite H10 in H12.
                  apply Property_dom in H12; contradiction.
                + apply AxiomII in H12; destruct H12; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; rewrite H10 in H13.
                  apply Property_dom in H13; contradiction.
                + double H12; apply AxiomII in H12; apply AxiomII in H13.
                  destruct H12, H13; double H10; apply Theorem19 in H10.
                  apply H17 in H10; apply Theorem19 in H19; apply H18 in H19.
                  apply Theorem55 in H10; destruct H10; apply Theorem49 in H12;
                  auto; apply Theorem55 in H19; destruct H19;
                  apply Theorem49 in H13; auto; rewrite H20, H21; auto. }
            split; auto; split.
            + apply Theorem114; unfold Section; intros; split.
              * unfold Included; intros; apply AxiomII in H13.
                destruct H13, H14; apply AxiomII in H14; destruct H14, H15.
                { apply Property_dom in H15; apply AxiomII.
                  split; Ens; eapply Theorem111; eauto. }
                { apply AxiomII in H15; destruct H15; apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; unfold FirstMember in H7.
                  destruct H7; apply AxiomII in H7; rewrite H10; tauto. }
              * split; try (apply Theorem107; apply Theorem113); intros.
                destruct H13, H14; apply AxiomII in H14; destruct H14, H16.
                apply AxiomII in H16; destruct H16, H17.
                { apply AxiomII; split; Ens.
                  assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                  { apply Property_Value; auto; apply Property_dom in H17.
                    unfold Rrelation in H15; apply AxiomII_P in H15.
                    destruct H15; eapply Lemma128; eauto. }
                  exists ((En_f' g) [u]); apply AxiomII; split; Ens. }
                { assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                  { apply Property_Value; auto; apply AxiomII in H17.
                    destruct H17; apply Theorem19 in H10; apply H18 in H10.
                    apply Theorem55 in H10; destruct H10; try apply Theorem49;
                    auto; subst v; unfold FirstMember in H7; destruct H7.
                    generalize (classic (u ∈ dom( En_f' g))); intro.
                    destruct H20; auto; absurd (Rrelation u E y); auto;
                    try apply H10; apply AxiomII; repeat split; Ens.
                    apply AxiomII; split; Ens. }
                  apply AxiomII; split; Ens; exists ((En_f' g)[u]).
                  apply AxiomII; split; Ens. }
            + split; intros.
              * apply Property_Value in H13; auto.
                apply AxiomII in H13; destruct H13, H14.
                { apply AxiomII_P in H14; destruct H14, H15.
                  destruct H16 as [h [H16 [H17 [H18 H19]]]]; double H19.
                  apply Property_dom in H20; rewrite Theorem70 in H19; auto.
                  apply AxiomII_P in H19; destruct H19.
                  assert (h ⊂ En_f' g).
                  { unfold Included; intros; double H16.
                    unfold Function, Relation in H23; destruct H23 as [H23 _].
                    double H22; apply H23 in H24; destruct H24 as [a [b H24]].
                    rewrite H24 in *; clear H23 H24; apply AxiomII_P.
                    split; try Ens; double H22; apply Property_dom in H23.
                    split; try apply AxiomII; Ens.
                    split; try Ens; eapply Theorem111; eauto. }
                  assert ((En_f' g ∪ [[y, g[En_f' g]]]) |
                           (z0) = En_f' g | (z0)).
                  { unfold Restriction; rewrite Theorem6'; rewrite Theorem8.
                    assert ((z0) × μ ∩ [[y, g [En_f' g]]] = Φ).
                    { apply AxiomI; split; intros; apply AxiomII in H23;
                      destruct H23, H24; auto.
                      PP H24 a b; apply AxiomII_P in H26; destruct H26, H27.
                      apply AxiomII in H25; destruct H25.
                      apply Theorem19 in H10; apply H29 in H10.
                      apply Theorem55 in H10; apply Theorem49 in H25; auto.
                      destruct H10; rewrite H10 in H27.
                      assert (y ∈ dom( h)). { eapply Lemma128; eauto. }
                      apply Property_Value in H31; auto; apply H22 in H31.
                      apply Property_dom in H31; unfold FirstMember in H7.
                      destruct H7; apply AxiomII in H7; destruct H7, H33.
                      apply AxiomII in H34; destruct H34; contradiction. }
                    rewrite H23; rewrite Theorem6; rewrite Theorem17.
                    apply Theorem6'. }
                  rewrite H21; rewrite H23.
                  assert (h | (z0) = En_f' g | (z0)).
                  { apply AxiomI; split; intros.
                    - apply AxiomII in H24; destruct H24, H25.
                      apply AxiomII; repeat split; auto.
                    - apply AxiomII in H24; destruct H24, H25; apply AxiomII.
                      repeat split; auto; rewrite Theorem70; auto.
                      PP H26 a b; apply AxiomII_P in H27.
                      apply AxiomII_P; split; auto; destruct H27 as [_ [H27 _]].
                      assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
                      apply Property_Value in H28; auto; apply H22 in H28.
                      eapply H; eauto. }
                  rewrite <- H24; auto. }
                { apply AxiomII in H14; destruct H14; double H10.
                  apply Theorem19 in H10; apply H15 in H10.
                  apply Theorem55 in H10; apply Theorem49 in H13; auto.
                  destruct H10; subst z0; rewrite H17.
                  assert ((En_f' g ∪ [[y, g[En_f' g]]]) | (y) = En_f' g | (y)).
                  { apply AxiomI; split; intros.
                    - apply AxiomII in H10; destruct H10, H18.
                      apply AxiomII in H18; destruct H18, H20.
                      + apply AxiomII; tauto.
                      + PP H19 a b; apply AxiomII_P in H21; destruct H21, H22.
                        apply AxiomII in H20; destruct H20.
                        apply Theorem19 in H16; apply H24 in H16.
                        apply Theorem55 in H16; apply Theorem49 in H21; auto.
                        destruct H16; rewrite H16 in H22.
                        generalize (Theorem101 y); intro; contradiction. 
                    - unfold Restriction; rewrite Theorem6'; rewrite Theorem8.
                      apply AxiomII; split; Ens; left; rewrite Theorem6'; Ens. }
                  rewrite H10; unfold FirstMember in H7; destruct H7.
                  apply AxiomII in H7; destruct H7, H19; apply AxiomII in H20.
                  destruct H20; rewrite Lemma128'; auto. }
              * apply AxiomII; split; Ens; right; apply AxiomII; split; Ens. }
        unfold FirstMember in H7; destruct H7.
        assert (y ∈ dom(En_f' g ∪ [[y, g [En_f' g]]])).
        { apply AxiomII; split; Ens; exists g [En_f' g].
          assert (Ensemble ([y, g [En_f' g]])).
          { apply Theorem49; split; Ens; apply Theorem69 in H4.
            apply Theorem19; auto. }
          apply AxiomII; split; Ens; right; apply AxiomII; auto. }
        apply AxiomII in H7; destruct H7, H11; apply AxiomII in H12.
        destruct H12; elim H13; apply AxiomII in H10; destruct H10, H14.
        apply H8 in H14; apply Property_dom in H14; auto.
      * apply Theorem69 in H4; rewrite H2, H4; auto.
Qed.

Hint Resolve Theorem128 : set.


(* VIII Axiom of infinity : For some y, y is a set, Φ ∈ y and (x ∪ {x}) ∈ y
   whenever x ∈ y. *)

Axiom AxiomVIII : exists y, Ensemble y /\ Φ ∈ y
  /\ (forall x, x ∈ y -> (x ∪ [x]) ∈ y).

Hint Resolve AxiomVIII : set.


(* Definition129 : x is an integer if and only if x is an ordinal and E⁻¹
   well-orders x. *)

Definition Integer x : Prop := Ordinal x /\ KWellOrder (E ⁻¹) x.

Hint Unfold Integer : set.


(* Definition130 : x is an E-last member of y is and only if x is an E⁻¹-first
   member of y. *)

Definition LastMember x E y : Prop := FirstMember x (E ⁻¹) y.

Hint Unfold LastMember : set.


(* Definition131 : W = {x : x is an integer}. *)

Definition W : Class := \{ λ x, Integer x \}.

Hint Unfold W : set.


(* Theorem132 : A member of an integer is an integer. *)

Theorem Theorem132 : forall x y, Integer x -> y∈x -> Integer y.
Proof.
  intros.
  unfold Integer in H; unfold Integer; destruct H.
  double H; apply Lemma_xy with (y:= y∈x) in H2; auto.
  apply Theorem111 in H2; split; auto.
  unfold KWellOrder in H1; unfold KWellOrder.
  unfold Ordinal in H; destruct H.
  unfold full in H3; apply H3 in H0.
  destruct H1; split; intros.
  - unfold Connect in H1; unfold Connect; intros.
    apply H1; destruct H5; unfold Included in H0.
    apply H0 in H5; apply H0 in H6; split; auto.
  - destruct H5; apply H4; split; auto.
    apply (Theorem28 _ y _); auto.
Qed.

Hint Resolve Theorem132 : set.


(* Theorem133 : If y∈R and x is an E-last member of y, then y = x+1. *)

Theorem Theorem133 : forall x y,
  y ∈ R /\ LastMember x E y -> y = PlusOne x.
Proof.
  intros; destruct H.
  unfold LastMember, FirstMember in H0.
  unfold R in H; apply AxiomII in H; destruct H, H0.
  double H1; add (x ∈ y) H3; apply Theorem111 in H3.
  assert (x ∈ R). { unfold R; apply AxiomII; Ens. }
  apply Theorem123 in H4; unfold FirstMember in H4; destruct H4.
  assert (y ∈ \{ λ z, z ∈ R /\ x ≺ z \}).
  { apply AxiomII; repeat split; auto.
    unfold R; apply AxiomII; split; auto. }
  apply H5 in H6; clear H5; generalize (Theorem113); intros.
  destruct H5; clear H7; apply Theorem107 in H5.
  unfold KWellOrder in H5; destruct H5; clear H7.
  unfold Connect in H5; apply AxiomII in H4; destruct H4, H7.
  clear H8; assert (y ∈ R /\ (PlusOne x) ∈ R).
  { split; auto; unfold R; apply AxiomII; Ens. }
  apply H5 in H8; clear H5; destruct H8; try contradiction.
  destruct H5; auto; unfold Rrelation, E in H5.
  apply AxiomII_P in H5; destruct H5.
  apply H2 in H8; elim H8; unfold Rrelation, Inverse.
  apply AxiomII_P; split; try apply Theorem49; Ens.
  unfold E; apply AxiomII_P; split; try apply Theorem49; Ens.
  unfold PlusOne; apply Theorem4; right.
  unfold Singleton; apply AxiomII; Ens.
Qed.

Hint Resolve Theorem133 : set.


(* Theorem134 : If x ∈ W, then x+1 ∈ W. *)

Theorem Theorem134 : forall x, x ∈ W -> (PlusOne x) ∈ W.
Proof.
  intros.
  unfold W in H; apply AxiomII in H; destruct H.
  unfold Integer in H0; destruct H0.
  unfold W; apply AxiomII; split.
  - unfold PlusOne; apply AxiomIV; split; auto.
    apply Theorem42 in H; auto.
  - unfold Integer; split.
    + assert (x ∈ R). { apply AxiomII; Ens. }
      apply Lemma123 in H2; apply AxiomII in H2; apply H2.
    + unfold KWellOrder in H1; unfold KWellOrder.
      destruct H1; split; intros.
      { clear H2; unfold Connect in H1; unfold Connect; intros.
        unfold PlusOne in H2; destruct H2; apply Theorem4 in H2.
        apply Theorem4 in H3; destruct H2, H3.
        - apply H1; auto.
        - unfold Singleton in H3; apply AxiomII in H3; destruct H3.
          rewrite <- H4 in H2; try apply Theorem19; Ens.
          right; left; unfold Rrelation, Inverse, E.
          apply AxiomII_P; split; try apply Theorem49; Ens.
          apply AxiomII_P; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply AxiomII in H2; destruct H2.
          rewrite <- H4 in H3; try apply Theorem19; Ens.
          left; unfold Rrelation, Inverse, E.
          apply AxiomII_P; split; try apply Theorem49; Ens.
          apply AxiomII_P; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply AxiomII in H2; destruct H2.
          unfold Singleton in H3; apply AxiomII in H3; destruct H3.
          right; right; rewrite H4, H5; try apply Theorem19; Ens. }
      { destruct H3; unfold PlusOne in H3.
        generalize (classic (x ∈ y)); intro; destruct H5.
        - exists x; unfold FirstMember; split; intros; auto.
          intro; unfold Rrelation in H7; apply AxiomII_P in H7.
          destruct H7; apply AxiomII_P in H8; destruct H8.
          apply H3 in H6; apply Theorem4 in H6; destruct H6.
          + eapply Theorem102; eauto.
          + apply AxiomII in H6; destruct H6.
            rewrite H10 in H9; try apply Theorem19; Ens.
            apply Theorem101 in H9; auto.
        - apply H2; split; auto; unfold Included; intros; double H6.
          apply H3 in H6; apply Theorem4 in H6; destruct H6; auto.
          apply AxiomII in H6; destruct H6; apply Theorem19 in H.
          rewrite <- H8 in H5; auto; contradiction. }
Qed.

Hint Resolve Theorem134 : set.


(* Theorem135 :  Φ ∈ W and if x ∈ W, then Φ ≠ x+1. *)

Theorem Theorem135 : forall x, 
  Φ ∈ W /\ (x ∈ W -> Φ ≠ PlusOne x).
Proof.
  intros; split; intros.
  - unfold W; apply AxiomII; split.
    + generalize AxiomVIII; intros; destruct H, H, H0; Ens.
    + unfold Integer; split.
      * unfold Ordinal; split.
        -- unfold Connect; intros; destruct H.
           generalize (Theorem16 u); contradiction.
        -- unfold full; intros.
           generalize (Theorem16 m); contradiction.
      * unfold KWellOrder; split; intros.
        -- unfold Connect; intros; destruct H.
           generalize (Theorem16 u); contradiction.
        -- destruct H; generalize (Theorem26 y); intros.
           absurd (y = Φ); try apply Theorem27; auto.
  - intro; unfold PlusOne in H0; assert (x ∈ Φ).
    { rewrite H0; apply Theorem4; right.
      unfold Singleton; apply AxiomII; split; Ens. }
    generalize (Theorem16 x); intro; contradiction.
Qed.

Hint Resolve Theorem135 : set.


(* Theorem137 : If x⊂W, Φ∈x and u+1∈x whenever u∈x, then x = w. *)

Corollary Property_W : Ordinal W.
Proof.
  unfold Ordinal; split.
  - unfold Connect; intros; destruct H; unfold W in H, H0.
    apply AxiomII in H; apply AxiomII in H0; destruct H, H0.
    unfold Integer in H1, H2; destruct H1, H2; add (Ordinal v) H1.
    apply Theorem110 in H1; destruct H1 as [H1|[H1|H1]]; try tauto.
    + left; unfold Rrelation, E; apply AxiomII_P.
      split; auto; apply Theorem49; split; auto.
    + right; left; unfold Rrelation, E; apply AxiomII_P.
      split; auto; apply Theorem49; split; auto.
  - unfold full; intros; unfold Included; intros.
    unfold W in H; apply AxiomII in H; destruct H.
    apply (Theorem132 _ z) in H1; auto.
    unfold W; apply AxiomII; Ens.
Qed.

Theorem Theorem137 : forall x,
  x ⊂ W -> Φ ∈ x ->
  (forall u, u ∈ x -> (PlusOne u) ∈ x) -> x = W.
Proof.
  intros.
  generalize (classic (x = W)); intros; destruct H2; auto.
  assert (exists y, FirstMember y E (W ~ x)).
  { assert (KWellOrder E W).
    { apply Theorem107; apply Property_W. }
    unfold KWellOrder in H3; destruct H3; apply H4; split.
    - unfold Included; intros; unfold Setminus in H5.
      apply Theorem4' in H5; apply H5.
    - intro; apply Property_Φ in H; apply H in H5.
      symmetry in H5; contradiction. }
  destruct H3 as [y H3]; unfold FirstMember in H3; destruct H3.
  unfold Setminus in H3; apply Theorem4' in H3; destruct H3.
  unfold W in H3; apply AxiomII in H3; destruct H3; double H6.
  unfold Integer in H7; destruct H7; unfold KWellOrder in H8.
  destruct H8; assert (y ⊂ y /\ y ≠ Φ).
  { split; try unfold Included; auto.
    intro; rewrite H10 in H5; unfold Complement in H5.
    apply AxiomII in H5; destruct H5; contradiction. }
  apply H9 in H10; clear H9; destruct H10 as [u H9].
  assert (u ∈ x).
  { unfold FirstMember in H9; destruct H9; clear H10.
    generalize (classic (u∈x)); intros; destruct H10; auto.
    assert (u ∈ (W ~ x)).
    { unfold Setminus; apply Theorem4'; split.
      - unfold W; apply AxiomII; split; Ens.
        apply Theorem132 in H9; auto.
      - unfold Complement; apply AxiomII; Ens. }
    apply H4 in H11; elim H11; unfold Rrelation, E.
    apply AxiomII_P; split; try apply Theorem49; Ens. }
  assert (y ∈ R /\ LastMember u E y).
  { split; auto; unfold R; apply AxiomII; Ens. }
  apply Theorem133 in H11; apply H1 in H10; rewrite <- H11 in H10.
  clear H11; unfold Complement in H5; apply AxiomII in H5.
  destruct H5; unfold NotIn in H11; contradiction.
Qed.

Hint Resolve Theorem137 : set.


(* Theorem138 : W ∈ R. *)

Theorem Theorem138 : W ∈ R.
Proof.
  unfold R; apply AxiomII; split; try apply Property_W.
  generalize AxiomVIII; intros; destruct H, H, H0.
  assert (W ∩ x = W).
  { apply Theorem137; intros.
    - unfold Included; intros; apply Theorem4' in H2; apply H2.
    - apply Theorem4'; split; auto; apply Theorem135; auto.
    - apply Theorem4' in H2; destruct H2; apply Theorem134 in H2.
      apply H1 in H3; apply Theorem4'; split; auto. }
  rewrite <- H2; apply Theorem33 with (x:=x); auto.
  unfold Included; intros; apply Theorem4' in H3; apply H3.
Qed.

Hint Resolve Theorem138 : set.


(* Mathematical Induction *)

Theorem MiniMember_Principle : forall S,
  S ⊂ W /\ S ≠ Φ -> exists a, a ∈ S /\ (forall c, c ∈ S -> a ≼ c).
Proof.
  intros; destruct H.
  assert (exists y, FirstMember y E S).
  { assert (KWellOrder E W).
    { apply Theorem107; apply Property_W. }
    unfold KWellOrder in H1; destruct H1; apply H2; auto. }
  destruct H1; exists x; unfold FirstMember in H1; destruct H1.
  split; auto; intros; double H3; apply H2 in H4.
  unfold Included in H; apply H in H1; apply H in H3.
  unfold W in H1, H3; apply AxiomII in H1; apply AxiomII in H3.
  destruct H1, H3; unfold Integer in H5, H6; destruct H5, H6.
  add (Ordinal c) H5; clear H6 H7 H8; apply Theorem110 in H5.
  unfold LessEqual; destruct H5 as [H5|[H5|H5]]; try tauto.
  elim H4; unfold Rrelation, E; apply AxiomII_P; split; auto.
  apply Theorem49; split; Ens.
Qed.

Definition En_S P : Class := \{ λ x, x ∈ W /\ ~ (P x) \}.

Theorem Mathematical_Induction : forall (P: Class -> Prop),
  P Φ -> (forall k, k ∈ W /\ P k -> P (PlusOne k)) ->
  (forall n, n ∈ W -> P n).
Proof.
  intros.
  generalize (classic ((En_S P) = Φ)); intros; destruct H2.
  - generalize (classic (P n)); intros; destruct H3; auto.
    assert (n ∈ (En_S P)). { apply AxiomII; split; Ens. }
    rewrite H2 in H4; generalize (Theorem16 n); contradiction.
  - assert ((En_S P) ⊂ W).
    { unfold En_S, Included; intros; apply AxiomII in H3; apply H3. }
    add ((En_S P) <> Φ) H3; clear H2.
    apply MiniMember_Principle in H3; destruct H3 as [h H3], H3.
    unfold En_S in H2; apply AxiomII in H2; destruct H2, H4.
    unfold W in H4; apply AxiomII in H4; clear H2; destruct H4.
    double H4; unfold Integer in H6; destruct H6.
    unfold KWellOrder in H7; destruct H7.
    assert (h ⊂ h /\ h ≠ Φ).
    { split; try (unfold Included; intros; auto).
      generalize (classic (h = Φ)); intros; destruct H9; auto.
      rewrite H9 in H5; contradiction. }
    apply H8 in H9; clear H8; destruct H9.
    assert (h ∈ R /\ LastMember x E h).
    { split; auto; unfold R; apply AxiomII; split; auto. }
    apply Theorem133 in H9; unfold PlusOne in H9.
    unfold FirstMember in H8; destruct H8.
    generalize (classic (x ∈ (En_S P))); intros; destruct H11.
    + apply H3 in H11; assert (x ∈ h).
      { rewrite H9; apply Theorem4; right; apply AxiomII; Ens. }
      unfold LessEqual in H11; destruct H11.
      * add (x ∈ h) H11; clear H12.
        generalize (Theorem102 h x); intros; contradiction.
      * rewrite H11 in H12; generalize (Theorem101 x); contradiction.
    + assert (x ∈ (En_S P) <-> (Ensemble x /\ x ∈ W /\ ~ (P x))).
      { unfold En_S; split; intros.
        - apply AxiomII in H12; apply H12.
        - apply AxiomII; auto. }
      apply definition_not in H12; auto; clear H11.
      apply not_and_or in H12; destruct H12.
      * absurd (Ensemble x); Ens.
      * assert (x ∈ W).
        { unfold W; apply AxiomII; split; Ens.
          apply Theorem132 in H8; auto. }
        apply not_and_or in H11; destruct H11; try contradiction.
        apply NNPP in H11; add (P x) H12; clear H11.
        apply H0 in H12; unfold PlusOne in H12.
        rewrite <- H9 in H12; contradiction.
Qed.


(* Definition139 : c is a choice function if and only if c is a function and
   c(x) ∈ x for each member x of domain c. *)

Definition ChoiceFunction c : Prop :=
  Function c /\ (forall x, x ∈ dom(c) -> c[x] ∈ x).

Hint Unfold ChoiceFunction : set.


(* IX Axiom of Choice : There is a choice function c whose domain is μ ~ {Φ}. *)

Axiom AxiomIX : exists c, ChoiceFunction c /\ dom(c) = μ ~ [Φ].

Hint Resolve AxiomIX : set.


(* Theorem140 : If x is a set there is a 1_1 function whose range is x and
   whose domain is an ordinal number. *)

Lemma Ex_Lemma140 : forall x c,
  Ensemble x -> ChoiceFunction c ->
  (exists g, forall h, Ensemble h -> g[h] = c[x ~ ran(h)]).
Proof.
  intros.
  unfold ChoiceFunction in H0; destruct H0.
  exists (\{\ λ u v, v = c [x ~ ran(u)] \}\); intros.
  apply AxiomI; split; intros.
  - apply AxiomII; split; Ens; intros.
    apply AxiomII in H3; destruct H3.
    apply H5; clear H5; apply AxiomII; split; Ens.
    apply AxiomII_P; split; try apply Theorem49; Ens.
    apply AxiomII in H4; destruct H4.
    rewrite Theorem70 in H5; auto.
    apply AxiomII_P in H5; apply H5.
  - apply AxiomII; split; Ens; intros.
    apply AxiomII in H4; destruct H4.
    apply AxiomII_P in H5; destruct H5.
    rewrite H6; auto.
Qed.

Lemma Lemma140 : forall f g y,
  y ∈ dom(f) -> f [y] = g [f|(y)] -> Ensemble (f|(y)).
Proof.
  intros.
  generalize (classic ((f|(y)) ∈ dom(g))); intros; destruct H1; Ens.
  apply Theorem69 in H1; rewrite H1 in H0; clear H1.
  apply Theorem69 in H; rewrite H0 in *.
  generalize (Theorem101 μ); intros; contradiction.
Qed.

Theorem Theorem140 : forall x,
  Ensemble x -> exists f, Function1_1 f /\ ran(f) = x /\ Ordinal_Number dom(f).
Proof.
  intros.
  generalize AxiomIX; intros; destruct H0 as [c H0], H0.
  double H0; apply (Ex_Lemma140 x _) in H2; auto; destruct H2 as [g H2].
  generalize (Theorem128 g); intros; destruct H3 as [f H3], H3, H4.
  unfold ChoiceFunction in H0; destruct H0; exists f.
  assert (Function1_1 f).
  { unfold Function1_1; split; auto.
    unfold Function; split; intros.
    - unfold Relation; intros; PP H7 a b; Ens.
    - unfold Inverse in H7; destruct H7.
      apply AxiomII_P in H7; apply AxiomII_P in H8; destruct H7, H8.
      clear H7 H8; double H9; apply Property_dom in H8.
      double H10; apply Property_dom in H10.
      generalize (classic (y = z)); intros; destruct H11; auto.
      assert (Ordinal y /\ Ordinal z).
      { split; apply (Theorem111 dom(f) _); auto. }
      elim H12; intros; apply Theorem110 in H12.
      assert (Ordinal_Number y /\ Ordinal_Number z).
      { unfold Ordinal_Number, R; split; apply AxiomII; Ens. }
      clear H13 H14; destruct H15; apply H5 in H13; apply H5 in H14.
      rewrite H2 in H13, H14; try apply (Lemma140 _ g _); auto.
      clear H2 H5; apply Property_Value in H8; auto.
      apply Property_Value in H10; auto.
      unfold Function in H3; destruct H3.
      add ([y,f[y]] ∈ f) H7; add ([z,f[z]] ∈ f) H9.
      apply H3 in H7; apply H3 in H9; rewrite H9 in H7; clear H9.
      double H8; double H10; apply Property_ran in H8.
      apply Property_ran in H10; destruct H12.
      + assert (f[z] ∈ ran(f|(z))).
        { rewrite H7; unfold Range; apply AxiomII; split; Ens.
          exists y; unfold Restriction; apply Theorem4'; split; auto.
          unfold Cartesian; apply AxiomII_P; split; Ens.
          split; auto; apply Theorem19; Ens. }
        assert ((x ~ ran(f|(z))) ∈ dom(c)).
        { generalize (classic ((x ~ ran(f|(z))) ∈ dom(c))); intros.
          destruct H16; auto; apply Theorem69 in H16; auto.
          rewrite H16 in H14; rewrite H14 in H10; AssE μ.
          generalize Theorem39; intros; contradiction. }
        apply H6 in H16; unfold Setminus at 2 in H16.
        rewrite <- H14 in H16; apply Theorem4' in H16; destruct H16.
        unfold Complement in H17; apply AxiomII in H17; destruct H17.
        unfold NotIn in H18; contradiction.
      + destruct H12; try contradiction.
        assert (f[y] ∈ ran(f|(y))).
        { rewrite <- H7; unfold Range; apply AxiomII; split; Ens.
          exists z; unfold Restriction; apply Theorem4'; split; auto.
          unfold Cartesian; apply AxiomII_P; split; Ens.
          split; auto; apply Theorem19; Ens. }
        assert ((x ~ ran(f|(y))) ∈ dom(c)).
        { generalize (classic ((x ~ ran(f|(y))) ∈ dom(c))); intros.
          destruct H16; auto; apply Theorem69 in H16; auto.
          rewrite H16 in H13; rewrite H13 in H8; AssE μ.
          generalize Theorem39; intros; contradiction. }
        apply H6 in H16; unfold Setminus at 2 in H16.
        rewrite <- H13 in H16; apply Theorem4' in H16; destruct H16.
        unfold Complement in H17; apply AxiomII in H17; destruct H17.
        unfold NotIn in H18; contradiction. }
  split; auto; assert (ran(f) ⊂ x).
  { unfold Included; intros; unfold Range in H8; apply AxiomII in H8.
    destruct H8, H9; double H9; apply Property_dom in H10.
    assert (Ordinal_Number x0).
    { unfold Ordinal_Number, R; apply AxiomII; split; Ens.
      apply (Theorem111 dom(f) _); split; auto. }
    apply H5 in H11; rewrite H2 in H11; try apply (Lemma140 _ g _); auto.
    apply Property_Value in H10; auto; destruct H3.
    add ([x0,f[x0]]∈f) H9; apply H12 in H9; rewrite <- H9 in H11.
    assert ((x ~ ran(f|(x0))) ∈ dom(c)).
    { generalize (classic ((x ~ ran(f|(x0))) ∈ dom(c))); intros.
      destruct H13; auto; apply Theorem69 in H13; auto.
      rewrite H13 in H11; rewrite H11 in H9; rewrite <- H9 in H10.
      clear H9 H11 H13; apply Property_ran in H10; AssE μ.
      generalize Theorem39; intros; contradiction. }
    apply H6 in H13; rewrite <- H11 in H13.
    unfold Setminus in H13; apply Theorem4' in H13; apply H13. }
  assert (Ensemble dom(f)).
  { unfold Function1_1 in H7; destruct H7 as [H9 H7]; clear H9.
    generalize (Property_F11 f); intros; destruct H9; rewrite <- H9 in H8.
    rewrite <- H10; apply AxiomV; apply Theorem33 in H8; auto. }
  assert (Ordinal_Number dom(f)).
  { unfold Ordinal_Number; apply AxiomII; split; auto. }
  split; auto; apply H5 in H10.
  assert (f|(dom(f)) = f).
  { unfold Restriction; apply AxiomI; split; intros.
    - apply AxiomII in H11; apply H11.
    - apply AxiomII; repeat split; Ens; unfold Function, Relation in H3.
      double H11; apply H3 in H12; destruct H12 as [a [b H12]].
      rewrite H12 in *; clear H12; apply AxiomII_P; repeat split; Ens.
      + apply Property_dom in H11; auto.
      + apply Property_ran in H11; apply Theorem19; Ens. }
  rewrite H11 in *; clear H11.
  rewrite H2 in H10; try apply Theorem75; auto.
  generalize (Theorem101 dom(f)); intros.
  apply Theorem69 in H11; auto; rewrite H10 in H11.
  generalize (classic ((x ~ ran(f)) ∈ dom(c))); intros; destruct H12.
  - apply Theorem69 in H12; auto; rewrite H11 in H12.
    generalize (Theorem101 μ); intros; contradiction.
  - rewrite H1 in H12; unfold Setminus at 2 in H12.
    assert ((x ~ ran(f)) ∈ (μ ∩ ¬[Φ]) <-> (x ~ ran(f)) ∈ μ /\
            (x ~ ran(f)) ∈ ¬[Φ]).
    { split; intros; try apply Theorem4'; auto. }
    apply definition_not in H13; auto; clear H12.
    assert (Ensemble (x ~ ran(f))).
    { apply (Theorem33 x _); auto; unfold Included.
      intros; apply AxiomII in H12; apply H12. }
    apply not_and_or in H13; destruct H13.
    + elim H13; apply Theorem19; auto.
    + assert ((x ~ ran(f)) ∈ ¬[Φ] <-> Ensemble (x ~ ran(f)) /\
              (x ~ ran(f)) ∉ [Φ]).
      { split; intros; try apply AxiomII; auto.
        apply AxiomII in H14; apply H14. }
      apply definition_not in H14; auto; clear H13.
      apply not_and_or in H14; destruct H14; try contradiction.
      unfold NotIn in H13; apply NNPP in H13.
      unfold Singleton in H13; apply AxiomII in H13; destruct H13.
      generalize AxiomVIII; intros; destruct H15, H15, H16.
      AssE Φ; clear H15 H16 H17; apply Theorem19 in H18.
      apply H14 in H18; symmetry; apply -> Property_Φ in H18; auto.
Qed.

Hint Resolve Theorem140 : set.


(* Definition144 : x ≈ y if and only if there is a 1_1 function f with
   domain f = x and range f = y. *)

Definition Equivalent x y : Prop :=
  exists f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.

Notation "x ≈ y" := (Equivalent x y) (at level 70).

Hint Unfold Equivalent : set.


(* Theorem145 : x ≈ x. *)

Theorem Theorem145 : forall x, x ≈ x.
Proof.
  intros.
  unfold Equivalent.
  exists (\{\ λ u v, u ∈ x /\ u = v \}\); split.
  - unfold Function1_1; split.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H a b; Ens.
      * destruct H; apply AxiomII_P in H.
        apply AxiomII_P in H0; destruct H, H0, H1, H2.
        rewrite <- H3, <- H4; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H a b; Ens.
      * unfold Inverse in H; destruct H; apply AxiomII_P in H.
        apply AxiomII_P in H0; destruct H, H0.
        apply AxiomII_P in H1; apply AxiomII_P in H2.
        destruct H1, H2, H3, H4; rewrite H5, H6; auto.
   - split.
     + apply AxiomI; split; intros.
       * unfold Domain in H; apply AxiomII in H; destruct H, H0.
         apply AxiomII_P in H0; apply H0.
       * unfold Domain; apply AxiomII; split; Ens.
         exists z; apply AxiomII_P; repeat split; auto.
         apply Theorem49; split; Ens.
     + apply AxiomI; split; intros.
       * unfold Range in H; apply AxiomII in H; destruct H, H0.
         apply AxiomII_P in H0; destruct H0, H1.
         rewrite H2 in H1; auto.
       * unfold Range; apply AxiomII; split; Ens.
         exists z; apply AxiomII_P; repeat split; auto.
         apply Theorem49; split; Ens.
Qed.

Hint Resolve Theorem145 : set.


(* Theorem146 : If x ≈ y, then y ≈ x. *)

Theorem Theorem146 : forall x y, x ≈ y -> y ≈ x.
Proof.
  intros.
  unfold Equivalent in H; destruct H as [f H], H, H0.
  unfold Equivalent; exists f⁻¹; split.
  - unfold Function1_1 in H; destruct H.
    unfold Function1_1; split; try rewrite Theorem61; try apply H; auto.
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


(* Theorem147 : If x ≈ y and y ≈ z, then x ≈ z. *)

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


(* Definition148 : x is a cardinal number if and onlu if x is a ordinal number
   and, if y∈R and y≺x, then it is false that x ≈ y. *)

Definition Cardinal_Number x : Prop :=
  Ordinal_Number x /\ (forall y, y∈R -> y ≺ x -> ~ (x ≈ y)).

Hint Unfold Cardinal_Number : set.


(* Definition149 : C = {x : x is a cardinal number}. *)

Definition C : Class := \{ λ x, Cardinal_Number x \}.

Hint Unfold C : set.


(* Definition151 : P = {(x,y) : x ≈ y and y∈C}. *)

Definition P : Class := \{\ λ x y, x ≈ y /\ y∈C \}\.

Hint Unfold P : set.


(* Theorem152 : P is a function, domain P = μ and range P = C. *)

Theorem Theorem152 : Function P /\ dom(P) = μ /\ ran(P) = C.
Proof.
  unfold P; repeat split; intros.
  - unfold Relation; intros; PP H a b; Ens.
  - destruct H; apply AxiomII_P in H; apply AxiomII_P in H0.
    destruct H, H0, H1, H2; apply Theorem146 in H1.
    apply (Theorem147 _ _ z) in H1; auto; clear H H0 H2.
    unfold C in H3, H4; apply AxiomII in H3; destruct H3.
    apply AxiomII in H4; destruct H4.
    unfold Cardinal_Number in H0, H3; destruct H0, H3.
    unfold Ordinal_Number in H0, H3.
    assert (Ordinal y /\ Ordinal z).
    { unfold R in H0, H3; apply AxiomII in H0.
      apply AxiomII in H3; destruct H0, H3; split; auto. }
    apply Theorem110 in H6; destruct H6.
    + apply Theorem146 in H1; apply H5 in H0; auto; try contradiction.
    + destruct H6; auto; apply H4 in H3; auto; try contradiction.
  - apply AxiomI; split; intros; try apply Theorem19; Ens.
    apply Theorem19 in H; double H; apply Theorem140 in H0.
    destruct H0 as [f H0], H0, H1; apply AxiomII; split; auto.
    assert (KWellOrder E \{ λ x, x ≈ z /\ Ordinal x \}).
    { assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ R).
      { unfold Included; intros; apply AxiomII in H3.
        destruct H3, H4; apply AxiomII; split; auto. }
      apply (Lemma97 _ E _) in H3; auto.
      apply Theorem107; apply Theorem113. }
    unfold KWellOrder in H3; destruct H3 as [H4 H3]; clear H4.
    assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ \{ λ x, x ≈ z /\ Ordinal x \}
            /\ \{ λ x, x ≈ z /\ Ordinal x \} ≠ Φ).
    { split; try unfold Included; auto.
      apply Property_NotEmpty; exists dom(f); apply AxiomII.
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
      apply Theorem145.
Qed.

Hint Resolve Theorem152 : set.


(* Property of P *)

Corollary Property_PClass : forall x, Ensemble x -> P [x] ∈ C.
Proof.
  intros.
  generalize Theorem152; intros; destruct H0, H1.
  apply Theorem19 in H; rewrite <- H1 in H.
  apply Property_Value in H; auto.
  apply Property_ran in H; rewrite H2 in H; auto.
Qed.

Hint Resolve Property_PClass : set.


(* Theorem153 : If x is a set, then P(x) ≈ x. *)

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


(* Theorem163 : If x∈w, y∈w and x+1 ≈ y+1, then x ≈ y. *)

Ltac SplitEns := apply AxiomII; split; Ens.

Ltac SplitEnsP := apply AxiomII_P; split; try apply Theorem49; Ens.

Definition En_g' f x y : Class :=
  \{\ λ u v, [u,v] ∈ (f ~ ([[x,f[x]]] ∪ [[f⁻¹[y],y]])) \/
      [u,v] = [f⁻¹[y],f[x]] \/ [u,v] = [x,y] \}\.

Theorem Theorem163 : forall x y,
  x∈W -> y∈W -> (PlusOne x) ≈ (PlusOne y) -> x ≈ y.
Proof.
  intros.
  unfold Equivalent in H1; destruct H1 as [f H1], H1, H2.
  unfold Function1_1 in H1; destruct H1; unfold Equivalent.
  exists ((En_g' f x y) | (x)); repeat split; intros.
  - unfold Relation; intros; unfold Restriction in H5.
    apply Theorem4' in H5; destruct H5; PP H6 a b; Ens.
  - destruct H5; unfold Restriction in H5, H6.
    apply Theorem4' in H5; apply Theorem4' in H6.
    destruct H5, H6; clear H8; unfold En_g' in H5, H6.
    apply AxiomII_P in H5; apply AxiomII_P in H6; destruct H5,H6.
    unfold Cartesian in H7; apply AxiomII_P in H7; clear H5.
    destruct H7, H7; clear H10; destruct H8, H9.
    + unfold Setminus in H8, H9; apply Theorem4' in H8.
      apply Theorem4' in H9; destruct H8, H9; clear H10 H11.
      unfold Function in H1; apply H1 with (x:= x0); auto.
    + destruct H9.
      * unfold Setminus in H8; apply Theorem4' in H8; destruct H8.
        unfold Complement in H10; apply AxiomII in H10; clear H5.
        destruct H10; elim H10; clear H10; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H10.
        apply Theorem49 in H6; apply Theorem55 in H9; auto.
        destruct H9; clear H10; double H8; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H8.
        apply H1 in H8; clear H10; rewrite H9 in H8.
        rewrite <- Lemma96''' in H8; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply Theorem4; right.
        unfold Singleton; apply AxiomII; split; Ens.
      * apply Theorem49 in H6; apply Theorem55 in H9; auto; destruct H9.
        rewrite H9 in H7; generalize (Theorem101 x); contradiction.
    + destruct H8.
      * unfold Setminus in H9; apply Theorem4' in H9; destruct H9.
        unfold Complement in H10; apply AxiomII in H10; clear H6.
        destruct H10; elim H10; clear H10; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H10.
        apply Theorem49 in H5; apply Theorem55 in H8; auto.
        destruct H8; clear H10; double H9; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H9.
        apply H1 in H9; clear H10; rewrite H8 in H9.
        rewrite <- Lemma96''' in H9; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply Theorem4; right.
        unfold Singleton; apply AxiomII; split; Ens.
      * apply Theorem49 in H5; apply Theorem55 in H8; auto; destruct H8.
        rewrite H8 in H7; generalize (Theorem101 x); contradiction.
    + apply Theorem49 in H5; apply Theorem49 in H6.
      destruct H8, H9; apply Theorem55 in H8; apply Theorem55 in H9; auto.
      * destruct H8, H9; rewrite H10, H11; auto.
      * destruct H9; rewrite H9 in H7.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H8; rewrite H8 in H7.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H8; rewrite H8 in H7.
        generalize (Theorem101 x); intros; contradiction.
  - unfold Relation; intros; PP H5 a b; Ens.
  - destruct H5; unfold Inverse, Restriction in H5, H6.
    apply AxiomII_P in H5; apply AxiomII_P in H6; destruct H5, H6.
    apply Theorem4' in H7; apply Theorem4' in H8; destruct H7, H8.
    apply AxiomII_P in H7; apply AxiomII_P in H8; destruct H7, H8.
    unfold Cartesian in H9; apply AxiomII_P in H9; clear H7.
    destruct H9, H9; clear H13; apply AxiomII_P in H10; clear H8.
    destruct H10, H10; clear H13; destruct H11, H12.
    + unfold Setminus in H11, H12; apply Theorem4' in H11.
      apply Theorem4' in H12; destruct H11, H12; clear H13 H14.
      assert ([x0,y0] ∈ f⁻¹ /\ [x0,z] ∈ f⁻¹).
      { unfold Inverse; split; apply AxiomII_P; split; auto. }
      unfold Function in H4; apply H4 in H13; auto.
    + destruct H12.
      * unfold Setminus in H11; apply Theorem4' in H11; destruct H11.
        clear H13; apply Theorem49 in H8; apply Theorem55 in H12; auto.
        destruct H12; rewrite H13 in *; double H11.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],y0] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply AxiomII_P; split; auto; AssE [x,f[x]].
          apply Theorem49 in H15; destruct H15; apply Theorem49; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H9; generalize (Theorem101 x); contradiction.
      * unfold Setminus in H11; apply Theorem4' in H11; destruct H11.
        unfold Complement in H13; apply AxiomII in H13; clear H7.
        destruct H13; elim H13; clear H13; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H13.
        apply Theorem49 in H8; apply Theorem55 in H12; auto.
        destruct H12; rewrite H13 in *; clear H6 H8 H12 H13.
        assert ([y,y0] ∈ f⁻¹). { apply AxiomII_P; Ens. }
        double H6; apply Property_dom in H8; apply Property_Value in H8; auto.
        add ([y,y0] ∈ f⁻¹) H8; apply H4 in H8; rewrite H8; auto.
    + destruct H11.
      * unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
        clear H13; apply Theorem49 in H7; apply Theorem55 in H11; auto.
        destruct H11; rewrite H13 in *; double H12.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],z] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply AxiomII_P; split; auto; AssE [x,f[x]].
          apply Theorem49 in H15; destruct H15; apply Theorem49; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H10; generalize (Theorem101 x); contradiction.
      * unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
        unfold Complement in H13; apply AxiomII in H13; clear H8.
        destruct H13; elim H13; clear H13; apply Theorem4.
        right; apply AxiomII; split; auto; intros; clear H13.
        apply Theorem49 in H7; apply Theorem55 in H11; auto.
        destruct H11; rewrite H13 in *; clear H5 H7 H11 H13.
        assert ([y,z] ∈ f⁻¹). { apply AxiomII_P; Ens. }
        double H5; apply Property_dom in H7; apply Property_Value in H7; auto.
        add ([y,z] ∈ f⁻¹) H7; apply H4 in H7; rewrite H7; auto.
    + apply Theorem49 in H7; apply Theorem49 in H8.
      destruct H11, H12; apply Theorem55 in H11; apply Theorem55 in H12; auto.
      * destruct H11, H12; rewrite H11, H12; auto.
      * destruct H12; rewrite H12 in H10.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H11; rewrite H11 in H9.
        generalize (Theorem101 x); intros; contradiction.
      * destruct H12; rewrite H12 in H10.
        generalize (Theorem101 x); intros; contradiction.
  - apply AxiomI; split; intros.
    + unfold Domain in H5; apply AxiomII in H5; destruct H5, H6.
      unfold Restriction in H6; apply Theorem4' in H6; destruct H6.
      unfold Cartesian in H7; apply AxiomII_P in H7; apply H7.
    + unfold Domain; apply AxiomII; split; Ens.
      assert ([x,f[x]] ∈ f).
      { apply Property_Value; auto; rewrite H2; unfold PlusOne.
        apply Theorem4; right; apply AxiomII; split; Ens. }
      generalize (classic (z = f⁻¹[y])); intros; destruct H7.
      * rewrite H7 in *; AssE [x,f[x]]; clear H6 H7.
        apply Theorem49 in H8; destruct H8.
        exists f[x]; unfold Restriction; apply Theorem4'.
        split; SplitEnsP; split; try apply Theorem19; auto.
      * assert (z ∈ dom(f)). { rewrite H2; apply Theorem4; tauto. }
        apply Property_Value in H8; auto; AssE [z,f[z]].
        apply Theorem49 in H9; destruct H9; exists f[z].
        unfold Restriction; apply Theorem4'; split; SplitEnsP.
        { left; unfold Setminus; apply Theorem4'; split; auto.
          unfold Complement; apply AxiomII; split; Ens.
          intro; apply Theorem4 in H11; destruct H11.
          - apply AxiomII in H11; destruct H11; clear H11.
            assert ([x,f[x]] ∈ μ). { apply Theorem19; Ens. }
            apply H12 in H11; clear H12; apply Theorem55 in H11; auto.
            destruct H11; rewrite H11 in H5; generalize (Theorem101 x); auto.
          - apply AxiomII in H11; destruct H11; clear H11.
            assert ([(f⁻¹)[y],y] ∈ μ).
            { apply Theorem19; Ens; exists f.
              assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply Theorem4; right.
                apply AxiomII; split; Ens. }
              rewrite Lemma96' in H11; apply Property_Value in H11; auto.
              apply AxiomII_P in H11; apply H11. }
            apply H12 in H11; clear H12; apply Theorem55 in H11; auto.
            destruct H11; contradiction. }
        { split; try apply Theorem19; auto. }
  - apply AxiomI; split; intros.
    + unfold Range in H5; apply AxiomII in H5; destruct H5, H6.
      unfold Restriction in H6; apply Theorem4' in H6; destruct H6.
      unfold Cartesian in H7; apply AxiomII_P in H7; destruct H7.
      clear H7; destruct H8; clear H8; unfold En_g' in H6.
      apply AxiomII_P in H6; destruct H6, H8 as [H8|[H8|H8]].
      * unfold Setminus in H8; apply Theorem4' in H8; destruct H8.
        unfold Complement in H9; apply AxiomII in H9; clear H6.
        destruct H9; double H8; apply Property_ran in H10; rewrite H3 in H10.
        unfold PlusOne in H10; apply Theorem4 in H10; destruct H10; auto.
        apply AxiomII in H10; clear H5; destruct H10.
        rewrite H10 in *; try apply Theorem19; Ens; clear H10.
        double H8; apply Property_ran in H10; rewrite Lemma96' in H10.
        apply Property_Value in H10; auto; apply Theorem49 in H6.
        destruct H6; clear H11; add ([y,x0] ∈ f⁻¹) H10; try SplitEnsP.
        apply H4 in H10; rewrite H10 in H9; elim H9.
        apply Theorem4; right; SplitEns.
      * apply Theorem49 in H6; apply Theorem55 in H8; auto; destruct H8.
        assert (x ∈ dom(f)).
        { rewrite H2; unfold PlusOne; apply Theorem4; right.
          unfold Singleton; apply AxiomII; split; Ens. }
        double H10; apply Property_Value in H11; auto.
        apply Property_ran in H11; rewrite H3 in H11; unfold PlusOne in H11.
        apply Theorem4 in H11; rewrite H9 in *; destruct H11; auto.
        apply AxiomII in H11; clear H5; destruct H11.
        rewrite <- H11 in H8; try apply Theorem19; Ens.
        pattern f at 2 in H8; rewrite <- Theorem61 in H8; try apply H1.
        rewrite <- Lemma96''' in H8; try rewrite Theorem61; try apply H1; auto.
        { rewrite H8 in H7; generalize (Theorem101 x); contradiction. }
        { rewrite <- Lemma96; auto. }
      * apply Theorem49 in H6; apply Theorem55 in H8; auto; destruct H8.
        rewrite H8 in H7; generalize (Theorem101 x); contradiction.
    + unfold Range; apply AxiomII; split; Ens.
      assert (z∈ran(f)). { rewrite H3; unfold PlusOne; apply Theorem4; auto. }
      generalize (classic (z = f[x])); intros; destruct H7.
      * rewrite H7 in *; clear H7.
        assert (y ∈ ran(f)).
        { rewrite H3; unfold PlusOne; apply Theorem4; right.
          unfold Singleton; apply AxiomII; split; Ens. }
        double H7; rewrite Lemma96' in H8; apply Property_Value in H8; auto.
        apply Property_ran in H8; rewrite <- Lemma96 in H8; rewrite H2 in H8.
        unfold PlusOne in H8; apply Theorem4 in H8; destruct H8.
        { exists (f⁻¹)[y]; unfold Restriction; apply Theorem4'.
          split; SplitEnsP; split; try apply Theorem19; Ens. }
        { unfold Singleton in H8; apply AxiomII in H8; destruct H8.
          rewrite <- H9 in H5; try apply Theorem19; Ens.
          rewrite <- Lemma96''' in H5; auto.
          generalize (Theorem101 y); intros; contradiction. }
      * unfold Range in H6; apply AxiomII in H6; destruct H6, H8; exists x0.
        AssE [x0,z]; unfold Restriction; apply Theorem4'; split.
        { unfold En_g'; apply AxiomII_P; split; auto; left.
          unfold Setminus; apply Theorem4'; split; auto; unfold Complement.
          apply AxiomII; split; auto; intro; apply Theorem4 in H10.
          destruct H10; apply AxiomII in H10; destruct H10.
          - assert ([x,f[x]] ∈ μ); clear H10.
            { apply Theorem19; Ens; exists f; apply Property_Value; auto.
              rewrite H2; unfold PlusOne; apply Theorem4; right.
              unfold Singleton; apply AxiomII; split; Ens. }
            apply H11 in H12; clear H11; apply Theorem49 in H9.
            apply Theorem55 in H12; auto; destruct H12; tauto.
          - assert ([(f⁻¹)[y], y] ∈ μ); clear H10.
            { apply Theorem19; Ens; exists f. assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply Theorem4; right.
                apply AxiomII; split; Ens. }
              rewrite Lemma96' in H10; apply Property_Value in H10; auto.
              apply AxiomII_P in H10; apply H10. }
            apply H11 in H12; clear H11; apply Theorem49 in H9.
            apply Theorem55 in H12; auto; destruct H12; rewrite H11 in H5.
            generalize (Theorem101 y); intros; contradiction. }
        { double H8; apply Property_dom in H10; rewrite H2 in H10.
          unfold PlusOne in H10; apply Theorem4 in H10; unfold Cartesian.
          apply AxiomII_P; repeat split; auto; try apply Theorem19; Ens.
          destruct H10; auto; apply AxiomII in H10; destruct H10.
          rewrite H11 in H8; try apply Theorem19; Ens; double H8.
          apply Property_dom in H12; apply Property_Value in H12; auto.
          add ([x,z] ∈ f) H12; apply H1 in H12; symmetry in H12; tauto. }
Qed.

Hint Resolve Theorem163 : set.

(* Theorem164 : w ⊂ C. *)

Theorem Theorem164 : W ⊂ C.
Proof.
  intros.
  unfold Included; apply Mathematical_Induction.
  - assert (Φ ∈ W); try apply Theorem135; try apply W.
    unfold W in H; apply AxiomII in H; destruct H; unfold Integer in H0.
    destruct H0; unfold C; apply AxiomII.
    unfold Cardinal_Number, Ordinal_Number; repeat split; intros; auto.
    + unfold R; apply AxiomII; split; auto.
    + unfold Less in H3; generalize (Theorem16 y); contradiction.
  - intros; destruct H; double H; apply Theorem134 in H1; unfold W in H1.
    apply AxiomII in H1; unfold Integer in H1; destruct H1, H2.
    unfold C in H0; apply AxiomII in H0; destruct H0.
    unfold Cardinal_Number, Ordinal_Number in H4; destruct H4.
    unfold C; apply AxiomII; split; auto; split; intros.
    + unfold Ordinal_Number, R; apply AxiomII; split; auto.
    + unfold Less, PlusOne in H7; apply Theorem4 in H7; destruct H7.
      * assert (y ∈ W).
        { unfold W; apply AxiomII; split; Ens.
          unfold W in H; apply AxiomII in H; destruct H.
          apply Theorem132 in H7; auto. }
        intro; clear H6; double H8; apply AxiomII in H6; destruct H6.
        unfold Integer in H10; destruct H10; unfold KWellOrder in H11.
        destruct H11 as [H12 H11]; clear H12.
        generalize (classic (y = Φ)); intros; destruct H12.
        { rewrite H12 in H9; clear H12; unfold Equivalent in H9.
          destruct H9 as [f H9]; destruct H9, H12.
          assert (k ∈ (PlusOne k)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply AxiomII; split; Ens. }
          rewrite <- H12 in H14; unfold Function1_1 in H9; destruct H9.
          apply Property_Value in H14; auto; apply Property_ran in H14.
          rewrite H13 in H14; generalize (Theorem16 f[k]); contradiction. }
        { assert (y ⊂ y /\ y ≠ Φ). { split; unfold Included; Ens. }
          apply H11 in H13; clear H11 H12; destruct H13.
          assert (y = PlusOne x).
          { apply Theorem133; split; auto; try apply AxiomII; Ens. }
          unfold FirstMember in H11; destruct H11; clear H13.
          rewrite H12 in H9; apply Theorem163 in H9; auto.
          - assert (x ∈ R /\ x ≺ k).
            { unfold Less; split.
              - unfold R; apply AxiomII; split; Ens.
                apply Theorem111 with (x:= y); auto.
              - unfold R in H4; apply AxiomII in H4; destruct H4.
                unfold Ordinal, full in H13; destruct H13.
                apply H14 in H7; apply H7 in H11; auto. }
            destruct H13; apply H5 in H14; auto.
          - generalize Property_W; intros; unfold Ordinal, full in H13.
            destruct H13; apply H14 in H8; apply H8 in H11; auto. }
      * unfold Singleton in H7; apply AxiomII in H7; destruct H7.
        assert (k ∈ μ); try apply Theorem19; Ens; apply H8 in H9.
        clear H6 H7 H8; rewrite H9; intro; clear H9; double H.
        apply AxiomII in H7; clear H0; destruct H7; unfold Integer in H7.
        destruct H7; unfold KWellOrder in H8; destruct H8; clear H8.
        generalize (classic (k = Φ)); intros; destruct H8.
        { rewrite H8 in H6; clear H8; unfold Equivalent in H6.
          destruct H6 as [f H6]; destruct H6, H8.
          assert (Φ ∈ (PlusOne Φ)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply AxiomII; split; auto; generalize AxiomVIII; intros.
            destruct H11, H11, H12; Ens. }
          rewrite <- H8 in H11; unfold Function1_1 in H6; destruct H6.
          apply Property_Value in H11; auto; apply Property_ran in H11.
          rewrite H10 in H11; generalize (Theorem16 f[Φ]); contradiction. }
        { assert (k ⊂ k /\ k ≠ Φ). { split; unfold Included; Ens. }
          apply H9 in H10; clear H8 H9; destruct H10.
          assert (k = PlusOne x).
          { apply Theorem133; split; auto; try apply AxiomII; Ens. }
          unfold FirstMember in H8; destruct H8; clear H10.
          pattern k at 2 in H6; rewrite H9 in H6; apply Theorem163 in H6; auto.
          - apply H5 in H8; try contradiction; unfold R; apply AxiomII.
            split; Ens; apply Theorem111 with (x:= k); auto.
          - unfold W; apply AxiomII; split; Ens.
            apply AxiomII in H; destruct H; apply Theorem132 in H8; auto. }
Qed.

Hint Resolve Theorem164 : set.


(* Definition166 : x is finite if and only if P(x)∈W. *)

Definition Finite (x: Class) : Prop := P [x] ∈ W.

Hint Unfold Finite : set.


(* Theorem167 : x is finite if and only if there is r such that r well-orders x
   and r⁻¹ well-orders x. *)

Lemma Lemma167 : forall r x f,
  KWellOrder r P[x] -> Function1_1 f -> dom(f) = x ->
  ran(f) = P[x] -> KWellOrder \{\ λ u v, Rrelation f[u] r f[v] \}\ x.
Proof.
  intros.
  unfold Function1_1 in H0; destruct H0.
  unfold KWellOrder; split; intros.
  - unfold Connect; intros; destruct H4; rewrite <- H1 in H4, H5.
    AssE u; AssE v; apply Property_Value in H4; auto.
    apply Property_Value in H5; auto; double H4; double H5.
    apply Property_ran in H8; apply Property_ran in H9.
    rewrite H2 in H8, H9; unfold KWellOrder, Connect in H.
    destruct H; clear H10; add (f[v] ∈ P[x]) H8; apply H in H8.
    clear H H9; destruct H8 as [H | [H | H]].
    + left; unfold Rrelation; apply AxiomII_P; split; try apply Theorem49; auto.
    + right; left; apply AxiomII_P; split; try apply Theorem49; auto.
    + right; right; rewrite H in H4; clear H.
      assert ([f[v],u] ∈ f⁻¹ /\ [f[v],v] ∈ f⁻¹).
      { unfold Inverse; split; apply AxiomII_P; split; auto.
        - apply Theorem49; split; apply Property_ran in H4; Ens.
        - apply Theorem49; split; apply Property_ran in H5; Ens. }
      unfold Function in H3; apply H3 in H; auto.
  - assert (ran(f|(y)) ⊂ P [x] /\ ran(f|(y)) ≠ Φ).
    { destruct H4; split.
      - unfold Included; intros; unfold Range in H6; apply AxiomII in H6.
        destruct H6, H7; unfold Restriction in H7; apply Theorem4' in H7.
        destruct H7; apply Property_ran in H7; rewrite H2 in H7; auto.
      - apply Property_NotEmpty in H5; destruct H5; double H5; apply H4 in H6.
        rewrite <- H1 in H6; apply Property_Value in H6; auto.
        double H6; apply Property_ran in H7; apply Property_NotEmpty.
        exists f[x0]; unfold Range; apply AxiomII; split; Ens.
        exists x0; unfold Restriction; apply Theorem4'; split; auto.
        unfold Cartesian; apply AxiomII_P; repeat split; Ens.
        apply Theorem19; Ens. }
    apply H in H5; unfold FirstMember in H5; destruct H5, H5.
    unfold Range in H5; apply AxiomII in H5; destruct H5, H7.
    unfold Restriction in H7; apply Theorem4' in H7; destruct H7.
    exists x1; unfold FirstMember; split; intros.
    + unfold Cartesian in H8; apply AxiomII_P in H8; apply H8.
    + clear H8; double H9; apply H4 in H9; rewrite <- H1 in H9.
      apply Property_Value in H9; auto.
      assert (f[y0] ∈ ran(f|(y))).
      { AssE [y0,f[y0]]; apply Theorem49 in H10; destruct H10.
        unfold Range; apply AxiomII; split; auto.
        exists y0; unfold Restriction; apply Theorem4'; split; auto.
        apply AxiomII_P; repeat split; try apply Theorem49; auto.
        apply Theorem19; auto. }
      apply H6 in H10; clear H6; intro; elim H10; clear H10.
      unfold Rrelation at 1 in H6; apply AxiomII_P in H6; destruct H6.
      double H7; apply Property_dom in H11; apply Property_Value in H11; auto.
      add ([x1,f[x1]] ∈ f) H7; apply H0 in H7; rewrite H7; auto.
Qed.

Theorem Theorem167 : forall x,
  Finite x <-> exists r, KWellOrder r x /\ KWellOrder (r⁻¹) x.
Proof.
  intros; split; intros.
  - unfold Finite in H.
    generalize (classic (Ensemble x)); intros; destruct H0.
    + unfold W in H; apply AxiomII in H; destruct H.
      unfold Integer in H1; destruct H1; apply Theorem107 in H1.
      apply Theorem153 in H0; apply Theorem146 in H0.
      unfold Equivalent in H0; destruct H0 as [f H0], H0, H3.
      exists (\{\ λ u v, Rrelation f[u] E f[v] \}\); split.
      * apply Lemma167; auto.
      * assert (\{\ λ u v, Rrelation f [u] E f [v] \}\⁻¹ = 
                \{\ λ u v, Rrelation f [u] E⁻¹ f [v] \}\).
        { apply AxiomI; split; intros.
          - PP H5 a b; apply AxiomII_P; apply AxiomII_P in H6; destruct H6.
            apply AxiomII_P in H7; destruct H7; split; auto.
            unfold Rrelation in H8; unfold Rrelation, Inverse.
            apply AxiomII_P; split; auto; AssE [f[b],f[a]].
            apply Theorem49 in H9; destruct H9; apply Theorem49; auto.
          - PP H5 a b; apply AxiomII_P in H6; destruct H6.
            unfold Rrelation, Inverse in H7; apply AxiomII_P in H7; destruct H7.
            apply Theorem49 in H6; destruct H6; apply AxiomII_P.
            split; try apply Theorem49; auto; apply AxiomII_P.
            split; try apply Theorem49; auto. }
        rewrite H5; apply Lemma167; auto.
    + generalize Theorem152; intros; destruct H1, H2.
      assert (x∉dom(P)). { rewrite H2; intro; apply Theorem19 in H4; tauto. }
      apply Theorem69 in H4; rewrite H4 in H; AssE μ.
      generalize Theorem39; intros; contradiction.
  - destruct H as [r H], H; unfold Finite.
    generalize Theorem113; intros; destruct H1; clear H2.
    apply Theorem107 in H1; add (KWellOrder E R) H; clear H1.
    apply Theorem99 in H; destruct H as [f H], H, H1.
    unfold Order_PXY in H1; destruct H1, H3, H4, H5; double H6.
    apply Theorem114 in H7; add (Ordinal W) H7; try apply Property_W.
    apply Theorem110 in H7; destruct H7.
    + destruct H2.
      * assert (P[x] = ran(f)).
        { apply Theorem164 in H7; clear H0; AssE ran(f).
          apply Theorem96 in H4; destruct H4; clear H8.
          assert (dom(f) ≈ ran(f)). { unfold Equivalent; exists f; auto. }
          unfold Function1_1 in H4; destruct H4.
          rewrite (Lemma96 f), (Lemma96' f) in *.
          apply AxiomV in H0; auto; rewrite H2 in *; double H0.
          apply Theorem153 in H0; apply Property_PClass in H10.
          apply Theorem147 with (z:= dom(f⁻¹)) in H0; auto; clear H2 H8.
          unfold C in H7, H10; apply AxiomII in H7; apply AxiomII in H10.
          destruct H7, H10; clear H2 H8; unfold Cardinal_Number in H7, H10.
          destruct H7, H10; unfold Ordinal_Number in H2, H8; double H2.
          double H8; unfold R in H11, H12; apply AxiomII in H11.
          apply AxiomII in H12; destruct H11, H12; clear H11 H12.
          add (Ordinal dom(f⁻¹)) H14; clear H13.
          apply Theorem110 in H14; destruct H14 as [H11 | [H11 | H11]]; auto.
          - apply H7 in H11; auto; apply Theorem146 in H0; contradiction.
          - apply H10 in H11; auto; contradiction. }
          rewrite H8; auto.
      * rewrite H2 in H7; add (W ∈ R) H7; try apply Theorem138.
        generalize (Theorem102 R W); intros; contradiction.
    + assert (W ⊂ ran(f)).
      { destruct H7; try (rewrite H7; unfold Included; auto).
        apply Theorem114 in H6; unfold Ordinal, full in H6.
        destruct H6; apply H8 in H7; auto. }
      assert (~ exists z, FirstMember z E⁻¹ W).
      { intro; destruct H9; unfold FirstMember in H9; destruct H9.
        AssE x0; apply Theorem134 in H9; AssE (PlusOne x0).
        apply H10 in H9; elim H9; clear H9 H10.
        unfold Rrelation, Inverse, E; apply AxiomII_P.
        split; try apply Theorem49; auto; apply AxiomII_P.
        split; try apply Theorem49; auto; unfold PlusOne.
        apply Theorem4; right; apply AxiomII; auto. }
      double H5; unfold Section in H10; destruct H10; clear H11.
      apply Lemma97 with (r:= r⁻¹) in H10; auto; clear H6; double H4.
      apply Theorem96 in H6; destruct H6; clear H11; destruct H6 as [H11 H6].
      clear H11; elim H9; clear H9; unfold KWellOrder in H10; destruct H10.
      assert (ran(f⁻¹|(W)) ⊂ dom(f) /\ ran(f⁻¹|(W)) ≠ Φ).
      { split; unfold Included; intros.
        - unfold Range in H11; apply AxiomII in H11; destruct H11, H12.
          unfold Restriction in H12; apply Theorem4' in H12; destruct H12.
          unfold Inverse in H12; apply AxiomII_P in H12; destruct H12.
          apply Property_dom in H14; auto.
        - assert (Φ ∈ W); try apply Theorem135; auto; double H11.
          apply H8 in H12; rewrite Lemma96' in H12.
          apply Property_Value in H12; auto; AssE [Φ,(f⁻¹)[Φ]].
          apply Theorem49 in H13; destruct H13; apply Property_NotEmpty.
          exists f⁻¹[Φ]; unfold Range; apply AxiomII; split; auto.
          exists Φ; unfold Restriction; apply Theorem4'; split; auto.
          apply AxiomII_P; repeat split; try apply Theorem49; auto.
          apply Theorem19; auto. }
      apply H10 in H11; clear H10; destruct H11; exists f[x0].
      unfold FirstMember in H10; destruct H10; split; intros.
      * clear H11; unfold Range in H10; apply AxiomII in H10; destruct H10, H11.
        unfold Restriction in H11; apply Theorem4' in H11; destruct H11.
        apply AxiomII_P in H12; destruct H12; clear H12; destruct H13.
        clear H13; apply AxiomII_P in H11; destruct H11; double H13.
        apply Property_dom in H14; apply Property_Value in H14; auto.
        add ([x0,f[x0]] ∈ f) H13; clear H14; apply H in H13.
        rewrite H13 in H12; auto.
      * double H12; apply H8 in H13; apply AxiomII in H13; destruct H13, H14.
        AssE [x1,y]; apply Theorem49 in H15; destruct H15; clear H16.
        assert (x1 ∈ ran(f⁻¹|(W))).
        { unfold Range; apply AxiomII; split; auto; exists y.
          unfold Restriction; apply Theorem4'; split.
          - unfold Inverse; apply AxiomII_P; split; try apply Theorem49; auto.
          - apply AxiomII_P; repeat split; try apply Theorem49; auto.
            apply Theorem19; auto. }
        apply H11 in H16; clear H11; unfold Range in H10; apply AxiomII in H10.
        destruct H10, H11; unfold Restriction in H11; apply Theorem4' in H11.
        destruct H11; clear H17; unfold Inverse in H11; apply AxiomII_P in H11.
        clear H10; destruct H11; apply Property_dom in H11; double H14.
        apply Property_dom in H17; add (x1∈dom(f)) H11; double H11; clear H17.
        unfold Connect in H9; apply H9 in H18; clear H9; intro.
        unfold Rrelation, Inverse, E in H9; apply AxiomII_P in H9; destruct H9.
        clear H9; apply AxiomII_P in H17; destruct H17.
        destruct H18 as [H18|[H18|H18]]; try contradiction.
        { clear H16; unfold Order_Pr in H4; destruct H11.
          assert (x1 ∈ dom(f) /\ x0 ∈ dom(f) /\ Rrelation x1 r x0).
          { repeat split; auto; unfold Rrelation, Inverse in H18.
            apply AxiomII_P in H18; unfold Rrelation; apply H18. }
          apply H4 in H19; clear H4 H9 H13 H15; unfold Rrelation, E in H19.
          apply AxiomII_P in H19; destruct H19; clear H4.
          apply Property_Value in H16; auto; add ([x1,f[x1]] ∈ f) H14.
          apply H in H14; rewrite H14 in H17; add (f[x1] ∈ f[x0]) H17.
          generalize (Theorem102 f[x0] f[x1]); intros; contradiction. }
        { rewrite H18 in H17; clear H9 H15 H16; destruct H11.
          apply Property_Value in H11; auto; add ([x1,y] ∈ f) H11.
          unfold Function in H; apply H in H11; rewrite H11 in H17.
          generalize (Theorem101 y); intros; contradiction. }
Qed.

Hint Resolve Theorem167 : set.


(* Theorem168 : If x and y are finite so is x∪y. *)

Theorem Theorem168 : forall x y,
  Finite x /\ Finite y -> Finite (x ∪ y).
Proof.
  intros; destruct H.
  apply Theorem167 in H; apply Theorem167 in H0.
  destruct H as [r H], H0 as [s H0], H, H0; apply Theorem167.
  exists (\{\ λ u v, (u∈x /\ v∈x /\ Rrelation u r v) \/
  (u∈(y~x) /\ v∈(y~x) /\ Rrelation u s v) \/ (u∈x /\ v∈(y~x)) \}\); split.
  - clear H1 H2; unfold KWellOrder in H, H0; destruct H, H0.
    unfold KWellOrder; split; intros.
    + clear H1 H2; unfold Connect in H, H0; unfold Connect; intros.
      destruct H1; apply Theorem4 in H1; apply Theorem4 in H2.
      unfold Rrelation; destruct H1, H2.
      * clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
        clear H; destruct H0 as [H | [H | H]]; try tauto.
        { left; SplitEnsP. } { right; left; SplitEnsP. }
      * clear H0; generalize (classic (v ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { left; SplitEnsP; right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * clear H0; generalize (classic (u ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { right; left; SplitEnsP.
          right; right; split; auto; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * generalize (classic (u∈x)) (classic (v∈x)); intros; destruct H3, H4.
        { clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
          clear H; destruct H0 as [H | [H | H]]; try tauto.
          - left; SplitEnsP.
          - right; left; SplitEnsP. }
        { left; SplitEnsP; right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { right; left; SplitEnsP; right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { clear H; assert (u ∈ y /\ v ∈ y); auto; apply H0 in H.
          clear H0; destruct H as [H | [H | H]]; try tauto.
          - left; SplitEnsP; right; left; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns.
          - right; left; SplitEnsP.
            right; left; unfold Setminus; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns. }
    + generalize (classic (\{ λ z, z ∈ y0 /\ z ∈ x \} = Φ)).
      clear H H0; destruct H3; intros; destruct H3.
      * assert (y0 ⊂ y).
        { unfold Included; intros; double H4.
          apply H in H5; apply Theorem4 in H5; destruct H5; auto.
          generalize (Theorem16 z); intros; elim H6; clear H6.
          rewrite <- H3; apply AxiomII; repeat split; Ens. }
        add (y0 ≠ Φ) H4; apply H2 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply AxiomII_P in H1; destruct H1.
        unfold Rrelation; destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (Theorem16 y1); intros.
          elim H5; rewrite <- H3; apply AxiomII; repeat split; Ens. }
        { destruct H4; clear H5; generalize (Theorem16 y1); intros.
          elim H5; rewrite <- H3; apply AxiomII; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈x\} ⊂ x).
        { unfold Included; intros; apply AxiomII in H4; apply H4. }
        add (\{λ z, z∈y0 /\ z∈x\} <> Φ) H4; apply H1 in H4; clear H1 H2.
        destruct H4 as [z H1]; exists z; unfold FirstMember in H1.
        destruct H1; apply AxiomII in H1; destruct H1, H4.
        unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H7.
        { assert (y1 ∈ \{λ z, z∈y0 /\ z∈x\}).
          { apply AxiomII; repeat split; Ens. }
          apply H2 in H8; intro; elim H8; clear H2 H8.
          unfold Rrelation in H9; apply AxiomII_P in H9; destruct H9.
          unfold Rrelation; destruct H8 as [H8|[H8|H8]]; try apply H8.
          - destruct H8; clear H9; unfold Setminus in H8; apply AxiomII in H8.
            destruct H8, H9; unfold Complement in H10; apply AxiomII in H10.
            destruct H10; contradiction.
          - destruct H8; clear H8; unfold Setminus in H9; apply AxiomII in H9.
            destruct H9, H9; unfold Complement in H10; apply AxiomII in H10.
            destruct H10; contradiction. }
        { intro; unfold Rrelation in H8; apply AxiomII_P in H8.
          destruct H8, H9 as [H9|[H9|H9]], H9; try contradiction.
          destruct H10; clear H8 H9 H11; unfold Setminus in H10.
          apply AxiomII in H10; destruct H10, H9; unfold Complement in H10.
          apply AxiomII in H10; destruct H10; contradiction. }
  - unfold KWellOrder; split; intros.
    + clear H1 H2; unfold KWellOrder in H, H0; destruct H, H0.
      clear H1 H2; unfold Connect in H, H0; unfold Connect; intros.
      destruct H1; apply Theorem4 in H1; apply Theorem4 in H2.
      unfold Rrelation; destruct H1, H2.
      * clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
        clear H; destruct H0 as [H | [H | H]]; try tauto.
        { right; left; unfold Inverse; SplitEnsP; SplitEnsP. }
        { left; SplitEnsP; SplitEnsP. }
      * clear H0; generalize (classic (v ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { right; left; SplitEnsP; SplitEnsP.
          right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * clear H0; generalize (classic (u ∈ x)); intros; destruct H0.
        { assert (u ∈ x /\ v ∈ x); auto; apply H in H3.
          clear H; destruct H3 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { left; SplitEnsP; SplitEnsP.
          right; right; split; auto; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
      * generalize (classic (u∈x)) (classic (v∈x)); intros; destruct H3, H4.
        { clear H0; assert (u ∈ x /\ v ∈ x); auto; apply H in H0.
          clear H; destruct H0 as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
          - left; SplitEnsP; SplitEnsP. }
        { right; left; SplitEnsP; SplitEnsP.
          right; right; split; auto; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { left; SplitEnsP; SplitEnsP.
          right; right; split; auto; unfold Setminus; apply Theorem4'.
          split; auto; unfold Complement; SplitEns. }
        { clear H; assert (u ∈ y /\ v ∈ y); auto; apply H0 in H.
          clear H0; destruct H as [H | [H | H]]; try tauto.
          - right; left; SplitEnsP; SplitEnsP.
            right; left; unfold Setminus; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns.
          - left; SplitEnsP; SplitEnsP; right; left; repeat split; auto.
            + apply Theorem4'; split; auto; SplitEns.
            + apply Theorem4'; split; auto; SplitEns. }
    + clear H H0; unfold KWellOrder in H1, H2.
      destruct H1, H2; clear H H1; destruct H3.
      generalize (classic (\{λ z, z∈y0 /\ z∈(y~x)\}=Φ)); intros; destruct H3.
      * assert (y0 ⊂ x).
        { unfold Included; intros; double H4.
          apply H in H5; apply Theorem4 in H5; destruct H5; auto.
          generalize (classic (z ∈ x)); intros; destruct H6; auto.
          generalize (Theorem16 z); intros; elim H7; clear H7.
          rewrite <- H3; apply AxiomII; repeat split; Ens.
          unfold Setminus; apply Theorem4'; split; auto.
          unfold Complement; apply AxiomII; split; Ens. }
        add (y0 ≠ Φ) H4; apply H0 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply AxiomII_P in H1; destruct H1.
        apply AxiomII_P in H4; destruct H4 as [H5 H4]; clear H5.
        unfold Rrelation, Inverse; apply AxiomII_P; split; auto.
        destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (Theorem16 z); intros.
          elim H5; rewrite <- H3; apply AxiomII; repeat split; Ens. }
        { destruct H4; clear H4; generalize (Theorem16 y1); intros.
          elim H4; rewrite <- H3; apply AxiomII; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈(y~x)\} ⊂ y).
        { unfold Included; intros; apply AxiomII in H4; destruct H4, H5.
          unfold Setminus in H6; apply Theorem4' in H6; apply H6. }
        add (\{λ z, z∈y0 /\ z∈(y~x)\} <> Φ) H4; apply H2 in H4; clear H0 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; apply AxiomII in H0; destruct H0, H4.
        unfold Setminus in H5; apply Theorem4' in H5; destruct H5.
        unfold Complement in H6; apply AxiomII in H6; clear H0; destruct H6.
        unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H8.
        { intro; unfold Rrelation in H9; apply AxiomII_P in H9; destruct H9.
          apply AxiomII_P in H10; destruct H10 as [H11 H10]; clear H11.
          destruct H10 as [H10|[H10|H10]], H10; try contradiction.
          destruct H11; clear H9 H10 H12; unfold Setminus in H11.
          apply AxiomII in H11; destruct H11, H10; unfold Complement in H11.
          apply AxiomII in H11; destruct H11; contradiction. }
        { assert (y1 ∈ \{λ z, z ∈ y0 /\ z ∈ (y ~ x)\}).
          { apply AxiomII; repeat split; Ens; apply H in H7.
            apply Theorem4 in H7; destruct H7; try contradiction.
            apply Theorem4'; split; auto; apply AxiomII; split; Ens. }
          apply H2 in H9; intro; elim H9; clear H2 H9.
          unfold Rrelation in H10; apply AxiomII_P in H10; destruct H10.
          apply AxiomII_P in H9; destruct H9 as [H10 H9]; clear H10.
          unfold Rrelation, Inverse; SplitEnsP.
          destruct H9 as [H9|[H9|H9]], H9; try contradiction; apply H10. }
Qed.

Hint Resolve Theorem168 : set.


(* Some properties about finite *)

Lemma Property_Finite : forall (A B: Class),
  Finite A -> B ⊂ A -> Finite B.
Proof.
  intros.
  apply Theorem167 in H; destruct H as [r H], H.
  apply Theorem167; exists r; split.
  - unfold KWellOrder, Connect in H; destruct H.
    unfold KWellOrder, Connect; split; intros.
    + destruct H3; apply H; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
  - unfold KWellOrder, Connect in H1; destruct H1.
    unfold KWellOrder, Connect; split; intros.
    + destruct H3; apply H1; auto.
    + destruct H3; apply H2; split; auto.
      add (B ⊂ A) H3; apply Theorem28 in H3; auto.
Qed.


Lemma Finite_Single : forall z, Ensemble z -> Finite ([z]).
Proof.
  intros.
  apply Theorem167; exists E; split.
  - unfold KWellOrder; split; intros.
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
  - unfold KWellOrder; split; intros.
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
