Require Export Axiomatic_Set_Theory.


Module Fin.

(* VIII Axiom of infinity : For some y, y is a set, Φ ∈ y and (x ∪ {x}) ∈ y
   whenever x ∈ y. *)

Axiom Axiom_Infinity : exists y, Ensemble y /\ Φ ∈ y
  /\ (forall x, x ∈ y -> (x ∪ [x]) ∈ y).

Hint Resolve Axiom_Infinity : set.


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
    apply H1; destruct H5; unfold Subclass in H0.
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
  unfold R in H; apply Axiom_Scheme in H; destruct H, H0.
  double H1; add (x ∈ y) H3; apply Theorem111 in H3.
  assert (x ∈ R). { unfold R; apply Axiom_Scheme; Ens. }
  apply Theorem123 in H4; unfold FirstMember in H4; destruct H4.
  assert (y ∈ \{ λ z, z ∈ R /\ x ≺ z \}).
  { apply Axiom_Scheme; repeat split; auto.
    unfold R; apply Axiom_Scheme; split; auto. }
  apply H5 in H6; clear H5; generalize (Theorem113); intros.
  destruct H5; clear H7; apply Theorem107 in H5.
  unfold KWellOrder in H5; destruct H5; clear H7.
  unfold Connect in H5; apply Axiom_Scheme in H4; destruct H4, H7.
  clear H8; assert (y ∈ R /\ (PlusOne x) ∈ R).
  { split; auto; unfold R; apply Axiom_Scheme; Ens. }
  apply H5 in H8; clear H5; destruct H8; try contradiction.
  destruct H5; auto; unfold Rrelation, E in H5.
  apply Axiom_SchemeP in H5; destruct H5.
  apply H2 in H8; elim H8; unfold Rrelation, Inverse.
  apply Axiom_SchemeP; split; try apply Theorem49; Ens.
  unfold E; apply Axiom_SchemeP; split; try apply Theorem49; Ens.
  unfold PlusOne; apply Theorem4; right.
  unfold Singleton; apply Axiom_Scheme; Ens.
Qed.

Hint Resolve Theorem133 : set.


(* Theorem134 : If x ∈ W, then x+1 ∈ W. *)

Theorem Theorem134 : forall x, x ∈ W -> (PlusOne x) ∈ W.
Proof.
  intros.
  unfold W in H; apply Axiom_Scheme in H; destruct H.
  unfold Integer in H0; destruct H0.
  unfold W; apply Axiom_Scheme; split.
  - unfold PlusOne; apply Axiom_Union; split; auto.
    apply Theorem42 in H; auto.
  - unfold Integer; split.
    + assert (x ∈ R). { apply Axiom_Scheme; Ens. }
      apply Lemma123 in H2; apply Axiom_Scheme in H2; apply H2.
    + unfold KWellOrder in H1; unfold KWellOrder.
      destruct H1; split; intros.
      { clear H2; unfold Connect in H1; unfold Connect; intros.
        unfold PlusOne in H2; destruct H2; apply Theorem4 in H2.
        apply Theorem4 in H3; destruct H2, H3.
        - apply H1; auto.
        - unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
          rewrite <- H4 in H2; try apply Theorem19; Ens.
          right; left; unfold Rrelation, Inverse, E.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply Axiom_Scheme in H2; destruct H2.
          rewrite <- H4 in H3; try apply Theorem19; Ens.
          left; unfold Rrelation, Inverse, E.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply Axiom_Scheme in H2; destruct H2.
          unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
          right; right; rewrite H4, H5; try apply Theorem19; Ens. }
      { destruct H3; unfold PlusOne in H3.
        generalize (classic (x ∈ y)); intro; destruct H5.
        - exists x; unfold FirstMember; split; intros; auto.
          intro; unfold Rrelation in H7; apply Axiom_SchemeP in H7.
          destruct H7; apply Axiom_SchemeP in H8; destruct H8.
          apply H3 in H6; apply Theorem4 in H6; destruct H6.
          + eapply Theorem102; eauto.
          + apply Axiom_Scheme in H6; destruct H6.
            rewrite H10 in H9; try apply Theorem19; Ens.
            apply Theorem101 in H9; auto.
        - apply H2; split; auto; unfold Subclass; intros; double H6.
          apply H3 in H6; apply Theorem4 in H6; destruct H6; auto.
          apply Axiom_Scheme in H6; destruct H6; apply Theorem19 in H.
          rewrite <- H8 in H5; auto; contradiction. }
Qed.

Hint Resolve Theorem134 : set.


(* Theorem135 :  Φ ∈ W and if x ∈ W, then Φ ≠ x+1. *)

Theorem Theorem135 : forall x, 
  Φ ∈ W /\ (x ∈ W -> Φ ≠ PlusOne x).
Proof.
  intros; split; intros.
  - unfold W; apply Axiom_Scheme; split.
    + generalize Axiom_Infinity; intros; destruct H, H, H0; Ens.
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
      unfold Singleton; apply Axiom_Scheme; split; Ens. }
    generalize (Theorem16 x); intro; contradiction.
Qed.

Hint Resolve Theorem135 : set.


(* Theorem137 : If x⊂W, Φ∈x and u+1∈x whenever u∈x, then x = w. *)

Corollary Property_W : Ordinal W.
Proof.
  unfold Ordinal; split.
  - unfold Connect; intros; destruct H; unfold W in H, H0.
    apply Axiom_Scheme in H; apply Axiom_Scheme in H0; destruct H, H0.
    unfold Integer in H1, H2; destruct H1, H2; add (Ordinal v) H1.
    apply Theorem110 in H1; destruct H1 as [H1|[H1|H1]]; try tauto.
    + left; unfold Rrelation, E; apply Axiom_SchemeP.
      split; auto; apply Theorem49; split; auto.
    + right; left; unfold Rrelation, E; apply Axiom_SchemeP.
      split; auto; apply Theorem49; split; auto.
  - unfold full; intros; unfold Subclass; intros.
    unfold W in H; apply Axiom_Scheme in H; destruct H.
    apply (Theorem132 _ z) in H1; auto.
    unfold W; apply Axiom_Scheme; Ens.
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
    - unfold Subclass; intros; unfold Setminus in H5.
      apply Theorem4' in H5; apply H5.
    - intro; apply Property_Φ in H; apply H in H5.
      symmetry in H5; contradiction. }
  destruct H3 as [y H3]; unfold FirstMember in H3; destruct H3.
  unfold Setminus in H3; apply Theorem4' in H3; destruct H3.
  unfold W in H3; apply Axiom_Scheme in H3; destruct H3; double H6.
  unfold Integer in H7; destruct H7; unfold KWellOrder in H8.
  destruct H8; assert (y ⊂ y /\ y ≠ Φ).
  { split; try unfold Subclass; auto.
    intro; rewrite H10 in H5; unfold Complement in H5.
    apply Axiom_Scheme in H5; destruct H5; contradiction. }
  apply H9 in H10; clear H9; destruct H10 as [u H9].
  assert (u ∈ x).
  { unfold FirstMember in H9; destruct H9; clear H10.
    generalize (classic (u∈x)); intros; destruct H10; auto.
    assert (u ∈ (W ~ x)).
    { unfold Setminus; apply Theorem4'; split.
      - unfold W; apply Axiom_Scheme; split; Ens.
        apply Theorem132 in H9; auto.
      - unfold Complement; apply Axiom_Scheme; Ens. }
    apply H4 in H11; elim H11; unfold Rrelation, E.
    apply Axiom_SchemeP; split; try apply Theorem49; Ens. }
  assert (y ∈ R /\ LastMember u E y).
  { split; auto; unfold R; apply Axiom_Scheme; Ens. }
  apply Theorem133 in H11; apply H1 in H10; rewrite <- H11 in H10.
  clear H11; unfold Complement in H5; apply Axiom_Scheme in H5.
  destruct H5; unfold NotIn in H11; contradiction.
Qed.

Hint Resolve Theorem137 : set.


(* Theorem138 : W ∈ R. *)

Theorem Theorem138 : W ∈ R.
Proof.
  unfold R; apply Axiom_Scheme; split; try apply Property_W.
  generalize Axiom_Infinity; intros; destruct H, H, H0.
  assert (W ∩ x = W).
  { apply Theorem137; intros.
    - unfold Subclass; intros; apply Theorem4' in H2; apply H2.
    - apply Theorem4'; split; auto; apply Theorem135; auto.
    - apply Theorem4' in H2; destruct H2; apply Theorem134 in H2.
      apply H1 in H3; apply Theorem4'; split; auto. }
  rewrite <- H2; apply Theorem33 with (x:=x); auto.
  unfold Subclass; intros; apply Theorem4' in H3; apply H3.
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
  unfold Subclass in H; apply H in H1; apply H in H3.
  unfold W in H1, H3; apply Axiom_Scheme in H1; apply Axiom_Scheme in H3.
  destruct H1, H3; unfold Integer in H5, H6; destruct H5, H6.
  add (Ordinal c) H5; clear H6 H7 H8; apply Theorem110 in H5.
  unfold LessEqual; destruct H5 as [H5|[H5|H5]]; try tauto.
  elim H4; unfold Rrelation, E; apply Axiom_SchemeP; split; auto.
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
    assert (n ∈ (En_S P)). { apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H4; generalize (Theorem16 n); contradiction.
  - assert ((En_S P) ⊂ W).
    { unfold En_S, Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    add ((En_S P) <> Φ) H3; clear H2.
    apply MiniMember_Principle in H3; destruct H3 as [h H3], H3.
    unfold En_S in H2; apply Axiom_Scheme in H2; destruct H2, H4.
    unfold W in H4; apply Axiom_Scheme in H4; clear H2; destruct H4.
    double H4; unfold Integer in H6; destruct H6.
    unfold KWellOrder in H7; destruct H7.
    assert (h ⊂ h /\ h ≠ Φ).
    { split; try (unfold Subclass; intros; auto).
      generalize (classic (h = Φ)); intros; destruct H9; auto.
      rewrite H9 in H5; contradiction. }
    apply H8 in H9; clear H8; destruct H9.
    assert (h ∈ R /\ LastMember x E h).
    { split; auto; unfold R; apply Axiom_Scheme; split; auto. }
    apply Theorem133 in H9; unfold PlusOne in H9.
    unfold FirstMember in H8; destruct H8.
    generalize (classic (x ∈ (En_S P))); intros; destruct H11.
    + apply H3 in H11; assert (x ∈ h).
      { rewrite H9; apply Theorem4; right; apply Axiom_Scheme; Ens. }
      unfold LessEqual in H11; destruct H11.
      * add (x ∈ h) H11; clear H12.
        generalize (Theorem102 h x); intros; contradiction.
      * rewrite H11 in H12; generalize (Theorem101 x); contradiction.
    + assert (x ∈ (En_S P) <-> (Ensemble x /\ x ∈ W /\ ~ (P x))).
      { unfold En_S; split; intros.
        - apply Axiom_Scheme in H12; apply H12.
        - apply Axiom_Scheme; auto. }
      apply definition_not in H12; auto; clear H11.
      apply not_and_or in H12; destruct H12.
      * absurd (Ensemble x); Ens.
      * assert (x ∈ W).
        { unfold W; apply Axiom_Scheme; split; Ens.
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

Axiom Axiom_Choice : exists c, ChoiceFunction c /\ dom(c) = μ ~ [Φ].

Hint Resolve Axiom_Choice : set.


(* Theorem140 : If x is a set there is a 1_1 function whose range is x and
   whose domain is an ordinal number. *)

Lemma Ex_Lemma140 : forall x c,
  Ensemble x -> ChoiceFunction c ->
  (exists g, forall h, Ensemble h -> g[h] = c[x ~ ran(h)]).
Proof.
  intros.
  unfold ChoiceFunction in H0; destruct H0.
  exists (\{\ λ u v, v = c [x ~ ran(u)] \}\); intros.
  apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; split; Ens; intros.
    apply Axiom_Scheme in H3; destruct H3.
    apply H5; clear H5; apply Axiom_Scheme; split; Ens.
    apply Axiom_SchemeP; split; try apply Theorem49; Ens.
    apply Axiom_Scheme in H4; destruct H4.
    rewrite Theorem70 in H5; auto.
    apply Axiom_SchemeP in H5; apply H5.
  - apply Axiom_Scheme; split; Ens; intros.
    apply Axiom_Scheme in H4; destruct H4.
    apply Axiom_SchemeP in H5; destruct H5.
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
  generalize Axiom_Choice; intros; destruct H0 as [c H0], H0.
  double H0; apply (Ex_Lemma140 x _) in H2; auto; destruct H2 as [g H2].
  generalize (Theorem128 g); intros; destruct H3 as [f H3], H3, H4.
  unfold ChoiceFunction in H0; destruct H0; exists f.
  assert (Function1_1 f).
  { unfold Function1_1; split; auto.
    unfold Function; split; intros.
    - unfold Relation; intros; PP H7 a b; Ens.
    - unfold Inverse in H7; destruct H7.
      apply Axiom_SchemeP in H7; apply Axiom_SchemeP in H8; destruct H7, H8.
      clear H7 H8; double H9; apply Property_dom in H8.
      double H10; apply Property_dom in H10.
      generalize (classic (y = z)); intros; destruct H11; auto.
      assert (Ordinal y /\ Ordinal z).
      { split; apply (Theorem111 dom(f) _); auto. }
      elim H12; intros; apply Theorem110 in H12.
      assert (Ordinal_Number y /\ Ordinal_Number z).
      { unfold Ordinal_Number, R; split; apply Axiom_Scheme; Ens. }
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
        { rewrite H7; unfold Range; apply Axiom_Scheme; split; Ens.
          exists y; unfold Restriction; apply Theorem4'; split; auto.
          unfold Cartesian; apply Axiom_SchemeP; split; Ens.
          split; auto; apply Theorem19; Ens. }
        assert ((x ~ ran(f|(z))) ∈ dom(c)).
        { generalize (classic ((x ~ ran(f|(z))) ∈ dom(c))); intros.
          destruct H16; auto; apply Theorem69 in H16; auto.
          rewrite H16 in H14; rewrite H14 in H10; AssE μ.
          generalize Theorem39; intros; contradiction. }
        apply H6 in H16; unfold Setminus at 2 in H16.
        rewrite <- H14 in H16; apply Theorem4' in H16; destruct H16.
        unfold Complement in H17; apply Axiom_Scheme in H17; destruct H17.
        unfold NotIn in H18; contradiction.
      + destruct H12; try contradiction.
        assert (f[y] ∈ ran(f|(y))).
        { rewrite <- H7; unfold Range; apply Axiom_Scheme; split; Ens.
          exists z; unfold Restriction; apply Theorem4'; split; auto.
          unfold Cartesian; apply Axiom_SchemeP; split; Ens.
          split; auto; apply Theorem19; Ens. }
        assert ((x ~ ran(f|(y))) ∈ dom(c)).
        { generalize (classic ((x ~ ran(f|(y))) ∈ dom(c))); intros.
          destruct H16; auto; apply Theorem69 in H16; auto.
          rewrite H16 in H13; rewrite H13 in H8; AssE μ.
          generalize Theorem39; intros; contradiction. }
        apply H6 in H16; unfold Setminus at 2 in H16.
        rewrite <- H13 in H16; apply Theorem4' in H16; destruct H16.
        unfold Complement in H17; apply Axiom_Scheme in H17; destruct H17.
        unfold NotIn in H18; contradiction. }
  split; auto; assert (ran(f) ⊂ x).
  { unfold Subclass; intros; unfold Range in H8; apply Axiom_Scheme in H8.
    destruct H8, H9; double H9; apply Property_dom in H10.
    assert (Ordinal_Number x0).
    { unfold Ordinal_Number, R; apply Axiom_Scheme; split; Ens.
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
    rewrite <- H10; apply Axiom_Substitution; apply Theorem33 in H8; auto. }
  assert (Ordinal_Number dom(f)).
  { unfold Ordinal_Number; apply Axiom_Scheme; split; auto. }
  split; auto; apply H5 in H10.
  assert (f|(dom(f)) = f).
  { unfold Restriction; apply Axiom_Extent; split; intros.
    - apply Axiom_Scheme in H11; apply H11.
    - apply Axiom_Scheme; repeat split; Ens; unfold Function, Relation in H3.
      double H11; apply H3 in H12; destruct H12 as [a [b H12]].
      rewrite H12 in *; clear H12; apply Axiom_SchemeP; repeat split; Ens.
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
    { apply (Theorem33 x _); auto; unfold Subclass.
      intros; apply Axiom_Scheme in H12; apply H12. }
    apply not_and_or in H13; destruct H13.
    + elim H13; apply Theorem19; auto.
    + assert ((x ~ ran(f)) ∈ ¬[Φ] <-> Ensemble (x ~ ran(f)) /\
              (x ~ ran(f)) ∉ [Φ]).
      { split; intros; try apply Axiom_Scheme; auto.
        apply Axiom_Scheme in H14; apply H14. }
      apply definition_not in H14; auto; clear H13.
      apply not_and_or in H14; destruct H14; try contradiction.
      unfold NotIn in H13; apply NNPP in H13.
      unfold Singleton in H13; apply Axiom_Scheme in H13; destruct H13.
      generalize Axiom_Infinity; intros; destruct H15, H15, H16.
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
      * destruct H; apply Axiom_SchemeP in H.
        apply Axiom_SchemeP in H0; destruct H, H0, H1, H2.
        rewrite <- H3, <- H4; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H a b; Ens.
      * unfold Inverse in H; destruct H; apply Axiom_SchemeP in H.
        apply Axiom_SchemeP in H0; destruct H, H0.
        apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
        destruct H1, H2, H3, H4; rewrite H5, H6; auto.
   - split.
     + apply Axiom_Extent; split; intros.
       * unfold Domain in H; apply Axiom_Scheme in H; destruct H, H0.
         apply Axiom_SchemeP in H0; apply H0.
       * unfold Domain; apply Axiom_Scheme; split; Ens.
         exists z; apply Axiom_SchemeP; repeat split; auto.
         apply Theorem49; split; Ens.
     + apply Axiom_Extent; split; intros.
       * unfold Range in H; apply Axiom_Scheme in H; destruct H, H0.
         apply Axiom_SchemeP in H0; destruct H0, H1.
         rewrite H2 in H1; auto.
       * unfold Range; apply Axiom_Scheme; split; Ens.
         exists z; apply Axiom_SchemeP; repeat split; auto.
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
    + unfold Domain; apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H2; destruct H2, H3.
        apply Axiom_SchemeP in H3; destruct H3.
        apply Property_ran in H4; rewrite H1 in H4; auto.
      * apply Axiom_Scheme; split; Ens.
        rewrite <- H1 in H2; unfold Range in H2.
        apply Axiom_Scheme in H2; destruct H2, H3.
        exists (x0); apply Axiom_SchemeP; split; auto.
        apply Theorem49; AssE ([x0,z]).
        apply Theorem49 in H4; destruct H4; Ens.
    + unfold Range; apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H2; destruct H2, H3.
        apply Axiom_SchemeP in H3; destruct H3.
        apply Property_dom in H4; rewrite H0 in H4; auto.
      * apply Axiom_Scheme; split; Ens.
        rewrite <- H0 in H2; unfold Domain in H2.
        apply Axiom_Scheme in H2; destruct H2, H3.
        exists (x0); apply Axiom_SchemeP; split; auto.
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
      * destruct H7; apply Axiom_SchemeP in H7; destruct H7, H9.
        apply Axiom_SchemeP in H8; destruct H8, H10; clear H7 H8.
        unfold Function in H, H0; destruct H9, H10, H, H0.
        add ([x0,x2] ∈ f1) H7; apply H11 in H7; rewrite H7 in H8.
        add ([x2,z0] ∈ f2) H8; apply H12 in H8; auto.
    + unfold Function; split; intros.
      * unfold Relation; intros; PP H7 a b; Ens.
      * unfold Inverse in H7; destruct H7; apply Axiom_SchemeP in H7.
        apply Axiom_SchemeP in H8; destruct H7, H8; clear H7 H8.
        apply Axiom_SchemeP in H9; destruct H9, H8.
        apply Axiom_SchemeP in H10; destruct H10, H10; clear H7 H9.
        unfold Function in H5, H6; destruct H8, H10, H5, H6.
        assert ([x0,x1] ∈ f2⁻¹ /\ [x0,x2] ∈ f2⁻¹).
        { unfold Inverse; split.
          - apply Axiom_SchemeP; split; auto; AssE [x1,x0].
            apply Theorem49 in H13; destruct H13.
            apply Theorem49; split; auto.
          - apply Axiom_SchemeP; split; auto; AssE [x2,x0].
            apply Theorem49 in H13; destruct H13.
            apply Theorem49; split; auto. }
        apply H12 in H13; rewrite H13 in H7; clear H8 H10 H12 H13.
        assert ([x2,y0] ∈ f1⁻¹ /\ [x2,z0] ∈ f1⁻¹).
        { unfold Inverse; split.
          - apply Axiom_SchemeP; split; auto; AssE [y0,x2].
            apply Theorem49 in H8; destruct H8.
            apply Theorem49; split; auto.
          - apply Axiom_SchemeP; split; auto; AssE [z0,x2].
            apply Theorem49 in H8; destruct H8.
            apply Theorem49; split; auto. }
        apply H11 in H8; auto.
  - rewrite <- H1, <- H4; split.
    + apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H5; destruct H5, H6.
        apply Axiom_SchemeP in H6; destruct H6, H7, H7.
        apply Property_dom in H7; auto.
      * apply Axiom_Scheme; split; Ens; apply Axiom_Scheme in H5.
        destruct H5, H6; double H6; apply Property_ran in H7.
        rewrite H3 in H7; rewrite <- H2 in H7; apply Axiom_Scheme in H7.
        destruct H7, H8; exists x1; apply Axiom_SchemeP; split; Ens.
        AssE [z0,x0]; AssE [x0,x1]; apply Theorem49 in H9.
        apply Theorem49 in H10; destruct H9, H10.
        apply Theorem49; split; auto.
    + apply Axiom_Extent; split; intros.
      * apply Axiom_Scheme in H5; destruct H5, H6.
        apply Axiom_SchemeP in H6; destruct H6, H7, H7.
        apply Property_ran in H8; auto.
      * apply Axiom_Scheme; split; Ens; apply Axiom_Scheme in H5.
        destruct H5, H6; double H6; apply Property_dom in H7.
        rewrite H2 in H7; rewrite <- H3 in H7; apply Axiom_Scheme in H7.
        destruct H7, H8; exists x1; apply Axiom_SchemeP; split; Ens.
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
  - destruct H; apply Axiom_SchemeP in H; apply Axiom_SchemeP in H0.
    destruct H, H0, H1, H2; apply Theorem146 in H1.
    apply (Theorem147 _ _ z) in H1; auto; clear H H0 H2.
    unfold C in H3, H4; apply Axiom_Scheme in H3; destruct H3.
    apply Axiom_Scheme in H4; destruct H4.
    unfold Cardinal_Number in H0, H3; destruct H0, H3.
    unfold Ordinal_Number in H0, H3.
    assert (Ordinal y /\ Ordinal z).
    { unfold R in H0, H3; apply Axiom_Scheme in H0.
      apply Axiom_Scheme in H3; destruct H0, H3; split; auto. }
    apply Theorem110 in H6; destruct H6.
    + apply Theorem146 in H1; apply H5 in H0; auto; try contradiction.
    + destruct H6; auto; apply H4 in H3; auto; try contradiction.
  - apply Axiom_Extent; split; intros; try apply Theorem19; Ens.
    apply Theorem19 in H; double H; apply Theorem140 in H0.
    destruct H0 as [f H0], H0, H1; apply Axiom_Scheme; split; auto.
    assert (KWellOrder E \{ λ x, x ≈ z /\ Ordinal x \}).
    { assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ R).
      { unfold Subclass; intros; apply Axiom_Scheme in H3.
        destruct H3, H4; apply Axiom_Scheme; split; auto. }
      apply (Lemma97 _ E _) in H3; auto.
      apply Theorem107; apply Theorem113. }
    unfold KWellOrder in H3; destruct H3 as [H4 H3]; clear H4.
    assert (\{ λ x, x ≈ z /\ Ordinal x \} ⊂ \{ λ x, x ≈ z /\ Ordinal x \}
            /\ \{ λ x, x ≈ z /\ Ordinal x \} ≠ Φ).
    { split; try unfold Subclass; auto.
      apply Property_NotEmpty; exists dom(f); apply Axiom_Scheme.
      unfold Ordinal_Number, R in H2; apply Axiom_Scheme in H2; destruct H2.
      split; auto; split; auto; unfold Equivalent; exists f; auto. }
    apply H3 in H4; destruct H4; unfold FirstMember in H4; destruct H4.
    apply Axiom_Scheme in H4; destruct H4, H6.
    exists x; apply Axiom_SchemeP.
    repeat split; try apply Theorem49; auto.
    + apply Theorem146; unfold Equivalent; Ens.
    + unfold C; apply Axiom_Scheme; split; auto.
      unfold Cardinal_Number; split; intros.
      { unfold Ordinal_Number, R; apply Axiom_Scheme; auto. }
      { unfold Less in H9; unfold R in H8.
        apply Axiom_Scheme in H8; destruct H8; intro.
        assert (y ∈ \{ λ x,x ≈ z /\ Ordinal x \}).
        { apply Axiom_Scheme; split; auto; split; auto.
          apply Theorem146 in H11; apply (Theorem147 _ x _); auto. }
        apply H5 in H12; apply H12; unfold Rrelation, E.
        apply Axiom_SchemeP; split; try apply Theorem49; auto. }
  - unfold Range; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H; destruct H, H0.
      apply Axiom_SchemeP in H0; apply H0.
    + apply Axiom_Scheme; split; Ens; exists z; apply Axiom_SchemeP.
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
  unfold P at 2 in H; apply Axiom_SchemeP in H.
  apply Theorem146; apply H.
Qed.

Hint Resolve Theorem153 : set.


(* Theorem163 : If x∈w, y∈w and x+1 ≈ y+1, then x ≈ y. *)

Ltac SplitEns := apply Axiom_Scheme; split; Ens.

Ltac SplitEnsP := apply Axiom_SchemeP; split; try apply Theorem49; Ens.

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
    apply Axiom_SchemeP in H5; apply Axiom_SchemeP in H6; destruct H5,H6.
    unfold Cartesian in H7; apply Axiom_SchemeP in H7; clear H5.
    destruct H7, H7; clear H10; destruct H8, H9.
    + unfold Setminus in H8, H9; apply Theorem4' in H8.
      apply Theorem4' in H9; destruct H8, H9; clear H10 H11.
      unfold Function in H1; apply H1 with (x:= x0); auto.
    + destruct H9.
      * unfold Setminus in H8; apply Theorem4' in H8; destruct H8.
        unfold Complement in H10; apply Axiom_Scheme in H10; clear H5.
        destruct H10; elim H10; clear H10; apply Theorem4.
        right; apply Axiom_Scheme; split; auto; intros; clear H10.
        apply Theorem49 in H6; apply Theorem55 in H9; auto.
        destruct H9; clear H10; double H8; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H8.
        apply H1 in H8; clear H10; rewrite H9 in H8.
        rewrite <- Lemma96''' in H8; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply Theorem4; right.
        unfold Singleton; apply Axiom_Scheme; split; Ens.
      * apply Theorem49 in H6; apply Theorem55 in H9; auto; destruct H9.
        rewrite H9 in H7; generalize (Theorem101 x); contradiction.
    + destruct H8.
      * unfold Setminus in H9; apply Theorem4' in H9; destruct H9.
        unfold Complement in H10; apply Axiom_Scheme in H10; clear H6.
        destruct H10; elim H10; clear H10; apply Theorem4.
        right; apply Axiom_Scheme; split; auto; intros; clear H10.
        apply Theorem49 in H5; apply Theorem55 in H8; auto.
        destruct H8; clear H10; double H9; apply Property_dom in H10.
        apply Property_Value in H10; auto; add ([x0,f[x0]] ∈ f) H9.
        apply H1 in H9; clear H10; rewrite H8 in H9.
        rewrite <- Lemma96''' in H9; auto. rewrite H8, H9; auto.
        rewrite H3; unfold PlusOne; apply Theorem4; right.
        unfold Singleton; apply Axiom_Scheme; split; Ens.
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
    apply Axiom_SchemeP in H5; apply Axiom_SchemeP in H6; destruct H5, H6.
    apply Theorem4' in H7; apply Theorem4' in H8; destruct H7, H8.
    apply Axiom_SchemeP in H7; apply Axiom_SchemeP in H8; destruct H7, H8.
    unfold Cartesian in H9; apply Axiom_SchemeP in H9; clear H7.
    destruct H9, H9; clear H13; apply Axiom_SchemeP in H10; clear H8.
    destruct H10, H10; clear H13; destruct H11, H12.
    + unfold Setminus in H11, H12; apply Theorem4' in H11.
      apply Theorem4' in H12; destruct H11, H12; clear H13 H14.
      assert ([x0,y0] ∈ f⁻¹ /\ [x0,z] ∈ f⁻¹).
      { unfold Inverse; split; apply Axiom_SchemeP; split; auto. }
      unfold Function in H4; apply H4 in H13; auto.
    + destruct H12.
      * unfold Setminus in H11; apply Theorem4' in H11; destruct H11.
        clear H13; apply Theorem49 in H8; apply Theorem55 in H12; auto.
        destruct H12; rewrite H13 in *; double H11.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],y0] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply Axiom_SchemeP; split; auto; AssE [x,f[x]].
          apply Theorem49 in H15; destruct H15; apply Theorem49; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H9; generalize (Theorem101 x); contradiction.
      * unfold Setminus in H11; apply Theorem4' in H11; destruct H11.
        unfold Complement in H13; apply Axiom_Scheme in H13; clear H7.
        destruct H13; elim H13; clear H13; apply Theorem4.
        right; apply Axiom_Scheme; split; auto; intros; clear H13.
        apply Theorem49 in H8; apply Theorem55 in H12; auto.
        destruct H12; rewrite H13 in *; clear H6 H8 H12 H13.
        assert ([y,y0] ∈ f⁻¹). { apply Axiom_SchemeP; Ens. }
        double H6; apply Property_dom in H8; apply Property_Value in H8; auto.
        add ([y,y0] ∈ f⁻¹) H8; apply H4 in H8; rewrite H8; auto.
    + destruct H11.
      * unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
        clear H13; apply Theorem49 in H7; apply Theorem55 in H11; auto.
        destruct H11; rewrite H13 in *; double H12.
        apply Property_ran in H14; apply Property_Value' in H14; auto.
        assert ([f[x],z] ∈ f⁻¹ /\ [f[x],x] ∈ f⁻¹).
        { unfold Inverse; split; apply Axiom_SchemeP; split; auto; AssE [x,f[x]].
          apply Theorem49 in H15; destruct H15; apply Theorem49; auto. }
        unfold Function in H4; apply H4 in H15; auto.
        rewrite H15 in H10; generalize (Theorem101 x); contradiction.
      * unfold Setminus in H12; apply Theorem4' in H12; destruct H12.
        unfold Complement in H13; apply Axiom_Scheme in H13; clear H8.
        destruct H13; elim H13; clear H13; apply Theorem4.
        right; apply Axiom_Scheme; split; auto; intros; clear H13.
        apply Theorem49 in H7; apply Theorem55 in H11; auto.
        destruct H11; rewrite H13 in *; clear H5 H7 H11 H13.
        assert ([y,z] ∈ f⁻¹). { apply Axiom_SchemeP; Ens. }
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
  - apply Axiom_Extent; split; intros.
    + unfold Domain in H5; apply Axiom_Scheme in H5; destruct H5, H6.
      unfold Restriction in H6; apply Theorem4' in H6; destruct H6.
      unfold Cartesian in H7; apply Axiom_SchemeP in H7; apply H7.
    + unfold Domain; apply Axiom_Scheme; split; Ens.
      assert ([x,f[x]] ∈ f).
      { apply Property_Value; auto; rewrite H2; unfold PlusOne.
        apply Theorem4; right; apply Axiom_Scheme; split; Ens. }
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
          unfold Complement; apply Axiom_Scheme; split; Ens.
          intro; apply Theorem4 in H11; destruct H11.
          - apply Axiom_Scheme in H11; destruct H11; clear H11.
            assert ([x,f[x]] ∈ μ). { apply Theorem19; Ens. }
            apply H12 in H11; clear H12; apply Theorem55 in H11; auto.
            destruct H11; rewrite H11 in H5; generalize (Theorem101 x); auto.
          - apply Axiom_Scheme in H11; destruct H11; clear H11.
            assert ([(f⁻¹)[y],y] ∈ μ).
            { apply Theorem19; Ens; exists f.
              assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply Theorem4; right.
                apply Axiom_Scheme; split; Ens. }
              rewrite Lemma96' in H11; apply Property_Value in H11; auto.
              apply Axiom_SchemeP in H11; apply H11. }
            apply H12 in H11; clear H12; apply Theorem55 in H11; auto.
            destruct H11; contradiction. }
        { split; try apply Theorem19; auto. }
  - apply Axiom_Extent; split; intros.
    + unfold Range in H5; apply Axiom_Scheme in H5; destruct H5, H6.
      unfold Restriction in H6; apply Theorem4' in H6; destruct H6.
      unfold Cartesian in H7; apply Axiom_SchemeP in H7; destruct H7.
      clear H7; destruct H8; clear H8; unfold En_g' in H6.
      apply Axiom_SchemeP in H6; destruct H6, H8 as [H8|[H8|H8]].
      * unfold Setminus in H8; apply Theorem4' in H8; destruct H8.
        unfold Complement in H9; apply Axiom_Scheme in H9; clear H6.
        destruct H9; double H8; apply Property_ran in H10; rewrite H3 in H10.
        unfold PlusOne in H10; apply Theorem4 in H10; destruct H10; auto.
        apply Axiom_Scheme in H10; clear H5; destruct H10.
        rewrite H10 in *; try apply Theorem19; Ens; clear H10.
        double H8; apply Property_ran in H10; rewrite Lemma96' in H10.
        apply Property_Value in H10; auto; apply Theorem49 in H6.
        destruct H6; clear H11; add ([y,x0] ∈ f⁻¹) H10; try SplitEnsP.
        apply H4 in H10; rewrite H10 in H9; elim H9.
        apply Theorem4; right; SplitEns.
      * apply Theorem49 in H6; apply Theorem55 in H8; auto; destruct H8.
        assert (x ∈ dom(f)).
        { rewrite H2; unfold PlusOne; apply Theorem4; right.
          unfold Singleton; apply Axiom_Scheme; split; Ens. }
        double H10; apply Property_Value in H11; auto.
        apply Property_ran in H11; rewrite H3 in H11; unfold PlusOne in H11.
        apply Theorem4 in H11; rewrite H9 in *; destruct H11; auto.
        apply Axiom_Scheme in H11; clear H5; destruct H11.
        rewrite <- H11 in H8; try apply Theorem19; Ens.
        pattern f at 2 in H8; rewrite <- Theorem61 in H8; try apply H1.
        rewrite <- Lemma96''' in H8; try rewrite Theorem61; try apply H1; auto.
        { rewrite H8 in H7; generalize (Theorem101 x); contradiction. }
        { rewrite <- Lemma96; auto. }
      * apply Theorem49 in H6; apply Theorem55 in H8; auto; destruct H8.
        rewrite H8 in H7; generalize (Theorem101 x); contradiction.
    + unfold Range; apply Axiom_Scheme; split; Ens.
      assert (z∈ran(f)). { rewrite H3; unfold PlusOne; apply Theorem4; auto. }
      generalize (classic (z = f[x])); intros; destruct H7.
      * rewrite H7 in *; clear H7.
        assert (y ∈ ran(f)).
        { rewrite H3; unfold PlusOne; apply Theorem4; right.
          unfold Singleton; apply Axiom_Scheme; split; Ens. }
        double H7; rewrite Lemma96' in H8; apply Property_Value in H8; auto.
        apply Property_ran in H8; rewrite <- Lemma96 in H8; rewrite H2 in H8.
        unfold PlusOne in H8; apply Theorem4 in H8; destruct H8.
        { exists (f⁻¹)[y]; unfold Restriction; apply Theorem4'.
          split; SplitEnsP; split; try apply Theorem19; Ens. }
        { unfold Singleton in H8; apply Axiom_Scheme in H8; destruct H8.
          rewrite <- H9 in H5; try apply Theorem19; Ens.
          rewrite <- Lemma96''' in H5; auto.
          generalize (Theorem101 y); intros; contradiction. }
      * unfold Range in H6; apply Axiom_Scheme in H6; destruct H6, H8; exists x0.
        AssE [x0,z]; unfold Restriction; apply Theorem4'; split.
        { unfold En_g'; apply Axiom_SchemeP; split; auto; left.
          unfold Setminus; apply Theorem4'; split; auto; unfold Complement.
          apply Axiom_Scheme; split; auto; intro; apply Theorem4 in H10.
          destruct H10; apply Axiom_Scheme in H10; destruct H10.
          - assert ([x,f[x]] ∈ μ); clear H10.
            { apply Theorem19; Ens; exists f; apply Property_Value; auto.
              rewrite H2; unfold PlusOne; apply Theorem4; right.
              unfold Singleton; apply Axiom_Scheme; split; Ens. }
            apply H11 in H12; clear H11; apply Theorem49 in H9.
            apply Theorem55 in H12; auto; destruct H12; tauto.
          - assert ([(f⁻¹)[y], y] ∈ μ); clear H10.
            { apply Theorem19; Ens; exists f. assert (y ∈ ran(f)).
              { rewrite H3; unfold PlusOne; apply Theorem4; right.
                apply Axiom_Scheme; split; Ens. }
              rewrite Lemma96' in H10; apply Property_Value in H10; auto.
              apply Axiom_SchemeP in H10; apply H10. }
            apply H11 in H12; clear H11; apply Theorem49 in H9.
            apply Theorem55 in H12; auto; destruct H12; rewrite H11 in H5.
            generalize (Theorem101 y); intros; contradiction. }
        { double H8; apply Property_dom in H10; rewrite H2 in H10.
          unfold PlusOne in H10; apply Theorem4 in H10; unfold Cartesian.
          apply Axiom_SchemeP; repeat split; auto; try apply Theorem19; Ens.
          destruct H10; auto; apply Axiom_Scheme in H10; destruct H10.
          rewrite H11 in H8; try apply Theorem19; Ens; double H8.
          apply Property_dom in H12; apply Property_Value in H12; auto.
          add ([x,z] ∈ f) H12; apply H1 in H12; symmetry in H12; tauto. }
Qed.

Hint Resolve Theorem163 : set.

(* Theorem164 : w ⊂ C. *)

Theorem Theorem164 : W ⊂ C.
Proof.
  intros.
  unfold Subclass; apply Mathematical_Induction.
  - assert (Φ ∈ W); try apply Theorem135; try apply W.
    unfold W in H; apply Axiom_Scheme in H; destruct H; unfold Integer in H0.
    destruct H0; unfold C; apply Axiom_Scheme.
    unfold Cardinal_Number, Ordinal_Number; repeat split; intros; auto.
    + unfold R; apply Axiom_Scheme; split; auto.
    + unfold Less in H3; generalize (Theorem16 y); contradiction.
  - intros; destruct H; double H; apply Theorem134 in H1; unfold W in H1.
    apply Axiom_Scheme in H1; unfold Integer in H1; destruct H1, H2.
    unfold C in H0; apply Axiom_Scheme in H0; destruct H0.
    unfold Cardinal_Number, Ordinal_Number in H4; destruct H4.
    unfold C; apply Axiom_Scheme; split; auto; split; intros.
    + unfold Ordinal_Number, R; apply Axiom_Scheme; split; auto.
    + unfold Less, PlusOne in H7; apply Theorem4 in H7; destruct H7.
      * assert (y ∈ W).
        { unfold W; apply Axiom_Scheme; split; Ens.
          unfold W in H; apply Axiom_Scheme in H; destruct H.
          apply Theorem132 in H7; auto. }
        intro; clear H6; double H8; apply Axiom_Scheme in H6; destruct H6.
        unfold Integer in H10; destruct H10; unfold KWellOrder in H11.
        destruct H11 as [H12 H11]; clear H12.
        generalize (classic (y = Φ)); intros; destruct H12.
        { rewrite H12 in H9; clear H12; unfold Equivalent in H9.
          destruct H9 as [f H9]; destruct H9, H12.
          assert (k ∈ (PlusOne k)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply Axiom_Scheme; split; Ens. }
          rewrite <- H12 in H14; unfold Function1_1 in H9; destruct H9.
          apply Property_Value in H14; auto; apply Property_ran in H14.
          rewrite H13 in H14; generalize (Theorem16 f[k]); contradiction. }
        { assert (y ⊂ y /\ y ≠ Φ). { split; unfold Subclass; Ens. }
          apply H11 in H13; clear H11 H12; destruct H13.
          assert (y = PlusOne x).
          { apply Theorem133; split; auto; try apply Axiom_Scheme; Ens. }
          unfold FirstMember in H11; destruct H11; clear H13.
          rewrite H12 in H9; apply Theorem163 in H9; auto.
          - assert (x ∈ R /\ x ≺ k).
            { unfold Less; split.
              - unfold R; apply Axiom_Scheme; split; Ens.
                apply Theorem111 with (x:= y); auto.
              - unfold R in H4; apply Axiom_Scheme in H4; destruct H4.
                unfold Ordinal, full in H13; destruct H13.
                apply H14 in H7; apply H7 in H11; auto. }
            destruct H13; apply H5 in H14; auto.
          - generalize Property_W; intros; unfold Ordinal, full in H13.
            destruct H13; apply H14 in H8; apply H8 in H11; auto. }
      * unfold Singleton in H7; apply Axiom_Scheme in H7; destruct H7.
        assert (k ∈ μ); try apply Theorem19; Ens; apply H8 in H9.
        clear H6 H7 H8; rewrite H9; intro; clear H9; double H.
        apply Axiom_Scheme in H7; clear H0; destruct H7; unfold Integer in H7.
        destruct H7; unfold KWellOrder in H8; destruct H8; clear H8.
        generalize (classic (k = Φ)); intros; destruct H8.
        { rewrite H8 in H6; clear H8; unfold Equivalent in H6.
          destruct H6 as [f H6]; destruct H6, H8.
          assert (Φ ∈ (PlusOne Φ)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply Axiom_Scheme; split; auto; generalize Axiom_Infinity; intros.
            destruct H11, H11, H12; Ens. }
          rewrite <- H8 in H11; unfold Function1_1 in H6; destruct H6.
          apply Property_Value in H11; auto; apply Property_ran in H11.
          rewrite H10 in H11; generalize (Theorem16 f[Φ]); contradiction. }
        { assert (k ⊂ k /\ k ≠ Φ). { split; unfold Subclass; Ens. }
          apply H9 in H10; clear H8 H9; destruct H10.
          assert (k = PlusOne x).
          { apply Theorem133; split; auto; try apply Axiom_Scheme; Ens. }
          unfold FirstMember in H8; destruct H8; clear H10.
          pattern k at 2 in H6; rewrite H9 in H6; apply Theorem163 in H6; auto.
          - apply H5 in H8; try contradiction; unfold R; apply Axiom_Scheme.
            split; Ens; apply Theorem111 with (x:= k); auto.
          - unfold W; apply Axiom_Scheme; split; Ens.
            apply Axiom_Scheme in H; destruct H; apply Theorem132 in H8; auto. }
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
    + left; unfold Rrelation; apply Axiom_SchemeP; split; try apply Theorem49; auto.
    + right; left; apply Axiom_SchemeP; split; try apply Theorem49; auto.
    + right; right; rewrite H in H4; clear H.
      assert ([f[v],u] ∈ f⁻¹ /\ [f[v],v] ∈ f⁻¹).
      { unfold Inverse; split; apply Axiom_SchemeP; split; auto.
        - apply Theorem49; split; apply Property_ran in H4; Ens.
        - apply Theorem49; split; apply Property_ran in H5; Ens. }
      unfold Function in H3; apply H3 in H; auto.
  - assert (ran(f|(y)) ⊂ P [x] /\ ran(f|(y)) ≠ Φ).
    { destruct H4; split.
      - unfold Subclass; intros; unfold Range in H6; apply Axiom_Scheme in H6.
        destruct H6, H7; unfold Restriction in H7; apply Theorem4' in H7.
        destruct H7; apply Property_ran in H7; rewrite H2 in H7; auto.
      - apply Property_NotEmpty in H5; destruct H5; double H5; apply H4 in H6.
        rewrite <- H1 in H6; apply Property_Value in H6; auto.
        double H6; apply Property_ran in H7; apply Property_NotEmpty.
        exists f[x0]; unfold Range; apply Axiom_Scheme; split; Ens.
        exists x0; unfold Restriction; apply Theorem4'; split; auto.
        unfold Cartesian; apply Axiom_SchemeP; repeat split; Ens.
        apply Theorem19; Ens. }
    apply H in H5; unfold FirstMember in H5; destruct H5, H5.
    unfold Range in H5; apply Axiom_Scheme in H5; destruct H5, H7.
    unfold Restriction in H7; apply Theorem4' in H7; destruct H7.
    exists x1; unfold FirstMember; split; intros.
    + unfold Cartesian in H8; apply Axiom_SchemeP in H8; apply H8.
    + clear H8; double H9; apply H4 in H9; rewrite <- H1 in H9.
      apply Property_Value in H9; auto.
      assert (f[y0] ∈ ran(f|(y))).
      { AssE [y0,f[y0]]; apply Theorem49 in H10; destruct H10.
        unfold Range; apply Axiom_Scheme; split; auto.
        exists y0; unfold Restriction; apply Theorem4'; split; auto.
        apply Axiom_SchemeP; repeat split; try apply Theorem49; auto.
        apply Theorem19; auto. }
      apply H6 in H10; clear H6; intro; elim H10; clear H10.
      unfold Rrelation at 1 in H6; apply Axiom_SchemeP in H6; destruct H6.
      double H7; apply Property_dom in H11; apply Property_Value in H11; auto.
      add ([x1,f[x1]] ∈ f) H7; apply H0 in H7; rewrite H7; auto.
Qed.

Theorem Theorem167 : forall x,
  Finite x <-> exists r, KWellOrder r x /\ KWellOrder (r⁻¹) x.
Proof.
  intros; split; intros.
  - unfold Finite in H.
    generalize (classic (Ensemble x)); intros; destruct H0.
    + unfold W in H; apply Axiom_Scheme in H; destruct H.
      unfold Integer in H1; destruct H1; apply Theorem107 in H1.
      apply Theorem153 in H0; apply Theorem146 in H0.
      unfold Equivalent in H0; destruct H0 as [f H0], H0, H3.
      exists (\{\ λ u v, Rrelation f[u] E f[v] \}\); split.
      * apply Lemma167; auto.
      * assert (\{\ λ u v, Rrelation f [u] E f [v] \}\⁻¹ = 
                \{\ λ u v, Rrelation f [u] E⁻¹ f [v] \}\).
        { apply Axiom_Extent; split; intros.
          - PP H5 a b; apply Axiom_SchemeP; apply Axiom_SchemeP in H6; destruct H6.
            apply Axiom_SchemeP in H7; destruct H7; split; auto.
            unfold Rrelation in H8; unfold Rrelation, Inverse.
            apply Axiom_SchemeP; split; auto; AssE [f[b],f[a]].
            apply Theorem49 in H9; destruct H9; apply Theorem49; auto.
          - PP H5 a b; apply Axiom_SchemeP in H6; destruct H6.
            unfold Rrelation, Inverse in H7; apply Axiom_SchemeP in H7; destruct H7.
            apply Theorem49 in H6; destruct H6; apply Axiom_SchemeP.
            split; try apply Theorem49; auto; apply Axiom_SchemeP.
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
          apply Axiom_Substitution in H0; auto; rewrite H2 in *; double H0.
          apply Theorem153 in H0; apply Property_PClass in H10.
          apply Theorem147 with (z:= dom(f⁻¹)) in H0; auto; clear H2 H8.
          unfold C in H7, H10; apply Axiom_Scheme in H7; apply Axiom_Scheme in H10.
          destruct H7, H10; clear H2 H8; unfold Cardinal_Number in H7, H10.
          destruct H7, H10; unfold Ordinal_Number in H2, H8; double H2.
          double H8; unfold R in H11, H12; apply Axiom_Scheme in H11.
          apply Axiom_Scheme in H12; destruct H11, H12; clear H11 H12.
          add (Ordinal dom(f⁻¹)) H14; clear H13.
          apply Theorem110 in H14; destruct H14 as [H11 | [H11 | H11]]; auto.
          - apply H7 in H11; auto; apply Theorem146 in H0; contradiction.
          - apply H10 in H11; auto; contradiction. }
          rewrite H8; auto.
      * rewrite H2 in H7; add (W ∈ R) H7; try apply Theorem138.
        generalize (Theorem102 R W); intros; contradiction.
    + assert (W ⊂ ran(f)).
      { destruct H7; try (rewrite H7; unfold Subclass; auto).
        apply Theorem114 in H6; unfold Ordinal, full in H6.
        destruct H6; apply H8 in H7; auto. }
      assert (~ exists z, FirstMember z E⁻¹ W).
      { intro; destruct H9; unfold FirstMember in H9; destruct H9.
        AssE x0; apply Theorem134 in H9; AssE (PlusOne x0).
        apply H10 in H9; elim H9; clear H9 H10.
        unfold Rrelation, Inverse, E; apply Axiom_SchemeP.
        split; try apply Theorem49; auto; apply Axiom_SchemeP.
        split; try apply Theorem49; auto; unfold PlusOne.
        apply Theorem4; right; apply Axiom_Scheme; auto. }
      double H5; unfold Section in H10; destruct H10; clear H11.
      apply Lemma97 with (r:= r⁻¹) in H10; auto; clear H6; double H4.
      apply Theorem96 in H6; destruct H6; clear H11; destruct H6 as [H11 H6].
      clear H11; elim H9; clear H9; unfold KWellOrder in H10; destruct H10.
      assert (ran(f⁻¹|(W)) ⊂ dom(f) /\ ran(f⁻¹|(W)) ≠ Φ).
      { split; unfold Subclass; intros.
        - unfold Range in H11; apply Axiom_Scheme in H11; destruct H11, H12.
          unfold Restriction in H12; apply Theorem4' in H12; destruct H12.
          unfold Inverse in H12; apply Axiom_SchemeP in H12; destruct H12.
          apply Property_dom in H14; auto.
        - assert (Φ ∈ W); try apply Theorem135; auto; double H11.
          apply H8 in H12; rewrite Lemma96' in H12.
          apply Property_Value in H12; auto; AssE [Φ,(f⁻¹)[Φ]].
          apply Theorem49 in H13; destruct H13; apply Property_NotEmpty.
          exists f⁻¹[Φ]; unfold Range; apply Axiom_Scheme; split; auto.
          exists Φ; unfold Restriction; apply Theorem4'; split; auto.
          apply Axiom_SchemeP; repeat split; try apply Theorem49; auto.
          apply Theorem19; auto. }
      apply H10 in H11; clear H10; destruct H11; exists f[x0].
      unfold FirstMember in H10; destruct H10; split; intros.
      * clear H11; unfold Range in H10; apply Axiom_Scheme in H10; destruct H10, H11.
        unfold Restriction in H11; apply Theorem4' in H11; destruct H11.
        apply Axiom_SchemeP in H12; destruct H12; clear H12; destruct H13.
        clear H13; apply Axiom_SchemeP in H11; destruct H11; double H13.
        apply Property_dom in H14; apply Property_Value in H14; auto.
        add ([x0,f[x0]] ∈ f) H13; clear H14; apply H in H13.
        rewrite H13 in H12; auto.
      * double H12; apply H8 in H13; apply Axiom_Scheme in H13; destruct H13, H14.
        AssE [x1,y]; apply Theorem49 in H15; destruct H15; clear H16.
        assert (x1 ∈ ran(f⁻¹|(W))).
        { unfold Range; apply Axiom_Scheme; split; auto; exists y.
          unfold Restriction; apply Theorem4'; split.
          - unfold Inverse; apply Axiom_SchemeP; split; try apply Theorem49; auto.
          - apply Axiom_SchemeP; repeat split; try apply Theorem49; auto.
            apply Theorem19; auto. }
        apply H11 in H16; clear H11; unfold Range in H10; apply Axiom_Scheme in H10.
        destruct H10, H11; unfold Restriction in H11; apply Theorem4' in H11.
        destruct H11; clear H17; unfold Inverse in H11; apply Axiom_SchemeP in H11.
        clear H10; destruct H11; apply Property_dom in H11; double H14.
        apply Property_dom in H17; add (x1∈dom(f)) H11; double H11; clear H17.
        unfold Connect in H9; apply H9 in H18; clear H9; intro.
        unfold Rrelation, Inverse, E in H9; apply Axiom_SchemeP in H9; destruct H9.
        clear H9; apply Axiom_SchemeP in H17; destruct H17.
        destruct H18 as [H18|[H18|H18]]; try contradiction.
        { clear H16; unfold Order_Pr in H4; destruct H11.
          assert (x1 ∈ dom(f) /\ x0 ∈ dom(f) /\ Rrelation x1 r x0).
          { repeat split; auto; unfold Rrelation, Inverse in H18.
            apply Axiom_SchemeP in H18; unfold Rrelation; apply H18. }
          apply H4 in H19; clear H4 H9 H13 H15; unfold Rrelation, E in H19.
          apply Axiom_SchemeP in H19; destruct H19; clear H4.
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
        { unfold Subclass; intros; double H4.
          apply H in H5; apply Theorem4 in H5; destruct H5; auto.
          generalize (Theorem16 z); intros; elim H6; clear H6.
          rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
        add (y0 ≠ Φ) H4; apply H2 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply Axiom_SchemeP in H1; destruct H1.
        unfold Rrelation; destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (Theorem16 y1); intros.
          elim H5; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
        { destruct H4; clear H5; generalize (Theorem16 y1); intros.
          elim H5; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈x\} ⊂ x).
        { unfold Subclass; intros; apply Axiom_Scheme in H4; apply H4. }
        add (\{λ z, z∈y0 /\ z∈x\} <> Φ) H4; apply H1 in H4; clear H1 H2.
        destruct H4 as [z H1]; exists z; unfold FirstMember in H1.
        destruct H1; apply Axiom_Scheme in H1; destruct H1, H4.
        unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H7.
        { assert (y1 ∈ \{λ z, z∈y0 /\ z∈x\}).
          { apply Axiom_Scheme; repeat split; Ens. }
          apply H2 in H8; intro; elim H8; clear H2 H8.
          unfold Rrelation in H9; apply Axiom_SchemeP in H9; destruct H9.
          unfold Rrelation; destruct H8 as [H8|[H8|H8]]; try apply H8.
          - destruct H8; clear H9; unfold Setminus in H8; apply Axiom_Scheme in H8.
            destruct H8, H9; unfold Complement in H10; apply Axiom_Scheme in H10.
            destruct H10; contradiction.
          - destruct H8; clear H8; unfold Setminus in H9; apply Axiom_Scheme in H9.
            destruct H9, H9; unfold Complement in H10; apply Axiom_Scheme in H10.
            destruct H10; contradiction. }
        { intro; unfold Rrelation in H8; apply Axiom_SchemeP in H8.
          destruct H8, H9 as [H9|[H9|H9]], H9; try contradiction.
          destruct H10; clear H8 H9 H11; unfold Setminus in H10.
          apply Axiom_Scheme in H10; destruct H10, H9; unfold Complement in H10.
          apply Axiom_Scheme in H10; destruct H10; contradiction. }
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
        { unfold Subclass; intros; double H4.
          apply H in H5; apply Theorem4 in H5; destruct H5; auto.
          generalize (classic (z ∈ x)); intros; destruct H6; auto.
          generalize (Theorem16 z); intros; elim H7; clear H7.
          rewrite <- H3; apply Axiom_Scheme; repeat split; Ens.
          unfold Setminus; apply Theorem4'; split; auto.
          unfold Complement; apply Axiom_Scheme; split; Ens. }
        add (y0 ≠ Φ) H4; apply H0 in H4; clear H0 H1 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; unfold FirstMember; split; auto; intros.
        double H2; apply H1 in H4; clear H1; intro; elim H4; clear H4.
        unfold Rrelation in H1; apply Axiom_SchemeP in H1; destruct H1.
        apply Axiom_SchemeP in H4; destruct H4 as [H5 H4]; clear H5.
        unfold Rrelation, Inverse; apply Axiom_SchemeP; split; auto.
        destruct H4 as [H4|[H4|H4]]; try apply H4.
        { destruct H4; clear H5; generalize (Theorem16 z); intros.
          elim H5; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
        { destruct H4; clear H4; generalize (Theorem16 y1); intros.
          elim H4; rewrite <- H3; apply Axiom_Scheme; repeat split; Ens. }
      * assert (\{λ z, z∈y0 /\ z∈(y~x)\} ⊂ y).
        { unfold Subclass; intros; apply Axiom_Scheme in H4; destruct H4, H5.
          unfold Setminus in H6; apply Theorem4' in H6; apply H6. }
        add (\{λ z, z∈y0 /\ z∈(y~x)\} <> Φ) H4; apply H2 in H4; clear H0 H2.
        destruct H4 as [z H0]; exists z; unfold FirstMember in H0.
        destruct H0; apply Axiom_Scheme in H0; destruct H0, H4.
        unfold Setminus in H5; apply Theorem4' in H5; destruct H5.
        unfold Complement in H6; apply Axiom_Scheme in H6; clear H0; destruct H6.
        unfold FirstMember; split; auto; intros.
        generalize (classic (y1∈x)); intros; destruct H8.
        { intro; unfold Rrelation in H9; apply Axiom_SchemeP in H9; destruct H9.
          apply Axiom_SchemeP in H10; destruct H10 as [H11 H10]; clear H11.
          destruct H10 as [H10|[H10|H10]], H10; try contradiction.
          destruct H11; clear H9 H10 H12; unfold Setminus in H11.
          apply Axiom_Scheme in H11; destruct H11, H10; unfold Complement in H11.
          apply Axiom_Scheme in H11; destruct H11; contradiction. }
        { assert (y1 ∈ \{λ z, z ∈ y0 /\ z ∈ (y ~ x)\}).
          { apply Axiom_Scheme; repeat split; Ens; apply H in H7.
            apply Theorem4 in H7; destruct H7; try contradiction.
            apply Theorem4'; split; auto; apply Axiom_Scheme; split; Ens. }
          apply H2 in H9; intro; elim H9; clear H2 H9.
          unfold Rrelation in H10; apply Axiom_SchemeP in H10; destruct H10.
          apply Axiom_SchemeP in H9; destruct H9 as [H10 H9]; clear H10.
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
      apply Axiom_Scheme in H0; apply Axiom_Scheme in H1.
      destruct H0, H1; double H.
      apply Theorem19 in H; apply Theorem19 in H4.
      apply H2 in H; apply H3 in H4.
      rewrite <- H4 in H; tauto.
    + destruct H0; apply Property_NotEmpty in H1.
      destruct H1; exists x; unfold FirstMember.
      split; auto; intros; unfold Subclass in H0.
      apply H0 in H1; apply H0 in H2.
      unfold Singleton in H1, H2; double H.
      apply Axiom_Scheme in H1; apply Axiom_Scheme in H2; destruct H1, H2.
      apply Theorem19 in H; apply Theorem19 in H3.
      apply H4 in H; apply H5 in H3.
      rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation in H6; unfold E in H6.
      apply Axiom_SchemeP in H6; destruct H6.
      generalize (Theorem101 y0); intros; contradiction.
  - unfold KWellOrder; split; intros.
    + unfold Connect; intros; destruct H0.
      unfold Singleton in H0, H1.
      apply Axiom_Scheme in H0; apply Axiom_Scheme in H1.
      destruct H0, H1; double H.
      apply Theorem19 in H; apply Theorem19 in H4.
      apply H2 in H; apply H3 in H4.
      rewrite <- H4 in H; tauto.
    + destruct H0; apply Property_NotEmpty in H1; auto.
      destruct H1; exists x; unfold FirstMember.
      split; auto; intros; unfold Subclass in H0.
      apply H0 in H1; apply H0 in H2.
      unfold Singleton in H1, H2; double H.
      apply Axiom_Scheme in H1; apply Axiom_Scheme in H2; destruct H1, H2.
      apply Theorem19 in H; apply Theorem19 in H3.
      apply H4 in H; apply H5 in H3.
      rewrite <- H3 in H; rewrite H.
      intro; unfold Rrelation in H6; unfold Inverse in H6.
      apply Axiom_SchemeP in H6; destruct H6; unfold E in H7.
      apply Axiom_SchemeP in H7; destruct H7.
      generalize (Theorem101 y0); intros; contradiction.
Qed.


(* Nest *)

Definition Nest f : Prop := forall A B, A∈f /\ B∈f -> A⊂B \/ B⊂A.

Hint Unfold Nest : Axiom_of_Choice.


(* Finite Characteristic Set *)

Definition Finite_Character f : Prop :=
  Ensemble f /\ (forall F, F∈f -> (forall z, z ⊂ F /\ Finite z -> z∈f))
  /\ (forall F, Ensemble F /\ (forall z, z ⊂ F /\ Finite z -> z∈f) -> F∈f).

Hint Unfold Finite_Character : Axiom_of_Choice.


(* Property of Finite Characteristic Set *)

Proposition Property_FinChar : forall f: Class,
  Finite_Character f /\ f ≠ Φ -> (forall A B, A ∈ f /\ B ⊂ A -> B ∈ f)
  /\ (forall φ, φ ⊂ f /\ Nest φ -> (∪φ) ∈ f).
Proof.
  intros; destruct H.
  unfold Finite_Character in H; destruct H; split; intros.
  - destruct H2; apply H1; intros; split.
    + apply Theorem33 in H3; Ens.
    + intros; destruct H4; apply H1 with (z:=z) in H2; auto.
      split; try (apply Theorem28 with (y:=B); split); auto.
  - destruct H2; apply H1.
    split; try (apply Axiom_Amalgamation; apply Theorem33 in H2); auto.
    intro A; intros; destruct H4; unfold Finite in H5.
    generalize (classic (φ = Φ)); intros; destruct H6.
    + rewrite H6 in *; clear H6; rewrite Theorem24' in H4.
      add (Φ ⊂ A) H4; try apply (Theorem26 A); apply Theorem27 in H4.
      rewrite H4 in *; clear H4; apply Property_NotEmpty in H0.
      destruct H0; generalize (Theorem26 x); intros.
      apply H1 with (z:= Φ) in H0; auto.
    + assert (Ensemble A).
      { apply Theorem33 in H2; auto; apply Axiom_Amalgamation in H2.
        apply Theorem33 in H4; auto. }
      double H7; apply Theorem153 in H8; apply Theorem146 in H8.
      assert (forall D, D ∈ \{ λ D, D ≈ P [A] /\ D ⊂ ∪ φ \} ->
              exists B, B ∈ φ /\ D ⊂ B).
      { apply Mathematical_Induction with (n:= P[A]); auto; intros.
        - apply Axiom_Scheme in H9; destruct H9, H10.
          generalize (classic (D = Φ)); intros; destruct H12.
          + rewrite H12 in *; apply Property_NotEmpty in H6; destruct H6.
            exists x; split; auto; apply Theorem26.
          + unfold Equivalent in H10; destruct H10 as [g H10], H10, H13, H10.
            apply Property_NotEmpty in H12; destruct H12; rewrite <- H13 in H12.
            apply Property_Value in H12; auto; apply Property_ran in H12.
            rewrite H14 in H12; generalize (Theorem16 g[x]); contradiction.
        - clear H H0 H2 H4 H5 H6 H7 H8 A.
          destruct H9; apply Axiom_Scheme in H10; destruct H10, H4.
          unfold Equivalent in H4; destruct H4 as [g H4], H4, H4, H6.
          assert (k ∈ (PlusOne k)).
          { unfold PlusOne; apply Theorem4; right; unfold Singleton.
            apply Axiom_Scheme; split; Ens. }
          rewrite <- H8 in H9; unfold Range in H9; apply Axiom_Scheme in H9.
          destruct H9, H10; double H10; apply Property_dom in H11.
          rewrite H6 in H11.
          assert ((D ~ [x]) ∈ \{ λ D0, D0 ≈ k /\ D0 ⊂ ∪ φ \}).
          { apply Axiom_Scheme; repeat split.
            - unfold Setminus; apply Theorem33 with (x:= D); auto.
              unfold Subclass; intros; apply Theorem4' in H12; apply H12.
            - clear H0 H1; unfold Equivalent; exists (g | (D ~ [x])).
              repeat split; unfold Relation; intros.
              + unfold Restriction in H0; apply Theorem4' in H0.
                destruct H0; PP H1 a b; Ens.
              + destruct H0; apply Theorem4' in H0; apply Theorem4' in H1.
                destruct H0 as [H0 _], H1 as [H1 _].
                apply H4 with (x:= x0); auto.
              + PP H0 a b; Ens.
              + destruct H0; apply Axiom_SchemeP in H0; apply Axiom_SchemeP in H1.
                destruct H0, H1; apply Theorem4' in H12; apply Theorem4' in H13.
                destruct H12 as [H12 _], H13 as [H13 _]; apply H7 with (x:=x0).
                split; apply Axiom_SchemeP; Ens.
              + apply Axiom_Extent; split; intros.
                * unfold Domain in H0; apply Axiom_Scheme in H0; destruct H0, H1.
                  unfold Restriction in H1; apply Theorem4' in H1; destruct H1.
                  unfold Cartesian in H12; apply Axiom_SchemeP in H12; apply H12.
                * unfold Domain; apply Axiom_Scheme; split; Ens.
                  double H0; unfold Setminus in H1; apply Theorem4' in H1.
                  destruct H1 as [H1 _]; rewrite <- H6 in H1.
                  apply Property_Value in H1; auto; exists g[z].
                  unfold Restriction; apply Theorem4'; split; auto.
                  unfold Cartesian; apply Axiom_SchemeP; repeat split; Ens.
                  AssE [z,g[z]]; apply Theorem49 in H12; destruct H12.
                  apply Theorem19; auto.
              + apply Axiom_Extent; split; intros.
                * unfold Range in H0; apply Axiom_Scheme in H0; destruct H0, H1.
                  unfold Restriction in H1; apply Theorem4' in H1.
                  destruct H1; unfold Cartesian in H12; apply Axiom_SchemeP in H12.
                  destruct H12, H13 as [H13 _]; unfold Setminus in H13.
                  apply Theorem4' in H13; destruct H13; double H1.
                  apply Property_ran in H15; rewrite H8 in H15.
                  apply Theorem4 in H15; destruct H15; auto; clear H0.
                  unfold Singleton in H15; apply Axiom_Scheme in H15; destruct H15.
                  rewrite H15 in H1; try apply Theorem19; Ens; clear H0 H12 H15.
                  assert ([k,x] ∈ g⁻¹ /\ [k,x0] ∈ g⁻¹).
                  { split; apply Axiom_SchemeP; split; try apply Theorem49; Ens. }
                  apply H7 in H0; rewrite <- H0 in H14; apply Axiom_Scheme in H14.
                  destruct H14, H14; apply Axiom_Scheme; auto.
                * unfold Range; apply Axiom_Scheme; split; Ens.
                  assert (z ∈ ran(g)). { rewrite H8; apply Theorem4; tauto. }
                  apply Axiom_Scheme in H1; destruct H1, H12; exists x0.
                  unfold Restriction; apply Theorem4'; split; auto.
                  unfold Cartesian; apply Axiom_SchemeP; split; Ens.
                  split; try apply Theorem19; auto; unfold Setminus.
                  double H12; apply Property_dom in H13; rewrite H6 in H13.
                  apply Theorem4'; split; auto; unfold Complement.
                  apply Axiom_Scheme; split; Ens; intro; apply Axiom_Scheme in H14.
                  destruct H14; rewrite H15 in H12; try apply Theorem19; Ens.
                  add ([x, z] ∈ g) H10; apply H4 in H10; rewrite H10 in H0.
                  generalize (Theorem101 z); intros; contradiction.
            - unfold Subclass, Setminus; intros; apply Theorem4' in H12.
              destruct H12; apply H5 in H12; auto. }
          apply H0 in H12; clear H0; destruct H12 as [B H12]; apply H5 in H11.
          clear H4 H6 H7 H8 H9 H10; apply Axiom_Scheme in H11; destruct H11.
          destruct H4 as [C H4], H4, H12; assert (B ∈ φ /\ C ∈ φ); auto.
          unfold Nest in H3; apply H3 in H9; destruct H9.
          + add (B ⊂ C) H8; apply Theorem28 in H8; clear H9.
            exists C; split; auto; unfold Subclass; intros.
            generalize (classic (z = x)); intros; destruct H10.
            * rewrite H10; auto.
            * apply H8; unfold Setminus; apply Theorem4'; split; auto.
              unfold Complement; apply Axiom_Scheme; split; Ens; intro.
              destruct H10; apply Axiom_Scheme in H11; apply H11.
              apply Theorem19; auto.
          + apply H9 in H4; clear H9; exists B; split; auto; unfold Subclass.
            intros; generalize (classic (z = x)); intros; destruct H10.
            * rewrite H10; auto.
            * apply H8; unfold Setminus; apply Theorem4'; split; auto.
              unfold Complement; apply Axiom_Scheme; split; Ens; intro.
              destruct H10; apply Axiom_Scheme in H11; apply H11.
              apply Theorem19; auto. }
    assert (A ∈ \{ λ D0, D0 ≈ P [A] /\ D0 ⊂ ∪ φ \}).
    { apply Axiom_Scheme; repeat split; auto. }
    apply H9 in H10; clear H9; destruct H10 as [B H10], H10.
    apply H2 in H9; apply H1 with (z:= A) in H9; auto.
Qed.


End Fin.

Export Fin.

