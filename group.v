Require Import Ensembles ssrfun Description Relations_1 IndefiniteDescription
  Classical_Prop.

Require Import base.

(* 群的第一定义 *)
Module group_first.

Record class_of {A : Type} (X : Ensemble A) := Class {
  base :> assoc_law X;
  _ : exists_solution base X;
}.

Structure type {A : Type} := Pack {sort :> Ensemble A; _ : class_of sort}.

Notation Group_Fst := type.
Notation Group_Fst_Class := class_of.

Definition is_fst_group {A: Type} (G : Ensemble A) (op: A -> A -> A) :=
  binary_operation op G /\ associative op /\ exists_solution op G /\ notEmpty G.

End group_first.

Export group_first.

(* 群的第二定义 *)
Module group_second.

Record class_of {A : Type} (X : Ensemble A) := Class {
  base :> assoc_law X;
  zero : A;
  inv : A -> A;
  _ : left_id zero base; (* 左单位元 *)
  _ : left_inverse zero inv base;  (* 左逆元 *)
}.

Structure type {A : Type} := Pack {sort :> Ensemble A; _ : class_of sort}.

Notation Group_Snd := type.
Notation Group_Snd_Class := class_of.

Definition is_snd_group {A: Type} (G : Ensemble A) (op: A -> A -> A) :=
  binary_operation op G /\ associative op /\ notEmpty G /\
  exists (zero: A), left_id zero op /\ exists (inv: A -> A), left_inverse zero inv op.

End group_second.

Export group_second.

Module group.

Record class_of {A : Type} (X : Ensemble A) := Class {
  base :> assoc_law X;
  zero : A;
  inv : A -> A;
  _ : left_id zero base; (* 左单位元 *)
  _ : right_id zero base;
  _ : left_inverse zero inv base;  (* 左逆元 *)
  _ : right_inverse zero inv base;
}.

Structure type {A : Type} := Pack {sort :> Ensemble A; _ : class_of sort}.

Notation Group := type.
Notation Group_Class := class_of.

Definition is_group {A: Type} (G : Ensemble A) (op: A -> A -> A) :=
  binary_operation op G /\ associative op /\ notEmpty G /\
  exists (zero: A), left_id zero op /\ right_id zero op /\ 
  exists (inv: A -> A), left_inverse zero inv op /\ right_inverse zero inv op.



End group.

Export group.

Arguments group.Pack {A}.
Arguments group.Class {A}.

(* 可证 *)
Lemma groupfsttosnd {A: Type} (G : Ensemble A) (op: A -> A -> A) :
  is_fst_group G op <-> is_snd_group G op.
Proof.
  split.
  - intros. destruct H, H0, H1. red in H, H, H0, H1, H2.
    split; auto. split; auto. split; auto.
    assert (exists zero : A, left_id zero op).
    { destruct H2. generalize H1 H2; intros.
      specialize (H1 x x). destruct H1, H1, H5.
      exists x1. red; intros.
      specialize (H3 x x2). destruct H3, H3, H6.
      rewrite <- H3. specialize (H0 x1 x x3).
      rewrite  H0. rewrite H5; auto. }
    destruct H3. exists x. split; auto.
    rename x into e. unfold left_inverse.
    assert (forall a, {a' : A | op a' a = e}).
    { intros. apply constructive_indefinite_description.
      specialize (H1 a e). destruct H1; auto. }
    exists (fun a => proj1_sig (X a)); eauto.  
    intros. 
    pose proof (X x). destruct (X x). simpl; auto. 
  - intros. destruct H,H0, H1, H2, H2, H3. 
    rename x into e; rename x0 into inv.
    red in H, H, H0, H2, H3. split; auto.
    split; auto. split; auto. red. intros.
Admitted.

(* 可证 *)
Lemma groupsndto {A: Type} (G : Ensemble A) (op: A -> A -> A) :
  is_snd_group G op <-> is_group G op.
Proof.
  split.
  - admit.
  - intros. destruct H, H0, H1, H2, H2, H3, H4, H4. 
    repeat split; auto. exists x; split; auto.
    exists x0; auto.
Admitted.

(* 子群 *)
Section subgroups.

Variable A : Type.

Definition grouptoclass (G : @Group A) := let: group.Pack _ imp as G' := G 
  return Group_Class G' in imp.

Definition zeroG (G : @Group A) := zero G (grouptoclass G).

Definition invG (G : @Group A) := inv G (grouptoclass G).

Definition addG (G : @Group A) := add G (grouptoclass G).

Structure sub_group (G : @Group A) := sub_Group{
  subGens :> Ensemble A;
  _ : notEmpty subGens;
  _ : Included subGens G;
  _ : is_group subGens (addG G); 
}.

(* 由子群作成的群 *)
Definition subgrouptogroup (G : @Group A) (H : sub_group G) : @Group A.
  destruct H, i0, H0. destruct H1 as [K H1]. 
  clear H1. unfold addG, grouptoclass in H,H0.
  destruct G, c, base0. simpl in *.
  Check (Assoc A subGens0 add0 H H0 K).
  Check (group.Class subGens0 (Assoc A subGens0 add0 H H0 n) zero0 inv0 l r l0 r0).
  Check (group.Pack subGens0 (group.Class subGens0 (Assoc A subGens0 add0 H H0 n) zero0 inv0 l r l0 r0)).
  exact (group.Pack subGens0 (group.Class subGens0 (Assoc A subGens0 add0 H H0 n) zero0 inv0 l r l0 r0)).
Defined.

End subgroups.


Arguments grouptoclass {A}.
Arguments zeroG {A}.
Arguments invG {A}.
Arguments addG {A}.
Arguments sub_group {A}.

Section groupTheorem.
Variable A : Type.
Variable G : @Group A.

Axiom invG_pro : forall a, In G a -> In G (invG G a).

Lemma group_assoc : forall (a b c : A), addG G a (addG G b c) = addG G (addG G a b) c.
Proof. 
  intros. 
  unfold addG; unfold grouptoclass.
  destruct G, c0, base0; simpl; auto.
Qed.
Lemma group_bin : binary_operation (addG G) G.
Proof.
  red; red. unfold addG, grouptoclass.
  destruct G, c, base0; simpl.
  red in b, b; auto.
Qed.

Lemma group_operation_pro : forall a b, invG G (addG G a (invG G b)) = addG G b (invG G a).
Admitted.

Lemma group_operation_pro1 : forall x y z, 
  (addG G (addG G x (invG G y)) (addG G y (invG G z))) = addG G x (invG G z).
Admitted.

Lemma group_operation_pro2 : forall x, (addG G x (invG G x)) = zeroG G.
Proof.
  unfold addG, invG, zeroG, grouptoclass.
  destruct G, c; simpl; auto.
Qed.


End groupTheorem.

Hint Rewrite group_assoc.

Section II_8_Theorem.

Variable A : Type.

Variable G : @Group A.

(* H是G的子群 则有如下性质 (1) 任意a b属于H 则 add a b 属于H  
                        (2) a属于H，-> inv a 属于H *)
Theorem theorem_II_8_1to (H : sub_group G) : 
  (forall a b, In H a -> In H b -> In H (addG G a b)) /\ 
  (forall a, In H a -> In H (invG G a)).
Proof.
  split.
  - destruct H, i0; simpl; auto. red in b, b. intros.
    apply (b a0 b0) in H; auto.
    destruct H, H. rewrite H1; auto.
  - intros. generalize invG_pro; intros.
    specialize (H1 A (subgrouptogroup A G H) a).
    destruct H; simpl in *; auto.
    destruct i0; simpl in *; auto. 
    destruct a0; simpl in *; auto.
    destruct a1; simpl in *; auto.
    destruct G; simpl in *; auto.
    destruct c; simpl in *; auto.
    destruct base0; simpl in *; auto.
Qed.

(* 集合X有如下性质 *)
Theorem theorem_II_8_1from (X : Ensemble A) : notEmpty X -> Included X G -> 
  (forall a b, In X a -> In X b -> In X (addG G a b)) /\ (forall a, In X a -> In X (invG G a)) ->
  is_snd_group X (addG G).
Proof.
  intros. destruct H1. split.
  red; red. intros. exists (addG G x y). split; auto.
  split. red. unfold addG, grouptoclass.
  unfold addG, grouptoclass in H1, H2; simpl.
  destruct G, c, base0; simpl; auto.  
  split; auto. unfold addG, grouptoclass.
  destruct G, c; simpl; auto.
  exists zero0; split; auto. exists inv0; auto.
Qed.

Lemma inference_II_8' (H : sub_group G) : In H (zeroG G) /\ zeroG (subgrouptogroup A G H) = zeroG G.
Proof.
  split.
  - generalize (theorem_II_8_1to H); intros. destruct H0.
    destruct H; simpl. destruct n; simpl.
    simpl in H1, H0. generalize i1; intros. apply H1 in i1.
    apply (H0 x (invG G x)) in i2; auto. 
    rewrite group_operation_pro2 in i2; auto.
  - unfold subgrouptogroup. destruct H; simpl in *; auto.
    destruct i0; simpl in *; auto. destruct a; simpl in *; auto.
    destruct a0; simpl in *; auto. destruct G; simpl in *; auto.
    destruct c; simpl in *; auto. destruct base0; simpl in *; auto.
Qed.

Lemma inference_II_8'' (H : sub_group G) : forall a, In H a -> invG (subgrouptogroup A G H) a = invG G a.
Proof.
  intros. 
  unfold subgrouptogroup. destruct H; simpl in *; auto.
  destruct i0; simpl in *; auto.
  destruct a0; simpl in *; auto.
  destruct a1; simpl in *; auto.
  destruct G; simpl in *; auto.
  destruct c; simpl in *; auto.
  destruct base0; simpl in *; auto.
Qed.

(* 子群的充要条件 可证 *)
Theorem theorem_II_8_2to (H : sub_group G) : forall a b, In H a -> In H b -> In H (addG G a (invG G b)).
Admitted.

(* 可证 *)
Theorem theorem_II_8_2from (X : Ensemble A) : notEmpty X -> Included X G -> 
  (forall a b, In X a -> In X b -> In X (addG G a (invG G b))) ->
  is_snd_group X (addG G).
Admitted.

End II_8_Theorem.

Section coset.

Inductive right_coset {A : Type} (G : @Group A) (H : sub_group G) (a : A) : Ensemble A :=
  right_coset_intro : forall b, In H (addG G a (invG G b)) -> In (right_coset G H a) b.

Inductive left_coset {A : Type} (G : @Group A) (H : sub_group G) (a : A) : Ensemble A :=
  left_coset_intro : forall b,  In H (addG G (invG G b) a ) -> In (left_coset G H a) b.
End coset.

Section normal_subgroups.

Variable A : Type.

Structure normal_subgroup (G : @Group A) := normal_SubGroup{
  normalSubGens :> sub_group G ;
  _ : forall a, Same_set (right_coset G normalSubGens a) (left_coset G normalSubGens a);
}.

End normal_subgroups.

Arguments normal_subgroup {A}.
Arguments normal_SubGroup {A}.


Section quotient_groups.

(* 陪集 *)
Variable A : Type.

(* G是一个群，H是G的不变子群，给一个元素repr；返回其一个陪集类型 *)
Structure coset (G: @Group A) (H: normal_subgroup G) : Type := makeCoset{
  repr : A ;
}.

(* 提取出代表元 *)
Definition coset_to_repr G H (a : coset G H) : A.
  destruct a as [a].
  exact a.
Defined.

(* 元间的关系 即 a与b等价 <-> a*b逆 属于H  *)
Definition right_coset_element_relation (G: @Group A) (H: sub_group G) (a b : A) :=
  In H (addG G a (invG G b)).


(* 该关系是一个等价关系 *)
Lemma right_coset_relation_is_equivalence (G: @Group A) (H: sub_group G) :
  Equivalence (right_coset_element_relation G H).
Proof.
  split.
  - red. red. intros. generalize inference_II_8'; intros.
    specialize (H0 A G H). destruct H0. unfold addG, invG, grouptoclass.
    destruct G, c; simpl. red in r0. remember r0; clear Heqe.
    specialize (r0 x). rewrite r0; auto.
  - red. unfold right_coset_element_relation.
    intros.
    generalize theorem_II_8_1to; intros. specialize (H2 A G H).
    destruct H2. 
    apply (H2 (addG G x (invG G y)) (addG G y (invG G z))) in H0; auto.
    rewrite group_operation_pro1 in H0; auto.
  - red. unfold right_coset_element_relation. intros.
    generalize theorem_II_8_1to; intro H2. specialize (H2 A G H).
    destruct H2. apply H2 in H0.
    rewrite group_operation_pro in H0; auto.
Qed.

(* coset 相等 *)
Definition coset_eq (G: @Group A) (H: normal_subgroup G) (a b : coset G H) :=
  exists c, In (right_coset G H c) (coset_to_repr G H a) /\
            In (right_coset G H c) (coset_to_repr G H b).


(* coest相等的外延公理 *)
Axiom coset_eq_axiom : forall (G: @Group A) (H: normal_subgroup G) (a b : coset G H),
  a = b <-> coset_eq G H a b.

(* 两个陪集相等 那么他们的代表元等价 即 addG a invG b 属于 H *)
Lemma coset_pro1 (G: @Group A) (H: normal_subgroup G) (a b : coset G H) : 
  coset_eq G H a b <-> In H (addG G (coset_to_repr G H a) (invG G (coset_to_repr G H b))).
Proof.
  split.
  - intros. destruct H0, H0.
    generalize right_coset_relation_is_equivalence; intros.
    specialize (H2 G H). destruct H2. 
    red in H2, H3, H4. unfold right_coset_element_relation in H3, H4.
    destruct a, b; simpl.
    simpl in H0, H1. destruct H0, H1.
    apply H4 in H0. apply (H3 b x b0) in H0; auto.
  - destruct a, b; simpl. intros.
    red. exists repr0. split.
    + apply right_coset_intro; simpl. 
      rewrite group_operation_pro2. generalize (inference_II_8' A G H); intros.
      tauto.
    + apply right_coset_intro in H0. auto.
Qed.

(* 给一个a 返回包含a的陪集 *)
Definition quotient_mapping (G: @Group A) (H: normal_subgroup G) (a: A) : coset G H.
  exact (makeCoset G H a).
Defined.


Definition quotient_z G H : coset G H.
    apply (makeCoset _ _ (zeroG G)).
Defined.


Definition quotient_add G H : coset G H -> coset G H -> coset G H.
    intros a b.
    (* this is dumb,but basically we just don't care about the coset repr *)
    destruct a as [a].
    destruct b as [b].
    exact (makeCoset _ _ ((addG G) a b)).
Defined.


Definition quotient_inv G H: coset G H -> coset G H.
  intros a.
  destruct a as [a].
  exact (makeCoset _ _ ((invG G) a)).
Defined.


Inductive quotient_ens G H : Ensemble (coset G H) :=
  quotient_ens_intro : forall a, In G a -> In (quotient_ens G H) (makeCoset G H a).

Lemma quotient_pro G H : binary_operation (quotient_add G H) (quotient_ens G H).
Proof.
  red; red; intros.
  destruct H0, H1.
  destruct G; simpl. 
  unfold addG, grouptoclass. 
  destruct c, base0. red in b, b.
  apply (b a a0) in H0; auto.
  destruct H0, H0.
  exists (makeCoset (Pack sort0 (Class sort0 (Assoc A sort0 add0 b a1 n) zero0 inv0 l r l0 r0)) H x).
  split. apply quotient_ens_intro; auto.
  simpl. rewrite H2; auto.
Qed.

Definition quotient_assoc_law (G: @Group A) (H: normal_subgroup G) : assoc_law (quotient_ens G H).
  apply (base.Assoc _ _ (quotient_add G H)).
  generalize group_bin; intros. 
  specialize (H0 A G).
  red; red. intros. destruct H1, H2.
  red in H0, H0. apply (H0 a a0) in H1; auto.
  destruct H1, H1.
  exists (makeCoset G H x).
  split; auto. apply quotient_ens_intro; auto.
  unfold quotient_add; auto. rewrite H3; auto.
  red. intros [x] [y] [z].
  unfold quotient_add. autorewrite with core; auto.
  red. destruct G, c, base0, n; simpl.
  exists (makeCoset (Pack sort0 (Class sort0 (Assoc A sort0 add0 b a (ex_intro [eta In sort0] x i)) zero0 inv0 l r l0 r0)) H x).
  apply quotient_ens_intro; auto.
Defined.


(* 可证 *)
Definition quotient_Group_Class (G: @Group A) (H:  normal_subgroup G) : Group_Class (quotient_ens G H).
  apply (group.Class _ (quotient_assoc_law G H) (quotient_z G H) (quotient_inv G H)).
  - red; intros. unfold quotient_z. destruct x; simpl.
    unfold addG, zeroG, grouptoclass.
    destruct G, c; simpl; auto. red in l.
    pose proof (l repr0). rewrite H0; auto.
  - red; intros. unfold quotient_z. destruct x; simpl.
    unfold addG, zeroG, grouptoclass.
    destruct G, c; simpl; auto. red in r.
    pose proof (r repr0). rewrite H0; auto.
  - red; intros. unfold quotient_z, quotient_inv. destruct x; simpl.
    unfold addG, invG, zeroG, grouptoclass; simpl; auto.
    destruct G, c; simpl; auto.
    red in l0. pose proof (l0 repr0).
    rewrite H0; auto.
  - red; intros. unfold quotient_z, quotient_inv. destruct x; simpl.
    unfold addG, invG, zeroG, grouptoclass; simpl; auto.
    destruct G, c; simpl; auto.
    red in r0. pose proof (r0 repr0).
    rewrite H0; auto.
Defined.

(* 商群  可证 *)
Definition quotient_group (G: @Group A) (H: normal_subgroup G) : @Group (coset G H).
    apply (group.Pack _ (quotient_Group_Class G H)).
Defined.


End quotient_groups.

Arguments coset {A}.
Arguments makeCoset {A}.

(* 加群 *)
Module group_add.

Record class_of {A : Type} (X : Ensemble A) := Class {
  base :> Group_Class X;
  _ : commutative base;
}.

Structure type {A : Type} := Pack {sort :> Ensemble A; _ : class_of sort}.

Notation Group_Add := type.
Notation Group_Add_Class := class_of.

Definition is_add_group {A: Type} (G : Ensemble A) (op: A -> A -> A) :=
  is_group G op /\ commutative op.

End group_add.

Export group_add.













