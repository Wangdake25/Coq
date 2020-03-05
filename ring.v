Require Import Ensembles ssrfun Description Relations_1 IndefiniteDescription
  Classical_Prop.

Require Import base group.

(*环*)
Module ring.

Record class_of {A : Type} (X : Ensemble A) := Class{
  base :> Group_Add_Class X;
  mul : A -> A -> A;
  _ : binary_operation mul X;
  _ : associative mul;
  _ : left_distributive mul base;
  _ : right_distributive mul base;
}.

Structure type {A : Type} := Pack {sort :> Ensemble A; _ : class_of sort}.

Notation Ring := type.
Notation Ring_Class := class_of.

Definition is_ring {A: Type} (G : Ensemble A) (add mul: A -> A -> A) :=
  is_add_group G add  /\ binary_operation mul G /\ associative mul /\ 
  left_distributive mul add /\ right_distributive mul add.

End ring.

Export ring.

Arguments ring.Pack {A}.
Arguments ring.Class {A}.

(*交换环*)
Module commutative_ring.

Record class_of {A : Type} (X : Ensemble A) := Class{
  base :> Ring_Class X;
  _ : commutative base; 
}.

Structure type {A : Type} := Pack {sort :> Ensemble A; _ : class_of sort}.

Notation Commu_Ring := type.
Notation Commu_Ring_Class := class_of.

Definition is_commu_ring {A: Type} (G : Ensemble A) (add mul: A -> A -> A) :=
  is_ring G add mul /\ commutative mul.

(* 给一个环，返回一个交换环 *)

(* Definition ring_to_commuring {A : Type} (R : @Ring A) (H : commutative (ring.toclass R)) : Commu_Ring :=
  Pack A R (Class A R (ring.toclass R) H). *)

End commutative_ring.

Export commutative_ring.



Section subring.

Variable A : Type.

Variable R : @Ring A.

Check mul R.

Definition ringtoclass := let: ring.Pack ens imp as R' := R 
  return Ring_Class R' in imp.

Check ringtoclass.

Check mul R ringtoclass.

Check @add A R ringtoclass.

Check @inv A R ringtoclass.

Check @zero A R ringtoclass.

Definition mulR := mul R ringtoclass.

Definition addR := @add A R ringtoclass.

Definition invR := @inv A R ringtoclass.

Definition zeroR := @zero A R ringtoclass.

Lemma ring_inv : forall a, addR a (invR a) = zeroR.
Proof.
  unfold addR, invR, zeroR, ringtoclass.
  destruct R, c, base0, base0; simpl; auto.
Qed.

Lemma ring_zero_pro : forall a, mulR a zeroR = zeroR /\ mulR zeroR a = zeroR.
Proof.
  intros. unfold mulR, zeroR, ringtoclass.
  destruct R, c, base0, base0, base0; simpl; auto.
  - split. 
    assert (mul0 a (add0 a (inv0 a)) = add0 (mul0 a a) (inv0 (mul0 a a))).
    { red in r. specialize (r a a (inv0 a)).
      assert ((group_add.Class A sort0 
      (group.Class sort0 (Assoc A sort0 add0 b0 a1 n) 
      zero0 inv0 l0 r0 l1 r1) c) a (inv0 a) = add0 a (inv0 a)).
      { auto. }
      rewrite H in r.
      assert ((group_add.Class A sort0 (group.Class sort0 (Assoc A sort0 add0 b0 a1 n) zero0 inv0 l0 r0 l1 r1) c)
      (mul0 a a) (mul0 a (inv0 a)) = add0 (mul0 a a) (mul0 a (inv0 a))).
      { auto. }
      rewrite H0 in r. clear H H0.
      
Admitted.

Lemma ring_bin_add : binary_operation addR R.
Proof.
  red; red. unfold addR, ringtoclass.
  destruct R, c, base0, base0, base0; simpl.
  red in b, b; auto.
Qed.

Lemma ring_bin_mul : binary_operation mulR R.
Proof.
  red; red. unfold mulR, ringtoclass.
  destruct R, c; simpl.
  red in b, b; auto.
Qed.



(* 子环 *)
Structure sub_ring := sub_Ring {
  subRens :> Ensemble A;
  _ : notEmpty subRens;
  _ : Included subRens R;
  _ : is_ring subRens addR mulR; 
  }.

(* 理想子环 *)
Structure ideal := makeIdeal{
  idealens :> Ensemble A;
  _ : Included idealens R;
  _ : notEmpty idealens;
  _ : forall a b, In idealens a -> In idealens b -> In idealens (addR a (invR b));
  _ : forall a r, In idealens a -> In R r -> In idealens (mulR a r) /\ In idealens (mulR r a);
  }.

Definition is_ideal (X : Ensemble A) := notEmpty X /\ Included X R /\ 
  (forall a b, In X a -> In X b -> In X (addR a (invR b))) /\
  (forall a r, In X a -> In R r -> In X (mulR a r) /\ In X (mulR r a)).

End subring.

Arguments mulR {A} _.
Arguments addR {A} _.
Arguments invR {A} _.
Arguments zeroR {A} _.
Arguments ringtoclass {A} _.
Arguments ideal {A}.
Arguments is_ideal {A}.
Arguments makeIdeal {A}.

Section III_7_Theorem.

(* 一个理想是一个加群 *)
Variable A : Type.

Variable R : @Ring A.

Variable I : ideal R.

(* 理想子环对于加法来说是一个加群 *)
Lemma ideal_is_addgroup : is_add_group I (addR R).
Proof.
  generalize theorem_II_8_2from; intros. specialize (H A).
  unfold addR, ringtoclass.
  destruct I. 
  unfold addR in i0; unfold invR in i0 ;unfold ringtoclass in i0.
  unfold mulR in a; unfold ringtoclass in a.
  destruct R, c, base0; simpl.
  specialize (H (group.Pack sort0 base0) idealens0).
  apply H in n; auto.
  unfold addG in n; unfold grouptoclass in n.
  split; auto.
  apply groupsndto in n; auto.
Qed.

End III_7_Theorem.


Section III_5_Theorem.

(* 两个环同态 *)

Structure homomorphism_ring {A : Type} {B : Type} (R1 : @Ring A) (R2 : @Ring B) := 
  makeHomomorphismring{
  h :> A -> B ;
  _ : homomorphism R1 R2 (addR R1) (addR R2) h;
  _ : homomorphism R1 R2 (mulR R1) (mulR R2) h;
    }.

Structure r_kernel {A B : Type} (R1 : @Ring A) (R2 : @Ring B) (h : homomorphism_ring R1 R2) := 
  makeRKernel{
  r_kerens :> Ensemble A;
  _ : notEmpty r_kerens;
  _ : Included r_kerens R1;
  _ : forall a, In r_kerens a <-> h a = zeroR R2;
    }.


Section Th1.
Variable A B : Type.

Variable R : @Ring A.

Variable X : Ensemble B.

Variable Xadd Xmul : B -> B -> B.

Hypothesis Xproperty1 : notEmpty X.

Hypothesis Xproperty2 : binary_operation Xadd X /\ binary_operation Xmul X.

Check addR.

(* R 是一个环，X是一个非空集合，存在一个h  使得R和X对于两种运算来说同态，那么X也是一个环 *)
Theorem Theorem1 : (exists h : A -> B, homomorphism R X (addR R) Xadd h /\ 
  homomorphism R X (mulR R) Xmul h) -> is_ring X Xadd Xmul.
Proof.
  intros.
  destruct H, H, Xproperty2.
  split; auto. 
Admitted.

End Th1.

Section Th2.

Variable A B : Type.

Variable R1 : @Ring A.

Variable R2 : @Ring B.

Hypothesis h : homomorphism_ring R1 R2.

(* R1的零元的像是R2的零元 *)
Theorem Theorem2_1 : h (zeroR R1) = zeroR R2.
Admitted.

(* a的逆元的像是像的逆元 *)
Theorem Theorem2_2 : forall a,  h ((invR R1) a) = invR R2 (h a).
Admitted.

(* R1是交换环 则R2也是交换环 *)
Definition ring_iscomm {B : Type} (Y : @Ring B) := commutative (mul Y (ringtoclass Y)).

(* R2也是交换环 *)
Theorem Theorem2_3 : ring_iscomm R1 -> ring_iscomm R2.
Admitted.

(* R1有单位元 *)
Theorem Theorem2_4 : exists e, left_id e (ringtoclass R1) /\ right_id e (ringtoclass R1) ->
  left_id (h e) (ringtoclass R2) /\ right_id (h e) (ringtoclass R2).
Admitted.

End Th2.

End III_5_Theorem.

(* 商环  剩余类*)
Section residueclass.

Variable A : Type.

(* 返回R对于加法来说作成的群 *)
Definition ring_to_group (R : @Ring A) : @Group A := group.Pack R (ringtoclass R).

(* R对于加法来说作成的群 该加法满足交换律  *)
Lemma ring_to_group_iscomm (R : @Ring A) : commutative (addG (ring_to_group R)).
Proof.
  unfold addG, ring_to_group, grouptoclass, ringtoclass.
  destruct R, c, base0; simpl; auto.
Qed.

(*  理想是R作成的加法群的子群 *)
Definition ideal_to_subgroup (R : @Ring A) (I : ideal R) : sub_group (ring_to_group R).
  generalize ideal_is_addgroup; intros.
  specialize (H A R I).
  destruct H. destruct I.
  Check sub_Group A (ring_to_group R) idealens0 n i H.
  exact (sub_Group A (ring_to_group R) idealens0 n i H).
Defined.

Definition ideal_to_subpro (R : @Ring A) (I : ideal R) : 
  forall a : A, Same_set (right_coset (ring_to_group R) (ideal_to_subgroup R I) a)
                 (left_coset (ring_to_group R) (ideal_to_subgroup R I) a).
  split; intros. red. intros. destruct H.
  apply left_coset_intro; auto.
  generalize ring_to_group_iscomm; intros.
  red in H0. specialize (H0 R a (invG (ring_to_group R) b)). 
  rewrite <- H0; auto.
  red; intros. destruct H. apply right_coset_intro; auto.
  generalize ring_to_group_iscomm; intros.
  red in H0. specialize (H0 R a (invG (ring_to_group R) b)).
  rewrite H0; auto.
Defined.

(* I作成R作成的加法群的一个不变子群 *)
Definition ideal_to_normal_subgroup (R : @Ring A) (I : ideal R) : 
  normal_subgroup (ring_to_group R).
  generalize ideal_to_subpro; intros.
  specialize (H R I).
  exact (normal_SubGroup (ring_to_group R) (ideal_to_subgroup R I) H).
Defined.


(* a属于理想，则a属于理想作成的子群 *)
Lemma ideal_to_subgroup_pro (R : @Ring A) (I : ideal R) : 
  forall a, In I a -> In (ideal_to_subgroup R I) a.
Proof.
  intros. unfold ideal_to_subgroup; simpl.
  destruct (ideal_is_addgroup A R I); simpl; auto.
  destruct I; simpl; auto.
Qed.
(* a属于理想做成的子群，则a属于该子群形成的不变子群 *)
Lemma ideal_to_subgroup_pro1 (R : @Ring A) (I : ideal R) : 
  forall a, In (ideal_to_subgroup R I) a -> In (ideal_to_normal_subgroup R I) a.
Proof.
  intros. unfold ideal_to_subgroup in H. 
  destruct (ideal_is_addgroup A R I) in H; simpl; auto.
Qed.   

Lemma ideal_to_nor_pro (R : @Ring A) (I : ideal R) : 
  forall a, In I a -> In (ideal_to_normal_subgroup R I) a.
Proof.
  intros.
  apply ideal_to_subgroup_pro in H; apply ideal_to_subgroup_pro1 in H; auto.
Qed.


Definition residue_class (R: @Ring A) (I : ideal R) : Type := 
  coset (ring_to_group R) (ideal_to_normal_subgroup R I).


(* 提取出代表元 *)
Definition residue_to_repr R I (a : residue_class R I) : A.
  red in a.
  Check coset_to_repr.
  exact (coset_to_repr A (ring_to_group R) (ideal_to_normal_subgroup R I) a).
Defined.

(* 给一个a 返回包含a的陪集 *)
Definition residue_mapping (R: @Ring A) (I : ideal R) (a: A) : residue_class R I.
  red.
  Check makeCoset (ring_to_group R) (ideal_to_normal_subgroup R I) a. 
  exact (makeCoset (ring_to_group R) (ideal_to_normal_subgroup R I) a).
Defined.

(* 由e构成的陪集 *)
Definition residue_z R I : residue_class R I.
    apply (makeCoset _ _ (zeroR R)).
Defined.


(* 陪集的加法 *)
Definition residue_add R I : residue_class R I -> residue_class R I -> residue_class R I.
    intros a b.
    destruct a as [a].
    destruct b as [b].
    exact (makeCoset _ _ ((addR R) a b)).
Defined.

Definition residue_mul R I : residue_class R I -> residue_class R I -> residue_class R I.
    intros a b.
    destruct a as [a].
    destruct b as [b].
    exact (makeCoset _ _ ((mulR R) a b)).
Defined.

(* 剩余类集合 *)
Inductive residue_ens R I : Ensemble (residue_class R I) :=
  residue_ens_intro : forall a, In R a -> In (residue_ens R I) (makeCoset _ _ a).

(* 剩余类上的加法是一个二元运算 *)
Lemma residue_pro R I : binary_operation (residue_add R I) (residue_ens R I).
Proof.
  unfold binary_operation, operation.
  intros. destruct H, H0. 
  destruct R, c, base0, base0, base0; simpl.
  red in b0, b0. apply (b0 a a0) in H; auto.
  destruct H, H.
  exists (makeCoset (ring_to_group
  (ring.Pack sort0
           (ring.Class sort0
              (group_add.Class A sort0
                 (group.Class sort0 (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1)
                 c) mul0 b a1 l r))) (ideal_to_normal_subgroup (ring.Pack sort0
           (ring.Class sort0
              (group_add.Class A sort0
                 (group.Class sort0 (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1)
                 c) mul0 b a1 l r)) I) x).
  split; simpl.
  apply residue_ens_intro; auto.
  simpl. 
  unfold addR, ringtoclass; simpl.
  rewrite H1; auto.
Qed.

Lemma residue_pro1 R I : binary_operation (residue_mul R I) (residue_ens R I).
Proof.
  unfold binary_operation, operation.
  intros. destruct H, H0. 
  destruct R, c; simpl.
  red in b, b. apply (b a a0) in H; auto.
  destruct H, H.
  exists (makeCoset (ring_to_group
  (ring.Pack sort0 (ring.Class sort0 base0 mul0 b a1 l r))) (ideal_to_normal_subgroup 
  (ring.Pack sort0 (ring.Class sort0 base0 mul0 b a1 l r)) I) x).
  split; simpl.
  apply residue_ens_intro; auto.
  unfold mulR, ringtoclass; simpl.
  rewrite H1; auto.
Qed.

Lemma residue_pro2 R I : notEmpty (residue_ens R I).
Proof.
  unfold notEmpty.
  destruct R, c, base0, base0, base0, n; simpl.
  exists (makeCoset ( ring_to_group (ring.Pack sort0
            (ring.Class sort0
               (group_add.Class A sort0
                  (group.Class sort0 (Assoc A sort0 add0 b0 a0 (ex_intro [eta In sort0] x i)) zero0 inv0 l0 r0 l1 r1) c) mul0 b a
               l r))) (ideal_to_normal_subgroup (ring.Pack sort0
            (ring.Class sort0
               (group_add.Class A sort0
                  (group.Class sort0 (Assoc A sort0 add0 b0 a0 (ex_intro [eta In sort0] x i)) zero0 inv0 l0 r0 l1 r1) c) mul0 b a
               l r)) I) x).
  apply residue_ens_intro; auto.
Qed.

End residueclass.

Arguments residue_class {A}.
Arguments residue_mapping {A}.
Arguments residue_z {A}.
Arguments residue_add {A}.
Arguments residue_mul {A}.
Arguments residue_ens {A}.
Arguments residue_to_repr {A}.

Section III_8_Theorem.

Variable A : Type.

(* 假定R是一个环，I是他的一个理想，R/ 是模I的剩余类作成的集合，那么R与R/同态 *)
(* 即存在一个h，关于加法同态同时关于乘法同态 *)
Theorem III_8_1' (R : @Ring A) (I : ideal R) : 
  exists h, homomorphism R (residue_ens R I) (addR R) (residue_add R I) h /\
  homomorphism R (residue_ens R I) (mulR R) (residue_mul R I) h.
Proof.
  exists (residue_mapping R I). split.
  - split. unfold addR, ringtoclass.
    destruct R, c, base0, base0, base0; simpl; auto.
    split. apply (residue_pro A R I).
    split. red. split. red. intros. 
    exists (makeCoset (ring_to_group A R) (ideal_to_normal_subgroup A R I) x); split; auto.
    apply residue_ens_intro; auto.
    intros [b]. unfold residue_mapping.
    exists b; auto.
    intros.
    unfold residue_add, addR, residue_mapping; auto.
  - split. unfold mulR, ringtoclass.
    destruct R, c; simpl; auto.
    split. apply (residue_pro1 A R I).
    split. red. split. red. intros.
    exists (makeCoset (ring_to_group A R) (ideal_to_normal_subgroup A R I) x); split; auto.
    apply residue_ens_intro; auto.
    intros [b]. unfold residue_mapping.
    exists b; auto.
    intros.
    unfold residue_add, addR, residue_mapping; auto.
Qed.

Theorem III_8_1'' (R : @Ring A) (I : ideal R) : 
  is_ring (residue_ens R I) (residue_add R I) (residue_mul R I).
Proof.
  generalize Theorem1; intros.
  generalize residue_pro2; intros.
  specialize (H0 A R I).
  generalize residue_pro1; intros.
  generalize residue_pro; intros.
  specialize (H1 A R I); specialize (H2 A R I).
  assert (binary_operation (residue_add R I) (residue_ens R I) /\
    binary_operation (residue_mul R I) (residue_ens R I)).
  { split; auto. }
  specialize (H A (residue_class R I) R (residue_ens R I) (residue_add R I) 
  (residue_mul R I) H0 H3).
  generalize III_8_1'; intros.
  apply H in H4; auto.
Qed.


Variable B : Type.

(* R 和 R1 是两个环，并且R与R1同态，那么这个同态满射的核是R的一个理想 *)
Theorem III_8_2' (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) : 
  is_ideal R ker. 
Proof.
  destruct ker.
  split; simpl; auto. split; auto. split. 
  - intros. apply i0 in H; apply i0 in H0.
    generalize Theorem2_2; intro XX.
    specialize (XX A B R R1 h b).
    destruct h, h1, a0, a0; simpl.
    generalize e; intros.
    specialize (e0 a (invR R b)).
    assert ((makeHomomorphismring A B R R1 h0 (conj b0 (conj b1 (conj s e))) h2) a = h0 a).
    { auto. }
    rewrite H1 in H. rewrite H in e0.
    assert ((makeHomomorphismring A B R R1 h0 (conj b0 (conj b1 (conj s e))) h2) b = h0 b).
    { auto. }
    assert ((makeHomomorphismring A B R R1 h0 (conj b0 (conj b1 (conj s e))) h2) (invR R b) 
    = h0 (invR R b)). { auto. }
    rewrite H2 in H0, XX.  rewrite H3 in XX.
    rewrite XX in e0. rewrite H0 in e0.
    clear H1; clear H2; clear H3.
    rewrite ring_inv in e0.
    apply i0; auto.
  - intros. split.
    + destruct h, h2, a0, a0; simpl.
      generalize e; intros.
      specialize (e0 a r). apply i0.
      apply i0 in H.
      assert ((makeHomomorphismring A B R R1 h0 h1 (conj b (conj b0 (conj s e)))) a = h0 a).
      { auto. }
      assert ((makeHomomorphismring A B R R1 h0 h1 (conj b (conj b0 (conj s e)))) (mulR R a r) 
      = h0 (mulR R a r)). { auto. }
      rewrite H1 in H. rewrite H2. rewrite H in e0.
      generalize ring_zero_pro; intros.
      specialize (H3 B R1 (h0 r)).
      destruct H3. rewrite H4 in e0; auto.
    + destruct h, h2, a0, a0; simpl.
      generalize e; intros.
      specialize (e0 r a). apply i0.
      apply i0 in H.
      assert ((makeHomomorphismring A B R R1 h0 h1 (conj b (conj b0 (conj s e)))) a = h0 a).
      { auto. }
      assert ((makeHomomorphismring A B R R1 h0 h1 (conj b (conj b0 (conj s e)))) (mulR R r a) 
      = h0 (mulR R r a)). { auto. }
      rewrite H1 in H. rewrite H2. rewrite H in e0.
      generalize ring_zero_pro; intros.
      specialize (H3 B R1 (h0 r)).
      destruct H3. rewrite H3 in e0; auto.
Qed.

Definition ker_to_ideal (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) : 
  ideal R.
  generalize III_8_2'; intros.
  specialize (H R R1 h ker). 
  destruct H, H0, H1. destruct ker.
  exact (makeIdeal R r_kerens0 H0 H H1 H2).
Defined.

Definition III_8_2''_map (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) 
  (a : residue_class R (ker_to_ideal R R1 h ker)) : B.
  exact (h (residue_to_repr R (ker_to_ideal R R1 h ker) a)).
Defined.

Lemma ker_to_ideal_addpro (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) : 
  binary_operation (residue_add R (ker_to_ideal R R1 h ker)) 
  (residue_ens R (ker_to_ideal R R1 h ker)).
Proof.
  red; red; intros.
  destruct H, H0, R, c, base0, base0, base0; simpl.
  red in b0, b0.
  apply (b0 a a0) in H; auto. destruct H, H.
  exists (makeCoset (ring_to_group A (ring.Pack sort0 (ring.Class sort0 
          (group_add.Class A sort0 (group.Class sort0 
          (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1) c) mul0 b a1 l r)) ) 
         (ideal_to_normal_subgroup A (ring.Pack sort0 (ring.Class sort0 
          (group_add.Class A sort0 (group.Class sort0 
          (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1) c) mul0 b a1 l r))
           (ker_to_ideal
           (ring.Pack sort0 (ring.Class sort0 (group_add.Class A sort0 
            (group.Class sort0 (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1) c) 
          mul0 b a1 l r)) R1 h
           ker) ) x);split; auto.
  apply residue_ens_intro; auto.
  unfold addR; simpl. rewrite H1; auto.
Qed.

Lemma ker_to_ideal_mulpro (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) : 
  binary_operation (residue_mul R (ker_to_ideal R R1 h ker)) 
  (residue_ens R (ker_to_ideal R R1 h ker)).
Proof.
  red; red; intros.
  destruct H, H0, R, c, base0, base0, base0; simpl.
  red in b, b.
  apply (b a a0) in H; auto. destruct H, H.
  exists (makeCoset (ring_to_group A (ring.Pack sort0 (ring.Class sort0 
          (group_add.Class A sort0 (group.Class sort0 
          (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1) c) mul0 b a1 l r)) ) 
         (ideal_to_normal_subgroup A (ring.Pack sort0 (ring.Class sort0 
          (group_add.Class A sort0 (group.Class sort0 
          (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1) c) mul0 b a1 l r))
           (ker_to_ideal
           (ring.Pack sort0 (ring.Class sort0 (group_add.Class A sort0 
            (group.Class sort0 (Assoc A sort0 add0 b0 a2 n) zero0 inv0 l0 r0 l1 r1) c) 
          mul0 b a1 l r)) R1 h
           ker) ) x);split; auto.
  apply residue_ens_intro; auto.
  unfold mulR; simpl. rewrite H1; auto.
Qed.

Lemma ker_to_ideal_pro1 (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) :
  forall a, In ker a -> In (ker_to_ideal R R1 h ker) a.
Proof.
  intros.  
  unfold ker_to_ideal; simpl. destruct ker; simpl.
  destruct (III_8_2' R R1 h (makeRKernel A B R R1 h r_kerens0 n i i0)); simpl; auto.
  destruct a0; simpl; auto. destruct a0; simpl ;auto.
Qed.

Lemma ker_to_nor_pro (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) :
  forall a, In ker a -> 
  In (ideal_to_normal_subgroup A R (ker_to_ideal R R1 h ker)) a.
Proof.
  intros. 
  apply ker_to_ideal_pro1 in H; auto.
  apply ideal_to_nor_pro in H; auto.
Qed.

(* R R1是环，h是R和R1同态满射，ker是这个同态满射的核， 那么R/ker的剩余类与R1之间存在一个一一映射  *)
Lemma III_8_2''_mapismap (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) :  
  bijective (III_8_2''_map R R1 h ker) (residue_ens R (ker_to_ideal R R1 h ker)) R1.
Proof.
  split.
  - split.
    + red; intros. destruct H, h, h1, a0, a0, s; simpl.
      apply m in H; auto.
    + destruct h, h1, a, a, s; simpl.
      intros. remember e0. 
      clear Heqe1. specialize (e0 b1).
      destruct e0.
      exists (makeCoset (ring_to_group A R) 
      (ideal_to_normal_subgroup A R (ker_to_ideal R R1 
      (makeHomomorphismring A B R R1 h0 (conj b (conj b0 (conj (conj m e1) e))) h2) ker)) x); auto. 
  - apply injec.
    split.
    + red; intros. destruct H, h, h1, a0, a0, s; simpl.
      apply m in H; auto.
    + intros.  generalize coset_eq_axiom; intros.
      specialize (H0 A (ring_to_group A R) 
      (ideal_to_normal_subgroup A R (ker_to_ideal R R1 h ker)) a b).
      destruct H0. apply logic_pro in H1; auto.
      generalize coset_pro1; intros.
      specialize (H2 A (ring_to_group A R) 
      (ideal_to_normal_subgroup A R (ker_to_ideal R R1 h ker)) a b).
      destruct H2. apply logic_pro in H3; auto. clear H2. clear H0.
      unfold III_8_2''_map; simpl.
      destruct ker; simpl; auto. destruct a, b; simpl; auto.
      generalize i0; intros.
      generalize ker_to_nor_pro; intros.
      specialize (H0 R R1 h (makeRKernel A B R R1 h r_kerens0 n i i0)).
      simpl. rename repr0 into repr1; rename repr into repr0.
       specialize (H0 (addG (ring_to_group A R)
          (coset_to_repr A (ring_to_group A R) (ideal_to_normal_subgroup A R (ker_to_ideal R R1 h (makeRKernel A B R R1 h r_kerens0 n i i0)))
             {| repr := repr0 |})
          (invG (ring_to_group A R)
             (coset_to_repr A (ring_to_group A R) (ideal_to_normal_subgroup A R (ker_to_ideal R R1 h (makeRKernel A B R R1 h r_kerens0 n i i0)))
                {| repr := repr1 |})))).
      apply logic_pro in H0; auto.
      specialize (i1 (addG (ring_to_group A R)
          (coset_to_repr A (ring_to_group A R) (ideal_to_normal_subgroup A R (ker_to_ideal R R1 h (makeRKernel A B R R1 h r_kerens0 n i i0)))
             {| repr := repr0 |})
          (invG (ring_to_group A R)
             (coset_to_repr A (ring_to_group A R) (ideal_to_normal_subgroup A R (ker_to_ideal R R1 h (makeRKernel A B R R1 h r_kerens0 n i i0)))
                {| repr := repr1 |})))).
      destruct i1 as [H5 H6 ]. clear H5.
      apply logic_pro in H6; auto. clear H0 H1 H3.
      assert (addR R = addG (ring_to_group A R)).
      { auto. } rewrite <- H0 in H6.
      unfold coset_to_repr in H6; simpl.
      assert (invR R = invG (ring_to_group A R)). { auto. }
      rewrite <- H1 in H6. clear H0 H1.
      destruct h, h1, a, a; simpl; auto. generalize e; intros.
      specialize (e0 repr0 (invR R repr1)).
      assert ((makeHomomorphismring A B R R1 h0 (conj b (conj b0 (conj s e))) h2)
       (addR R repr0 (invR R repr1)) = h0 (addR R repr0 (invR R repr1))).
      { auto. }
      rewrite H0 in H6. rewrite e0 in H6.
      generalize Theorem2_2; intros.
      specialize (H1 A B R R1 
      (makeHomomorphismring A B R R1 h0 (conj b (conj b0 (conj s e))) h2) repr1).
      assert ((makeHomomorphismring A B R R1 h0 (conj b (conj b0 (conj s e))) h2) 
            repr1 = h0 repr1).
      { auto. }
      rewrite H2 in H1.
      assert ((makeHomomorphismring A B R R1 h0 (conj b (conj b0 (conj s e))) h2) 
      (invR R repr1) = h0 (invR R repr1)).  { auto. }
      rewrite H3 in H1. clear H2 H3.
      rewrite H1 in H6. 
      generalize (classic (h0 repr0 <> h0 repr1)); intros.
      destruct H2; auto. apply NNPP in H2.
      assert (addR R1 (h0 repr0) (invR R1 (h0 repr1)) = addR R1 (h0 repr1) (invR R1 (h0 repr1))).
      {  rewrite H2; auto. }
      rewrite ring_inv in H3; auto.
Qed.

Theorem III_8_2'' (R : @Ring A) (R1 : @Ring B) (h : homomorphism_ring R R1) (ker : r_kernel R R1 h) : 
  exists hmap, 
  isomorphism (residue_ens R (ker_to_ideal R R1 h ker)) R1 (residue_add R (ker_to_ideal R R1 h ker)) (addR R1)  hmap /\
  isomorphism (residue_ens R (ker_to_ideal R R1 h ker)) R1 (residue_mul R (ker_to_ideal R R1 h ker)) (mulR R1)  hmap.
Proof.
  exists (III_8_2''_map R R1 h ker). split.
  - split. apply ker_to_ideal_addpro; auto.
    split. apply ring_bin_add; auto.
    split. apply III_8_2''_mapismap.
    intros. destruct a, b; simpl.
    unfold III_8_2''_map; simpl.
    destruct h, h1, a, a; simpl.
    apply e.
  - split. apply ker_to_ideal_mulpro; auto.
    split. apply ring_bin_mul; auto.
    split. apply III_8_2''_mapismap.
    intros. destruct a, b; simpl.
    unfold III_8_2''_map; simpl.
    destruct h, h2, a, a; simpl.
    apply e.
Qed.

End III_8_Theorem.

Arguments ring_to_group {A}.
Arguments ring_to_group_iscomm {A}.
Arguments ideal_to_subgroup {A}.
Arguments ideal_to_normal_subgroup {A}.



(*整环*)
Module z_ring.

Record class_of {A : Type} (X : Ensemble A) := Class{
  base :> Ring_Class X;
  one_mul : A;
  _ : commutative base;
  _ : left_id one_mul base;
  _ : right_id one_mul base;
  _ : forall a b, base a b = zero X base -> a = zero X base \/ b = zero X base;   
}.

Structure type {A : Type} := Pack {sort : Ensemble A; _ : class_of sort}.


Notation Z_Ring := type.
Notation Z_Ring_Class := class_of.

End z_ring.

Export z_ring.

(*除环*)
Module div_ring.
 
Record class_of {A : Type} (X : Ensemble A) := Class{
  base :> Ring_Class X;  (* 环 *)
  one_mul : A;    (* 有一个单位元 *)
  opp_mul : A -> A;
  _ : exists a, a <> zero X base; 
  _ : forall a, a <> zero X base -> left_inverse one_mul opp_mul base;
  _ : forall a, a <> zero X base -> right_inverse one_mul opp_mul base;
}.

Structure type {A : Type} := Pack {sort : Ensemble A; _ : class_of sort}.


Notation Div_Ring := type.
Notation Div_Ring_Class := class_of.

End div_ring.

Export div_ring.

