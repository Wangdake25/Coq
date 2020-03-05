Require Import Ensembles ssrfun Description Relations_1 IndefiniteDescription
  Classical_Prop.

Arguments In {U} _ _.
Arguments Included {U} _ _.
Arguments Same_set {U}.
Arguments Equivalence {U}.

Module base.

Section definition.

Definition map {A B : Type} (f : A -> B) (X : Ensemble A) (Y : Ensemble B) :=
  forall x, In X x -> exists y, In Y y /\ f x = y.

Definition injective1 {A B : Type} (f : A -> B) (X : Ensemble A) (Y : Ensemble B) :=
  map f X Y /\ forall a b, a <> b -> f a <> f b.

Definition injective2 {A B : Type} (f : A -> B) (X : Ensemble A) (Y : Ensemble B) :=
  map f X Y /\ forall a b, f a = f b -> a = b.

Definition surjective {A B : Type} (f : A -> B) (X : Ensemble A) (Y : Ensemble B) :=
  map f X Y /\ forall b, exists a, f a = b.

Definition bijective {A B : Type} (f : A -> B) (X : Ensemble A) (Y : Ensemble B) :=
  surjective f X Y /\ injective2 f X Y.

Inductive invertible {X Y:Type} (f:X->Y) : Prop :=
  | intro_invertible: forall g:Y->X,
  (forall x:X, g (f x) = x) -> (forall y:Y, f (g y) = y) ->
  invertible f.

Definition operation {A B D : Type} (f : A -> B -> D) 
  (X : Ensemble A) (Y : Ensemble B) (Z : Ensemble D) :=
  forall x y, In X x -> In Y y -> exists z, In Z z /\ f x y = z.

Definition one_operation {A : Type} (f : A -> A) (X Y : Ensemble A) := 
  map f X Y.

Definition binary_operation {A : Type} (f : A -> A -> A) (X : Ensemble A) := 
  operation f X X X.

(* 同态映射 *)
Definition homomorphism_map {A B : Type} (X : Ensemble A) (Y : Ensemble B) 
  (f : A -> A -> A) (g : B -> B -> B) (h : A -> B) :=
  binary_operation f X /\ binary_operation g Y /\ map h X Y /\ 
  forall a b, h (f a b) = g (h a) (h b).

(* 同态满射 *)
Definition homomorphism {A B : Type} (X : Ensemble A) (Y : Ensemble B) 
  (f : A -> A -> A) (g : B -> B -> B) (h : A -> B) :=
  binary_operation f X /\ binary_operation g Y /\ surjective h X Y /\ 
  forall a b, h (f a b) = g (h a) (h b).

(* 同构 *)
Definition isomorphism {A B : Type} (X : Ensemble A) (Y : Ensemble B) 
  (f : A -> A -> A) (g : B -> B -> B) (h : A -> B) :=
  binary_operation f X /\ binary_operation g Y /\ bijective h X Y /\ 
  forall a b, h (f a b) = g (h a) (h b).

Definition exists_solution {A : Type} (f : A -> A -> A) (X : Ensemble A) :=
  forall a b, (exists x, f a x = b) /\ (exists y,f y a = b). 

(* A不为空 *)
Definition notEmpty {A : Type} (X : Ensemble A) := 
  exists a, In X a.

Lemma injec {A B : Type} (f : A -> B) (X : Ensemble A) (Y : Ensemble B) :
  injective1 f X Y <-> injective2 f X Y.
Proof.
  split; intros.
  - destruct H. split; auto; intros.
    generalize (classic (a = b)); intros.
    destruct H2; auto. apply H0 in H2; auto.
    contradiction.
  - destruct H. split; auto.
Qed. 

(* 可证 *)
Lemma logic_pro : forall (P Q : Prop), (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros; auto.
Qed.

End definition.

Section base_law.

Record assoc_law {A : Type} (X : Ensemble A) : Type := Assoc {
  add :> A -> A -> A; (* 代数运算 *)
  _ : binary_operation add X;
  _ : associative add; (* 加法满足结合律 *)
  _ : notEmpty X;
}.

End base_law.

End base.

Export base.


