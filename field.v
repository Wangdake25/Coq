Require Import Ensembles ssrfun Description Relations_1 IndefiniteDescription
  Classical_Prop.

Require Import base group ring.
(*域*)
Module field.
  
Record class_of {A : Type} (X : Ensemble A) := Class{
  base :> Div_Ring_Class X;  (* 环 *)
  _ : commutative base;
}.

Structure type {A : Type} := Pack {sort : Ensemble A; _ : class_of sort}.

Notation Field := type.
Notation Field_Class := class_of.

End field.

Export field.
