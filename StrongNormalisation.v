
(*
 *  ____  _                         
 * / ___|| |_ _ __ ___  _ __   __ _ 
 * \___ \| __| '__/ _ \| '_ \ / _` |
 *  ___) | |_| | | (_) | | | | (_| |
 * |____/ \__|_|  \___/|_| |_|\__, |
 *                            |___/ 
 *  _   _                            _ _           _   _             
 * | \ | | ___  _ __ _ __ ___   __ _| (_)___  __ _| |_(_) ___  _ __  
 * |  \| |/ _ \| '__| '_ ` _ \ / _` | | / __|/ _` | __| |/ _ \| '_ \ 
 * | |\  | (_) | |  | | | | | | (_| | | \__ \ (_| | |_| | (_) | | | |
 * |_| \_|\___/|_|  |_| |_| |_|\__,_|_|_|___/\__,_|\__|_|\___/|_| |_|
 *                                                                   
 *)

Require Import Coq.Init.Wf.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Init.Peano.
Require Import FreeMonoid.

Definition Inv (T : Type) (R : T -> T -> Prop) : T -> T -> Prop
    := fun (x y : T) => R y x.

Definition strongly_normalizing (T : Type) (R : T -> T -> Prop) : Prop
    := well_founded (Inv T R).

Definition monotome_morphism (T T' : Type) (R : T -> T -> Prop) (R' : T' -> T' -> Prop) (f : T -> T') : Prop :=
    forall (x y : T), R x y -> R' (f x) (f y).

Theorem preimage_well_founded' (T T' : Type) (R : T -> T -> Prop) (R' : T' -> T' -> Prop) (f : T -> T') :
    monotome_morphism T T' R R' f -> well_founded R' -> forall (y : T'), forall (x : T), y = f x -> Acc R x.
Proof.
    intros mono wfR' y. pose (wfR' y) as HAccy.
    induction HAccy. clear H. rename H0 into Hind.
    intros a Heq. constructor. intros b Hba.
    rewrite -> Heq in Hind. apply (Hind (f b) (mono b a Hba) b).
    reflexivity.
Qed.

Theorem preimage_well_founded (T T' : Type) (R : T -> T -> Prop) (R' : T' -> T' -> Prop) (f : T -> T') :
    monotome_morphism T T' R R' f -> well_founded R' -> well_founded R.
Proof.
    intros mono wfR' x.
    apply (preimage_well_founded' T T' R R' f mono wfR' (f x) x).
    reflexivity.
Qed.

Fixpoint monoidLength (T : Type) (xs : FreeMonT T) : nat
    := match xs with
       | Empty _      => O
       | App _ _ tail => S (monoidLength T tail)
       end.

Inductive WithInv (T : Type) : Type
    := Reg    : T -> WithInv T
    |  ForInv : T -> WithInv T
    .

Inductive Reduction (T : Type) : FreeMonT (WithInv T) -> FreeMonT (WithInv T) -> Prop
    := LeftRed  : forall (x : T), forall (tl : FreeMonT (WithInv T)),
                  Reduction T (App (WithInv T) (ForInv T x) (App (WithInv T) (Reg T x) tl)) tl
    |  RightRed : forall (x : T), forall (tl : FreeMonT (WithInv T)),
                  Reduction T (App (WithInv T) (Reg T x) (App (WithInv T) (ForInv T x) tl)) tl
    |  CtxRed   : forall (x : WithInv T), forall (m m' : FreeMonT (WithInv T)),
                  Reduction T m m' -> Reduction T (App (WithInv T) x m) (App (WithInv T) x m')
    .

Lemma monoidLength_monotone (T : Type) :
    monotome_morphism (FreeMonT (WithInv T)) nat
                      (Inv (FreeMonT (WithInv T)) (Reduction T)) lt
                      (monoidLength (WithInv T)).
Proof.
    unfold monotome_morphism. intros m m' Hred. induction Hred; simpl; try auto.
    unfold lt. apply le_n_S. assumption.
Qed.

Theorem reduction_normalizing (T : Type) : strongly_normalizing (FreeMonT (WithInv T)) (Reduction T).
Proof.
    unfold strongly_normalizing.
    apply (preimage_well_founded (FreeMonT (WithInv T)) nat
                                 (Inv (FreeMonT (WithInv T)) (Reduction T)) lt
                                 (monoidLength (WithInv T))).
    - apply monoidLength_monotone.
    - exact lt_wf.
Qed.

