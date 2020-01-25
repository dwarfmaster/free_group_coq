
(* Construction of the free group *)

Require Import Coq.Init.Logic.

Axiom functionnal_extensionality : forall (A B : Type),
    forall (f g : A -> B), (forall (x : A), f x = g x) -> f = g.
Axiom axiomK : forall (P : Prop), forall (p q : P), p = q.

(*
 *  _____                __  __                   _     _ 
 * |  ___| __ ___  ___  |  \/  | ___  _ __   ___ (_) __| |
 * | |_ | '__/ _ \/ _ \ | |\/| |/ _ \| '_ \ / _ \| |/ _` |
 * |  _|| | |  __/  __/ | |  | | (_) | | | | (_) | | (_| |
 * |_|  |_|  \___|\___| |_|  |_|\___/|_| |_|\___/|_|\__,_|
 *                                                        
 *)

Record Monoid : Type := mkMon {
    type          : Type;
    op            : type -> type -> type;
    empty         : type;
    emptyCorrect  : forall (x : type), op x empty = x /\ op empty x = x;
    associativity : forall (x y z : type), op x (op y z) = op (op x y) z;
}.

Definition is_monoid_morphism (M M' : Monoid) (f : type M -> type M') : Prop :=
    f (empty M) = empty M' /\ forall (x y : type M), f (op M x y) = op M' (f x) (f y).

Record MonoidMorphism (M M' : Monoid) : Type := mkMonMorphism {
    monmor : type M -> type M';
    monmor_correct : is_monoid_morphism M M' monmor;
}.

Definition is_free_monoid_over (T : Type) (M : Monoid) : Prop :=
    forall (M' : Monoid),
      exists (F : (T -> type M') -> MonoidMorphism M M'),
      exists (G : (type M -> type M') -> (T -> type M')),
           (forall (f : T -> type M'), G (monmor M M' (F f)) = f)
        /\ (forall (m : MonoidMorphism M M'), monmor M M' (F (G (monmor M M' m))) = monmor M M' m).

Inductive FreeMonT (T : Type) : Type
    := App : T -> FreeMonT T -> FreeMonT T
    | Empty : FreeMonT T
    .

Fixpoint append {T : Type} (x y : FreeMonT T) : FreeMonT T :=
    match x with
    | Empty _   => y
    | App _ h t => App T h (append t y)
    end.

Lemma append_empty (T : Type) :
    forall (x : FreeMonT T), append x (Empty T) = x /\ append (Empty T) x = x.
Proof.
    intro x. split; simpl; try reflexivity.
    induction x; simpl; try reflexivity.
    rewrite -> IHx. reflexivity.
Qed.

Lemma append_associative (T : Type) :
    forall (x y z : FreeMonT T), append x (append y z) = append (append x y) z.
Proof.
    intros x y z.
    induction x; simpl; try reflexivity.
    rewrite -> IHx. reflexivity.
Qed.

Let FreeMon (T : Type) : Monoid := mkMon (FreeMonT T) append (Empty T) (append_empty T) (append_associative T).

Fixpoint freemonmap' (T : Type) (M : Monoid) (f : T -> type M) (x : FreeMonT T) : type M :=
    match x with
    | Empty _   => empty M
    | App _ h t => op M (f h) (freemonmap' T M f t)
    end.

Lemma freemonmap_is_morphism (T : Type) :
    forall (M : Monoid), forall (f : T -> type M), is_monoid_morphism (FreeMon T) M (freemonmap' T M f).
Proof.
    unfold is_monoid_morphism. intros M f. simpl; split; try reflexivity. 
    intros x y. induction x; simpl.
    - rewrite <- (associativity M). rewrite -> IHx. reflexivity.
    - rewrite -> (proj2 (emptyCorrect M (freemonmap' T M f y))).
      reflexivity.
Qed.

Let makeFreeMonMorphism (T : Type) (M : Monoid) (f : T -> type M) : MonoidMorphism (FreeMon T) M :=
    mkMonMorphism (FreeMon T) M (freemonmap' T M f) (freemonmap_is_morphism T M f).

Let applyOnBasis (T : Type) (M : Monoid) (m : (FreeMonT T) -> type M) (x : T) :=
    m (App T x (Empty T)).

Lemma freemonmapOnBasis (T : Type) (M : Monoid) :
    forall (m : MonoidMorphism (FreeMon T) M),
      freemonmap' T M (applyOnBasis T M (monmor (FreeMon T) M m)) = monmor (FreeMon T) M m.
Proof.
    intro m. unfold applyOnBasis. apply functionnal_extensionality. intro x.
    pose (monmor_correct (FreeMon T) M m) as morphism.
    induction x; simpl.
    - rewrite -> IHx.
      unfold is_monoid_morphism in morphism. destruct morphism as [ _ morphism ].
      rewrite <- morphism. unfold FreeMon at 2. simpl. reflexivity.
    - unfold is_monoid_morphism in morphism. destruct morphism as [ morphism _ ].
      simpl in morphism. rewrite -> morphism. reflexivity.
Qed.

Lemma FreeMon_is_free_monoid (T : Type) : is_free_monoid_over T (FreeMon T).
Proof.
    unfold is_free_monoid_over. intros M. exists (makeFreeMonMorphism T M).
    exists (applyOnBasis T M). split.
    - intro f. unfold applyOnBasis. apply functionnal_extensionality. intro x.
      unfold makeFreeMonMorphism. simpl. apply (emptyCorrect M).
    - intro m. unfold makeFreeMonMorphism. simpl.
      exact (freemonmapOnBasis T M m).
Qed.

