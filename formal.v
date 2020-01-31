
(* Construction of the free group *)

Require Import Coq.Init.Logic.

Axiom functionnal_extensionality : forall (A B : Type),
    forall (f g : A -> B), (forall (x : A), f x = g x) -> f = g.

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

(*
 *   ____             __ _                           
 *  / ___|___  _ __  / _| |_   _  ___ _ __   ___ ___ 
 * | |   / _ \| '_ \| |_| | | | |/ _ \ '_ \ / __/ _ \
 * | |__| (_) | | | |  _| | |_| |  __/ | | | (_|  __/
 *  \____\___/|_| |_|_| |_|\__,_|\___|_| |_|\___\___|
 *                                                   
 *)

 Definition strongly_confluent (T : Type) (R : T -> T -> Prop) : Prop
     := forall (a b c : T), R a b -> R a c
          -> (b = c) \/ (R b c) \/ (R c b) \/ (exists (d : T), R b d /\ R c d).

Theorem reduction_strongly_confluent' (T : Type) :
    forall (a b c : (FreeMonT (WithInv T))), Reduction T a b -> Reduction T a c
        -> (b = c) \/ (exists (d : (FreeMonT (WithInv T))), Reduction T b d /\ Reduction T c d).
Proof.
    unfold strongly_confluent. intros a b c Hab.
    remember a as x. remember b as y.
    rewrite -> Heqy in Hab. rewrite -> Heqx in Hab.
    generalize dependent c. generalize dependent y. generalize dependent x.
    induction Hab.

    - intros a Heqx b Heqy c Hbc. destruct Hbc.
      + inversion Heqx. left. assumption.
      + inversion Heqx.
      + destruct Hbc.
        * inversion Heqx.
        * inversion Heqx. left. rewrite Heqy. symmetry. assumption.
        * inversion Heqx. right. exists m'. rewrite -> H2 in Hbc. rewrite <- Heqy in Hbc.
          split; try assumption. apply LeftRed.

    - intros a Heqx b Heqy z Hbc. destruct Hbc.
      + inversion Heqx.
      + inversion Heqx. left. assumption.
      + destruct Hbc.
        * inversion Heqx. left. rewrite Heqy. symmetry. assumption.
        * inversion Heqx.
        * inversion Heqx. right. exists m'. rewrite -> H2 in Hbc. rewrite <- Heqy in Hbc.
          split; try assumption. apply RightRed.

    - intros a Heqx b Heqy c Hred. destruct Hred.
      + destruct Hab; inversion Heqx.
        * left. rewrite <- H1. rewrite -> H0. assumption.
        * right. exists m'. split; try assumption.
          rewrite -> Heqy. rewrite <- H0. rewrite <- H1. apply LeftRed.
      + destruct Hab; inversion Heqx.
        * left. rewrite <- H1. rewrite -> H0. assumption.
        * right. exists m'. split; try assumption.
          rewrite -> Heqy. rewrite <- H0. rewrite <- H1. apply RightRed.
      + inversion Heqx. rewrite -> H1 in Hred.
        pose (IHHab m (eq_refl m) m' (eq_refl m') m'0 Hred) as Hind.
        destruct Hind as [ Hctxeq | [ red [ Hctxredm' Hctxredm'0 ] ] ].
        * left. rewrite -> Heqy. rewrite <- Hctxeq. reflexivity.
        * right. exists (App (WithInv T) x red). rewrite -> Heqy.
          split; apply CtxRed; assumption.
Qed.

Theorem reduction_strongly_confluent (T : Type) : strongly_confluent (FreeMonT (WithInv T)) (Reduction T).
Proof.
    intros a b c Hab Hbc. pose (reduction_strongly_confluent' T a b c Hab Hbc) as prf.
    destruct prf.
    - left. assumption.
    - right. right. right. assumption.
Qed.


(*
 *  ____          _            _   _             
 * |  _ \ ___  __| |_   _  ___| |_(_) ___  _ __  
 * | |_) / _ \/ _` | | | |/ __| __| |/ _ \| '_ \ 
 * |  _ <  __/ (_| | |_| | (__| |_| | (_) | | | |
 * |_| \_\___|\__,_|\__,_|\___|\__|_|\___/|_| |_|
 *                                               
 *  __  __                  _     _               
 * |  \/  | ___  _ __ _ __ | |__ (_)___ _ __ ___  
 * | |\/| |/ _ \| '__| '_ \| '_ \| / __| '_ ` _ \ 
 * | |  | | (_) | |  | |_) | | | | \__ \ | | | | |
 * |_|  |_|\___/|_|  | .__/|_| |_|_|___/_| |_| |_|
 *                   |_|                          
 *)

Lemma append_ctx_left (T : Type) :
    forall (a b c : FreeMonT (WithInv T)), Reduction T b c -> Reduction T (append a b) (append a c).
Proof.
    intros a. induction a.
    - intros b c Hbc. simpl. apply CtxRed. apply IHa. assumption.
    - simpl. intros b c Hbc. exact Hbc.
Qed.

Lemma append_ctx_right (T : Type) :
    forall (a b c : FreeMonT (WithInv T)), Reduction T a b -> Reduction T (append a c) (append b c).
Proof.
    intros a b c Hab. generalize dependent c. induction Hab; intro c; simpl; constructor.
    apply IHHab.
Qed.

Inductive trefl_closure {T : Type} (R : T -> T -> Prop) : T -> T -> Prop
    := ReflClosure  : forall (a : T), trefl_closure R a a
    |  TransClosure : forall (a b c : T), R a b -> trefl_closure R b c -> trefl_closure R a c
    .

Lemma append_ctx_left_closure (T : Type) :
    forall (a b c : FreeMonT (WithInv T)), trefl_closure (Reduction T) b c
      -> trefl_closure (Reduction T) (append a b) (append a c).
Proof.
    intros a b c Hbc. induction Hbc; try constructor.
    apply (TransClosure (Reduction T) (append a a0) (append a b)); try assumption.
    apply append_ctx_left. assumption.
Qed.

Lemma append_ctx_right_closure (T : Type) :
    forall (a b c : FreeMonT (WithInv T)), trefl_closure (Reduction T) a b
      -> trefl_closure (Reduction T) (append a c) (append b c).
Proof.
    intros a b c Hab. induction Hab; try constructor.
    apply (TransClosure (Reduction T) (append a c) (append b c)); try assumption.
    apply append_ctx_right. assumption.
Qed.

Lemma trefl_closure_append (T : Type) (R : T -> T -> Prop) :
    forall (a b c : T), trefl_closure R a b -> trefl_closure R b c -> trefl_closure R a c.
Proof.
    intros a b c Hab. generalize dependent c. induction Hab; intros third Hthird; try assumption.
    apply (TransClosure R a b); try assumption. apply IHHab. exact Hthird.
Qed.

Theorem reduction_compatible_append (T : Type) :
    forall (a b c d : FreeMonT (WithInv T)),
        trefl_closure (Reduction T) a c -> trefl_closure (Reduction T) b d
        -> trefl_closure (Reduction T) (append a b) (append c d).
Proof.
    intros a b c d Hac Hbd.
    pose (append_ctx_right_closure T a c b Hac) as step1.
    pose (append_ctx_left_closure T c b d Hbd)  as step2.
    apply (trefl_closure_append (FreeMonT (WithInv T)) (Reduction T) (append a b) (append c b)); assumption.
Qed.


(*
 *  _   _                            _   _____                    
 * | \ | | ___  _ __ _ __ ___   __ _| | |  ___|__  _ __ _ __ ___  
 * |  \| |/ _ \| '__| '_ ` _ \ / _` | | | |_ / _ \| '__| '_ ` _ \ 
 * | |\  | (_) | |  | | | | | | (_| | | |  _| (_) | |  | | | | | |
 * |_| \_|\___/|_|  |_| |_| |_|\__,_|_| |_|  \___/|_|  |_| |_| |_|
 *                                                                
 *)

Definition normal_form { T : Type } (R : T -> T -> Prop) (x : T) : Prop
    := forall (y : T), R x y -> False.

Theorem confluence_unicity_of_normal_form { T : Type } (R : T -> T -> Prop):
    strongly_confluent T R ->
        forall (x n n' : T), R x n -> R x n' ->
            normal_form R n -> normal_form R n' -> n = n'.
Proof.
    intros Hconfl x n n' Hxn Hxn' Hnfn Hnfn'.
    unfold strongly_confluent in Hconfl.
    pose (Hconfl x n n' Hxn Hxn') as Hcases. destruct Hcases as [ Heq | [ Hred | [ Hred | Hexists ] ] ].
    - assumption.
    - exfalso. unfold normal_form in Hnfn. apply (Hnfn n'). assumption.
    - exfalso. unfold normal_form in Hnfn'. apply (Hnfn' n). assumption.
    - destruct Hexists as [ m [ Hred _ ] ]. exfalso. apply (Hnfn m). assumption.
Qed.

Lemma strongly_confluent_closure_step { T : Type } (R : T -> T -> Prop) :
    strongly_confluent T R ->
        forall (a b c : T), R a b -> trefl_closure R a c ->
            exists (d : T), trefl_closure R b d /\ trefl_closure R c d.
Proof.
    intros Hconfl a b c Hab Hac. generalize dependent b. induction Hac.
    - intros b Hab. exists b. split; try constructor. apply (TransClosure R a b); try constructor.
      assumption.
    - intros d Had. pose (Hconfl a b d H Had) as Hmeet.
      destruct Hmeet as [ Heq | [ Hbd | [ Hdb | [ e [ Hbe Hde ] ] ] ] ].
      + exists c. rewrite <- Heq. split; try assumption. constructor.
      + apply IHHac. assumption.
      + exists c. split; try constructor. apply (TransClosure R d b); assumption.
      + destruct (IHHac e Hbe) as [ f [ Hef Hcf ] ].
        exists f. split; try assumption. apply (TransClosure R d e); assumption.
Qed.

Lemma strongly_confluent_closure' { T : Type } (R : T -> T -> Prop) :
    strongly_confluent T R ->
        forall (a b c : T), trefl_closure R a b -> trefl_closure R a c ->
            exists (d : T), trefl_closure R b d /\ trefl_closure R c d.
Proof.
    intros Hconfl a b c Hab. generalize dependent c. induction Hab.
    - intros c Hac. exists c. split; try assumption. constructor.
    - intros d Had.
      destruct (strongly_confluent_closure_step R Hconfl a b d H Had) as [ f [ Hbf Hdf ] ].
      destruct (IHHab f Hbf) as [ e [ Hce Hfe ] ].
      exists e. split; try assumption.
      apply (trefl_closure_append T R d f); assumption.
Qed.

Lemma strongly_confluent_closure { T : Type } (R : T -> T -> Prop) :
    strongly_confluent T R -> strongly_confluent T (trefl_closure R).
Proof.
    intro Hconfl. unfold strongly_confluent. intros a b c Hab Hac.
    right. right. right. apply (strongly_confluent_closure' R Hconfl a b c Hab Hac).
Qed.

Theorem unicity_of_fully_reduction { T : Type }:
    forall (x n n' : FreeMonT (WithInv T)),
        trefl_closure (Reduction T) x n -> trefl_closure (Reduction T) x n' ->
            normal_form (trefl_closure (Reduction T)) n ->
                normal_form (trefl_closure (Reduction T)) n' -> n = n'.
Proof.
    apply confluence_unicity_of_normal_form.
    apply strongly_confluent_closure.
    apply reduction_strongly_confluent.
Qed.



