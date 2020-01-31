
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

Require Import FreeMonoid.
Require Import StrongNormalisation.
Require Import Confluence.

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


