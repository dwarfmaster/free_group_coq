
(*
 *  _   _                            _   _____                    
 * | \ | | ___  _ __ _ __ ___   __ _| | |  ___|__  _ __ _ __ ___  
 * |  \| |/ _ \| '__| '_ ` _ \ / _` | | | |_ / _ \| '__| '_ ` _ \ 
 * | |\  | (_) | |  | | | | | | (_| | | |  _| (_) | |  | | | | | |
 * |_| \_|\___/|_|  |_| |_| |_|\__,_|_| |_|  \___/|_|  |_| |_| |_|
 *                                                                
 *)

Require Import FreeMonoid.
Require Import StrongNormalisation.
Require Import Confluence.
Require Import RedMorphism.

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

