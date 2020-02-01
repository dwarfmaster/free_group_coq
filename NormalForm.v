
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

Fixpoint inv { T : Type } (x : WithInv T) : WithInv T
    := match x with
     | Reg    _ a => ForInv T a
     | ForInv _ a => Reg    T a
    end.

Inductive is_stable { T : Type } : FreeMonT (WithInv T) -> Prop
    := StableEmpty : is_stable (Empty (WithInv T))
    |  StableSing : forall (x : WithInv T), is_stable (App (WithInv T) x (Empty (WithInv T)))
    |  StableApp : forall (x y : WithInv T), forall (w : FreeMonT (WithInv T)),
            inv x <> y -> is_stable (App (WithInv T) y w)
                -> is_stable (App (WithInv T) x (App (WithInv T) y w)).

Lemma normal_form_sub { T : Type } :
    forall (x : WithInv T), forall (w : FreeMonT (WithInv T)),
        normal_form (Reduction T) (App (WithInv T) x w) -> normal_form (Reduction T) w.
Proof.
    intros x w Hnf. unfold normal_form. intros w' Hred.
    apply (Hnf (App (WithInv T) x w')). apply CtxRed.
    assumption.
Qed.

Theorem stable_is_normal_form { T : Type } :
    forall (x : FreeMonT (WithInv T)), is_stable x <-> normal_form (Reduction T) x.
Proof.
    intro x. split.
    - intro Hstable. induction Hstable.
      + unfold normal_form. intros x Hred. inversion Hred.
      + unfold normal_form. intros w Hred. inversion Hred. inversion H2.
      + unfold normal_form. intros w' Hred.
        remember (App (WithInv T) y w) as tl0.
        remember (App (WithInv T) x tl0) as tl1.
        destruct Hred.
        * rewrite -> Heqtl0 in Heqtl1. inversion Heqtl1.
          apply H. rewrite <- H1. rewrite <- H2. reflexivity.
        * rewrite -> Heqtl0 in Heqtl1. inversion Heqtl1.
          apply H. rewrite <- H1. rewrite <- H2. reflexivity.
        * unfold normal_form in IHHstable. apply (IHHstable m').
          inversion Heqtl1. rewrite <- H2. assumption.

    - intro Hnf. induction x; try constructor. destruct x.
      + apply StableApp.
        * intro Heq. destruct t.
          { apply (Hnf x). rewrite <- Heq. apply RightRed. }
          { apply (Hnf x). rewrite <- Heq. apply LeftRed. }
        * apply IHx. apply (normal_form_sub t). assumption.
      + apply StableSing.
Qed.

Axiom axiom_K_is_stable :
    forall (T : Type), forall (w : FreeMonT (WithInv T)), forall (p1 p2 : is_stable w), p1 = p2.

Definition DecEq (T : Type) : Type := forall (a b : T), { a = b } + { a <> b }.

Lemma deceq_within { T : Type } (deceq : DecEq T) : DecEq (WithInv T).
Proof.
    unfold DecEq. intros a b. destruct a; destruct b.
    - destruct (deceq t t0).
      * left. rewrite e. reflexivity.
      * right. intro H. apply n. inversion H. reflexivity.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - destruct (deceq t t0).
      * left. rewrite e. reflexivity.
      * right. intro H. apply n. inversion H. reflexivity.
Qed.

Theorem has_red_or_is_nf { T : Type } (deceq : DecEq T) :
    forall (w : FreeMonT (WithInv T)), normal_form (Reduction T) w
        \/ exists (w' : FreeMonT (WithInv T)), Reduction T w w'.
Proof.
    intro w. induction w.
    - destruct w.
      + destruct (deceq_within deceq (inv t) w).
        * destruct t.
          { right. rewrite <- e. exists w0. apply RightRed. }
          { right. rewrite <- e. exists w0. apply LeftRed. }
        * destruct IHw.
          { left. intros w1 Hred. remember (App (WithInv T) t (App (WithInv T) w w0)) as w'. destruct Hred.
            - apply n. inversion Heqw'. reflexivity.
            - apply n. inversion Heqw'. reflexivity.
            - inversion Heqw'. apply (H m'). rewrite <- H2. assumption.
          }
          { right. destruct H as [ w' Hred ]. exists (App (WithInv T) t w'). apply CtxRed. assumption. }
      + left. intros w' Hred. inversion Hred. inversion H2.
    - left. intros w Hred. inversion Hred.
Qed.

Theorem nf_exists' { T : Type } (deceq : DecEq T) :
    forall (a : FreeMonT (WithInv T)),
        (forall (b : FreeMonT (WithInv T)), Reduction T a b ->
            exists (nf : FreeMonT (WithInv T)), trefl_closure (Reduction T) b nf /\ normal_form (Reduction T) nf)
    -> exists (nf : FreeMonT (WithInv T)), trefl_closure (Reduction T) a nf /\ normal_form (Reduction T) nf.
Proof.
    intros a H. destruct (has_red_or_is_nf deceq a).
    - exists a. split; try constructor. assumption.
    - destruct H0 as [ b Hred ]. destruct (H b Hred) as [ nf [ Hrefl Hnf ] ].
      exists nf. split; try assumption. apply (TransClosure (Reduction T) a b); assumption.
Qed.

Theorem nf_exists { T : Type } (deceq : DecEq T) :
    forall (a : FreeMonT (WithInv T)),
        exists (nf : FreeMonT (WithInv T)), trefl_closure (Reduction T) a nf /\ normal_form (Reduction T) nf.
Proof.
    apply (well_founded_ind (reduction_normalizing T)).
    apply nf_exists'. assumption.
Qed.





