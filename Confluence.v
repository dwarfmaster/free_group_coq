
(*
 *   ____             __ _                           
 *  / ___|___  _ __  / _| |_   _  ___ _ __   ___ ___ 
 * | |   / _ \| '_ \| |_| | | | |/ _ \ '_ \ / __/ _ \
 * | |__| (_) | | | |  _| | |_| |  __/ | | | (_|  __/
 *  \____\___/|_| |_|_| |_|\__,_|\___|_| |_|\___\___|
 *                                                   
 *)

Require Import FreeMonoid.
Require Import StrongNormalisation.

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


