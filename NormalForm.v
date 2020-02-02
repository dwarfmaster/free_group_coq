
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
            normal_form (Reduction T) n ->
                normal_form (Reduction T) n' -> n = n'.
Proof.
    intros x n n' Hxn Hxn' Hnfn Hnfn'.
    pose (strongly_confluent_closure _ (reduction_strongly_confluent T)) as Hsconfl.
    destruct (Hsconfl x n n' Hxn Hxn') as [ Heq | [ Hnn' | [ Hn'n | [ rd H ] ] ] ].
    - assumption.
    - destruct Hnn'; try reflexivity. exfalso. apply (Hnfn b). assumption.
    - destruct Hn'n; try reflexivity. exfalso. apply (Hnfn' b). assumption.
    - destruct H as [ Hredn Hredn' ]. destruct Hredn; destruct Hredn'; try reflexivity.
      + exfalso. apply (Hnfn' b). assumption.
      + exfalso. apply (Hnfn b). assumption.
      + exfalso. apply (Hnfn b). assumption.
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

Fixpoint liftEq { T : Type } (deceq : T -> T -> bool) (x y : WithInv T) : bool
    := match x, y with
     | Reg    _ a, Reg    _ b => deceq a b
     | ForInv _ a, ForInv _ b => deceq a b
     | _,          _          => false
    end.

Fixpoint reduce { T : Type } (deceq : T -> T -> bool) (x : FreeMonT (WithInv T)) : FreeMonT (WithInv T) :=
    let witheq : WithInv T -> WithInv T -> bool := liftEq deceq in
    match x with
    | (App _ a w) => let reduced : FreeMonT (WithInv T) := reduce deceq w in
            match reduced with
            | (App _ b w') => if (witheq (inv a) b)
                                then w'
                                else (App (WithInv T) a (App (WithInv T) b w'))
            | Empty _      => App (WithInv T) a (Empty (WithInv T))
            end
    | Empty _ => Empty (WithInv T)
    end.

Definition DecEqCorrect { T : Type } (deceq : T -> T -> bool) : Prop
    := forall (a b : T), a = b <-> deceq a b = true.

Lemma lifteq_correct { T : Type } (deceq : T -> T -> bool) :
    forall (Hc : DecEqCorrect deceq), DecEqCorrect (liftEq deceq).
Proof.
    intros Hc a b. split. 
    - destruct a; destruct b; intro Heq; inversion Heq.
      + simpl. apply Hc. reflexivity.
      + simpl. apply Hc. reflexivity.
    - destruct a; destruct b; intro Heq; simpl in Heq; inversion Heq.
      + apply Hc in Heq. rewrite Heq. reflexivity.
      + apply Hc in Heq. rewrite Heq. reflexivity.
Qed.

Lemma inv_red { T : Type } :
    forall (a b : WithInv T), forall (w : FreeMonT (WithInv T)),
        inv a = b -> Reduction T (App _ a (App _ b w)) w.
Proof.
    intros a b w Heq. destruct a.
    - rewrite <- Heq. apply RightRed.
    - rewrite <- Heq. apply LeftRed.
Qed.

Lemma inv_invo { T : Type } :
    forall (a : WithInv T), inv (inv a) = a.
Proof.
    destruct a; reflexivity.
Qed.

Lemma inv_apply { T : Type } :
    forall (a b : WithInv T), inv a = b <-> a = inv b.
Proof.
    intros a b. destruct a; destruct b; split; intro Heq; inversion Heq; reflexivity.
Qed.

Lemma trefl_ctx_red { T : Type } :
    forall (a : WithInv T), forall (w w' : FreeMonT (WithInv T)),
        trefl_closure (Reduction T) w w' -> trefl_closure (Reduction T) (App _ a w) (App _ a w').
Proof.
    intros a w w' Hred. induction Hred.
    - constructor.
    - apply (TransClosure (Reduction T) _ (App (WithInv T) a b)); try assumption.
      apply CtxRed. assumption.
Qed.

Lemma trefl_red_inject { T : Type } (R : T -> T -> Prop) :
    forall (a b : T), R a b -> trefl_closure R a b.
Proof.
    intros a b Hred. apply (TransClosure R _ b); try assumption. constructor.
Qed.

Theorem reduce_is_reduction { T : Type } (deceq : T -> T -> bool) (decC : DecEqCorrect deceq) :
    forall (x : FreeMonT (WithInv T)), trefl_closure (Reduction T) x (reduce deceq x).
Proof.
    intro x. induction x.
    - simpl. remember (reduce deceq x) as red. destruct red.
      + remember (liftEq deceq (inv t) w) as test. destruct test.
        { symmetry in Heqtest. apply (lifteq_correct deceq decC) in Heqtest.
          apply (trefl_closure_append (FreeMonT (WithInv T)) (Reduction T)
                    _ (App (WithInv T) t (App (WithInv T) w red))).
          - apply trefl_ctx_red. assumption.
          - apply trefl_red_inject. apply inv_red. assumption.
        }
        { apply trefl_ctx_red. assumption. }
      + apply trefl_ctx_red. assumption.
    - simpl. constructor.
Qed.

Lemma eq_is_neq { T : Type } (deceq : T -> T -> bool) (eqdecC : DecEqCorrect deceq) :
    forall (a b : T), a <> b <-> deceq a b = false.
Proof.
    intros a b. split; intro H.
    - remember (deceq a b) as test. destruct test; try reflexivity.
      exfalso. apply H. apply eqdecC. symmetry. assumption.
    - intro Heq. apply eqdecC in Heq. rewrite -> H in Heq. inversion Heq.
Qed.

Theorem reduce_is_stable { T : Type } (deceq : T -> T -> bool) (decC : DecEqCorrect deceq) :
    forall (x : FreeMonT (WithInv T)), is_stable (reduce deceq x).
Proof.
    intro x. induction x.
    - simpl. remember (reduce deceq x) as red. destruct red; try constructor.
      remember (liftEq deceq (inv t) w) as test. destruct test.
      + apply stable_is_normal_form. apply (normal_form_sub w).
        apply stable_is_normal_form. assumption.
      + symmetry in Heqtest. apply (eq_is_neq (liftEq deceq) (lifteq_correct deceq decC)) in Heqtest.
        constructor; assumption.
    - constructor.
Qed.

Corollary reduce_is_normal_form { T : Type } (deceq : T -> T -> bool) (decC : DecEqCorrect deceq) :
    forall (x : FreeMonT (WithInv T)), normal_form (Reduction T) (reduce deceq x).
Proof.
    intro x. apply stable_is_normal_form. apply reduce_is_stable. assumption.
Qed.

Definition normal_form_of { T : Type } (R : T -> T -> Prop) (x y : T) : Prop
    := trefl_closure R x y /\ normal_form R y.

Theorem reduce_is_unique_normal_form { T : Type } (deceq : T -> T -> bool) (decC : DecEqCorrect deceq) :
    forall (x y : FreeMonT (WithInv T)),
        normal_form_of (Reduction T) x y <-> y = reduce deceq x.
Proof.
    intros x y. split.
    - intro Hnf. destruct Hnf. apply (unicity_of_fully_reduction x); try assumption.
      + apply reduce_is_reduction. assumption.
      + apply reduce_is_normal_form. assumption.
    - intro Hred. rewrite -> Hred. split.
      + apply reduce_is_reduction. assumption.
      + apply reduce_is_normal_form. assumption.
Qed.






