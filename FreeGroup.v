
(*
 *  _____                 ____                       
 * |  ___| __ ___  ___   / ___|_ __ ___  _   _ _ __  
 * | |_ | '__/ _ \/ _ \ | |  _| '__/ _ \| | | | '_ \ 
 * |  _|| | |  __/  __/ | |_| | | | (_) | |_| | |_) |
 * |_|  |_|  \___|\___|  \____|_|  \___/ \__,_| .__/ 
 *                                            |_|    
 *)

Require Import FreeMonoid.
Require Import StrongNormalisation.
Require Import Confluence.
Require Import RedMorphism.
Require Import NormalForm.

Record Group : Type := mkGrp {
    base : Monoid;
    inve  : type base -> type base;
    invCorrect : forall (a : type base), op base a (inve a) = empty base /\ op base (inve a) a = empty base;
}.

Definition gtype (g : Group) : Type := type (base g).
Definition gop (g : Group) : gtype g -> gtype g -> gtype g := op (base g).
Definition unit (g : Group) : gtype g := empty (base g).

Definition is_group_morphism (g g' : Group) (m : MonoidMorphism (base g) (base g')) : Prop :=
    forall (x : gtype g), monmor (base g) (base g') m (inve g x) = inve g' (monmor (base g) (base g') m x).

Record GroupMorphism (g g' : Group) : Type := mkGrpMor {
    morbase : MonoidMorphism (base g) (base g');
    morbase_correct : is_group_morphism g g' morbase;
}.

Definition grpmor { g g' : Group } (m : GroupMorphism g g') : gtype g -> gtype g'
    := monmor (base g) (base g') (morbase g g' m).

Definition is_free_group_over (T : Type) (G : Group) : Prop :=
    forall (G' : Group),
        exists (F : (T -> gtype G') -> GroupMorphism G G'),
        exists (H : (gtype G -> gtype G') -> (T -> gtype G')),
             (forall (f : T -> gtype G'), H (grpmor (F f)) = f)
          /\ (forall (h : GroupMorphism G G'), grpmor (F (H (grpmor h))) = grpmor h).

Record FreeGrpT (T : Type) : Type := mkFreeGrp {
    elem       : FreeMonT (WithInv T);
    elemNormal : is_stable elem;
}.

Definition forgetGrp { T : Type } : FreeGrpT T -> FreeMonT (WithInv T) := elem T.

Definition makeGrp { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq)
                                (x : FreeMonT (WithInv T))
                                : FreeGrpT T
    := mkFreeGrp T (reduce deceq x) (reduce_is_stable deceq deceqC x).

Definition freeGrpOp { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq)
                                  (x y : FreeGrpT T)
                                  : FreeGrpT T
    := makeGrp deceq deceqC (append (forgetGrp x) (forgetGrp y)).

Definition freeGrpNeutral { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) : FreeGrpT T
    := makeGrp deceq deceqC (Empty (WithInv T)).

Theorem reduction_out_append { T : Type } :
    forall (a b c d e : FreeMonT (WithInv T)),
        trefl_closure (Reduction T) a b -> trefl_closure (Reduction T) c d
        -> trefl_closure (Reduction T) (append b d) e
        -> trefl_closure (Reduction T) (append a c) e.
Proof.
    intros a b c d e Hab Hcd Happend.
    apply (trefl_closure_append _ (Reduction T) _ (append b d)); try assumption.
    apply reduction_compatible_append; assumption.
Qed.

Lemma reduce_push { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a b : FreeMonT (WithInv T)), trefl_closure (Reduction T) a b -> reduce deceq a = reduce deceq b.
Proof.
    intros a b Hred. symmetry.
    apply (reduce_is_unique_normal_form deceq deceqC a (reduce deceq b)).
    unfold normal_form_of. split; try (apply reduce_is_normal_form; assumption).
    apply (trefl_closure_append _ (Reduction T) _ b); try assumption.
    apply reduce_is_reduction. assumption.
Qed.

Theorem push_reduce_out_l { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a b : FreeMonT (WithInv T)),
        reduce deceq (append (reduce deceq a) b) = reduce deceq (append a b).
Proof.
    intros a b. symmetry. apply (reduce_push deceq deceqC).
    apply (reduction_out_append _ (reduce deceq a) _ b); try constructor.
    apply reduce_is_reduction. assumption.
Qed.

Theorem push_reduce_out_r { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a b : FreeMonT (WithInv T)),
        reduce deceq (append a (reduce deceq b)) = reduce deceq (append a b).
Proof.
    intros a b. symmetry. apply (reduce_push deceq deceqC).
    apply (reduction_out_append _ a _ (reduce deceq b)); try constructor.
    apply reduce_is_reduction. assumption.
Qed.

Theorem push_reduce_out { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a b : FreeMonT (WithInv T)),
        reduce deceq (append (reduce deceq a) (reduce deceq b)) = reduce deceq (append a b).
Proof.
    intros a b. symmetry. apply (reduce_push deceq deceqC).
    apply (reduction_out_append _ (reduce deceq a) _ (reduce deceq b));
        try (apply reduce_is_reduction; assumption).
    constructor.
Qed.

Theorem freeGrpOp_assoc' { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a b c : FreeGrpT T),
        elem T (freeGrpOp deceq deceqC a (freeGrpOp deceq deceqC b c))
            = elem T (freeGrpOp deceq deceqC (freeGrpOp deceq deceqC a b) c).
Proof.
    intros a b c. unfold freeGrpOp. unfold makeGrp. simpl.
    rewrite -> (push_reduce_out_l deceq deceqC).
    rewrite -> (push_reduce_out_r deceq deceqC).
    rewrite append_associative. reflexivity.
Qed.

Lemma reduce_useless_on_forgetGrp { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a : FreeGrpT T), reduce deceq (forgetGrp a) = elem T a.
Proof.
    intro a. symmetry. apply (reduce_is_unique_normal_form deceq deceqC).
    unfold normal_form_of. split; try constructor.
    apply stable_is_normal_form. apply (elemNormal T a).
Qed.

Theorem freeGrpOp_neutral' { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a : FreeGrpT T),
        elem T (freeGrpOp deceq deceqC a (freeGrpNeutral deceq deceqC)) = elem T a
     /\ elem T (freeGrpOp deceq deceqC (freeGrpNeutral deceq deceqC) a) = elem T a.
Proof.
    intro a. unfold freeGrpOp. unfold makeGrp. simpl.
    split; try (apply reduce_useless_on_forgetGrp; assumption).
    destruct (append_empty _ (forgetGrp a)) as [ HappE _ ]. rewrite HappE.
    apply reduce_useless_on_forgetGrp. assumption.
Qed.

Axiom eq_freegrp: forall (T : Type), forall (a b : FreeGrpT T), elem T a = elem T b -> a = b.

Theorem  freeGrpOp_assoc { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a b c : FreeGrpT T),
        freeGrpOp deceq deceqC a (freeGrpOp deceq deceqC b c)
            = freeGrpOp deceq deceqC (freeGrpOp deceq deceqC a b) c.
Proof.
    intros a b c. apply eq_freegrp. apply freeGrpOp_assoc'.
Qed.

Theorem freeGrpOp_neutral { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (a : FreeGrpT T),
        freeGrpOp deceq deceqC a (freeGrpNeutral deceq deceqC) = a
     /\ freeGrpOp deceq deceqC (freeGrpNeutral deceq deceqC) a = a.
Proof.
    intro a. destruct (freeGrpOp_neutral' deceq deceqC a). split; apply eq_freegrp; assumption.
Qed.

Let FreeGroupMon (T : Type) (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) : Monoid
    := mkMon (FreeGrpT T) (freeGrpOp deceq deceqC) (freeGrpNeutral deceq deceqC)
             (freeGrpOp_neutral deceq deceqC) (freeGrpOp_assoc deceq deceqC).

Fixpoint inverse' {T : Type} (x y : FreeMonT (WithInv T)) : FreeMonT (WithInv T)
    := match x with
     | App _ a a' => inverse' a' (App _ (inv a) y)
     | Empty _    => y
    end.

Definition inverse {T : Type} (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq)
                 (x : FreeGrpT T) : FreeGrpT T
    := makeGrp deceq deceqC (inverse' (elem T x) (Empty _)).

Lemma semantics_inverse' { T : Type }:
    forall (x y : FreeMonT (WithInv T)), inverse' x y = append (inverse' x (Empty _)) y.
Proof.
    intros x. induction x.
    - intros y. simpl. rewrite -> (IHx (App _ (inv t) (Empty _))).
      rewrite -> (IHx (App _ (inv t) y)). rewrite <- append_associative.
      simpl. reflexivity.
    - simpl. intro y. reflexivity.
Qed.

Lemma inverse_correct_r' { T : Type } :
    forall (x : FreeMonT (WithInv T)), trefl_closure (Reduction T) (append x (inverse' x (Empty _)))
                                                                   (Empty _).
Proof.
    intros x. induction x; try constructor.
    simpl inverse'. rewrite -> semantics_inverse'.
    apply (trefl_closure_append _ (Reduction T) _ (App _ t (App _ (inv t) (Empty _)))).
    - simpl. apply trefl_ctx_red. rewrite append_associative.
      assert ((App _ (inv t) (Empty _)) = append (Empty _) (App _ (inv t) (Empty _))) by reflexivity.
      rewrite H. clear H. apply reduction_compatible_append; try assumption.
      simpl. constructor.
    - apply (TransClosure (Reduction T) _ (Empty _)); try constructor.
      apply inv_red. reflexivity.
Qed.

Lemma inverse_correct_l' { T : Type } :
    forall (x : FreeMonT (WithInv T)), trefl_closure (Reduction T) (append (inverse' x (Empty _)) x)
                                                                   (Empty _).
Proof.
    intros x. induction x; try constructor.
    simpl inverse'. rewrite -> semantics_inverse'. rewrite <- append_associative.
    apply (trefl_closure_append _ (Reduction T) _ (append (inverse' x (Empty _)) x) ); try assumption.
    apply reduction_compatible_append; try constructor.
    apply (TransClosure _ _ x); try constructor. apply inv_red. apply inv_invo.
Qed.

Theorem inverse_correct_r { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (x : FreeGrpT T),
        elem T (freeGrpOp deceq deceqC x (inverse deceq deceqC x)) = elem T (freeGrpNeutral deceq deceqC).
Proof.
    intro x. unfold inverse. unfold freeGrpOp. unfold forgetGrp. unfold makeGrp. simpl.
    rewrite push_reduce_out_r; try assumption. symmetry. apply reduce_is_unique_normal_form; try assumption.
    unfold normal_form_of. split.
    - apply inverse_correct_r'.
    - apply stable_is_normal_form. constructor.
Qed.

Theorem inverse_correct_l { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (x : FreeGrpT T),
        elem T (freeGrpOp deceq deceqC (inverse deceq deceqC x) x) = elem T (freeGrpNeutral deceq deceqC).
Proof.
    intro x. simpl. rewrite push_reduce_out_l; try assumption. symmetry.
    apply reduce_is_unique_normal_form; try assumption.
    unfold normal_form_of. split.
    - apply inverse_correct_l'.
    - apply stable_is_normal_form. constructor.
Qed.

Theorem inverse_correct { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    forall (x : FreeGrpT T),
        freeGrpOp deceq deceqC x (inverse deceq deceqC x) = freeGrpNeutral deceq deceqC
     /\ freeGrpOp deceq deceqC (inverse deceq deceqC x) x = freeGrpNeutral deceq deceqC.
Proof.
    intro x. split.
    - apply eq_freegrp. apply inverse_correct_r.
    - apply eq_freegrp. apply inverse_correct_l.
Qed.

Let FreeGroup (T : Type) (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq)
    := mkGrp (FreeGroupMon T deceq deceqC) (inverse deceq deceqC) (inverse_correct deceq deceqC).





