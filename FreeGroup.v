
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

Definition liftF { T : Type } { G : Group } (f : T -> gtype G) (x : WithInv T) : gtype G
    := match x with
     | Reg _ a => f a
     | ForInv _ a => inve G (f a)
    end.

Definition freegrpmap { T : Type } { G : Group } (f : T -> gtype G) (x : FreeGrpT T) : gtype G
    := freemonmap' (WithInv T) (base G) (liftF f) (forgetGrp x).

Lemma reduction_preserves_map { T : Type } { G : Group }:
    forall (f : T -> gtype G), forall (x y : FreeMonT (WithInv T)),
        Reduction T x y -> freemonmap' _ _ (liftF f) x = freemonmap' _ _ (liftF f) y.
Proof.
    intros f x y Hred. remember x as ex. remember y as ey.
    generalize dependent x. generalize dependent y. induction Hred; intros a Ha b Hb.
    - simpl.
      rewrite (associativity (base G)). destruct (invCorrect G (f x)) as [ _ Hinv ]. rewrite Hinv.
      destruct (emptyCorrect (base G) (freemonmap' _ (base G) (liftF f) tl)) as [ _ Hneutral ].
      rewrite Hneutral. reflexivity.
    - simpl. rewrite (associativity (base G)). destruct (invCorrect G (f x)) as [ Hinv _ ].
      rewrite Hinv. destruct (emptyCorrect (base G) (freemonmap' _ (base G) (liftF f) tl)) as [ _ Hneutral ].
      rewrite Hneutral. reflexivity.
    - simpl. rewrite (IHHred m' (eq_refl m') m (eq_refl m)). reflexivity.
Qed.

Lemma trefl_reduction_preserves_map { T : Type } { G : Group }:
    forall (f : T -> gtype G), forall (x y : FreeMonT (WithInv T)),
        trefl_closure (Reduction T) x y -> freemonmap' _ _ (liftF f) x = freemonmap' _ _ (liftF f) y.
Proof.
    intros f x y Hred. induction Hred; try reflexivity.
    rewrite <- IHHred. apply reduction_preserves_map.
    assumption.
Qed.

Lemma freegrpmap_is_monoid_morphism { T : Type } { G : Group }
        (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq):
    forall (f : T -> gtype G), is_monoid_morphism (FreeGroupMon T deceq deceqC) (base G) (freegrpmap f).
Proof.
    intro f. unfold is_monoid_morphism. split.
    - simpl. reflexivity.
    - intros x y. unfold freegrpmap.
      pose (freemonmap_is_morphism (WithInv T) (base G) (liftF f)) as Hmorph.
      destruct Hmorph as [ _ Hmorph ].
      unfold forgetGrp. simpl. unfold forgetGrp.
      assert (forall (a b : FreeMonT (WithInv T)), freemonmap' _ _ (liftF f) (reduce deceq (append a b))
                = freemonmap' _ _ (liftF f) (op (FreeMonoid.FreeMon (WithInv T)) a b)) as H.
      { intros a b. symmetry. apply trefl_reduction_preserves_map. simpl.
        apply reduce_is_reduction. assumption. }
      rewrite -> H. rewrite Hmorph. reflexivity.
Qed.

Let makeFreeGrpMonMorphism { T : Type } { G : Group } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq)
        (f : T -> gtype G) : MonoidMorphism (FreeGroupMon T deceq deceqC) (base G)
    := mkMonMorphism (FreeGroupMon T deceq deceqC) (base G)
                     (freegrpmap f) (freegrpmap_is_monoid_morphism deceq deceqC f).

Lemma carac_inverse { G : Group } :
    forall (x y : gtype G), gop G x y = unit G -> inve G x = y.
Proof.
    intros x y Hinv. symmetry.
    assert (gop G (inve G x) (gop G x y) = gop G (inve G x) (unit G)) as Heq.
    { rewrite Hinv. reflexivity. }
    destruct (invCorrect G x) as [ _ HinvC ]. pose (associativity (base G) (inve G x) x y) as Hass.
    unfold gop in Heq. rewrite -> Hass in Heq. rewrite -> HinvC in Heq.
    clear HinvC. clear Hass. destruct (emptyCorrect (base G) y) as [ _ Hey ].
    destruct (emptyCorrect (base G) (inve G x)) as [ Hinve _ ].
    rewrite Hey in Heq. unfold unit in Heq. rewrite Hinve in Heq. assumption.
Qed.

Lemma eq_under_f (T T' : Type) :
    forall (f : T -> T'), forall (a b : T), a = b -> f a = f b.
Proof.
    intros f a b Heq. rewrite Heq. reflexivity.
Qed.

Lemma freegrpmap_is_group_morphism { T : Type } { G : Group }
        (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq):
    forall (f : T -> gtype G),
        is_group_morphism (FreeGroup T deceq deceqC) G (makeFreeGrpMonMorphism deceq deceqC f).
Proof.
    intro f. unfold is_group_morphism. intro x. simpl.
    symmetry. apply carac_inverse.
    destruct (freegrpmap_is_monoid_morphism deceq deceqC f) as [ Hunit Hop ].
    unfold gop. rewrite <- Hop. unfold unit. rewrite <- Hunit. apply eq_under_f.
    destruct (inverse_correct deceq deceqC x) as [ Hleft Hright ]. assumption.
Qed.

Let makeFreeGrpMorphism { T : Type } { G : Group } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq)
        (f : T -> gtype G) : GroupMorphism (FreeGroup T deceq deceqC) G
    := mkGrpMor (FreeGroup T deceq deceqC) G
                (makeFreeGrpMonMorphism deceq deceqC f)
                (freegrpmap_is_group_morphism deceq deceqC f).

Let applyOnGrpBasis { T : Type } { G : Group } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq)
        (m : (FreeGrpT T) -> gtype G) (x : T) : gtype G
    := m (makeGrp deceq deceqC (App _ (Reg _ x) (Empty _))).

Theorem free_group_is_free_group { T : Type } (deceq : T -> T -> bool) (deceqC : DecEqCorrect deceq) :
    is_free_group_over T (FreeGroup T deceq deceqC).
Proof.
    unfold is_free_group_over. intro G.
    exists (makeFreeGrpMorphism deceq deceqC). exists (applyOnGrpBasis deceq deceqC). split.

    - intro f. apply functionnal_extensionality. intro x.
      unfold applyOnGrpBasis. unfold makeFreeGrpMorphism. unfold makeGrp.
      unfold makeFreeGrpMonMorphism. unfold grpmor. simpl. unfold freegrpmap. simpl.
      destruct (emptyCorrect (base G) (f x)) as [ Hempty _ ]. assumption.

      (* TODO finish proof *)
    - intro h. apply functionnal_extensionality. intro x.
      unfold makeFreeGrpMorphism. unfold applyOnGrpBasis. unfold makeFreeGrpMonMorphism.
      unfold makeGrp. unfold freegrpmap. unfold grpmor. unfold forgetGrp. simpl.
      remember (elem T x) as e. generalize dependent x. induction e; intro a; simpl.
      + intro Heq.

    





