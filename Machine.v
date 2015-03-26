Module Type Machine.
Parameter Conf : Type.
Parameter Rel : Conf -> Conf -> Prop.
End Machine.

Module MetaTheory (mod : Machine).
Import mod.
Require Import List.
Import ListNotations.
Require Import Relations.

Infix "==>" := Rel(at level 80, no associativity).

Definition trc := clos_refl_trans Conf Rel.

Infix "=>>" := trc (at level 80, no associativity).


Lemma trc_refl c : c =>> c.
Proof. apply rt_refl. Qed.

Lemma trc_step c1 c2 : c1 ==> c2 -> c1 =>> c2.
Proof. apply rt_step. Qed.

Lemma trc_step_trans c1 c2 c3 : c1 =>> c2 -> c2 ==> c3 -> c1 =>> c3.
Proof. intros. eapply rt_trans; eauto using rt_step. Qed.

Lemma trc_step_trans' c1 c2 c3 : c1 ==> c2 -> c2 =>> c3 -> c1 =>> c3.
Proof. intros. eapply rt_trans; eauto using rt_step. Qed.

Lemma trc_trans c1 c2 c3 : c1 =>> c2 -> c2 =>> c3 -> c1 =>> c3.
Proof. apply rt_trans. Qed.


Hint Resolve trc_step trc_step_trans.
Hint Immediate trc_refl.

Lemma trc_ind' :
forall P : Conf -> Conf -> Prop,
(forall c : Conf, P c c) ->
(forall c1 c2 c3 : Conf, c1 ==> c2 -> c2 =>> c3 -> P c2 c3 -> P c1 c3) ->
forall c c0 : Conf, c =>> c0 -> P c c0.
Proof. 
  intros X Y Z c1 c2 S. unfold trc in S. rewrite -> clos_rt_rt1n_iff in S.
  induction S; eauto. rewrite <- clos_rt_rt1n_iff in S. eauto.
Qed.

Fixpoint tuple (ts : list Type) : Type :=
  match ts with
    | []       => unit
    | t :: ts' => (t * tuple ts')%type
  end.


Inductive SetCom : list Type -> Type :=
| BaseSet : Conf -> Prop -> SetCom nil
| ExSet {t ts} : (t -> SetCom ts) -> SetCom (t :: ts).

Definition funtail {t ts A} (x : t) (f : forall (args : tuple (t :: ts)),  A args) 
: forall (args : tuple ts), A (x, args) :=
  fun xs => f (x, xs).


Fixpoint mkSetCom {ts} (C : tuple ts -> Conf) (P : tuple ts -> Prop) : SetCom ts :=
  match ts return (tuple ts -> Conf) -> (tuple ts -> Prop) -> SetCom ts with
    | nil => fun C P => BaseSet (C tt) (P tt)
    | t :: ts' => fun C P => @ExSet t ts'  (fun x => @mkSetCom ts' (funtail x C) (funtail x P))
  end C P.



Fixpoint getConf {ts} (S : SetCom ts) : tuple ts -> Conf :=
  match S with
    | BaseSet C P => fun xs => C
    | ExSet _ _ ex => fun xs =>  let (x, xs') := xs in  getConf (ex x) xs'
  end.

Fixpoint getProp {ts} (S : SetCom ts) : tuple ts -> Prop :=
  match S with
    | BaseSet C P => fun xs => P
    | ExSet _ _ ex => fun xs => let (x, xs') := xs in getProp (ex x) xs'
  end.

Lemma getConf_sound ts (C : tuple ts -> Conf) P x : getConf (mkSetCom C P) x = C x.
Proof.
  intros. induction ts; destruct x. reflexivity. simpl. apply (IHts (funtail a0 C)).
Qed.


Lemma getProp_sound ts (C : tuple ts -> Conf) P x : getProp (mkSetCom C P) x = P x.
Proof.
  intros. induction ts;destruct x. reflexivity. simpl. apply (IHts _ (funtail a0 P)).
Qed.

Fixpoint  SetComElem  {ts} (C : Conf) (S : SetCom ts) : Prop :=
  match S with
      | BaseSet C' P => C' = C /\ P 
      | ExSet _ _ e => exists x, SetComElem C (e x)
  end.

Lemma set_com_elem {ts} (C : Conf) (S : SetCom ts) : 
  SetComElem C S <-> exists xs, getConf S xs = C /\ getProp S xs.
Proof.
  split; intros. 
  * induction S.
    - exists tt. assumption.

    - simpl in H. destruct H. apply H0 in H.
      decompose [ex and] H.  exists (x, x0). auto.
  * induction S.
    - decompose [ex and] H. simpl in *. tauto.
    - decompose [ex and] H. simpl. destruct x.
      exists t0. apply H0. exists t1. tauto.
Qed.


Inductive ConfSet : Type :=
  | Sing {ts} : SetCom ts -> ConfSet
  | Empty : ConfSet
  | Union : ConfSet -> ConfSet -> ConfSet.


Fixpoint ConfElem (C : Conf) (S : ConfSet) : Prop :=
  match S with
    | Sing _ s => SetComElem C s
    | Empty => False
    | Union S1 S2 => ConfElem C S1 \/  ConfElem C S2
  end.

Notation "{| C | P |}" := (Sing (mkSetCom C P)) (at level 70, no associativity).
Infix "∈" := ConfElem (at level 80, no associativity).
Infix "∪" := Union (at level 76, left associativity).

Notation "S ⊆ T" := (forall x, x ∈ S -> x ∈ T) (at level 80, no associativity).
Notation "S == T" := (S ⊆ T /\ T ⊆ S) (at level 80, no associativity).


Lemma mkSetComCompl' {ts} (S : SetCom ts) : {| getConf S | getProp S |} == Sing S.
Proof.
  simpl. split; intros; induction S; auto; simpl in *; destruct H; eexists; apply H0; apply H.
Qed.

Lemma sing_set_elem {ts} (C' : Conf) (C : tuple ts -> Conf) P :
  C' ∈ {| C | P |} <-> exists xs, C xs = C' /\ P xs.
Proof.
  simpl. rewrite set_com_elem. split; intro H; decompose [ex and] H; eexists; 
  rewrite getConf_sound in *; rewrite getProp_sound in *; split; eassumption.
Qed.




Notation "{ x .. y , C | P }" := (Sing (ExSet ( fun x =>  .. (ExSet (fun y => BaseSet C P)) ..  )))
(at level 70, x binder, y binder, no associativity).


Notation "{, C | P }" := (Sing (BaseSet C  P))
(at level 70, no associativity).



Lemma union_incll S T : S ⊆ S ∪ T.
Proof. simpl. auto. Qed.

Lemma union_inclr S T : T ⊆ S ∪ T.
Proof. simpl. auto. Qed.

Hint Resolve union_incll union_inclr.

Definition active (c : Conf) := exists c', c ==> c'.

(* normal form, an irreducible configuration *)

Definition nf (c : Conf) := forall c', ~ (c ==> c').

Hint Unfold active nf.


Lemma nf_trc c c' : nf c -> c =>> c' -> c = c'.
Proof.
  intros R S. destruct S using trc_ind'. reflexivity. autounfold in *. apply R in H. contradiction.
Qed.

Inductive barred (P : ConfSet) : Conf -> Prop :=
| barred_here c : c ∈ P -> barred P c
| barred_next c : (forall c', c ==> c' -> barred P c') -> active c -> barred P c.

Notation "C <| P" := (barred P C) (at level 80, no associativity).



Lemma barred_if c (P Q : ConfSet) : c <| P -> P ⊆ Q -> c <| Q.
Proof.
  intros. induction H. apply barred_here. auto.
  apply barred_next; assumption.
 Qed.

Definition NF (C : ConfSet) := forall c, c ∈ C -> nf c.

Proposition barred_closed c1 c2 P : 
  NF P -> c1 <| P -> c1 =>> c2 
  -> exists c3, c2 =>> c3 /\ c3 ∈ P.
Proof.
  intros A B S. generalize dependent B. induction S using trc_ind';intros.
  - induction B.
    + eauto.
    + destruct H1. specialize (H0 _ H1). decompose [ex and] H0. eauto using trc_step_trans'.
  - induction B.
    + apply A in H0. autounfold in *. apply H0 in H. contradiction.
    + eauto.
Qed.

Definition Barred (P Q : ConfSet) : Prop := forall c, c ∈ P -> c <| Q.
Hint Unfold Barred.

Infix "<<|" := Barred (at level 80, no associativity).

Proposition Barred_closed c1 c2 P C: 
  NF P -> C <<| P -> c1 ∈ C -> c1 =>> c2 
  -> exists c3, c2 =>> c3 /\ c3 ∈ P.
Proof.
  intros. eapply barred_closed;eauto.
Qed.


Lemma Barred_refl_if P Q : P ⊆ Q ->  P <<| Q.
Proof.
  unfold Barred. intros. apply barred_here. auto.
Qed.

Lemma Barred_if P P' Q Q' : P <<| Q -> P' ⊆ P -> Q ⊆ Q' -> P' <<| Q'.
Proof. unfold Barred. intros. eapply barred_if; eauto. Qed.


Lemma Barred_trans P Q R : P <<| Q -> Q <<| R -> P <<| R.
Proof.
  intros B1 B2.
  unfold Barred in *.
  intros. apply B1 in H. clear B1. 

  induction H. apply B2. assumption.
  apply barred_next. intros. apply H0. assumption. assumption.
Qed.

Lemma Barred_union_left P PQ Q : P <<| PQ -> Q <<| PQ -> P ∪ Q <<| PQ.
Proof.
  unfold Barred. intros. auto. simpl in H1. destruct H1; auto.
Qed.

Lemma Barred_union P P' Q Q' : P <<| P' -> Q <<| Q' -> P ∪ Q <<| P' ∪ Q'.
Proof.
  intros. apply Barred_union_left; eauto using Barred_if.
Qed.


Definition Reach (P Q : ConfSet) : Prop := forall c2, c2 ∈ Q -> exists c1, c1 ∈ P /\ c1 =>> c2.
Hint Unfold Reach.


Notation "P >>> Q" := (Reach P Q) (at level 80, no associativity).

Lemma Reach_refl_if P Q : Q ⊆ P -> P >>> Q.
Proof.
  unfold Reach. intros. exists c2.  split. auto. apply trc_refl.
Qed.


Lemma Reach_if P P' Q Q' : P >>> Q -> P ⊆ P' -> Q' ⊆ Q -> P' >>> Q'.
Proof.
  unfold Reach. intros. apply H1 in H2. apply H in H2. decompose [ex and] H2. eexists. split; eauto.
Qed.

Lemma Reach_trans P Q R : P >>> Q -> Q >>> R -> P >>> R.
Proof.
  unfold Reach. intros. apply H0 in H1. decompose [ex and] H1.
  apply H in H3. decompose [ex and] H3. eexists. split. eassumption. 
  eapply trc_trans; eassumption.
Qed.

Lemma Reach_union P P' Q Q' : P >>> P' -> Q >>> Q' -> P ∪ Q >>> P' ∪ Q'.
Proof.
  unfold Reach. intros. auto. destruct H1; [apply H in H1| apply H0 in H1];
  decompose [ex and] H1; eauto.
Qed.


Definition Bidir P Q := P >>> Q /\ P <<| Q.
Hint Unfold Reach.


Notation "P =|> Q" := (Bidir P Q) (at level 80, no associativity).

Lemma bidir_refl_iff P Q : P == Q -> P =|> Q.
Proof. split;[apply Reach_refl_if| apply Barred_refl_if]; tauto. Qed.


Lemma bidir_iff P P' Q Q' : P =|> Q -> P == P' -> Q == Q' -> P' =|> Q'.
Proof. 
  intros. destruct H. split; [eapply Reach_if| eapply Barred_if]; eauto; try tauto.
Qed.

Lemma bidir_refl P :  P =|> P.
Proof. apply bidir_refl_iff. auto. Qed.

Lemma bidir_trans P Q R : P =|> Q -> Q =|> R -> P =|> R.
Proof.
  unfold Bidir. intros. destruct H. destruct H0.
  split. eapply Reach_trans; eassumption. eapply Barred_trans; eassumption.
Qed.

Lemma bidir_union P P' Q Q' : P =|> P' -> Q =|> Q' -> P ∪ Q =|> P' ∪ Q'.
Proof.
  unfold Bidir. intros. split. apply Reach_union; tauto. apply Barred_union; tauto.
Qed.

Lemma Reach_step ts (C C' : tuple ts -> Conf) (P P' : tuple ts -> Prop) T: 
  (forall x, P' x -> C x  ==> C' x) -> (forall x, P' x -> P x) ->  {| C | P |} ∪ T >>> {| C' | P' |} ∪ T.
Proof.
  unfold Reach. intros. destruct H1.
  * rewrite sing_set_elem in H1. decompose [ex and] H1. subst. exists (C x). split. 
    - left. rewrite sing_set_elem. exists x. auto.
    - apply trc_step. auto.
  * exists c2. split; auto.
Qed.


Lemma Reach_barred ts (C C' : tuple ts -> Conf) (P P' : tuple ts -> Prop) T: 
  (forall x, P x -> C x  <| {| C' | P' |} ∪ T) ->  {| C | P |} ∪ T <<| {| C' | P' |} ∪ T. 
Proof.
  unfold Barred. intros. destruct H0. 
  * rewrite sing_set_elem in H0. decompose [ex and] H0. subst. auto.
  * left. right. auto.
Qed.

Theorem bidir_step  ts (C C' : tuple ts -> Conf) (P P' : tuple ts -> Prop) T:
  (forall x, P' x -> C x  ==> C' x) -> (forall x, P' x -> P x) -> (forall x, P x -> C x  <| {| C' | P' |} ∪ T)
  ->  {| C | P |} ∪ T =|> {| C' | P' |} ∪ T.
Proof.
  unfold Bidir. intros. auto using Reach_step, Reach_barred.
Qed.


(* The above lemma cannot be used directly in a proof
calculation. Therefore, we reformulat it using [getProp] and [getConf]
instead of the [ {| C | P |} ] construction. *)

Lemma union_sub_left S1 S2 T : S1 ⊆ S2 -> S1 ∪ T ⊆ S2 ∪ T .
Proof.
  intros. simpl in *. destruct H0; auto.
Qed.

Lemma union_eq_left S1 S2 T : S1 == S2 -> S1 ∪ T == S2 ∪ T .
Proof.
  simpl in *; split;intros; destruct H0; solve [left; destruct H; auto| right; destruct H; auto].
Qed.

Lemma union_sub_eq S1 S2 : S1 == S2 -> S1 ⊆ S2 .
Proof.
  intros. simpl in *. destruct H. auto.
Qed.

Lemma set_eq_ref S T : S == T -> T == S.
Proof.
  intros. destruct H. split; auto.
Qed.


Corollary bidir_step' ts (S S' : SetCom ts) T :
  (forall x, getProp S' x -> getConf S x  ==> getConf S' x) -> 
  (forall x, getProp S' x -> getProp S x) -> 
  (forall x, getProp S x -> getConf S x  <| Sing S' ∪ T) ->
  Sing S ∪ T =|> Sing S' ∪ T.
Proof.
  intros. 
  assert ({| getConf S | getProp S |} ∪ T =|> {| getConf S' | getProp S' |} ∪ T).
  apply bidir_step; auto. intros. eapply barred_if. apply H1. auto. apply union_sub_left.
  apply union_sub_eq. apply set_eq_ref. apply mkSetComCompl'.
  eapply bidir_iff. eassumption. 
  apply union_eq_left. apply mkSetComCompl'.
  apply union_eq_left. apply mkSetComCompl'.
Qed.



Ltac bidir_iff := intros; eapply bidir_iff; eauto; simpl; tauto.

(* The following lemmas are for guiding the proof search *)

Lemma bidir_step_simp ts (S S' : SetCom ts) :
  (forall x, getProp S' x -> getConf S x  ==> getConf S' x) -> 
  (forall x, getProp S' x -> getProp S x) -> 
  (forall x, getProp S x -> getConf S x  <| Sing S') ->
  Sing S =|> Sing S'.
Proof.
  intros. assert (Sing S ∪ Empty =|> Sing S' ∪ Empty).
  apply bidir_step'; auto; intros. eapply barred_if. eauto. simpl; tauto. bidir_iff.
Qed.

Lemma bidir_assoc1 S1 S2 S T : S1 ∪ (S ∪ T) =|> S2 ∪ (S ∪ T) -> (S1 ∪ S) ∪ T =|> (S2 ∪ S) ∪ T.
Proof. bidir_iff. Qed.

Lemma bidir_assoc2 S1 S2 S T : S1 ∪ (S ∪ T) =|> S2 ∪ (S ∪ T) -> (S ∪ S1) ∪ T =|> (S ∪ S2) ∪ T.
Proof. bidir_iff. Qed.

Lemma bidir_comm S1 S2 T : S1 ∪ T =|> S2 ∪ T -> T ∪ S1 =|> T ∪ S2.
Proof. bidir_iff. Qed.

End MetaTheory.
