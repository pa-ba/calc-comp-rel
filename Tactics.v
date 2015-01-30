Require Export Machine.

Module Calculation (mod : Machine).
Module Meta := MetaTheory mod.
Export Meta.
Require Import List.
Import ListNotations.

Definition Admit {A} : A. admit. Defined.




Ltac destruct_tuple := idtac; match goal with
  | [l : tuple nil |- _ ] => destruct l; destruct_tuple
  | [l : tuple (_ :: _) |- _ ] => destruct l; destruct_tuple
  | _ => idtac
end.



Ltac lift_union t := first [apply bidir_union; first [apply bidir_refl| lift_union t]| t].




Ltac eval_inv ev := let do_inv e H := (first [is_var e; fail 1|inversion H; subst; clear H])
                    in idtac; match goal with
                          | [ H: ev ?e _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ _ _ |- _ ] => do_inv e H
                          | _ => eauto
                        end.


Ltac dist' ev := simpl; intros; subst; ev;
                match goal with
                  | [ H: and _ _ |- _ ] => destruct H; dist' ev
                  | [ H: ex _ |- _ ] => destruct H; dist' ev
                  | [ H: or _ _ |- _ ] => destruct H; dist' ev
                  | [ |- and _ _ ] => split; dist' ev
                  | [ |- _ <-> _ ] => split; dist' ev
                  | [ |- ex _ ] => eexists; dist' ev
                  | [ |- or _ _] => solve [right;dist' ev|left; dist' ev]
                end.

Ltac dist := dist' eauto.



Ltac barred_nostep := apply barred_here; dist.
Ltac barred_step := 
  let h := fresh "barred_step" in
  apply barred_next; [intro; intro h; inversion h; subst; clear h|
                      unfold active;
                        repeat (match goal with
                                  | [T : and _ _ |- _] => destruct T
                                  | [T : ex _ |- _] => destruct T
                                end);
                               eexists;econstructor;eauto].


Ltac barred_onestep := barred_step; barred_nostep.
Ltac barred_tac := solve [barred_onestep | barred_nostep | 
                          barred_step ; solve [barred_nostep | barred_step ; solve [barred_nostep | barred_onestep]]].



Ltac check_exp x y := let h := fresh "check" in assert (h: x = y) by reflexivity; clear h.

Ltac check_rel Bidir Rel := first [check_exp Bidir Rel|
                             fail 2 "wrong goal; expected relation =>> but found" Rel].

Tactic Notation "[]" := apply bidir_refl.


Tactic Notation  (at level 2)    "=" "{?}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Bidir Rel;
                            let h := fresh "rewriting" in 
                            assert(h : forall c, c ∈ e2  <-> c ∈ rhs)
      | _ => fail 1 "goal is not a VM"
    end.



Tactic Notation  (at level 2)    "<|=" "{?}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Bidir Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Bidir e2 rhs) | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    "<|=" "{"tactic(t1) "}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Bidir Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Bidir e2 rhs) by (lift_union t1); 
                 apply (fun x => bidir_trans _ _ _ x h); clear h | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    "<|=" "{{"tactic(t1) "}}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Bidir Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Bidir e2 rhs) by t1; 
                 apply (fun x => bidir_trans _ _ _ x h); clear h | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    "<|=" "{"tactic(t1) "}?"  := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Bidir Rel;
        first [eapply Reach_trans; [idtac|solve[t1]] | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.


Tactic Notation  (at level 2)    "=" "{"tactic(t) "}" constr(e) := 
  <|= {{ apply bidir_refl_iff; dist' t }} e .

Ltac bidir_repeat := first [apply bidir_step' | 
                            first [apply bidir_assoc1 | apply bidir_assoc2| apply bidir_comm]; bidir_repeat
                            ].

Ltac bidir_search := first [apply bidir_step_simp | bidir_repeat].



Tactic Notation  (at level 2)    "<==" "{{" tactic(tb) "}}" "{" tactic(t) "}" constr(e) := 
  <|= {{  bidir_search; intro; destruct_tuple; simpl; intros; [t;tauto | auto;tauto | 
                            first[tb|fail 3 "cannot prove barred side condition"]] }} e.

Tactic Notation  (at level 2)    "<==" "{"tactic(t) "}" constr(e) := 
  <== {{ barred_tac }} {t} e.


Tactic Notation  (at level 2)  "begin" constr(rhs) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs'] => check_rel Bidir Rel; check_exp rhs rhs'
    | _ => fail 1 "rhs does not match"
  end.


End Calculation.
