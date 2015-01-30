(* Calculation of the simple arithmetic language. *)
Require Import List.
Require Import Tactics.

Require Import ZArith.
Local Open Scope Z_scope.

Inductive Expr : Set :=  Val (n : Z) | Add (x y : Expr).

Reserved Notation "x ⇓ y" (at level 70, no associativity).

Inductive eval : Expr -> Z -> Prop :=
| eval_val n : Val n ⇓ n
| eval_add x y m n : x ⇓ m -> y ⇓ n -> Add x y ⇓ (m + n)
where "x ⇓ y" := (eval x y).

Hint Constructors eval.

Inductive Instr : Set := PUSH (n : Z) | ADD.

Definition Code := list Instr.

Import ListNotations.


Fixpoint comp (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n :: c
    | Add x y => comp x (comp y (ADD :: c))
  end.

Definition Stack : Set := list Z.

Definition Conf : Set := prod Code  Stack.

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : (PUSH n :: c , s) ==> (c , n :: s)
| vm_add c s m n : (ADD :: c, m :: n :: s) ==> (c, (n + m) :: s)
where "x ==> y" := (VM x y).

Hint Constructors VM.

(* Boilerplate to import calculation tactics *)
Module VM <: Machine.
Definition Conf := Conf.
Definition Rel := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

Ltac by_eval := eval_inv (eval).

Theorem spec e P c :  { s, (comp e c, s) | P s} =|>
                        { s n, (c , n :: s) | (e ⇓ n) /\ P s}.
Proof.
  intros.
  generalize dependent c.
  generalize dependent P.
  induction e; intros.

  begin
    ({ s n', (c, n' :: s) | (Val n ⇓ n') /\ P s}).
  = {by_eval}
    ({ s, (c, n :: s) | P s}) .
  <== {apply vm_push}
    ({ s, (PUSH n :: c, s) | P s }) .
  [].

  begin
  ({s n, (c, n :: s) | Add e1 e2 ⇓ n /\ P s }) .
  = { by_eval }
  ({s n m, (c, (n + m) :: s) | e1 ⇓ n /\ e2 ⇓ m /\ P s}) .
  <== { apply vm_add }
  ({ s n m, (ADD :: c, m :: n :: s) | e1 ⇓ n /\ e2 ⇓ m /\ P s}).
  = { eauto }
  ({s' m, (ADD :: c, m :: s') | e2 ⇓ m /\ (exists s n, e1 ⇓ n /\ s' = n :: s /\ P s)} ).
  <|= { apply IHe2 }
  ({s, (comp e2 (ADD :: c), s) | exists s' n, e1 ⇓ n /\ s = n :: s' /\ P s'}).
  = { eauto }
  ({s n, (comp e2 (ADD :: c),  n :: s) | e1 ⇓ n /\ P s }).
  <|= { apply IHe1 }
  ({s, (comp e1 (comp e2 (ADD :: c)),  s) | P s }).
  [].
Qed.