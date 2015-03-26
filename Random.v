(* Calculation of the simple arithmetic language + random. *)
Require Import List.
Require Import Tactics.


Require Import ZArith.
Import Z.
Local Open Scope Z_scope.

Inductive Expr : Set :=  Val (n : Z) | Add (x y : Expr) | Rnd (x : Expr).

Reserved Notation "x ⇓ y" (at level 70, no associativity).

Inductive eval : Expr -> Z -> Prop :=
| eval_val n : Val n ⇓ n
| eval_add x y m n : x ⇓ m -> y ⇓ n -> Add x y ⇓ (m + n)
| eval_rnd x n m : x ⇓ n -> 0 <= m <= abs n -> Rnd x ⇓ m
where "x ⇓ y" := (eval x y).

Hint Constructors eval.

Inductive Instr : Set := PUSH (n : Z) | ADD | RND.

Definition Code := list Instr.

Import ListNotations.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n :: c
    | Add x y => comp' x (comp' y (ADD :: c))
    | Rnd x => comp' x (RND :: c)
  end.

Definition comp (e : Expr) : Code := comp' e nil.

Example comp_ex : comp (Add (Rnd (Val 5)) (Val 42)) = [PUSH 5; RND; PUSH 42; ADD].
reflexivity. Qed.

Example comp_ex2 : comp (Rnd (Val 0)) = [PUSH 0; RND].
reflexivity. Qed.

Definition Stack : Set := list Z.

Inductive Conf : Set := conf (c : Code) (s : Stack).

Notation "⟨ c , s ⟩" := (conf c s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : ⟨PUSH n :: c , s⟩ ==> ⟨c , n :: s⟩
| vm_add c s m n : ⟨ADD :: c, m :: n :: s⟩ ==> ⟨c, (n + m) :: s⟩
| vm_rnd c s n m : 0 <= m <= abs n -> ⟨RND :: c, n :: s⟩ ==> ⟨c, m :: s⟩
where "x ==> y" := (VM x y).

(* If we would not have the non-stuckness side condition for <|, we
would be able to prove the compiler "correct" even if we would add the
following additional rule for the VM:

vm_push' n c s : ⟨PUSH n :: c , s⟩ ==> ⟨ADD :: c , []⟩


 *)


Hint Constructors VM.

(* Boilerplate to import calculation tactics *)
Module VM <: Machine.
Definition Conf := Conf.
Definition Rel := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

Ltac by_eval := eval_inv (eval).

Lemma rnd_exists (n : Z) : (exists m, 0 <= m < n) <-> 0 < n.
Proof.
  split. intros. decompose [ex and] H. omega.
  intros. exists 0. omega.
Qed.


Theorem spec : forall e P c,
  { s, ⟨comp' e c, s⟩ | P s} =|> { s n, ⟨c , n :: s⟩ | (e ⇓ n) /\ P s}.
Proof.
  induction e;intros.

  begin
    ({ s n', ⟨c, n' :: s⟩ | Val n ⇓ n' /\ P s}).
  = {by_eval}
    ({ s, ⟨c, n :: s⟩ | P s}) .
  <== { apply vm_push }
    ({ s, ⟨PUSH n :: c, s⟩ | P s }) .
  [].

  begin
  ({s n, ⟨c, n :: s⟩ | Add e1 e2 ⇓ n /\ P s }) .
  = { by_eval }
  ({s n m, ⟨c, (n + m) :: s⟩ | e1 ⇓ n /\ e2 ⇓ m /\ P s}) .
  <== { apply vm_add }
  ({ s n m, ⟨ADD :: c, m :: n :: s⟩ | e1 ⇓ n /\ e2 ⇓ m /\ P s}).
  = { eauto }
  ({s' m, ⟨ADD :: c, m :: s'⟩ | e2 ⇓ m /\ (exists s n, e1 ⇓ n /\ s' = n :: s /\ P s)} ).
  <|= { apply IHe2 }
  ({s, ⟨comp' e2 (ADD :: c), s⟩ | exists s' n, e1 ⇓ n /\ s = n :: s' /\ P s'}).
  = { eauto }
  ({s n, ⟨comp' e2 (ADD :: c),  n :: s⟩ | e1 ⇓ n /\ P s }).
  <|= { apply IHe1 }
  ({s, ⟨comp' e1 (comp' e2 (ADD :: c)),  s⟩ | P s }).
  [].

  begin
  ({s m, ⟨c, m :: s⟩ | Rnd e ⇓ m /\ P s }) .
  = { by_eval }
  ({s m n, ⟨c, m :: s⟩ | e ⇓ n /\ 0 <= m <= abs n /\ P s }) .
  <== {apply vm_rnd} 
  ({s (m:Z) n, ⟨RND :: c, n :: s⟩ | e ⇓ n  /\ 0 <= m <= abs n /\ P s }).
  = {dist' auto}
  ({s n, ⟨RND :: c, n :: s⟩ | e ⇓ n /\ P s }) .
  <|= { apply IHe }
  ({s, ⟨comp' e (RND :: c), s⟩ | P s }) .
  [].
Qed.