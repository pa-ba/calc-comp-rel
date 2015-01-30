(* Calculation of the simple arithmetic language. *)
Require Import List.
Require Import Tactics.

Require Import ZArith.
Local Open Scope Z_scope.

Inductive Expr : Set := Val (n : Z) |Add (e1 e2 : Expr) 
                      | Throw | Catch (e h : Expr).

Reserved Notation "x ⇓ y" (at level 70, no associativity).

Inductive eval : Expr -> option Z -> Prop :=
| eval_val n : Val n ⇓ Some n
| eval_add x y m n : x ⇓ Some m -> y ⇓ Some n -> Add x y ⇓ Some (m + n)
| eval_add1 x y : x ⇓ None -> Add x y ⇓ None
| eval_add2 x y n : x ⇓ Some n -> y ⇓ None -> Add x y ⇓ None
| eval_throw : Throw ⇓ None
| eval_catch x h n : x ⇓ Some n -> Catch x h ⇓ Some n
| eval_catch_fail x h m : x ⇓ None -> h ⇓ m -> Catch x h ⇓ m
where "x ⇓ y" := (eval x y).

Hint Constructors eval.

Inductive Instr : Set := PUSH (n : Z) | ADD | THROW | UNMARK | MARK (h : list Instr).

Definition Code := list Instr.

Import ListNotations.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n :: c
    | Add x y => comp' x (comp' y (ADD :: c))
    | Throw => [THROW]
    | Catch e1 e2 => MARK (comp' e2 c) :: comp' e1 (UNMARK :: c)
  end.

Definition comp (e : Expr) : Code := comp' e [].

Inductive Elem : Set := VAL (n : Z) | HAN (c : Code).

Definition Stack : Set := list Elem.

Inductive Conf : Set  :=  conf (c : Code) (s : Stack)
                      |   fail (s : Stack).

Notation "⟨ c , s ⟩" := (conf c s).
Notation "⟪ s ⟫" := (fail s ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : ⟨PUSH n :: c, s⟩ ==> ⟨ c , VAL n :: s ⟩
| vm_add c s m n : ⟨ADD :: c, VAL m :: VAL n :: s⟩ ==> ⟨c, VAL (n + m) :: s⟩
| vm_add_fail n s : ⟪VAL n :: s ⟫ ==> ⟪s⟫
| vm_throw s c : ⟨ THROW :: c, s⟩ ==> ⟪s⟫
| vm_catch_fail s h : ⟪HAN h :: s⟫ ==> ⟨h,s⟩
| vm_unmark c n h s : ⟨UNMARK :: c, VAL n :: HAN h :: s⟩ ==> ⟨c, VAL n :: s⟩
| vm_mark h c s : ⟨MARK h :: c, s⟩ ==> ⟨c, HAN h :: s⟩
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

Theorem spec e P c :  { s, ⟨comp' e c , s⟩ | P s} =|>
                        { s n, ⟨c , VAL n :: s⟩ | e ⇓ Some n /\ P s} ∪ { s , ⟪ s ⟫ | e ⇓ None /\ P s }.
Proof.
  intros.
  generalize dependent c.
  generalize dependent P.
  induction e;intros.
   
   begin
    ({ s n', ⟨c, VAL n' :: s⟩ | Val n ⇓ Some n' /\ P s} ∪ 
     { s , ⟪ s ⟫ | Val n ⇓ None /\ P s }).
   = {by_eval}
    ({ s n' , ⟨c, VAL n' :: s⟩ | Val n ⇓ Some n' /\ P s}).
   = {by_eval}
    ({ s , ⟨c, VAL n :: s⟩ | P s}).
  <== {apply vm_push}
    ({ s, ⟨ PUSH n :: c, s⟩ | P s }) .
  [].

  begin
    ({s n, ⟨c, VAL n :: s⟩ | Add e1 e2 ⇓ Some n /\ P s } ∪ 
       { s , ⟪ s ⟫ | Add e1 e2 ⇓ None /\ P s }) .
  = {by_eval}
  ({s n m, ⟨c, VAL (n + m) :: s⟩ | e1 ⇓ Some n /\ e2 ⇓ Some m /\ P s} ∪ 
   { s n , ⟪ s ⟫ | e1 ⇓ Some n /\ e2 ⇓ None /\ P s } ∪ { s , ⟪ s ⟫ | e1 ⇓ None /\ P s }).
  <== {apply vm_add}
  ({ s n m, ⟨ADD :: c, VAL m :: VAL n :: s⟩ | e1 ⇓ Some n /\ e2 ⇓ Some m /\ P s} ∪
   { s n , ⟪ s ⟫ | e1 ⇓ Some n /\ e2 ⇓ None /\ P s } ∪ { s , ⟪ s ⟫ | e1 ⇓ None /\ P s }).
  <== {apply vm_add_fail}
  ({ s n m, ⟨ADD :: c, VAL m :: VAL n :: s⟩ | e1 ⇓ Some n /\ e2 ⇓ Some m /\ P s} ∪
   { s n , ⟪ VAL n :: s ⟫ | e1 ⇓ Some n /\ e2 ⇓ None /\ P s } ∪ { s , ⟪ s ⟫ | e1 ⇓ None /\ P s }).  
  = {auto}
  ({ s' m, ⟨ADD :: c, VAL m :: s'⟩ | e2 ⇓ Some m /\ (exists n s, s' = VAL n :: s /\ e1 ⇓ Some n /\ P s)} ∪
   { s' , ⟪ s' ⟫ | e2 ⇓ None /\ (exists n s, s' = VAL n :: s /\ e1 ⇓ Some n /\ P s) } ∪ 
   { s  , ⟪ s ⟫ | e1 ⇓ None /\ P s }).
  <|= { apply IHe2 }
  ({ s', ⟨comp' e2 (ADD :: c), s'⟩ | (exists n s, s' = VAL n :: s /\ e1 ⇓ Some n /\ P s)} 
     ∪ { s  , ⟪ s ⟫ | e1 ⇓ None /\ P s }).
  = { auto }
  ({ s n, ⟨comp' e2 (ADD :: c), VAL n :: s⟩ | e1 ⇓ Some n /\ P s} 
     ∪ { s  , ⟪ s ⟫ | e1 ⇓ None /\ P s }).
  <|= { apply IHe1 }
  ({ s, ⟨comp' e1 (comp' e2 (ADD :: c)), s⟩ | P s}).
  [].

  begin
    ({s n, ⟨c, VAL n :: s⟩ | Throw ⇓ Some n /\ P s } ∪ 
    { s , ⟪ s ⟫ | Throw ⇓ None /\ P s }).
  = {by_eval}
    ({ s , ⟪ s ⟫ | P s }).
  <== {apply vm_throw}
    ({ s , ⟨[THROW], s⟩ | P s }).
  [].

  begin
    ({s n, ⟨c, VAL n :: s⟩ | Catch e1 e2 ⇓ Some n /\ P s } ∪ 
    { s , ⟪ s ⟫ | Catch e1 e2 ⇓ None /\ P s }).
  = {by_eval}
    ({s n, ⟨c, VAL n :: s⟩ | e1 ⇓ Some n /\ P s } ∪ 
    {s n, ⟨c, VAL n :: s⟩ | e1 ⇓ None /\ e2 ⇓ Some n /\ P s } ∪ 
    { s , ⟪ s ⟫ | e1 ⇓ None /\ e2 ⇓ None /\ P s }).
  = {by_eval}
    ({s n, ⟨c, VAL n :: s⟩ | e1 ⇓ Some n /\ P s } ∪ 
    ({s n, ⟨c, VAL n :: s⟩ | e2 ⇓ Some n /\ (e1 ⇓ None /\ P s) } ∪ 
     { s , ⟪ s ⟫ | e2 ⇓ None /\ (e1 ⇓ None /\ P s) })).
  <|= { apply IHe2 }
    ({s n, ⟨c, VAL n :: s⟩ | e1 ⇓ Some n /\ P s } ∪ 
    {s, ⟨comp' e2 c, s⟩ | e1 ⇓ None /\ P s }).
  <== { apply vm_catch_fail }
    ({s n, ⟨c, VAL n :: s⟩ | e1 ⇓ Some n /\ P s } ∪ 
    {s, ⟪HAN (comp' e2 c) :: s⟫ | e1 ⇓ None /\ P s }).
  <== { apply vm_unmark }
    ({s n, ⟨UNMARK :: c, VAL n :: HAN (comp' e2 c) :: s⟩ | e1 ⇓ Some n /\ P s } ∪ 
    {s, ⟪HAN (comp' e2 c) :: s⟫ | e1 ⇓ None /\ P s }).
  = { auto }
    ({s' n, ⟨UNMARK :: c, VAL n :: s'⟩ | e1 ⇓ Some n /\ (exists s, s' = HAN (comp' e2 c) :: s /\ P s )} ∪ 
    {s', ⟪s'⟫ | e1 ⇓ None /\ (exists s, s' = HAN (comp' e2 c) :: s /\ P s ) }).
  <|= {apply IHe1}
    ({s', ⟨comp' e1 (UNMARK :: c), s'⟩ | (exists s, s' = HAN (comp' e2 c) :: s /\ P s ) }).
  = {auto}
    ({s, ⟨comp' e1 (UNMARK :: c), HAN (comp' e2 c) :: s⟩ | P s }).
  <== {apply vm_mark}
    ({s, ⟨MARK (comp' e2 c) :: comp' e1 (UNMARK :: c), s⟩ | P s }).
  [].
Qed.
