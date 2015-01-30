(* Calculation for a language with interrupts. *)
Require Import List.
Require Import Tactics.

Require Import ZArith.
Local Open Scope Z_scope.

Inductive Expr : Set := Val (n : Z) | Add (e1 e2 : Expr) | Throw | Catch (e h : Expr) 
                      | Seqn (e1 e2 : Expr) | Block (e : Expr) | Unblock (e : Expr).

Reserved Notation "x ⇓[ i ] y" (at level 70, no associativity).
Inductive Status : Set := B | U.


Inductive eval : Expr -> Status -> option Z -> Prop :=
| eval_val n i : Val n ⇓[i] Some n
| eval_throw i : Throw ⇓[i] None
| eval_add1 x y n m i : x ⇓[i] Some n -> y ⇓[i] Some m -> Add x y ⇓[i] Some (n + m)
| eval_add2 x y i : x ⇓[i] None -> Add x y ⇓[i] None
| eval_add3 x y n i : x ⇓[i] Some n -> y ⇓[i] None -> Add x y ⇓[i] None
| eval_seq1 x y n v i : x ⇓[i] Some n -> y ⇓[i] v -> Seqn x y ⇓[i] v
| eval_seq2  x y i : x ⇓[i] None -> Seqn x y ⇓[i] None
| eval_catch1 x y n i : x ⇓[i] Some n -> Catch x y ⇓[i] Some n
| eval_catch2 x y v i : x ⇓[i] None -> y ⇓[i] v -> Catch x y ⇓[i] v
| eval_block x v i : x ⇓[B] v -> Block x ⇓[i] v
| eval_unblock x v i : x ⇓[U] v -> Unblock x ⇓[i] v
| eval_int x : x ⇓[U] None
where "x ⇓[ i ] y" := (eval x i y).

Hint Constructors eval.

Inductive Instr : Set := PUSH (n : Z) | ADD | THROW | UNMARK | MARK (h : list Instr) 
                       | POP | RESET | BLOCK | UNBLOCK.

Definition Code := list Instr.

Import ListNotations.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n :: c
    | Add x y => comp' x (comp' y (ADD :: c))
    | Throw => [THROW]
    | Catch e1 e2 => MARK (comp' e2 c) :: comp' e1 (UNMARK :: c)
    | Seqn e1 e2 => comp' e1 (POP :: comp' e2 c)
    | Block e => BLOCK :: comp' e (RESET :: c)
    | Unblock e => UNBLOCK :: comp' e (RESET :: c)
  end.

Definition comp (e : Expr) : Code := comp' e nil.

Inductive Elem : Set := VAL (n : Z) | HAN (c : Code) | INT (s  : Status).

Definition Stack : Set := list Elem.

Inductive Conf : Set := conf (c : Code) (s : Stack) (i : Status)
                      | fail (s : Stack) (i : Status).

Notation "⟨ c , s , i ⟩" := (conf c s i).
Notation "⟪ s , i ⟫" := (fail s i ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
 | vm_push n c s i : ⟨PUSH n :: c, s, i⟩ ==> ⟨ c , VAL n :: s, i ⟩ 
 | vm_push_int n c s: ⟨PUSH n :: c, s, U⟩ ==> ⟪s, U⟫ 
 | vm_add c s m n i : ⟨ADD :: c, VAL m :: VAL n :: s, i⟩ ==> ⟨c, VAL (n + m) :: s, i⟩ 
 | vm_fail_val  m s i : ⟪VAL m :: s, i⟫ ==> ⟪s, i⟫
 | vm_throw c s i : ⟨ THROW :: c, s, i⟩ ==> ⟪s, i⟫ 
 | vm_fail_han s h i : ⟪HAN h :: s, i⟫ ==> ⟨h,s,i⟩
 | vm_unmark c n h s i : ⟨UNMARK :: c, VAL n :: HAN h :: s, i⟩ ==> ⟨c, VAL n :: s, i⟩ 
 | vm_mark h c s i : ⟨MARK h :: c, s, i⟩ ==> ⟨c, HAN h :: s, i⟩ 
 | vm_pop c n s i : ⟨POP :: c, VAL n :: s, i⟩ ==> ⟨c, s, i⟩
 | vm_reset c s n i j : ⟨RESET :: c, VAL n :: INT i :: s, j⟩ ==> ⟨c, VAL n :: s, i⟩
 | vm_block c s i : ⟨BLOCK :: c, s, i⟩ ==> ⟨c, INT i :: s, B⟩
 | vm_block_int c s : ⟨BLOCK :: c, s, U⟩ ==> ⟪s, U⟫
 | vm_unblock c s i : ⟨UNBLOCK :: c, s, i⟩ ==> ⟨c, INT i :: s, U⟩
 | vm_fail_int i j s : ⟪INT i :: s, j⟫ ==> ⟪s,i⟫
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

Theorem spec e P c :  { s i, ⟨comp' e c , s, i⟩ | P s i} =|>
                        { s i n, ⟨c , VAL n :: s, i⟩ | e ⇓[i] Some n /\ P s i}
                        ∪ { s i, ⟪s, i⟫ | e ⇓[i] None /\ P s i}.
Proof.
  intros.
  generalize dependent c.
  generalize dependent P.
  induction e;intros.
   
   begin
    ({ s i n', ⟨c, VAL n' :: s, i⟩ | Val n ⇓[i] Some n' /\ P s i} ∪ 
     { s i, ⟪s, i⟫ | Val n ⇓[i] None /\ P s i }).
   = {by_eval}
    ({ s i , ⟨c, VAL n :: s, i⟩ |  P s i} ∪
     { s , ⟪s, U⟫ | P s U }).
  <== {apply vm_push}
    ({ s i, ⟨ PUSH n :: c, s, i⟩ | P s i } ∪
     { s , ⟪s, U⟫ | P s U }).
  <== {apply vm_push_int}
    ({ s i, ⟨ PUSH n :: c, s, i⟩ | P s i } ∪
     { s, ⟨ PUSH n :: c, s, U⟩ | P s U }).
  = {auto}
    ({ s i, ⟨ PUSH n :: c, s, i⟩ | P s i }).
  [].

  begin
    ({s i n, ⟨c, VAL n :: s, i⟩ | Add e1 e2 ⇓[i] Some n /\ P s i } ∪ 
       { s i , ⟪s, i⟫ | Add e1 e2 ⇓[i] None /\ P s i }) .
  = {by_eval}
  ({s i n m, ⟨c, VAL (n + m) :: s, i⟩ | e1 ⇓[i] Some n /\ e2 ⇓[i] Some m /\ P s i} ∪ 
   { s i n , ⟪s, i⟫ | e1 ⇓[i] Some n /\ e2 ⇓[i] None /\ P s i } ∪ 
   { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <== {apply vm_add}
  ({ s i n m, ⟨ADD :: c, VAL m :: VAL n :: s, i⟩ | e1 ⇓[i] Some n /\ e2 ⇓[i] Some m /\ P s i} ∪ 
   { s i n , ⟪s, i⟫ | e1 ⇓[i] Some n /\ e2 ⇓[i] None /\ P s i } ∪ 
   { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <== {apply vm_fail_val}
  ({ s i n m, ⟨ADD :: c, VAL m :: VAL n :: s, i⟩ | e1 ⇓[i] Some n /\ e2 ⇓[i] Some m /\ P s i} ∪
   { s i n , ⟪ VAL n :: s, i ⟫ | e1 ⇓[i] Some n /\ e2 ⇓[i] None /\ P s i }
   ∪ { s i, ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  = { auto }
  ({ s' i m, ⟨ADD :: c, VAL m :: s', i⟩ | e2 ⇓[i] Some m /\ (exists n s, s' = VAL n :: s 
                                                        /\ e1 ⇓[i] Some n /\ P s i)} ∪
   { s' i, ⟪s', i⟫ | e2 ⇓[i] None /\ (exists n s, s' = VAL n :: s /\ e1 ⇓[i] Some n /\ P s i) } ∪ 
   { s i, ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <|= {apply IHe2}
  ({ s' i, ⟨comp' e2 (ADD :: c), s', i⟩ | (exists n s, s' = VAL n :: s /\ e1 ⇓[i] Some n /\ P s i)} 
     ∪ { s i, ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  = { auto }
  ({ s i n, ⟨comp' e2 (ADD :: c), VAL n :: s, i⟩ | e1 ⇓[i] Some n /\ P s i} 
     ∪ { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <|= { apply IHe1 }
  ({ s i, ⟨comp' e1 (comp' e2 (ADD :: c)), s, i⟩ | P s i}).
  [].

  begin
    ({s i n, ⟨c, VAL n :: s, i⟩ | Throw ⇓[i] Some n /\ P s i} ∪ 
    { s i , ⟪s, i⟫ | Throw ⇓[i] None /\ P s i}).
  = {by_eval}
    ({ s i , ⟪s, i⟫ | P s i}).
  <== {apply vm_throw}
    ({ s i , ⟨[THROW], s, i⟩ | P s i}).
  [].

  begin
    ({s i n, ⟨c, VAL n :: s, i⟩ | Catch e1 e2 ⇓[i] Some n /\ P s i } ∪ 
    { s i , ⟪s, i⟫ | Catch e1 e2 ⇓[i] None /\ P s i }).
  = {by_eval}
    ({s i n, ⟨c, VAL n :: s, i⟩ | e1 ⇓[i] Some n /\ P s i } ∪ 
    {s i n, ⟨c, VAL n :: s, i⟩ | e1 ⇓[i] None /\ e2 ⇓[i] Some n /\ P s i } ∪ 
    { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ e2 ⇓[i] None /\ P s i }).
  = {auto}
    ({s i n, ⟨c, VAL n :: s, i⟩ | e1 ⇓[i] Some n /\ P s i } ∪ 
    ({s i n, ⟨c, VAL n :: s, i⟩ | e2 ⇓[i] Some n /\ (e1 ⇓[i] None /\ P s i) } ∪ 
     { s i , ⟪s, i⟫ | e2 ⇓[i] None /\ (e1 ⇓[i] None /\ P s i) })).
  <|= { apply IHe2 }
    ({s i n, ⟨c, VAL n :: s, i⟩ | e1 ⇓[i] Some n /\ P s i } ∪ 
    {s i, ⟨comp' e2 c, s, i⟩ | e1 ⇓[i] None /\ P s i }).
  <== { apply vm_fail_han }
    ({s i n, ⟨c, VAL n :: s, i⟩ | e1 ⇓[i] Some n /\ P s i } ∪ 
    {s i, ⟪HAN (comp' e2 c) :: s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <== { apply vm_unmark }
    ({s i n, ⟨UNMARK :: c, VAL n :: HAN (comp' e2 c) :: s, i⟩ | e1 ⇓[i] Some n /\ P s i } ∪ 
    {s i, ⟪HAN (comp' e2 c) :: s, i⟫ | e1 ⇓[i] None /\ P s i }).
  = { auto }
    ({s' i n, ⟨UNMARK :: c, VAL n :: s', i⟩ | e1 ⇓[i] Some n /\ (exists s, s' = HAN (comp' e2 c) :: s /\ P s i )} ∪ 
    {s' i, ⟪s', i⟫ | e1 ⇓[i] None /\ (exists s, s' = HAN (comp' e2 c) :: s /\ P s i ) }).
  <|= {apply IHe1}
    ({s' i, ⟨comp' e1 (UNMARK :: c), s', i⟩ | (exists s, s' = HAN (comp' e2 c) :: s /\ P s i ) }).
  = {auto}
    ({s i, ⟨comp' e1 (UNMARK :: c), HAN (comp' e2 c) :: s, i⟩ | P s i }).
  <== {apply vm_mark}
    ({s i, ⟨MARK (comp' e2 c) :: comp' e1 (UNMARK :: c), s, i⟩ | P s i }).
  [].

  begin
    ({s i n, ⟨c, VAL n :: s, i⟩ | Seqn e1 e2 ⇓[i] Some n /\ P s i } ∪ 
    { s i , ⟪s, i⟫ | Seqn e1 e2 ⇓[i] None /\ P s i }).
  = {by_eval}
    ({s i n, ⟨c, VAL n :: s, i⟩ | e2 ⇓[i] Some n /\ (exists m, e1 ⇓[i] Some m) /\ P s i } ∪ 
    {s i, ⟪s, i⟫ | e2 ⇓[i] None /\ (exists m, e1 ⇓[i] Some m) /\ P s i } ∪ 
    { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <|= {apply IHe2}
    ({s i, ⟨comp' e2 c, s, i⟩ | (exists m, e1 ⇓[i] Some m) /\ P s i } ∪ 
    { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  = {eauto}
    ({s i m, ⟨comp' e2 c, s, i⟩ | e1 ⇓[i] Some m /\ P s i } ∪ 
    { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <== {apply vm_pop}
    ({s i m, ⟨POP :: comp' e2 c, VAL m :: s, i⟩ | e1 ⇓[i] Some m /\ P s i } ∪ 
    { s i , ⟪s, i⟫ | e1 ⇓[i] None /\ P s i }).
  <|= {apply IHe1}
    ({s i, ⟨comp' e1 (POP :: comp' e2 c), s, i⟩ | P s i }).
  [].
  
  begin
    ({s i n, ⟨c, VAL n :: s, i⟩ | Block e ⇓[i] Some n /\ P s i } ∪ 
    { s i, ⟪s, i⟫ | Block e ⇓[i] None /\ P s i }).
  = {by_eval}
    ({s i n, ⟨c, VAL n :: s, i⟩ | e ⇓[B] Some n /\ P s i } ∪ 
    { s i, ⟪s, i⟫ | e ⇓[B] None /\ P s i } ∪ 
    { s , ⟪s, U⟫ | P s U }).
  <== {apply vm_reset}
    ({s i n, ⟨RESET :: c, VAL n :: INT i :: s, B⟩ | e ⇓[B] Some n /\ P s i } ∪ 
    { s i, ⟪s, i⟫ | e ⇓[B] None /\ P s i } ∪ 
    { s , ⟪s, U⟫ | P s U }).
  <== {apply vm_fail_int}
    ({s i n, ⟨RESET :: c, VAL n :: INT i :: s, B⟩ | e ⇓[B] Some n /\ P s i } ∪ 
    { s i, ⟪INT i :: s, B⟫ | e ⇓[B] None /\ P s i } ∪ 
    { s , ⟪s, U⟫ | P s U }).
  = {auto}
    ({s' i' n, ⟨RESET :: c, VAL n :: s', i'⟩ | e ⇓[i'] Some n /\ 
                                             (i' = B /\ exists s i, s' = INT i :: s /\ P s i) } ∪ 
    { s' i', ⟪s', i'⟫ | e ⇓[i'] None /\ (i' = B /\ exists s i, s' = INT i :: s /\ P s i) } ∪ 
    { s , ⟪s, U⟫ | P s U }).
  <|= {apply IHe}
    ({s' i', ⟨comp' e (RESET :: c), s', i'⟩ | i' = B /\ exists s i, s' = INT i :: s /\ P s i } ∪
    { s , ⟪s, U⟫ | P s U }).
  = {auto}
    ({s i, ⟨comp' e (RESET :: c), INT i :: s, B⟩ | P s i } ∪
    { s , ⟪s, U⟫ | P s U }).
  <== {apply vm_block}
    ({s i, ⟨BLOCK :: comp' e (RESET :: c), s, i⟩ | P s i } ∪
    { s , ⟪s, U⟫ | P s U }).
  <== {apply vm_block_int}
    ({s i, ⟨BLOCK :: comp' e (RESET :: c), s, i⟩ | P s i } ∪
    {s, ⟨BLOCK :: comp' e (RESET :: c), s, U⟩ | P s U }).
  = {auto}
    ({s i, ⟨BLOCK :: comp' e (RESET :: c), s, i⟩ | P s i }).
  [].
  
  begin
    ({s i n, ⟨c, VAL n :: s, i⟩ | Unblock e ⇓[i] Some n /\ P s i } ∪ 
    { s i, ⟪s, i⟫ | Unblock e ⇓[i] None /\ P s i }).
  = {by_eval}
    ({s i n, ⟨c, VAL n :: s, i⟩ | e ⇓[U] Some n /\ P s i } ∪ 
    { s i, ⟪s, i⟫ | e ⇓[U] None /\ P s i } ∪ 
    { s , ⟪s, U⟫ | P s U }).
  = {auto}
    ({s i n, ⟨c, VAL n :: s, i⟩ | e ⇓[U] Some n /\ P s i } ∪ 
    { s i, ⟪s, i⟫ | e ⇓[U] None /\ P s i }).
  <== {apply vm_reset}
    ({s i n, ⟨RESET :: c, VAL n :: INT i :: s, U⟩ | e ⇓[U] Some n /\ P s i } ∪ 
    { s i, ⟪s, i⟫ | e ⇓[U] None /\ P s i }).
  <== {apply vm_fail_int}
    ({s i n, ⟨RESET :: c, VAL n :: INT i :: s, U⟩ | e ⇓[U] Some n /\ P s i } ∪ 
    { s i, ⟪INT i :: s, U⟫ | e ⇓[U] None /\ P s i }).
  = {auto}
    ({s' i' n, ⟨RESET :: c, VAL n :: s', i'⟩ | e ⇓[i'] Some n /\ 
                                             (i' = U /\ exists s i, s' = INT i :: s /\ P s i) } ∪ 
    { s' i', ⟪s', i'⟫ | e ⇓[i'] None /\ (i' = U /\ exists s i, s' = INT i :: s /\ P s i) }).
  <|= {apply IHe}
    ({s' i', ⟨comp' e (RESET :: c), s', i'⟩ | i' = U /\ exists s i, s' = INT i :: s /\ P s i }).
  = {auto}
    ({s i, ⟨comp' e (RESET :: c), INT i :: s, U⟩ | P s i }).
  <== {apply vm_unblock}
    ({s i, ⟨UNBLOCK :: comp' e (RESET :: c), s, i⟩ | P s i }).
  [].
Qed.
