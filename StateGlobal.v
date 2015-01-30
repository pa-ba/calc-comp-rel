(* Calculation for a language with interrupts and (global) state. *)
Require Import List.
Require Import Tactics.

Require Import ZArith.
Local Open Scope Z_scope.

Inductive Expr : Set := Val (n : Z) | Add (e1 e2 : Expr) | Throw | Catch (e h : Expr) 
                      | Seqn (e1 e2 : Expr) | Block (e : Expr) | Unblock (e : Expr)
                      | Put (e : Expr) | Get.

Reserved Notation "x ⇓[ i , q , p ] y" (at level 70, no associativity).
Inductive Status : Set := B | U.

Definition State := Z.

Inductive eval : Expr -> State -> Status -> option Z -> State -> Prop :=
| eval_val n i p : Val n ⇓[i,p,p] Some n
| eval_throw i p : Throw ⇓[i,p,p] None
| eval_add1 x y n m i q p r : x ⇓[i,p,q] Some n -> y ⇓[i,q,r] Some m
                              -> Add x y ⇓[i,p,r] Some (n + m)
| eval_add2 x y i q p : x ⇓[i,p,q] None -> Add x y ⇓[i,p,q] None
| eval_add3 x y n i q p r : x ⇓[i,p,q] Some n -> y ⇓[i,q,r] None -> Add x y ⇓[i,p,r] None
| eval_seq1 x y n v i q p r : x ⇓[i,p,q] Some n -> y ⇓[i,q,r] v -> Seqn x y ⇓[i,p,r] v
| eval_seq2  x y i q p : x ⇓[i,p,q] None -> Seqn x y ⇓[i,p,q] None
| eval_catch1 x y n i q p: x ⇓[i,p,q] Some n -> Catch x y ⇓[i,p,q] Some n
| eval_catch2 x y v i q p r : x ⇓[i,p,q] None -> y ⇓[i,q,r] v -> Catch x y ⇓[i,p,r] v
| eval_block x v i q p : x ⇓[B,p,q] v -> Block x ⇓[i,p,q] v
| eval_unblock x v i q p : x ⇓[U,p,q] v -> Unblock x ⇓[i,p,q] v
| eval_int x p : x ⇓[U,p,p] None
| eval_put1 x n i q p  : x ⇓[i,p,q] Some n -> Put x ⇓[i,p,n] Some n
| eval_put2 x i q p  : x ⇓[i,p,q] None -> Put x ⇓[i,p,q] None
| eval_get i p  : Get ⇓[i,p,p] Some p
where "x ⇓[ i , q , p ] y" := (eval x q i y p).

Hint Constructors eval.

Inductive Instr : Set := PUSH (n : Z) | ADD | THROW | UNMARK | MARK (h : list Instr) 
                       | POP | RESET | BLOCK | UNBLOCK | PUT | GET.

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
    | Put e => comp' e (PUT :: c)
    | Get => GET :: c
  end.

Definition comp (e : Expr) : Code := comp' e nil.

Inductive Elem : Set := VAL (n : Z) | HAN (c : Code) | INT (s  : Status).

Definition Stack : Set := list Elem.

Inductive Conf : Set := conf (c : Code) (s : Stack) (q : State) (i : Status)
                      | fail (s : Stack) (q : State) (i : Status).

Notation "⟨ c , s , q , i ⟩" := (conf c s q i).
Notation "⟪ s , q , i ⟫" := (fail s q i ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
 | vm_push n c s q i : ⟨PUSH n :: c, s, q, i⟩ ==> ⟨ c , VAL n :: s, q, i ⟩
 | vm_push_int n c s q: ⟨PUSH n :: c, s, q, U⟩ ==> ⟪s, q, U⟫
 | vm_add c s m n p i : ⟨ADD :: c, VAL m :: VAL n :: s,p, i⟩ ==> ⟨c, VAL (n + m) :: s, p, i⟩
 | vm_fail_val  m s p i : ⟪VAL m :: s, p, i⟫ ==> ⟪s, p, i⟫
 | vm_throw c s p i : ⟨ THROW :: c, s, p, i⟩ ==> ⟪s, p, i⟫
 | vm_fail_han s h p i : ⟪HAN h :: s, p, i⟫ ==> ⟨h,s,p,i⟩
 | vm_unmark c n h p s i : ⟨UNMARK :: c, VAL n :: HAN h :: s, p, i⟩ ==> ⟨c, VAL n :: s, p, i⟩
 | vm_mark h c p s i : ⟨MARK h :: c, s, p, i⟩ ==> ⟨c, HAN h :: s, p, i⟩
 | vm_pop c n s p i : ⟨POP :: c, VAL n :: s, p, i⟩ ==> ⟨c, s, p, i⟩
 | vm_reset c s n p i j : ⟨RESET :: c, VAL n :: INT i :: s, p, j⟩ ==> ⟨c, VAL n :: s, p, i⟩
 | vm_block c s p i : ⟨BLOCK :: c, s, p, i⟩ ==> ⟨c, INT i :: s, p, B⟩
 | vm_block_int c s p : ⟨BLOCK :: c, s, p, U⟩ ==> ⟪s, p, U⟫
 | vm_unblock c s p i : ⟨UNBLOCK :: c, s, p, i⟩ ==> ⟨c, INT i :: s, p, U⟩
 | vm_fail_int i j s p : ⟪INT i :: s, p, j⟫ ==> ⟪s, p, i⟫
 | vm_put c n s p i : ⟨PUT :: c, VAL n :: s, p, i⟩ ==> ⟨c, VAL n :: s, n, i⟩
 | vm_get c s p i : ⟨GET :: c, s, p, i⟩ ==> ⟨c, VAL p :: s, p, i⟩
 | vm_get_int c s p : ⟨GET :: c, s, p, U⟩ ==> ⟪s, p, U⟫
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

Theorem spec e P c :  { s p i, ⟨comp' e c , s, p, i⟩ | P s p i} =|>
                        { s p q i n, ⟨c, VAL n :: s, q, i⟩ | e ⇓[i,p,q] Some n /\ P s p i}
                        ∪ { s p q i, ⟪s, q, i⟫ | e ⇓[i,p,q] None /\ P s p i}.
Proof.
  intros.
  generalize dependent c.
  generalize dependent P.
  induction e;intros.
   
   begin
    ({ s p q i n', ⟨c, VAL n' :: s, q, i⟩ | Val n ⇓[i,p, q] Some n' /\ P s p i} ∪ 
     { s p q i, ⟪s, q, i⟫ | Val n ⇓[i,p,q] None /\ P s p i }).
   = {by_eval}
    ({ s p i , ⟨c, VAL n :: s, p, i⟩ |  P s p i} ∪
     { s p , ⟪s, p, U⟫ | P s p U }).
  <== {apply vm_push}
    ({ s p i, ⟨ PUSH n :: c, s, p, i⟩ | P s p i } ∪
     { s p , ⟪s, p, U⟫ | P s p U }).
  <== {apply vm_push_int}
    ({ s p i, ⟨ PUSH n :: c, s, p, i⟩ | P s p i } ∪
     { s p, ⟨ PUSH n :: c, s, p, U⟩ | P s p U }).
  = {auto}
    ({ s p i, ⟨ PUSH n :: c, s, p, i⟩ | P s p i }).
  [].

  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | Add e1 e2 ⇓[i,p,q] Some n /\ P s p i }
    ∪ { s p q i , ⟪s, q, i⟫ | Add e1 e2 ⇓[i,p,q] None /\ P s p i }) .
  = {by_eval}
    ({s p q r i n m, ⟨c, VAL (n+m) :: s, q, i⟩ | e1 ⇓[i,p,r] Some n /\ e2 ⇓[i,r,q] Some m /\ P s p i }
    ∪ { s p q r n i , ⟪s, q, i⟫ | e1 ⇓[i,p,r] Some n /\ e2 ⇓[i,r,q] None /\ P s p i }
    ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  <== {apply vm_add}
    ({s p q r i n m, ⟨ADD :: c, VAL m :: VAL n :: s, q, i⟩ | e1 ⇓[i,p,r] Some n /\ e2 ⇓[i,r,q] Some m /\ P s p i }
    ∪ { s p q r n i , ⟪s, q, i⟫ | e1 ⇓[i,p,r] Some n /\ e2 ⇓[i,r,q] None /\ P s p i }
    ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  <== {apply vm_fail_val}
    ({s p q r i n m, ⟨ADD :: c, VAL m :: VAL n :: s, q, i⟩ | e1 ⇓[i,p,r] Some n /\ e2 ⇓[i,r,q] Some m /\ P s p i }
    ∪ { s p q r n i , ⟪VAL n :: s, q, i⟫ | e1 ⇓[i,p,r] Some n /\ e2 ⇓[i,r,q] None /\ P s p i }
    ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  = { eauto }
    ({s' r q i m, ⟨ADD :: c, VAL m :: s', q, i⟩ | e2 ⇓[i,r,q] Some m /\ 
             (exists s p n, s' = VAL n :: s /\ e1 ⇓[i,p,r] Some n /\ P s p i) }
    ∪ { s' r q i , ⟪s', q, i⟫ | e2 ⇓[i,r,q] None /\ 
                        (exists s p n, s' = VAL n :: s /\ e1 ⇓[i,p,r] Some n /\ P s p i) }
    ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  <|= {apply IHe2}
    ({s' r i, ⟨comp' e2 (ADD :: c), s', r, i⟩ | (exists s p n, s' = VAL n :: s /\ e1 ⇓[i,p,r] Some n /\ P s p i) }
    ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  = {eauto}
    ({s p r i n, ⟨comp' e2 (ADD :: c), VAL n :: s, r, i⟩ | e1 ⇓[i,p,r] Some n /\ P s p i }
    ∪ { s p r i , ⟪s, r, i⟫ | e1 ⇓[i,p,r] None /\ P s p i }).
  <|= { apply IHe1 }
  ({ s p i, ⟨comp' e1 (comp' e2 (ADD :: c)), s, p, i⟩ | P s p i}).
  [].

  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | Throw ⇓[i,p,q] Some n /\ P s p i} ∪ 
    { s p q i , ⟪s, q, i⟫ | Throw ⇓[i,p,q] None /\ P s p i}).
  = {by_eval}
    ({ s p i , ⟪s, p, i⟫ | P s p i}).
  <== {apply vm_throw}
    ({ s p i , ⟨[THROW], s, p, i⟩ | P s p i}).
  [].

  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | Catch e1 e2 ⇓[i,p,q] Some n /\ P s p i } ∪ 
    { s p q i , ⟪s, q, i⟫ | Catch e1 e2 ⇓[i, p, q] None /\ P s p i }).
  = {by_eval}
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | e1 ⇓[i,p,q] Some n /\ P s p i } ∪ 
    {s p q r i n, ⟨c, VAL n :: s, q, i⟩ | e1 ⇓[i,p,r] None /\ e2 ⇓[i,r,q] Some n /\ P s p i } ∪ 
    { s p q r i , ⟪s, q, i⟫ | e1 ⇓[i,p,r] None /\ e2 ⇓[i,r,q] None /\ P s p i }).
  = {eauto}
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | e1 ⇓[i,p,q] Some n /\ P s p i } ∪ 
    ({s r q i n, ⟨c, VAL n :: s, q, i⟩ | e2 ⇓[i,r,q] Some n /\ (exists p, e1 ⇓[i,p,r] None /\ P s p i) } ∪ 
    { s r q i , ⟪s, q, i⟫ | e2 ⇓[i,r,q] None /\ (exists p, e1 ⇓[i,p,r] None /\ P s p i) })).
  <|= { apply IHe2 }
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | e1 ⇓[i,p,q] Some n /\ P s p i } ∪ 
    {s r i, ⟨comp' e2 c, s, r, i⟩ | exists p, e1 ⇓[i,p,r] None /\ P s p i }).
  <== { apply vm_fail_han }
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | e1 ⇓[i,p,q] Some n /\ P s p i } ∪ 
    {s r i, ⟪HAN (comp' e2 c) :: s, r, i⟫ | exists p, e1 ⇓[i,p,r] None /\ P s p i }).
  <== { apply vm_unmark }
    ({s p q i n, ⟨UNMARK :: c, VAL n :: HAN (comp' e2 c) :: s, q, i⟩ | e1 ⇓[i,p,q] Some n /\ P s p i } ∪ 
    {s r i, ⟪HAN (comp' e2 c) :: s, r, i⟫ | exists p, e1 ⇓[i,p,r] None /\ P s p i }).
  = { eauto }
    ({s' p q i n, ⟨UNMARK :: c, VAL n :: s', q, i⟩ | e1 ⇓[i,p,q] Some n /\ 
                                      (exists s, s' = HAN (comp' e2 c) :: s /\ P s p i) } ∪ 
    {s' p q i, ⟪s', q, i⟫ | e1 ⇓[i,p,q] None /\ (exists s, s' = HAN (comp' e2 c) :: s /\ P s p i) }).
  <|= {apply IHe1}
    ({s' p i, ⟨comp' e1 (UNMARK :: c), s', p, i⟩ | exists s, s' = HAN (comp' e2 c) :: s /\ P s p i }).
  = {auto}
    ({s p i, ⟨comp' e1 (UNMARK :: c), HAN (comp' e2 c) :: s, p, i⟩ | P s p i }).
  <== {apply vm_mark}
    ({s p i, ⟨MARK (comp' e2 c) :: comp' e1 (UNMARK :: c), s, p, i⟩ | P s p i }).
  [].  

  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | Seqn e1 e2 ⇓[i,p,q] Some n /\ P s p i } ∪ 
    { s p q i , ⟪s, q, i⟫ | Seqn e1 e2 ⇓[i,p,q] None /\ P s p i }).
  = {by_eval}
    ({s p q i n m r, ⟨c, VAL n :: s, q, i⟩ | e1 ⇓[i,p,r] Some m /\ e2 ⇓[i,r,q] Some n /\ P s p i }
     ∪ { s p q i m r , ⟪s, q, i⟫ | e1 ⇓[i,p,r] Some m /\ e2 ⇓[i,r,q] None /\ P s p i }
     ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  = {eauto}
    ({s r q i n, ⟨c, VAL n :: s, q, i⟩ | e2 ⇓[i,r,q] Some n /\ (exists p m, e1 ⇓[i,p,r] Some m /\ P s p i) }
     ∪ { s r q i , ⟪s, q, i⟫ | e2 ⇓[i,r,q] None /\ (exists p m, e1 ⇓[i,p,r] Some m /\ P s p i) }
     ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  <|= {apply IHe2}
    ({s r i, ⟨comp' e2 c, s, r, i⟩ | exists p m, e1 ⇓[i,p,r] Some m /\ P s p i }
     ∪ { s p q i , ⟪s, q, i⟫ | e1 ⇓[i,p,q] None /\ P s p i }).
  = {eauto}
    ({s p r i m, ⟨comp' e2 c, s, r, i⟩ | e1 ⇓[i,p,r] Some m /\ P s p i }
     ∪ { s p r i , ⟪s, r, i⟫ | e1 ⇓[i,p,r] None /\ P s p i }).
  <== {apply vm_pop}
    ({s p r i m, ⟨POP :: comp' e2 c, VAL m :: s, r, i⟩ | e1 ⇓[i,p,r] Some m /\ P s p i }
     ∪ { s p r i , ⟪s, r, i⟫ | e1 ⇓[i,p,r] None /\ P s p i }).
  <|= {apply IHe1}
    ({s p i, ⟨comp' e1 (POP :: comp' e2 c), s, p, i⟩ | P s p i }).
  [].
  
  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | Block e ⇓[i,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪s, q, i⟫ | Block e ⇓[i,p,q] None /\ P s p i }).
  = {by_eval}
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | e ⇓[B,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪s, q, i⟫ | e ⇓[B,p,q] None /\ P s p i } ∪
    { s p, ⟪s, p, U⟫ | P s p U }).
  <== {apply vm_reset}
    ({s p q i n, ⟨RESET :: c, VAL n :: INT i :: s, q, B⟩ | e ⇓[B,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪s, q, i⟫ | e ⇓[B,p,q] None /\ P s p i } ∪
    { s p, ⟪s, p, U⟫ | P s p U }).
  <== {apply vm_fail_int}
    ({s p q i n, ⟨RESET :: c, VAL n :: INT i :: s, q, B⟩ | e ⇓[B,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪INT i :: s, q, B⟫ | e ⇓[B,p,q] None /\ P s p i } ∪
    { s p, ⟪s, p, U⟫ | P s p U }).
  = {eauto}
    ({s' p q i' n, ⟨RESET :: c, VAL n :: s', q, i'⟩ | e ⇓[i',p,q] Some n /\ 
                    (exists s i, i' = B /\ s' = INT i :: s /\ P s p i) } ∪ 
    { s' p q i', ⟪s', q, i'⟫ | e ⇓[i',p,q] None /\ (exists s i, i' = B /\ s' = INT i :: s /\ P s p i) } ∪
    { s p, ⟪s, p, U⟫ | P s p U }).
  <|= {apply IHe}
    ({s' p i', ⟨comp' e (RESET :: c), s', p, i'⟩ |  exists s i, i' = B /\ s' = INT i :: s /\ P s p i }
    ∪  { s p, ⟪s, p, U⟫ | P s p U }).
  = {auto}
    ({s p i, ⟨comp' e (RESET :: c), INT i :: s, p, B⟩ | P s p i }
    ∪  { s p, ⟪s, p, U⟫ | P s p U }).
  <== {apply vm_block}
    ({s p i, ⟨BLOCK :: comp' e (RESET :: c), s, p, i⟩ | P s p i }
    ∪  { s p, ⟪s, p, U⟫ | P s p U }).
  <== {apply vm_block_int}
    ({s p i, ⟨BLOCK :: comp' e (RESET :: c), s, p, i⟩ | P s p i } ∪
    {s p, ⟨BLOCK :: comp' e (RESET :: c), s, p, U⟩ | P s p U }).
  = {auto}
    ({s p i, ⟨BLOCK :: comp' e (RESET :: c), s, p, i⟩ | P s p i }).
  [].

  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | Unblock e ⇓[i,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪s, q, i⟫ | Unblock e ⇓[i,p,q] None /\ P s p i }).
  = {by_eval}
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | e ⇓[U,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪s, q, i⟫ | e ⇓[U,p,q] None /\ P s p i } ∪
    { s p, ⟪s, p, U⟫ | P s p U }).
  = {auto}
    ({s p q i n, ⟨c, VAL n :: s, q, i⟩ | e ⇓[U,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪s, q, i⟫ | e ⇓[U,p,q] None /\ P s p i }).
  <== {apply vm_reset}
    ({s p q i n, ⟨RESET :: c, VAL n :: INT i :: s, q, U⟩ | e ⇓[U,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪s, q, i⟫ | e ⇓[U,p,q] None /\ P s p i }).
  <== {apply vm_fail_int}
    ({s p q i n, ⟨RESET :: c, VAL n :: INT i :: s, q, U⟩ | e ⇓[U,p,q] Some n /\ P s p i } ∪ 
    { s p q i, ⟪INT i :: s, q, U⟫ | e ⇓[U,p,q] None /\ P s p i }).
  = {eauto}
    ({s' p q i' n, ⟨RESET :: c, VAL n :: s', q, i'⟩ | e ⇓[i',p,q] Some n /\ 
                    (exists s i, i' = U /\ s' = INT i :: s /\ P s p i) } ∪ 
    { s' p q i', ⟪s', q, i'⟫ | e ⇓[i',p,q] None /\ (exists s i, i' = U /\ s' = INT i :: s /\ P s p i) }).
  <|= {apply IHe}
    ({s' p i', ⟨comp' e (RESET :: c), s', p, i'⟩ |  exists s i, i' = U /\ s' = INT i :: s /\ P s p i }).
  = {auto}
    ({s p i, ⟨comp' e (RESET :: c), INT i :: s, p, U⟩ | P s p i }).
  <== {apply vm_unblock}
    ({s p i, ⟨UNBLOCK :: comp' e (RESET :: c), s, p, i⟩ | P s p i }).
  [].
  

  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i ⟩ | Put e ⇓[ i, p, q] Some n /\ P s p i}
    ∪ {s p q i, ⟪s, q, i ⟫ | Put e ⇓[ i, p, q] None /\ P s p i}).
  = {by_eval}  
    ({s p q i n, ⟨c, VAL n :: s, n, i ⟩ | e ⇓[ i, p, q] Some n /\ P s p i}
    ∪ {s p q i, ⟪s, q, i ⟫ | e ⇓[ i, p, q] None /\ P s p i}).
  <== {apply vm_put}  
    ({s p q i n, ⟨PUT :: c, VAL n :: s, q, i ⟩ | e ⇓[ i, p, q] Some n /\ P s p i}
    ∪ {s p q i, ⟪s, q, i ⟫ | e ⇓[ i, p, q] None /\ P s p i}).
  <|= {apply IHe}  
    ({s p i, ⟨comp' e (PUT :: c), s, p, i ⟩ | P s p i}).
  [].

  begin
    ({s p q i n, ⟨c, VAL n :: s, q, i ⟩ | Get ⇓[ i, p, q] Some n /\ P s p i}
     ∪ {s p q i, ⟪s, q, i ⟫ | Get ⇓[ i, p, q] None /\ P s p i}).
  = {by_eval}
    ({s p i , ⟨c, VAL p :: s, p, i ⟩ | P s p i}
     ∪ {s p , ⟪s, p, U ⟫ |  P s p U}).
  <== {apply vm_get}
    ({s p i , ⟨GET :: c, s, p, i ⟩ | P s p i}
     ∪ {s p , ⟪s, p, U ⟫ |  P s p U}).
  <== {apply vm_get_int}
    ({s p i , ⟨GET :: c, s, p, i ⟩ | P s p i}
     ∪ {s p , ⟨GET :: c, s, p, U ⟩ |  P s p U}).
  = {auto}
    ({s p i , ⟨GET :: c, s, p, i ⟩ | P s p i}).
  [].
Qed.
