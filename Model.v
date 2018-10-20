(* Helpers *)
Fixpoint lessThan (n m: nat) : bool :=
  match (n, m) with
  | (0, 0) => false
  | (S n', 0) => false
  | (0, S m') => true
  | (S n', S m') => lessThan n' m'
  end.

Fixpoint lessEq (n m: nat) : bool :=
  match (n, m) with
  | (0, 0) => true
  | (S n', 0) => false
  | (0, S m') => true
  | (S n', S m') => lessEq n' m'
  end.

(* Valuation: a map from variable to values *)
Definition valuation := fmap var nat.

(* Stack: list is used as a stack with cons *)
Definition stack := list nat.

(* Stack: call stack for recursion, used to determine return location *)
Definition callstack := list (nat * valuation).

(* Binary Arithmetic *)
Inductive binop := Add | Sub | Mult.

(* Comparisons *)
Inductive cmp := | Eq | Ne | Lt | Le.

(* Instruction set *)
Inductive instruction :=
  | Exit (* Exit execution completely *)
  | Push (v: nat) (* Push value/variable into stack *)
  | Pop (* Discard of last value on stack *)
  | Load (v: var) (* Pop and store value in v *)
  | Store (v: var) (* Push value of v into stack *)
  | Binop (op: binop) (* Performs operation on two top variables in stack and pushes result *)
  (* | Input *)
  | If (c: cmp) (else_address: nat) (* relative address for body of else *)
  | Jump (n: nat) (* relative address to jump to *)
  | Return 
  | Call.

Definition instructions := list instruction.

(* (* data at memory location is either a value or an instruction *)
Inductive mem := 
| MemValue (v: nat)
| MemInst (i: instruction).

(* memory maps pointers to values/instructions *)
Definition memory := fmap nat mem. *)

(* Interpreters for particular kinds of instructions *)
Definition interp_pop (vstack: stack) : (nat * stack) :=
  match vstack with
  | nil => (0, nil)
  | cons v vs' => (v, vs')
  end.

Definition interp_push (v: nat) (vstack: stack) : stack :=
  cons v vstack.

Definition interp_load (v: var) (vstack: stack) (vals: valuation) : (stack * valuation) :=
  let (o1, vs1) := interp_pop vstack in
    (vs1, vals $+ (v, o1)).

Definition interp_store (v: var) (vstack: stack) (vals: valuation) : stack :=
  match vals $? v with
  | None => interp_push 0 vstack
  | Some v' => interp_push v' vstack
  end.

Definition interp_binop (op: binop) (vstack: stack) : stack :=
  let (o1, vs1) := interp_pop vstack in
  let (o2, vs2) := interp_pop vs1 in 
    cons (match op with
    | Add => o2 + o1
    | Sub => o2 - o1
    | Mult => o2 * o1
    end) vs2.

(* 0 means true, otherwise false *)
Definition interp_cmp (c: cmp) (vstack: stack) : (bool * stack) :=
  let (o1, vs1) := interp_pop vstack in
  let (o2, vs2) := interp_pop vs1 in 
    (match c with
    | Eq => if o1 ==n o2 then true else false
    | Ne => if o1 ==n o2 then false else true
    | Lt => lessThan o2 o1
    | Le => lessEq o2 o1
    end, vs2).

(* Syntactic Sugar for IL *)
Notation "Exit()" := Exit (at level 75).
Notation "Push ( x )" := (Push x%nat) (at level 75).
Notation "Pop()" := (Pop) (at level 75).
Notation "x <- Pop()" := (Load x) (at level 75).
Notation "Push <- x" := (Store x) (at level 75).

Notation "'When' ( c ) 'Then' i 'Else' e" := ( [ If c (S (length i)) ] ++ i ++ [ Jump (length e)] ++ e ) (at level 75).

Notation "Op(+)" := (Binop Add) (at level 75). 
Notation "Op(-)" := (Binop Sub) (at level 75).
Notation "Op(_*)" := (Binop Mult) (at level 75).

Notation "Op(==)" := (Eq) (at level 75).
Notation "Op(!=)" := (Ne) (at level 75).
Notation "Op(<)" := (Lt) (at level 75).
Notation "Op(<=)" := (Le) (at level 75).

(* Example Small-Step Semantics *)
Fixpoint instruction_per_index (i: nat) (p: instructions) : instruction :=
  match p with
  | nil => Exit
  | cons ins p' => if i ==n S (length p') then ins else instruction_per_index i p'
  end.

Fixpoint peek (vstack: stack) : nat :=
  match vstack with
  | nil => 0
  | cons n _ => n
  end.

Inductive step : instructions * nat * stack * valuation * callstack  -> 
                 instructions * nat * stack * valuation * callstack -> 
                 Prop :=
  | StepPush : forall pr pc vs vv cv n,
    instruction_per_index pc pr = Push n
    -> step (pr, pc, vs, vv, cv) (pr, S pc, interp_push n vs , vv, cv)
  | StepPop : forall pr pc vs vv cv,
    instruction_per_index pc pr = Pop
    -> step (pr, pc, vs, vv, cv) (pr, S pc, let (_, vs') := interp_pop vs in vs', vv, cv)
  | StepLoad : forall pr pc vs vv cv v,
    instruction_per_index pc pr = Load v
    -> step (pr, pc, vs, vv, cv) (let (vs', vv') := interp_load v vs vv in (pr, S pc, vs', vv', cv))
  | StepStore : forall pr pc vs vv cv v,
    instruction_per_index pc pr = Store v
    -> step (pr, pc, vs, vv, cv) (pr, S pc, interp_store v vs vv, vv, cv)
  | StepBinop : forall pr pc vs vv cv op,
    instruction_per_index pc pr = Binop op
    -> step (pr, pc, vs, vv, cv) (pr, S pc, interp_binop op vs, vv, cv)
  | StepIf : forall pr pc vs vv cv c e_addr,
    instruction_per_index pc pr = (If c e_addr)
    -> step (pr, pc, vs, vv, cv) 
       (let (b, vs') := interp_cmp c vs in (pr, S (if b then pc else e_addr + pc), vs', vv, cv) )
  | StepJump : forall pr pc vs vv cv n, 
    instruction_per_index pc pr = Jump n
    -> step (pr, pc, vs, vv, cv) (pr, S (pc + n), vs, vv, cv)
  | StepCall : forall pr pc vs vv cv,
    instruction_per_index pc pr = Call (* Save caller and variables in scope on the call stack *)
    -> step (pr, pc, vs, vv, cv) (let (n, vs') := interp_pop vs in (pr, n, vs', $0, cons (S pc, vv) cv))
  | StepExit : forall pr pc vs vv cv,
    instruction_per_index pc pr = Exit
    -> step (pr, pc, vs, vv, cv) (pr, 0, let (o, _) := interp_pop vs in [o], $0, nil)
  | StepReturn : forall pr pc vs vv cv rpc rvv rcv,
    instruction_per_index pc pr = Return (* Go back to the location and scope stored in call stack *)
    -> cv = cons (rpc, rvv) rcv
    -> step (pr, pc, vs, vv, cv) (pr, rpc, vs, rvv, rcv)
  | StepExitReturn : forall pr pc vs vv,
    instruction_per_index pc pr = Return (* Return with an empty call stack is equivalent to exit *)
    -> step (pr, pc, vs, vv, nil) (pr, 0, let (o, _) := interp_pop vs in [o], $0, nil).

