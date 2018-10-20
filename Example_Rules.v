Require Import Frap.
Load Model.
Load Automate.

Module FactorialRules.

  (* Example Program: Factorial *)
  Example factorial_prog := rev ([
      (* Assume input already on stack *)
      (* Fact function *)
      "tmp" <- Pop();
      Push <- "tmp";
      Push(0)
      ] ++
      When ( Op(==) ) Then [ Push(1); Return ] Else [
        Push <- "tmp";
        Push(1);
        Op(-);
        Push 1; (* Go back to the top *)
        Call;
        Push <- "tmp";
        Op(_*);
        Return
      ]).

  Compute factorial_prog.

  (* General Helpers about properties of our semantics *)
  Theorem StepTransitiveInversion : 
    forall x0 x1,
    step ^* x0 x1 -> (exists y, step ^* x0 y /\ step y x1) \/ x0 = x1.
  Proof.
    simplify.

    induct H.
    + equality.
    + first_order.
      - constructor.
        exists x0.
        propositional.
        apply TrcFront with (y := y); assumption.
      - constructor.
        exists x.
        propositional.
        * constructor.
        * rewrite H1 in *.
          assumption.
  Qed.

  (* Turn our semantics into a transition system to help prove rules as invariants *)
  Inductive factorial_initial (input : nat) :
  (instructions * nat * stack * valuation * callstack) -> Prop :=
    | FactorialInitial : factorial_initial input (factorial_prog, 1, [input], $0, []).

  Definition factorial_sys (input : nat) :
  trsys (instructions * nat * stack * valuation * callstack) := {|
    Initial := factorial_initial input;
    Step := step
  |}.

  (* Sample rules formalized as invariant *)
  Definition ProgramInvariant (prg : instructions)
  (state : (instructions * nat * stack * valuation * callstack)) : Prop :=
  let (state, _) := state in
  let (state, _) := state in
  let (state, _) := state in
  let (pr, pc) := state in
    pr = prg.

  Theorem ProgramIsInvariant : forall input,
    invariantFor (factorial_sys input) (ProgramInvariant factorial_prog).
  Proof.
    simplify.
    apply invariant_induction; simplify.
    + invert H; simplify; equality.
    + cases s; cases p; cases p; cases p.
      cases s'; cases p; cases p; cases p.
      simplify.
      rewrite H in *. clear H.
      invert H0; try equality.
      - match goal with
        | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
        | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
        | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
        end; equality.
      - match goal with
        | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
        | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
        | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
        end; equality.
      - match goal with
        | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
        | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
        | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
        end; equality.
  Qed.

  Definition ReturnToCallInvariant (calls : list nat)
  (state : (instructions * nat * stack * valuation * callstack)) : Prop :=
    let (_, cv) := state in
      forall addr vv, In (addr, vv) cv -> In addr calls.

  Definition StrongerReturnInvariant (pr : instructions) (calls : list nat)
    (state : (instructions * nat * stack * valuation * callstack)) : Prop :=
      ReturnToCallInvariant calls state /\ ProgramInvariant pr state.

  Theorem ReturnIsInvariant : forall input,
    invariantFor (factorial_sys input) (ReturnToCallInvariant [13]).
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := StrongerReturnInvariant factorial_prog [13]).
    + apply invariant_induction; simplify.
      - unfold StrongerReturnInvariant.
        invert H. simplify. propositional.
      - cases s. cases p. cases p. cases p.
        cases s'. cases p. cases p. cases p.
        unfold StrongerReturnInvariant in *.
        propositional;
        unfold ProgramInvariant in *;
        rewrite H2 in *; clear H2.
        * assert (i0 = factorial_prog) by (invert H0; try equality;
          match goal with
          | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
          | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
          | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
          end; equality).

          rewrite H in *. clear H.
          invert H0.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end; first_order.
         ** unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end.
         ** match goal with
             | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
             end.
           unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end; first_order.
         ** unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end; first_order.
         ** unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end; first_order.
         ** match goal with
             | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
             end.
           unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end; first_order.
        ** unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end; first_order.
        ** match goal with
             | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
             end.
           unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end; first_order.
           assert (addr = S n) by equality.
           assert (13 = addr) by linear_arithmetic.
           propositional.
        ** unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end.
        ** unfold instruction_per_index in H3;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end; first_order.
        ** unfold instruction_per_index in H2;
           simplify;
           repeat match goal with
           | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
            cases (pc ==n E); simplify; try equality
           end.
      * invert H0; try equality;
          match goal with
          | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
          | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
          | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
          end; equality.

    + simplify; unfold StrongerReturnInvariant in *; propositional.
  Qed.

  Definition CallFunctionStartInvariant (functions : list nat)
  (state : (instructions * nat * stack * valuation * callstack)) : Prop :=
    let (state, _) := state in
    let (state, _) := state in
    let (state, st) := state in
    let (pr, pc) := state in
      match (instruction_per_index pc pr) with
      | Call => 
        match st with
        | nil => False
        | cons addr _ => In addr functions
        end
      | _ => True
      end.

Check use_invariant.

  Definition StrongerCallFunctionInvariant (input : nat) (pr : instructions) (functions: list nat) (calls: list nat)
    (state : (instructions * nat * stack * valuation * callstack)) : Prop :=
      CallFunctionStartInvariant functions state /\ ProgramInvariant pr state /\ ReturnToCallInvariant calls state
      /\ step ^* (factorial_prog, 1, [input], $0, []) state.

  Theorem CallRule1 : forall input,
    invariantFor (factorial_sys input) (CallFunctionStartInvariant [1]).
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := StrongerCallFunctionInvariant input factorial_prog [1] [13]).
    * apply invariant_induction; simplify; unfold StrongerCallFunctionInvariant; propositional.
      + invert H; simplify; propositional.
      + invert H; simplify; propositional.
      + invert H; simplify; propositional.
      + invert H; constructor.
      + cases s. cases p. cases p. cases p.
        cases s'. cases p. cases p. cases p.
        unfold StrongerCallFunctionInvariant in *.
        propositional;
        unfold ProgramInvariant in *;
        rewrite H in *; clear H.
        - assert (i0 = factorial_prog) by (invert H0; try equality;
          match goal with
          | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
          | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
          | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
          end; equality).

          rewrite H in *. clear H.
          assert (T := H0).
          invert H0.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end.
          ** match goal with
             | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
             end.
             unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end.
             rewrite e in *.
             clear e n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11.
             assert (c1 = Op(==)) by equality; assert (e_addr = 3) by equality.
             rewrite H in *; rewrite H0 in *.
             clear H H0 H2.
             match goal with
             | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
             end.
             cases b.
             ++ simplify. propositional.
             ++ simplify. propositional.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
              cases (pc ==n E); simplify; try equality
             end.
             assert (n1 = 8) by equality.
             rewrite H in *. clear H H2. rewrite e in *. 
             clear e n0 n1 n2 n3 n4 n5 n6 n7 n8.
             simplify. propositional.
          ** match goal with
             | [H : (let (vs', vv') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (b, vs') := ?V in ?E) = _ |- _ ] => cases V
             | [H : (let (n0, vs') := ?V in ?E) = _ |- _ ] => cases V
             end.
             unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
               cases (pc ==n E); simplify; try equality
             end.
             rewrite e in *. clear e n2 n3 n4 H2.
             unfold_interp.
             cases s; simplify; try equality.
             propositional.
             symmetry in H. assert (n1 = n2) by equality.
             assert (s = s1) by equality. rewrite H in *.
             rewrite H0 in *. rewrite H1 in *. clear H H0 H1 Heq.
             simplify. propositional.
          ** unfold_interp. unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
               cases (pc ==n E); simplify; try equality
             end.
          ** unfold ReturnToCallInvariant in *.
             specialize H2 with (n0) (v0).
             assert (In (n0, v0) ((n0, v0) :: c0)) by (simplify; propositional).
             propositional.
             assert (13 = n0) by (simplify; propositional).
             symmetry in H2.
             rewrite H2 in *.
             clear H2 H0 H.
             simplify.
             propositional.
          ** unfold instruction_per_index in H2;
             simplify;
             repeat match goal with
             | [H : context[if (?pc ==n ?E) then _ else _] |- _ ] =>
             cases (pc ==n E); simplify; try equality
             end.

      + unfold StrongerCallFunctionInvariant in H.
        propositional.
        pose ProgramIsInvariant.
        specialize i with input.
        eapply use_invariant with (invariant := ProgramInvariant (factorial_prog)) (s'0 := s').
        - exact i.
        - simplify. 
          apply trc_trans with (s). exact H4.
          econstructor. exact H0. constructor.
        - simplify. constructor.
      + unfold StrongerCallFunctionInvariant in H.
        propositional.
        pose ReturnIsInvariant.
        specialize i with input.
        eapply use_invariant with (invariant := ReturnToCallInvariant [13]) (s'0 := s').
        - exact i.
        - simplify. 
          apply trc_trans with (s). exact H4.
          econstructor. exact H0. constructor.
        - simplify. constructor.
      + unfold StrongerCallFunctionInvariant in H.
        propositional.
        apply trc_trans with (s). assumption.
        econstructor. exact H0. constructor.
    * simplify; unfold StrongerCallFunctionInvariant in *; propositional.
  Qed.
End FactorialRules.

