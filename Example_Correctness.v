Require Import Frap.


Module FactorialCorrectness.
  Load Model.

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

  (* Examples just to get a feel of the system
     Proving correctness of our factorial example program in many ways *)
  Theorem factorial1_correct : step^* (factorial_prog, 1, [1], $0, nil) (factorial_prog, 0, [1], $0, nil).
  Proof.
    unfold factorial_prog.
    simplify.

    (* This segment of the proof is repeated for as many times
       as we recurse *)
    econstructor.
    eapply StepLoad.
    simplify. equality. simplify.

    econstructor.
    eapply StepStore.
    simplify. equality. simplify.

    econstructor.
    eapply StepPush.
    simplify. equality. simplify.

    econstructor.
    eapply StepIf.
    simplify. equality. simplify.
    unfold interp_cmp; unfold interp_store; unfold interp_push; unfold interp_pop; simplify.

    econstructor.
    eapply StepStore.
    simplify. equality. simplify.

    econstructor.
    eapply StepPush. 
    simplify. equality. simplify.

    econstructor.
    eapply StepBinop. 
    simplify. equality. simplify.

    econstructor.
    eapply StepPush. 
    simplify. equality. simplify.

    econstructor.
    eapply StepCall.
    simplify. equality. simplify.

    (* Recursion Call *)

    econstructor.
    eapply StepLoad.
    simplify. equality. simplify.
    unfold interp_cmp; unfold interp_store; unfold interp_push; unfold interp_pop; simplify.

    econstructor.
    eapply StepStore.
    simplify. equality. simplify.

    econstructor.
    eapply StepPush.
    simplify. equality. simplify.

    econstructor.
    eapply StepIf.
    simplify. equality. simplify.
    unfold interp_cmp; unfold interp_store; unfold interp_push; unfold interp_pop; simplify.

    econstructor.
    eapply StepPush. 
    simplify. equality. simplify.

    econstructor.
    eapply StepReturn. 
    simplify. equality. equality. simplify.

    (* Return From Recursion Call *)

    econstructor.
    eapply StepStore. 
    simplify. equality. simplify.

    econstructor.
    eapply StepBinop. 
    simplify. equality. simplify.

    econstructor.
    eapply StepExitReturn. 
    simplify. equality. simplify.
    unfold interp_cmp; unfold interp_store; unfold interp_push; unfold interp_pop; simplify.

    constructor.
  Qed.

  (* That was boring, I will try to automate this by attempting to apply whatever step that works *)
  Load Automate1.

  Theorem factorial1_correct' : step^* (factorial_prog, 1, [1], $0, nil) (factorial_prog, 0, [1], $0, nil).
  Proof.
    unfold factorial_prog.
    simplify.

    many_steps.
  Qed.

  (* We can make the automated step smarter, by picking the one that matches the targeted instruction *)
  Load Automate.

  Theorem factorial2_correct'' : step^* (factorial_prog, 1, [2], $0, []) (factorial_prog, 0, [2], $0, []).
  Proof.
    unfold factorial_prog.
    simplify.

    repeat smartStep.
  Qed.

  Theorem factorial3_correct'' : step^* (factorial_prog, 1, [3], $0, []) (factorial_prog, 0, [6], $0, []).
  Proof.
    unfold factorial_prog.
    simplify.

    repeat smartStep.
  Qed.

  Theorem factorial4_correct'' : step^* (factorial_prog, 1, [4], $0, []) (factorial_prog, 0, [24], $0, []).
  Proof.
    unfold factorial_prog.
    simplify.

    repeat smartStep.
  Qed.

  (* Prove factorial is correct for all inputs *)
  Fixpoint actual_factorial (n: nat) : nat := 
    match n with
    | 0 => 1
    | S n' => n * actual_factorial n'
    end.

  Lemma factorial_almost_correct : forall n st vs,
    n > 0 -> exists vv, step^* (factorial_prog, 1, n :: st, $0, vs) (factorial_prog, 15, (actual_factorial n) :: st, vv, vs).
  Proof.
    first_order.
    induct n.
    + linear_arithmetic.
    + cases (n).
      - simplify. eexists. simplify.
        unfold factorial_prog in *; simplify.
        repeat smartStep.
      - unfold factorial_prog in *; simplify.
        smartStep. smartStep.
        smartStep. smartStep.
        smartStep. smartStep.
        smartStep. smartStep.
        smartStep. smartStep.

        clear H.
        unfold_interp; simplify.
        specialize IHn with (st := st).
        specialize IHn with (vs := (13, $0 $+ ("tmp", S (S (n)))) :: vs).
        assert (S n > 0) by linear_arithmetic.
        propositional. clear H.
         first_order.

        eapply trc_trans.
        * exact H.
        * smartStep. smartStep. smartStep. 
          unfold_interp; simplify.
          assert 
            ((actual_factorial (n)) + n * (actual_factorial (n)) + ((actual_factorial (n))
             + n * (actual_factorial (n)) + n * ((actual_factorial (n)) + n * (actual_factorial (n))))
             = actual_factorial (S (S n)))
          by (simplify; linear_arithmetic).
          rewrite H0. clear H0.
          assert 
            ((((actual_factorial (n)) + n * (actual_factorial (n))) * (S (S (n))))
             = actual_factorial (S (S n)))
          by (simplify; ring).
          rewrite H0. clear H0. clear H.
          constructor.
  Qed.


  Theorem factorail_correct : forall n,
    step^* (factorial_prog, 1, [n], $0, []) (factorial_prog, 0, [actual_factorial n], $0, []).
  Proof.
    simplify.
    cases n.
    + unfold factorial_prog; repeat smartStep.
    + pose factorial_almost_correct.
      specialize e with (n := S n) (st := []) (vs := []).
      assert (S n > 0) by linear_arithmetic.
      first_order.
      eapply trc_trans.
      - exact H0.
      - unfold factorial_prog; simplify; repeat smartStep.
  Qed.

End FactorialCorrectness.
