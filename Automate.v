Ltac twoNatsEqualLtac n m :=
  match n with
  | 0 => 
    match m with
    | 0 => true
    | _ => false
         end
  | S ?n' => 
    match m with
    | 0 => true
    | S ?m' => twoNatsEqualLtac n' m'
    end
  end.

Ltac listLengthLtac ls :=
match ls with
  | nil => O
  | _ :: ?ls' =>
    let ls'' := listLengthLtac ls' in
      constr:(S ls'')
end.

Ltac instructionIndexLtac i p :=
  match p with
  | nil => constr:(Exit)
  | cons ?ins ?p' =>
    let l := listLengthLtac p' in
    let l' := constr:(S l) in
    let eq := (twoNatsEqualLtac i l') in
      match eq with
      | true => ins
      | false => let ins := instructionIndexLtac i p' in ins
      end
  end.

Ltac unfold_interp :=
  unfold interp_cmp in *;
  unfold interp_binop in *;
  unfold interp_store in *;
  unfold interp_load in *;
  unfold interp_push in *;
  unfold interp_pop in *.

Ltac smartStep :=
  econstructor; unfold_interp; simplify;
  match goal with
  | [ |- step ^* _ _] => simplify
  | [ |- step (?pr, ?pc, ?vs, ?vv, ?cv) _] =>
    match pr with
    | nil => simplify; constructor
    | _ =>
      try let ins := (instructionIndexLtac pc pr) in
      match ins with
      | Exit => eapply StepExit
      | Push _ => eapply StepPush
      | Pop => eapply StepPop
      | Load _ => eapply StepLoad
      | Store _ => eapply StepStore
      | Binop _ => eapply StepBinop
      | If _ _ => eapply StepIf
      | Jump _ => eapply StepJump
      | Call => eapply StepCall
      | Return => (* Check for empty call stack *)
        match cv with
        | nil => eapply StepExitReturn
        | _ => eapply StepReturn
        end
      end; simplify; try equality
    end
  end.
