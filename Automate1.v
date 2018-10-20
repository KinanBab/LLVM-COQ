Ltac unfold_interp1 :=
  unfold interp_cmp; unfold interp_binop; unfold interp_store; unfold interp_push; unfold interp_pop.

Ltac try_step := 
  try (eapply StepPush; simplify; equality); 
  try (eapply StepPop; simplify; equality);
  try (eapply StepLoad; simplify; equality); 
  try (eapply StepStore; simplify; equality);
  try (eapply StepBinop; simplify; equality); 
  try (eapply StepIf; simplify; equality);
  try (eapply StepJump; simplify; equality); 
  try (eapply StepCall; simplify; equality);
  try (eapply StepExit; simplify; equality);
  try (eapply StepReturn; simplify; equality);
  try (eapply StepExitReturn; simplify; equality).

Ltac many_steps := repeat (econstructor; try_step; simplify; unfold_interp1; simplify).