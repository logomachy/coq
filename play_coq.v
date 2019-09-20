(*First theorem play *)
(* parametrized by set , proposition (truth value) *)
Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x: A, q /\ p x) <-> (q /\ exists x : A , p x).
  (*there exists x in A such that q /\ p of x  (is the same thing) <=> as q and exists in A such that p of x*)
  
  
  
Proof.
  split. (* if and only if  =  implication both ways -> split to 2 subgoals*)
  intros. (*for implication/forall take hypothesis H*)
  destruct H as [y [H1 H2]]. (*destruct the hypothesis*)
  split.
  assumption.
  exists y.
  assumption.
  intros [H1 [y H2]].
  exists y.
  split.
  assumption.
  assumption.
  Qed.

(**)
Theorem frobenius2 (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x: A, q /\ p x) <-> (q /\ exists x : A , p x).
  
Proof.
  split.
  intros.
  destruct H as [y [H1 H2]].
  split.
  assumption.
  exists y.
  assumption.
  intros [H1 [y H2]].
  exists y.
  auto.
  Qed.
  
Theorem frobenius3 (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x: A, q /\ p x) <-> (q /\ exists x : A , p x).
  (*there exists x in A such that q /\ p of x  (is the same thing) <=> as q and exists in A such that p of x*)
Proof.
  split. (* if and only if  =  implication both ways -> split to 2 subgoals*)
  intros [y [H1 H2]]. (*for implication/forall take hypothesis H*)
  split.
  assumption.
  exists y.
  assumption.
  intros [H1 [y H2]].
  exists y.
  split; assumption.
  Qed.
  
(*First order logic*)
Theorem frobenius4 (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x: A, q /\ p x) <-> (q /\ exists x : A , p x).
  (*there exists x in A such that q /\ p of x  (is the same thing) <=> as q and exists in A such that p of x*)
Proof.
  firstorder.
  Qed.

  
Check frobenius.
Print frobenius2.
Check frobenius4.






  
  
  
Save.
