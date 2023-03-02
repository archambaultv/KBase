From Coq Require Import Lia.

Create HintDb KBaseHints.
Hint Constants Transparent : KBaseHints.

Ltac simplHyp :=
  repeat match goal with
  | [ H : ex _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _] => destruct H
  | [ H : ?x < 1 |- _] => assert (x = 0) by lia; subst; clear H
  | [ H : ?x <= 0 |- _] => assert (x = 0) by lia; subst; clear H
  end.

Ltac autoSpecialize :=
  match goal with
  | [H : forall y, ?foo ?x y -> ?p, 
     H2: ?foo ?x ?z |- _ ] => pose proof (H z H2)
  | [H : forall x y, ?foo x y -> ?p, 
     H2: ?foo ?x ?y |- _ ] => pose proof (H x y H2)
  end.

Ltac autodestruct :=
  match goal with
    | [|- context [if ?x then _ else _]] => 
          let Hx := fresh "Hx" in destruct x eqn: Hx
    | [|- context [match ?x with | _ => _ end]] => 
          let Hx := fresh "Hx" in destruct x eqn: Hx
  end.

Ltac autoInversion :=
  match goal with
    | [ H : _ |- _ ] => solve [inversion H]
  end.

Ltac lia' := try lia; try (elimtype False; lia).

(** The following tactic is inspired by the tactic with the same name in the book CPDT
  by Adam Chlipala (http://adam.chlipala.net/cpdt/)*)
Ltac crush' intuitionTac := 
  let sintuition :=
    (simpl in *; 
    intuition intuitionTac; 
    try subst;
    try congruence)

  with rewriter := idtac;
     (match goal with
        | [ H : _ |- _ ] => rewrite H by (crush' intuitionTac)
      end)

  with f_apply := idtac;
      (match goal with
        | [ |- ?F ?x = ?F ?y] => 
            assert (x = y) by (crush' intuitionTac); 
            congruence
        | [ |- ?F ?x1 ?x2 = ?F ?y1 ?y2] => 
            assert (x1 = y1) by (crush' intuitionTac); 
            assert (x2 = y2) by (crush' intuitionTac);
            congruence
        | [ |- ?F ?x1 ?x2 ?x3 = ?F ?y1 ?y2 ?y3] => 
            assert (x1 = y1) by (crush' intuitionTac); 
            assert (x2 = y2) by (crush' intuitionTac);
            assert (x3 = y3) by (crush' intuitionTac);
            congruence
        end) in

  intuitionTac; 
  sintuition; 
  try rewriter; 
  sintuition; 
  try f_apply; 
  lia'.

Ltac elnauto := auto with bool arith sets KBaseHints.
Ltac elneauto := eauto with bool arith sets KBaseHints.

Ltac crush := crush' elnauto.
Ltac ecrush := crush' elneauto.
