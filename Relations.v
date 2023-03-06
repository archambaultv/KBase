From Coq Require Import Relations.
From Coq Require Import Relations.Relation_Operators.
From KBase Require Import Tactics.

Section Definitions.

Context {A : Type}.

(* Most of this file is inspired by "Confluence and Normalization in Reduction Systems Lecture Notes"
   by Gert Smolka of Saarland University. December 16, 2015
   https://www.ps.uni-saarland.de/courses/sem-ws15/ars.pdf *)

Definition joinable (R : relation A) (x y : A) : Prop :=
  exists z, R x z /\ R y z.

Definition diamond (R : relation A) : Prop :=
  forall x y z, R x y -> R x z -> joinable R y z.

Definition confluent (R : relation A) : Prop :=
  diamond (clos_refl_trans_1n A R).

Definition semi_confluent (R : relation A) : Prop :=
  forall x y z, 
    R x y -> 
    clos_refl_trans_1n A R x z -> 
    joinable (clos_refl_trans_1n A R) y z.

Definition locally_confluent (R : relation A) : Prop :=
  forall x y z, 
    R x y -> 
    R x z -> 
    joinable (clos_refl_trans_1n A R) y z.

Definition reducible (R : relation A) (x : A) : Prop :=
  exists z, R x z.

Definition normal (R : relation A) (x : A) : Prop :=
  ~ (reducible R x).

Definition terminal (R : relation A) (x y : A) : Prop :=
  clos_refl_trans_1n A R x y /\ normal R y.

  (* Weak normalization *)
Definition WN (R : relation A) (x : A) : Prop :=
  exists z, terminal R x z.

  (* Strong normalization *)
Inductive SN (R : relation A) (x : A) : Prop :=
  | sn_intro : (forall y, R x y -> SN R y) -> SN R x.

Definition terminating (R : relation A) : Prop :=
    forall x, SN R x.

Fixpoint apply_n (n : nat) (f : A -> A) : A -> A :=
  match n with
    | 0 => fun x => x
    | S n => fun x => f (apply_n n f x)
  end. 

Definition triangle_op (R : relation A) (f : A -> A) : Prop :=
    forall x y, R x y -> R y (f x).

End Definitions.

#[global] Hint Resolve clos_rt1n_step : KBaseHints.
#[global] Hint Resolve rt1n_refl : KBaseHints.

Theorem clos_rt1n_trans : forall (A : Type) (R : relation A) x y z,
  clos_refl_trans_1n A R x y ->
  clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  intros A R x y z x_y y_z;
  apply clos_rt_rt1n;
  apply clos_rt1n_rt in x_y;
  apply clos_rt1n_rt in y_z;
  eauto using rt_trans.
Qed.

Theorem clos_rt1n_right : forall (A : Type) (R : relation A) x y z,
  clos_refl_trans_1n A R x y ->
  R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  intros A R x y z x_y y_z;
  apply (clos_rt1n_trans A R x y z); auto using clos_rt1n_step.
Qed.

#[global] Hint Extern 1 (clos_refl_trans_1n ?A ?R ?x ?z) =>
  match goal with
  | H1: clos_refl_trans_1n A R x ?y,
    H2: clos_refl_trans_1n A R ?y z |- _ => exact (clos_rt1n_trans A R x y z H1 H2)
  | H: R x ?y |- _ => apply (rt1n_trans A R x y z H)
  | H: clos_refl_trans_1n A R ?y z |- _ => apply (rt1n_trans A R x y z)
  | H: R ?y z |- _ => apply (clos_rt1n_right A R x y z)
  end : KBaseHints.

Section Properties.
  Context {A : Type}.

  (* Facts about clos_refl_trans_1n *)

  Theorem idempotence_rt : forall (R : relation A),
    same_relation A (clos_refl_trans_1n A R) 
      (clos_refl_trans_1n A (clos_refl_trans_1n A R)).
  Proof.
    split; intros x y x_y.
    - crush.
    - induction x_y; crush.
  Qed. 
  #[local] Hint Resolve idempotence_rt : KBaseHints.

  Theorem monotonicity_rt : forall R1 R2, 
    inclusion A R1 R2 -> 
    inclusion A (clos_refl_trans_1n A R1) (clos_refl_trans_1n A R2).
  Proof.
    unfold inclusion;
    intros R1 R2 H x y x_y;
    induction x_y; crush; autoSpecialize; crush.
  Qed.
  #[local] Hint Resolve monotonicity_rt : KBaseHints.

  Theorem preserve_rt : forall (R : relation A) (f : A -> A) x y,
    (forall x y, R x y -> R (f x) (f y)) ->
    clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R (f x) (f y).
  Proof.
    intros R f x y H x_y;
    induction x_y; crush.
  Qed.

  Theorem preserve_rt_left : forall (R : relation A) (f : A -> A -> A) x1 x2 z,
    (forall x1 x2 z, R x1 x2 -> R (f x1 z) (f x2 z)) ->
    clos_refl_trans_1n A R x1 x2 -> 
    clos_refl_trans_1n A R (f x1 z) (f x2 z).
  Proof.
    intros R f x1 x2 z HLeft x1_x2.
    exact (preserve_rt R (fun x => f x z) x1 x2 
      (fun x1 x2 x1_x2 => HLeft x1 x2 z x1_x2) x1_x2).
  Qed.
  #[local] Hint Resolve preserve_rt_left : KBaseHints.

  Theorem preserve_rt_right : forall (R : relation A) (f : A -> A -> A) x z1 z2,
    (forall x z1 z2, R z1 z2 -> R (f x z1) (f x z2)) ->
    clos_refl_trans_1n A R z1 z2 -> 
    clos_refl_trans_1n A R (f x z1) (f x z2).
  Proof.
    intros R f x z1 z2 HRight z1_z2;
    exact (preserve_rt R (fun z => f x z) z1 z2 
      (fun z1 z2 z1_z2 => HRight x z1 z2 z1_z2) z1_z2).
  Qed.
  #[local] Hint Resolve preserve_rt_right : KBaseHints.

  Theorem preserve_rt_para : forall (R : relation A) (f : A -> A -> A) x1 x2 z1 z2,
    (forall x1 x2 z, R x1 x2 -> R (f x1 z) (f x2 z)) ->
    (forall x z1 z2, R z1 z2 -> R (f x z1) (f x z2)) ->
    clos_refl_trans_1n A R x1 x2 -> 
    clos_refl_trans_1n A R z1 z2 -> 
    clos_refl_trans_1n A R (f x1 z1) (f x2 z2).
  Proof.
    intros R f x1 x2 z1 z2 HLeft HRight x1_x2 z1_z2;
    pose proof (preserve_rt_left R f x1 x2 z1 HLeft  x1_x2) as H1;
    pose proof (preserve_rt_right R f x2 z1 z2 HRight  z1_z2) as H2.
    crush.
  Qed.

  (* Facts about confluence and friend *)

  Theorem confluent_semi_confluent : forall (R : relation A),
  confluent R -> semi_confluent R.
  Proof.
    intros R C x y1 y2 x_y1 x_y2;
    destruct (C x y1 y2 (clos_rt1n_step _ _ _ _ x_y1) x_y2);
    ecrush.
  Qed.

  Theorem semi_confluent_confluent : forall (R : relation A),
  semi_confluent R -> confluent R.
  Proof.
    unfold semi_confluent.
    intros R D x y1 y2 y1H; generalize dependent y2.
    induction y1H as [x | x y z x_y y_z H]; 
    intros y2 x_y2; unfold joinable.
    - ecrush.
    - destruct (D x y y2 x_y x_y2) as [u [y_u y2_u]];
      destruct (H u y_u) as [v [z_v u_v]];
      ecrush.
  Qed. 
  #[local] Hint Resolve semi_confluent_confluent : KBaseHints.

  Lemma diamond_semi_confluent : forall (R : relation A),
    diamond R ->
    semi_confluent R.
  Proof.
    intros R D x y1 y2 x_y1 x_y2; generalize dependent y1;
    induction x_y2 as [x | x y2 z2 x_y2 y2_z2 H]; 
    intros y1 x_y1; unfold joinable.
    - ecrush.
    - destruct (D x y1 y2 x_y1 x_y2) as [u [y1_u y2_u]].
      destruct (H u y2_u);
      ecrush.
  Qed.
  #[local] Hint Resolve diamond_semi_confluent : KBaseHints.

  Lemma sandwich_same_rt : forall R1 R2,
    inclusion A R1 R2 ->
    inclusion A R2 (clos_refl_trans_1n A R1) ->
    same_relation A (clos_refl_trans_1n A R1) (clos_refl_trans_1n A R2).
  Proof.
    intros R1 R2 H1 H2;
    pose proof (monotonicity_rt R1 R2 H1) as H3;
    pose proof (monotonicity_rt R2 (clos_refl_trans_1n A R1) H2) as H4;
    pose proof (idempotence_rt R1) as [_ H5];
    split; ecrush.
  Qed.
  #[local] Hint Resolve sandwich_same_rt : KBaseHints.

  Lemma sandwich_confluence : forall R1 R2,
    inclusion A R1 R2 ->
    inclusion A R2 (clos_refl_trans_1n A R1) ->
    confluent R1 <-> confluent R2.
  Proof.
    intros R1 R2 R1inR2 R2inR1rt; 
    destruct (sandwich_same_rt _ _ R1inR2 R2inR1rt) as [H1 H2];
    split; 
    intros C x y z x_y x_z; unfold joinable.
    - assert (x_y_1 : clos_refl_trans_1n A R1 x y) by crush.
      assert (x_z_1 : clos_refl_trans_1n A R1 x z) by crush.
      destruct (C x y z x_y_1 x_z_1).
      ecrush.
    - assert (x_y_2 : clos_refl_trans_1n A R2 x y) by crush.
      assert (x_z_2 : clos_refl_trans_1n A R2 x z) by crush.
      destruct (C x y z x_y_2 x_z_2).
      ecrush.
  Qed.
  #[local] Hint Resolve sandwich_confluence : KBaseHints.

  Lemma sandwich_diamond : forall R1 R2,
    inclusion A R1 R2 ->
    inclusion A R2 (clos_refl_trans_1n A R1) ->
    diamond R2 -> confluent R1.
  Proof.
    intros R1 R2 H1 H2 D;
    assert (H : confluent R2) by crush;
    pose proof (sandwich_confluence R1 R2 H1 H2) as H3;
    crush.
  Qed.
  #[local] Hint Resolve sandwich_diamond : KBaseHints.

  Theorem confluent_locally_confluent : forall (R : relation A),
  confluent R -> locally_confluent R.
  Proof.
    intros R C x y1 y2 x_y1 x_y2;
    destruct (C x y1 y2 (clos_rt1n_step _ _ _ _ x_y1) (clos_rt1n_step _ _ _ _ x_y2));
    ecrush.
  Qed.

  (* Facts about reducibility, normal forms and friends *)

  Theorem nf_terminal : forall (R : relation A) x,
    normal R x -> terminal R x x.
  Proof.
    unfold terminal; crush.
  Qed.
  #[local] Hint Resolve nf_terminal : KBaseHints.

  Theorem nf_rt_equal : forall (R : relation A) x y,
    normal R x -> 
    clos_refl_trans_1n A R x y -> x = y.
  Proof.
    unfold normal; unfold reducible; 
    intros R x H y x_y; induction x_y; crush;
    exfalso; eauto.
  Qed.
  #[local] Hint Resolve nf_rt_equal : KBaseHints.

  Theorem nf_terminal_equal : forall (R : relation A) x y,
    normal R x -> 
    terminal R x y -> x = y.
  Proof.
    unfold terminal; ecrush.
  Qed. 
  #[local] Hint Resolve nf_terminal_equal : KBaseHints.

  Theorem terminal_step : forall (R : relation A) x y z,
    R x y -> terminal R y z -> terminal R x z.
  Proof.
    unfold terminal; ecrush.
  Qed.

  Lemma normal_step_false : forall (R : relation A) x y,
    normal R x -> R x y -> False.
  Proof.
    unfold normal; unfold reducible; intros; ecrush.
  Qed.
  #[local] Hint Resolve normal_step_false : KBaseHints.

  Theorem confluent_unique_nf : forall (R : relation A),
    confluent R -> 
    forall x y z, terminal R x y -> terminal R x z -> y = z.
  Proof.
    intros R C x y z Ty Tz.
    destruct Ty as [x_y nfy].
    destruct Tz as [x_z nfz].
    destruct (C x y z x_y x_z) as [u [y_u z_u]].
    rewrite (nf_rt_equal R y u nfy y_u).
    rewrite (nf_rt_equal R z u nfz z_u).
    auto.
  Qed.

  Theorem terminating_confluence : forall (R : relation A),
    terminating R ->
    locally_confluent R ->
    confluent R.
  Proof.
    intros R SNR C x; induction (SNR x) as [x H1 H2];
    intros y z x_y x_z; unfold joinable;
    destruct x_y as [| y y1 x_y y_y1 ].
    - ecrush.
    - destruct x_z as [| z z1 x_z z_z1].
      * ecrush.
      * destruct (C x y z x_y x_z) as [u [y_u z_u]].
        destruct (H2 y x_y y1 u y_y1 y_u) as [y' [y1_y' u_y']]. 
        destruct (H2 z x_z z1 u z_z1 z_u) as [z' [z1_z' z_z']].
        assert (H3 : clos_refl_trans_1n A R y z') by crush.
        assert (H4 : clos_refl_trans_1n A R y y') by crush.
        destruct (H2 y x_y z' y' H3 H4) as [t [z'_t y'_t]].
        exists t; crush.
  Qed.

  (* Facts triangle operators and normalizer *)

  Theorem triangle_diamond : forall (R : relation A) (f : A -> A),
    triangle_op R f ->
    diamond R.
  Proof.
    unfold triangle_op;
    intros R f Tf x y z x_y x_z;
    exists (f x); crush.
  Qed.
  #[local] Hint Resolve triangle_diamond : KBaseHints.

  Theorem triangle_confluent : forall (R1 R2 : relation A) (f : A -> A),
    inclusion A R1 R2 ->
    inclusion A R2 (clos_refl_trans_1n A R1) ->
    triangle_op R2 f ->
    confluent R1.
  Proof.
    ecrush.
  Qed.

End Properties.

#[global]
Hint Resolve 
  idempotence_rt
  monotonicity_rt
  preserve_rt
  preserve_rt_left
  preserve_rt_right
  preserve_rt_para
  diamond_semi_confluent
  semi_confluent_confluent
  nf_terminal
  normal_step_false
  confluent_unique_nf
  terminating_confluence 
  nf_terminal_equal
  nf_rt_equal
  triangle_confluent
  triangle_diamond
  sandwich_diamond
  sandwich_confluence 
  sandwich_same_rt : KBaseHints.

#[global]
Hint Unfold joinable reducible normal terminal WN : KBaseHints.

#[global]
Hint Extern 1 (terminal ?R ?x ?z) =>
match goal with
  | H: terminal ?R ?y z |- _ => apply (terminal_step R x y z)
  | H: R x ?y |- _ => apply (terminal_step R x y z H)
  end : KBaseHints.