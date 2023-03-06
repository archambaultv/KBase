From Coq Require Import Relations.
From Coq Require Import Arith.
From KBase Require Import Tactics.
From KBase Require Import Relations.

(** Definition of the terms *)
Inductive tm : Set :=
  | Idx : nat -> tm (* de Bruijn indices *)
  | Abs : tm -> tm
  | App : tm -> tm -> tm.

(** Shifting de Bruijn indices in terms *)

(* The function shift adds n to all indices greater or equal to k in the term t.
The index k takes into account the number of lambda abstraction *)
Fixpoint shift (t : tm) (n k : nat) : tm :=
  match t with
  | Idx i => if lt_dec i k then Idx i else Idx (i + n)
  | Abs t => Abs (shift t n (k + 1))
  | App t1 t2 => App (shift t1 n k) (shift t2 n k)
  end.

(* Let us prove some usefull theorems about shift. *)

Theorem shift_0 : forall t k,
  shift t 0 k = t.
Proof.
  induction t; crush; autodestruct; crush.
Qed.
#[export] Hint Resolve shift_0 : KBaseHints.
#[export] Hint Rewrite shift_0 : KBaseHints.

Theorem shift_merge : forall t n1 k1 n2 k2,
  k1 <= k2 ->
  k2 <= k1 + n1 ->
  shift (shift t n1 k1) n2 k2 = shift t (n1 + n2) k1.
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve shift_merge : KBaseHints.
#[export] Hint Rewrite shift_merge : KBaseHints.

Theorem shift_swap_le : forall t n1 k1 n2 k2,
  k2 <= k1 ->
  shift (shift t n1 k1) n2 k2 = shift (shift t n2 k2) n1 (k1 + n2).
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Rewrite shift_swap_le : KBaseHints.

(* This theorem is the reverse of the preceding one *)
Theorem shift_swap_ge : forall t n1 k1 n2 k2,
  k2 >= k1 + n1 ->
  shift (shift t n1 k1) n2 k2 = shift (shift t n2 (k2 - n1)) n1 k1.
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Rewrite shift_swap_ge : KBaseHints.

(** Let us now define the substitution *)
Fixpoint subst (t u : tm) (k : nat) : tm :=
  match t with
  | Idx i => match lt_eq_lt_dec i k with
            | inleft (left _) => Idx i
            | inleft (right _) => shift u k 0
            | inright _ => Idx (i - 1)
           end
  | Abs t => Abs (subst t u (k + 1))
  | App t1 t2 => App (subst t1 u k) (subst t2 u k)
  end.

(** Theorems about the substitution function *)

(** A shift can always be distributed over a substitution *)
Theorem subst_shift_swap : forall t u k1 n2 k2,
  k2 <= k1 ->
  shift (subst t u k1) n2 k2 = subst (shift t n2 k2) u (k1 + n2).
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve subst_shift_swap : KBaseHints.

Theorem subst_shift_swap2 : forall t u k1 n2 k2,
  k2 > k1 ->
  shift (subst t u k1) n2 k2 = subst (shift t n2 (k2 + 1)) (shift u n2 (k2 - k1)) k1.
Proof.
  induction t; crush; repeat (autodestruct; crush).
  assert (H2 : k2 >= 0 + k1) by crush.
  rewrite (shift_swap_ge u k1 0 n2 k2 H2).
  auto.
Qed.
#[export] Hint Resolve subst_shift_swap2 : KBaseHints. 

Theorem subst_shift_merge : forall t u k1 n2 k2,
  k2 <= k1 ->
  k1 < k2 + n2 ->
  subst (shift t n2 k2) u k1 = shift t (n2 - 1) k2.
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve subst_shift_merge : KBaseHints.

Theorem subst_shift_shift : forall t u k1 n2 k2 n3 k3,
  k1 + k3 < k2 ->
  k2 <= k1 + k3 + 1 + (n3 - n2) ->
  n2 <= n3 ->
  subst (shift t n2 k2) (shift u n3 k3) k1 = 
  shift (subst t (shift u (n3 - n2) k3) k1) n2 (k2 - 1).
Proof.
  induction t; crush; repeat (autodestruct; crush).
  repeat match goal with
  | [ |- context [shift (shift ?x ?n1 ?k1) ?k2 0]] => 
      rewrite (shift_swap_le x n1 k1 k2 0) by crush
  | [ |- shift ?x ?n1 ?k1 = shift (shift ?x (?n1 - ?n2) ?k1) ?n2 ?k2 ] => 
      rewrite (shift_merge x (n1 - n2) k1 n2 k2) by crush
  | [ |- context [?x - ?y + ?y]] => assert (x - y + y = x) by crush; auto
  end.
Qed.
#[export] Hint Resolve subst_shift_shift : KBaseHints.
#[export] Hint Rewrite subst_shift_shift : KBaseHints.


(** Also known as the substitution lemma *)
Theorem subst_swap : forall t u1 k1 u2 k2,
  k1 <= k2 ->
  subst (subst t u1 k1) u2 k2 = subst (subst t u2 (S k2)) (subst u1 u2 (k2 - k1)) k1.
Proof.
  induction t; crush; repeat (autodestruct; crush);
  (* We are left with to cases where we need to massage the hypothesis
     a little bit to apply subst_shift_swap and subst_shift_merge *)
  match goal with
  | [ |- subst (shift ?u1 ?k1 0) ?u2 ?k2 = shift (subst ?u1 ?u2 (?k2 - ?k1)) ?k1 0] =>
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        assert (H1 : 0 <= k2 - k1) by lia';
        pose proof (subst_shift_swap u1 u2 (k2 - k1) k1 0 H1) as H2;
        assert (H3 : k2 - k1 + k1 = k2) by lia';
        rewrite H3 in H2;
        auto
  | [ |- shift ?u2 ?n2 0 = subst (shift ?u (S ?n2) 0) ?u1 ?k1] =>
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      assert (H1 : 0 <= k1) by lia';
      assert (H2 : k1 < S n2) by lia';
      pose proof (subst_shift_merge u2 u1 k1 (S n2) 0 H1 H2);
      crush
  end.
Qed.
#[export] Hint Resolve subst_swap : KBaseHints.
#[export] Hint Rewrite <- subst_swap : KBaseHints.

(** Small steps *)
Inductive ss : tm -> tm -> Prop :=
  | ss_left : forall t1 t1' t2, ss t1 t1' -> ss (App t1 t2) (App t1' t2)
  | ss_right : forall t1 t2 t2', ss t2 t2' -> ss (App t1 t2) (App t1 t2')
  | ss_abs : forall t t', ss t t' -> ss (Abs t) (Abs t') 
  | ss_beta : forall t u, ss (App (Abs t) u) (subst t u 0).

#[export] Hint Constructors ss : KBaseHints.

Notation "ss*" := (clos_refl_trans_1n tm ss).

Lemma ss_shift : forall t t' n k,
  ss t t' ->
  ss (shift t n k) (shift t' n k).
Proof.
  intros t t' n k t_t'; 
  generalize dependent k;
  induction t_t'; intro k; crush.
  - pose proof (ss_beta (shift t n (k + 1)) (shift u n k));
    rewrite (subst_shift_shift t u 0 n (k + 1) n k) in H by crush;
    assert (H2 : k + 1 - 1 = k) by crush;
    rewrite H2 in H;
    assert (H3 : n - n = 0) by crush;
    rewrite H3 in H;
    rewrite (shift_0 u k) in H;
    auto.
Qed.
#[global] Hint Resolve ss_shift : KBaseHints.

Lemma ss_subst_left : forall t t' u k,
  ss t t' ->
  ss (subst t u k) (subst t' u k).
Proof.
  intros t t' u k t_t';
  generalize dependent k;
  induction t_t'; crush; repeat (autodestruct; crush).
  - pose proof (ss_beta (subst t u (k + 1)) (subst u0 u k)).
    assert (H3 : 0 <= k) by crush.
    pose proof (subst_swap t u0 0 u k H3) as H4.
    assert (S k = k + 1) by crush.
    assert (k - 0 = k) by crush.
    crush.
Qed.
#[global] Hint Resolve ss_subst_left : KBaseHints.

(** We want to prove the confluence of the small steps relation. We will first
        show that ss and pss defined below have the same reflexive transitive
        closure. Then prove that pss is confluent, thus proving ss confluent.*)

(** Parallel small steps *)
Inductive pss : tm -> tm -> Prop :=
| pss_i : forall i, pss (Idx i) (Idx i)
| pss_para : forall t1 t1' t2 t2', 
    pss t1 t1' -> 
    pss t2 t2' -> 
    pss (App t1 t2) (App t1' t2')
| pss_abs : forall t t', 
    pss t t' -> 
    pss (Abs t) (Abs t') 
| pss_beta : forall t t' u u', 
    pss t t' -> 
    pss u u' -> 
  pss (App (Abs t) u) (subst t' u' 0).

#[local] Hint Constructors pss : KBaseHints.

Notation "pss*" := (clos_refl_trans_1n tm pss).

Lemma pss_refl : reflexive tm pss.
Proof.
  intro t1;
  induction t1; crush.
Qed.
#[local] Hint Resolve pss_refl : KBaseHints.

Lemma inclusion_ss_pss : inclusion tm ss pss.
Proof.
  intros x y x_y; induction x_y; crush.
Qed.
#[local] Hint Resolve inclusion_ss_pss : KBaseHints.

Lemma inclusion_pss_ss_rt : inclusion tm pss ss*.
Proof.
  intros x y x_y; induction x_y; crush.
  - assert (H : ss* (App (Abs t) u) (App (Abs t') u')) by crush.
    pose proof (ss_beta t' u').
    crush.
Qed.
#[local] Hint Resolve inclusion_pss_ss_rt : KBaseHints.

Lemma pss_shift : forall t t' n k,
  pss t t' ->
  pss (shift t n k) (shift t' n k).
Proof.
  intros t t' n k t_t';
  generalize dependent k; 
  induction t_t'; crush.
  - specialize (IHt_t'1 (k + 1)).
    specialize (IHt_t'2 k).
    pose proof (pss_beta _ _ _ _ IHt_t'1  IHt_t'2) as H.
    rewrite (subst_shift_shift t' u' 0 n (k + 1) n k) in H by crush.
    assert (H2 : k + 1 - 1 = k) by crush.
    rewrite H2 in H.
    assert (H3 : n - n = 0) by crush.
    rewrite H3 in H.
    rewrite (shift_0 u' k) in H.
    crush. 
Qed.
#[local] Hint Resolve pss_shift : KBaseHints.

Lemma pss_subst : forall t t' u u' k,
  pss t t' ->
  pss u u' ->
  pss (subst t u k) (subst t' u' k).
Proof.
  intros t t' u u' k t_t';
  generalize dependent k;
  induction t_t'; crush; repeat (autodestruct; crush).
  - specialize (IHt_t'1 (k + 1) H).
    specialize (IHt_t'2 k H).
    pose proof (pss_beta _ _ _ _ IHt_t'1  IHt_t'2) as H2.
    assert (H3 : 0 <= k) by crush.
    pose proof (subst_swap t' u'0 0 u' k H3) as H4.
    assert (S k = k + 1) by crush.
    assert (k - 0 = k) by crush.
    crush.
Qed.
#[local] Hint Resolve pss_subst : KBaseHints.

(* Now we can easily prove ss_subst_right *)
(* Crush will use the fact that pss is sandwich between
   ss and ss*. *)
Lemma ss_subst_right : forall t u u' k,
  ss u u' ->
  ss* (subst t u k) (subst t u' k).
Proof.
  crush.
Qed.
#[global] Hint Resolve ss_subst_right : KBaseHints.

Lemma ss_subst_para : forall t t' u u' k,
  ss* t t' ->
  ss* u u' ->
  ss* (subst t' u' k) (subst t' u' k).
Proof.
  crush.
Qed.
#[global] Hint Resolve ss_subst_para : KBaseHints.

Fixpoint pss_normalizer (x : tm) : tm :=
  match x with
  | Idx i => Idx i
  | Abs t => Abs (pss_normalizer t)
  | App (Abs t) u => subst (pss_normalizer t) (pss_normalizer u) 0
  | App t1 t2 => App (pss_normalizer t1) (pss_normalizer t2)
  end.

Lemma Triangle_pss_normalizer : triangle_op pss pss_normalizer.
Proof.
  intros x y x_y; induction x_y; crush; autodestruct; crush.
  - inversion x_y1; subst.
    inversion IHx_y1; subst.
    crush.
Qed.
#[local] Hint Resolve Triangle_pss_normalizer : KBaseHints.

Lemma pss_diamond : diamond pss.
Proof.
  exact (triangle_diamond pss pss_normalizer Triangle_pss_normalizer).
Qed.
#[local] Hint Resolve pss_diamond : KBaseHints.

Lemma ss_confluent : confluent ss.
Proof.
  apply (triangle_confluent ss pss pss_normalizer); crush.
Qed.  
#[global] Hint Resolve ss_confluent : KBaseHints.