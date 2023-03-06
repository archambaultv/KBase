From Coq Require Import Relations.
From Coq Require Import Arith.
From Coq Require Import Program.Basics.
From KBase Require Import Tactics.
From KBase Require Import Relations.
From KBase Require LambdaCalculus.Terms.

Import LambdaCalculus.Terms(tm(..)).

(* Redo terms but with recursion schemes (or what is possible in Coq) *)

(* mapping free variables *)
Fixpoint map_freevar_k (f : nat -> nat) (t : tm) (k : nat) : tm :=
  match t with
  | Idx i => if lt_dec i k then Idx i else Idx (f (i - k) + k)
  | Abs t => Abs (map_freevar_k f t (k + 1))
  | App t1 t2 => App (map_freevar_k f t1 k) (map_freevar_k f t2 k)
  end.

Definition map_freevar (f : nat -> nat) (t : tm) : tm := map_freevar_k f t 0.
#[export] Hint Unfold map_freevar : KBaseHints.

(* map_freevar_k really is a functorial map for free variables *)

Theorem map_freevar_k_id : forall t k, map_freevar_k (fun x => x) t k = t.
Proof.
  unfold map_freevar_k; 
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve map_freevar_k_id : KBaseHints.

Theorem map_freevar_k_compose : forall f1 f2 t k, 
  map_freevar_k f2 (map_freevar_k f1 t k) k = map_freevar_k (compose f2 f1) t k.
Proof.
  unfold map_freevar_k; 
  induction t; crush; repeat (autodestruct; crush);
  match goal with
  | |- context[?e + ?k - ?k] => 
    let H := fresh "H"
    in assert (H : e + k - k = e) by crush; rewrite H; crush
  end.
Qed.
#[export] Hint Resolve map_freevar_k_compose : KBaseHints.

(* In general, with different k we cannot simply compose but we 
   can still extract t *)
Theorem map_freevar_k_compose : forall f1 f2 t k1 k2, 
  map_freevar_k f2 (map_freevar_k f1 t k1) k2 = 
  map_freevar_k (compf f1 k1 f2) t min(k1, k2).
Proof.
  unfold map_freevar_k; 
  induction t; crush; repeat (autodestruct; crush);
  match goal with
  | |- context[?e + ?k - ?k] => 
    let H := fresh "H"
    in assert (H : e + k - k = e) by crush; rewrite H; crush
  end.
Qed.
#[export] Hint Resolve map_freevar_k_compose : KBaseHints.

(* map_freevar always compose as a piece wise linear function *)


(* Working with higher order function without function extensionality 
   is no fun, but we can do it *)
Theorem map_freevar_ext : forall f1 f2 t k,
  (forall x, f1 x = f2 x) ->
  map_freevar_k f1 t k = map_freevar_k f2 t k.
Proof.
  induction t; crush.
Qed.
#[export] Hint Resolve map_freevar_ext : KBaseHints.

(* Same theorem but for map_freevar *)
Theorem map_freevar_id : forall t, map_freevar (fun x => x) t = t.
Proof.
  unfold map_freevar; crush.
Qed.
#[export] Hint Resolve map_freevar_id : KBaseHints.

Theorem map_freevar_compose : forall f1 f2 t, 
  map_freevar f2 (map_freevar f1 t) = map_freevar (compose f2 f1) t.
Proof.
  unfold map_freevar; crush.
Qed.
#[export] Hint Resolve map_freevar_compose : KBaseHints.

(* Shift can be expressed as a map *)
Definition shift (n : nat) (t : tm) : tm := map_freevar (fun x => x + n) t.
#[export] Hint Unfold shift : KBaseHints.

Theorem shift_0 : forall t, shift 0 t = t.
Proof.
  unfold shift; unfold map_freevar; intros;
  assert (H : forall x : nat, (fun x => x + 0) x = (fun x => x) x) by crush.
  pose proof (map_freevar_ext _ _ t 0 H);
  crush.
Qed.

Theorem shift_shift : forall t n1 n2, shift n2 (shift n1 t) = shift (n1 + n2) t.
Proof.
  unfold shift; intros. rewrite map_freevar_compose.
  assert (H : forall x : nat, 
    (compose (fun x : nat => x + n2) (fun x : nat => x + n1)) x = 
    (fun x => x + (n1 + n2)) x).
    - intros; unfold compose; crush.
    - pose proof (map_freevar_ext _ _ t 0 H); crush.
Qed.

(* We can also define a recursion scheme for substitution *)
Fixpoint subst_freevar_k (f : nat -> tm) (t : tm) (k : nat) : tm :=
  match t with
  | Idx i => if lt_dec i k then Idx i else (shift k (f (i - k)))
  | Abs t => Abs (subst_freevar_k f t (k + 1))
  | App t1 t2 => App (subst_freevar_k f t1 k) (subst_freevar_k f t2 k)
  end.

(* map_freevar_k is not quite a functorial map for free variables,
   but close *)
Theorem subst_freevar_k_id : forall t k, subst_freevar_k (fun x => Idx x) t k = t.
Proof.
  unfold subst_freevar_k; unfold shift; unfold map_freevar;
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve subst_freevar_k_id : KBaseHints.

Theorem subst_shift : forall f t n k,
  subst_freevar_k f (map_freevar_k (fun x : nat => x + k) t n) (k + n) =
  map_freevar_k (fun x : nat => x + k) (subst_freevar_k f t n) n.
Proof.
  induction t; intros k.
  - unfold shift; unfold map_freevar; crush; repeat (autodestruct; crush). 
    assert (H1 : n - k + k0 + k - (k0 + k) = n - k) by crush.
    rewrite H1.
    unfold shift. unfold map_freevar.
    pose proof (map_freevar_k_compose (fun x : nat => x + k)  (fun x : nat => x + k0)
      (f (n - k)) k).
    assert (H2 : n - 0 = n) by crush.
    
    crush.
  - simpl.

(* We cannot compose, but we can extract the t and k arguments,
   thus grouping the substitution functions together *)
Theorem subst_freevar_k_compose : forall f1 f2 t k, 
  subst_freevar_k f2 (subst_freevar_k f1 t k) k = 
  subst_freevar_k (fun i => subst_freevar_k f2 (f1 i) 0) t k.
Proof.
  induction t; crush; repeat (autodestruct; crush).
  match goal with
  | |- context[?e + ?k - ?k] => 
    let H := fresh "H"
    in assert (H : e + k - k = e) by crush; rewrite H; crush
  end.
Qed.