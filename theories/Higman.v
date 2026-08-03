(*| 

==============
Higman is well 
==============
:Author: Reinis Cirpons <reinis.cirpons@inria.fr>
:Description: A `Rocq <https://rocq-prover.org>`_ formalizaion of `Higman's lemma <https://en.wikipedia.org/wiki/Higman's_lemma>`_.

The goal of this short note is to give a self-contained formalization
of Higman's lemma:

  **Theorem**: Let :math:`\leq` be a well-quasi-order on a set
  :math:`T`. Then the associated Higman embedding order
  :math:`\leq^\ast` is a well-quasi-order on the set
  :math:`T^\ast` of words over :math:`T`.

We will explain what each of these terms means as they come up.
Generally, we do not assume prior knowledge of either Rocq
or Higmans lemma, and will try to gently introduce both.

For a much more detailed introduction to Rocq we recommend
Volume 1: *Logical Foundations* of the *Software foundations*
series [1]_ as well as the
the *Mathematical Components* book [2]_,
see also the `Rocq documentation <https://rocq-prover.org/docs>`_
page for more learning materials.

For a much more detailed introduction to the theory of
well-quasi-orders we recommend the lecture notes for the course
*Well-Quasi-Orders for Algorithms* [3]_.

|*)


(*|

About this document
===================

|*)
From Stdlib Require Import Btauto.
Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq choice eqtype path. (* .no-messages *)

(*|

Notations
=========

|*)

(* We reserve some notation for later, to make the lemmas easier to read.
   Roughly speaking:

   1. The notation <=_R will denote the non-strict base order on the alphabet.
   2. The notation <=^*_R will denote the non-strict Higman order
      induced by <=_R on words.
   3. The notations <=^^*_R will denote a computational version of the
      non-strict Higman order.
   4. The notations <_R, <^*_R and <^^*_R will denote the strict versions
      of the above orders.
   5. 
 *)

Declare Scope higman_order_scope.
Delimit Scope higman_order_scope with HO.
Local Open Scope higman_order_scope.

Reserved Notation "a <=_ R b"
  (at level 60, R name, b at level 70, format "a  <=_ R  b").
Reserved Notation "u <=^*_ R v"
  (at level 60, R name, v at level 70, format "u  <=^*_ R  v").
Reserved Notation "u <=^^*_ R v"
  (at level 60, R name, v at level 70, format "u  <=^^*_ R  v").
Reserved Notation "a <_ R b"
  (at level 60, R name, b at level 70, format "a  <_ R  b").
Reserved Notation "u <^*_ R v"
  (at level 60, R name, v at level 70, format "u  <^*_ R  v").
Reserved Notation "u <^^*_ R v"
  (at level 60, R name, v at level 70, format "u  <^^*_ R  v").

(*|

Quasi-orders
============

|*)

(* In this section we define some properties of quasi-orders.
   Rocq already has much of this formalized in the
   preorder module of the math-comp library:

     https://math-comp.github.io/htmldoc_2_5_0/mathcomp.order.preorder.html

   However, using this library requires us to do a bit of boilerplate
   to correctly register our orders, which I chose to avoid for
   simplicity of presentation in the first instance. 

   There should be no issue to integrate with the mathcomp preorder
   module later on. *)
Section QuasiOrder.

(* We start by declaring some recurring objects for this section. *)
(* We define T to be the base type over which some relations is
   defined. *)
Context {T: Type}.

(* We define R to be a relation on T.
   While we do not yet impose any requirements (like e.g. reflexivity or
   transitivity) on R, we think of it as a "non-strict" <= order on T. *)
(* The type "rel T" expands to "T -> T -> bool", i.e. R is a
   function taking in two arguments and returning a boolean.
   We interpret R a b = true to mean that a <= b holds. *)
(* Note that this framing also requires that R is effective, i.e.
   there is a program that can compute if a <= b holds or not.
   (More on this later) *)
Variable (R: rel T).

(* Lets denote the order on T by <= *)
Notation "a <= b" := (R a b).

(* Lets now define the strict order associate to R.
   Recall that a < b holds precisely when a <= b and not b <= a.
   We can translate this mathematical definition directly to Rocq
   as (a <= b) && ~~ (b <= a). Here && is the boolean conjunction
   and ~~ is the boolean negation. *)
Definition Lt a b := ((a <= b) && ~~ (b <= a)).
(* Lets give Lt a notation too. *)
Notation "a < b" := (Lt a b).

(* We can now state and prove our first lemma! *)
(* Lets prove that a < b and b <= c implies that a < c, provided R is
   transitive. *)
(* The statement of this lemma in Rocq is almost identical to what
   we write mathematically:

     transitive R -> forall a b c, a < b -> b <= c -> a < c

   Here the arrows "->" should be read as logical implications, i.e.
   X -> Y means if X then Y. Chaining multiple arrows then just means
   we add multiple hypotheses to the statement, i.e. X -> Y -> Z just
   means that if X and Y both hold, then Z also holds.

   So the statement above decyphers to:
     if R is transitive and a < b and b <= c then a < c.
*)

(* To see what transitive means in Rocq, we can Print its definition. *)
(* Doing so should produce something like the following: 

     transitive =
     fun (T : Type) (R : rel T) => forall y x z : T, R x y -> R y z -> R x z
         : forall [T : Type], rel T -> Prop
     Arguments transitive [T]%_type_scope R

   There is some boilerplate, but the crucial part is this:
   
     forall y x z : T, R x y -> R y z -> R x z

   In other words, transitive R means that x <= y and y <= z implies x <= z
   for all x y z.
*)
Print transitive.

(* We can now state the lemma and prove it. *)
Lemma lt_leq_lt: transitive R -> forall a b c, a < b -> b <= c -> a < c.
Proof.
  (* To prove the statement, lets first give names to some of the
     hypotheses and universally quantified elements.
     We can do this with the "move =>" tactic. Here we name the
     transitivity hypothesis Htrans, and the universally quantified
     variables a, b and c. *)
  move => Htrans a b c.
  (* We are now left with a goal of the form

     a < b -> b <= c -> a < c.

    We can unfold the definition of < to make it easier to understand what
    we need to prove. This can be done with the rewrite tactic.
  *)
  rewrite /(_ < _).
  (* TODO *)
  move/andP.
  case => Hab.
  move/negP => Hba Hbc.
  apply /andP; split.
  - apply Htrans with b.
  -- by exact Hab.
  -- by exact Hbc.
  - apply /negP => Hac; apply Hba.
  (* In fact Rocq can figure out trivial goals that are
     already in the context by itself, so we can just say

     by apply Htrans with c

     to close the goal automatically.
     *)
    by apply Htrans with c.
Qed.

Lemma leq_lt_lt: transitive R -> forall a b c, a <= b -> b < c -> a < c.
Proof.
  (* TODO *)
  move => Htrans a b c.
  move => Hab /andP [Hbc /negP Hcb].
  apply/andP; split;
    first by apply Htrans with b.
  by apply /negP => Hca; apply Hcb; apply Htrans with a.
Qed.

Lemma lt_transitive: transitive R -> transitive Lt.
Proof.
  move => Htrans a b c /andP [Hba _] Hac.
  by apply leq_lt_lt with a.
Qed.

(* I will not go into as much detail about proofs in the remainder of
   the file, but I wanted to walk you through these*)
End QuasiOrder.

(* Notations defined inside of sections are cleared after the section is
   closed. So we redeclare some notations globally now. *)
(* a <=_R b for the non-strict order and a <_R b for the strict one. *)
Notation "a <=_ R b" := (R a b).
Notation "a <_ R b" := (Lt R a b).

Section HigmanLeqOrder.
(* In this section we define the Higman order arising from a base order on
   some alphabet. *)

(* In this section we think of T as the type of the alphabet and R
   as the base relation on T. *)
Context {T: Type}.
Variable (R: rel T).

(*|

Higman's embedding order
========================

|*)

(* We first consider the non-strict Higman order in an inductive fashion.
   The type seq T is the type of sequences of elements in T, i.e. words,
   whose alphabet is T. *)
(* Note that the type of HigmanLeq is seq T -> seq T -> Prop, instead
   of seq T -> seq T -> bool like we had for R. This is because inductive
   definitions are non-effective by default. This is because an inductive
   definition only specifies inference rules, but there is no general
   purpose algorithm for deciding if a proposition holds given a set of
   inference rules (indeed this can be undecidable depending on the rules
   given). *)
(* We will give an alternative definition of HigmanLeq which is decidable
   later on, and prove that it is equivalent to the inductive
   definition. *)
Inductive HigmanLeq {T} (R: rel T): seq T -> seq T -> Prop :=
(* [::] is the empty word in Rocq*)
| HLeq_nil: forall u,
    [::] <=^*_R u
(* b::v is the left-concatenation of a letter to a word in Rocq*)
| HLeq_cons1: forall b u v,
    u <=^*_R v ->
    u <=^*_R (b::v)
| HLeq_cons2: forall a b u v,
    a <=_R b ->
    u <=^*_R v ->
    (a::u) <=^*_R (b::v)
(* A little notational convenience: we declare the notation as part of
   the definition, so we could write u <=^*_R v instead of HigmanLeq R u v
   above. *)
where "u <=^*_ R v" := (HigmanLeq R u v).

(* Now for the computable definition of HigmanLeq.
   Note that here the type of HigmanLeqDec is rel (seq T), i.e.
   the type of decidable relations on words. *)
(* "Fixpoint" is simply Rocq's way of indicating that the following
   is a recursive function definition. *)
Fixpoint HigmanLeqDec {T} (R: rel T): rel (seq T) :=
  (* Since rel (seq T) is a function type seq T -> seq T -> bool,
     we need to introduce a function and its arguments. *)
  fun u v =>
    (* Casework on u *)
    match u with
    (* First inference rule HLeq_nil tells us that [::] <= u for all u,
       so we return true *)
    | [::] => true
    | a::u' =>
      match v with
      (* u <= [::] can't work if u is non-empty, so return false*)
      | [::] => false
      (* Either HLeq_cons1 or HLeq_cons2 must be used, consider cases
         accordingly. Here || and && are just boolean or and boolean and. *)
      (* The "u <=^^*_R v'" and "u' <=^^*_R v'" expressions trigger
         a recursive call to the HigmanLeqDec function. Since the size
         of v always decreases, this is guaranteed to terminate. *)
      | b::v' => (u <=^^*_R v') || ((a <=_R b) && (u' <=^^*_R v'))
      end
    end
(* Note the double "^^" for the notation for HigmanLeqDec, as opposed to
   the single one for HigmanLeq. *)
where "u <=^^*_ R v" := (HigmanLeqDec R u v).

(* The following reflection lemma establishes that our definition
   of HigmanLeqDec is correct and equivalent to HigmanLeq,
   i.e. that it returns true if and only if there exists a proof of
   HigmanLeq u v, and returns false if and only if there exists a proof that
   HigmanLeq u v does not hold. *)
Lemma HigmanLeqDecP: forall u v,
  reflect (u <=^*_R v) (u <=^^*_R v).
Proof.
  move => u v; apply: (iffP idP).
  - elim: v u => [[_|//]|b v IH [_|a u /= /orP [|/andP [Hab]] /IH Huv]].
  -- by apply HLeq_nil.
  -- by apply HLeq_nil.
  -- by apply HLeq_cons1.
  -- by apply HLeq_cons2.
  - elim => [[//|//]|b [//|a {}u] {}v _ /= -> //|a b {}u {}v /= -> _ -> /=];
    by rewrite orbC.
Qed.

Lemma HigmanLeqDec_cons1: forall a u v,
  (a::u) <=^^*_R v -> u <=^^*_R v.
Proof.
  move => a [|a' u']; elim => [|b v IH] //.
  by move => /= /orP [/IH ->|/andP [_ ->]].
Qed.

Lemma HigmanLeqDec_cons2: forall a b u v,
  a <=_R b -> u <=^^*_R v -> (a::u) <=^^*_R (b::v).
Proof.
  by move => a b u v /= -> ->; rewrite orbC.
Qed.

(* We now show that transitivity of R is preserved by the Higman order. *)
Lemma HigmanLeqDec_trans: transitive R -> transitive (HigmanLeqDec R).
Proof.
  move => Htrans v u w; elim: w u v => [|c w IH] [|a u] [|b v] //.
  move => /= /orP [|/andP [Hab]] Huv /orP [|/andP [Hac]] Huw.
  - by rewrite (IH (a::u) v) // (HigmanLeqDec_cons1 b).
  - by rewrite (IH (a::u) v).
  - by rewrite (IH (a::u) (b::v)) // HigmanLeqDec_cons2.
  - by rewrite orbC (IH u v) // (Htrans b).
Qed.

(* A useful fact: the Higman order preserves the size order. *)
Lemma HigmanLeqDec_size: forall {u v},
  u <=^^*_R v -> size u <= size v.
Proof.
  move => u v /HigmanLeqDecP; elim => {u v} [//|b u v _ /leqW //|//].
Qed.

End HigmanLeqOrder.
Notation "a <=^*_ R b" := (HigmanLeq R a b).
Notation "a <=^^*_ R b" := (HigmanLeqDec R a b).

Section HigmanLtOrder.
(* In Rocq well-foundedness is the same as termination, i.e. it is a property
   of the strict order, as opposed to the non-strict order. In this
   section we endeavour to define the strict order and prove it is correct. *)

Context {T: Type}.
Variable (R: rel T).

(* Recall that we defined the strict order associate to R by
  
     (a <=_R b) && ~~ (b <=_R a)

   using the boolean and and not operators. *)
(* We define the strict propositional Higman order similarly below,
   but note that the logical and "/\" and logical negation "~" is
   used instead of their boolean counterparts "&&" and "~~". *)
Definition HigmanLt (R: rel T) a b := ((a <=^*_R b) /\ ~ (b <=^*_R a)).
Notation "a <^*_ R b" := (HigmanLt R a b).

(* Here we show that there is a decidable version of the same inequality
   using the HigmanLeqDec function. *)
Lemma HigmanLtP: forall u v,
  reflect (u <^*_R v) ((u <=^^*_R v) && ~~ (v <=^^*_R u)).
Proof.
  move => u v; apply (iffP idP) =>
    [/andP [/HigmanLeqDecP Huv /HigmanLeqDecP Hvu]
    |[/HigmanLeqDecP -> /HigmanLeqDecP ->] //]; by split.
Qed.

(* For the computational version, we choose to give a slightly more explicit
   definition, which will make our life much easier later on. *)
Fixpoint HigmanLtDec {T} (R: rel T): rel (seq T) :=
  fun u v =>
    match v with
    | [::] => false
    | b::v' =>
      match u with
      | [::] => true
      (* There are three non-trivial cases to consider: *)
      | a::u' =>
        (* If HLeq_cons1 was used, then u <= v' holds, and we add a
           letter b to v', so u must be strictly less than b::v' due to
           size considerations. *)
        (u <=^^*_R v') ||
        (* Otherwise HLeq_cons2 was used, and then we have two options:
           either the first letter is strictly smaller, or the remainder
           is strictly smaller. This is again due to size considerations. *)
        ((a <_R b) && (u' <=^^*_R v')) ||
        ((a <=_R b) && (u' <^^*_R v'))
      end
    end
where "u <^^*_ R v" := (HigmanLtDec R u v).

(* Prove correctness of the above formulat with a reflection lemma again. *)
Lemma HigmanLtDecP: forall u v,
  reflect (u <^*_R v) (u <^^*_R v).
Proof.
  move => u v; apply: (iffP idP) => [Huv |/HigmanLtP /andP [Huv Hvu]].
  - apply /HigmanLtP;
    elim: v u Huv => [[//|//]|b v IH [//|a u] /=].
    move => /orP [/orP [Huv|/andP [/andP [Hab Hba] Huv]]|/andP [Hab /IH /andP [Huv Hvu]]];
    apply /andP; split; rewrite ?Huv ?Hab // orbC // negb_or negb_and.
  -- apply /andP; split; first (apply /orP; right); apply/negP;
     move/HigmanLeqDec_size; move/HigmanLeqDec_size in Huv => /=;
      first by rewrite ltn_geF.
     by rewrite leq_gtF => [//|]; apply ltnW.
  -- apply/andP; split; first by apply /orP; left.
     apply /negP => /HigmanLeqDec_size /=.
     by move/HigmanLeqDec_size in Huv; rewrite ltn_geF.
  -- apply/andP; split; first by apply /orP; right.
     apply /negP => /HigmanLeqDec_size /=.
     by move/HigmanLeqDec_size in Huv; rewrite ltn_geF.
  - elim: v u Huv Hvu => [[//|//]|b v' IH [//|a u'] /=].
    move => /orP [-> //|/andP [Hab Huv]].
    rewrite /(_ <_R _) negb_or negb_and => /andP [Hbvu /orP [->|Hvu]];
      first by rewrite Hab Huv -orbA orbC.
    by rewrite orbC Hab IH.
Qed.

Lemma HigmanLtDecE: forall u v,
  (u <^^*_R v) = Lt (HigmanLeqDec R) u v.
Proof.
  move => u v; case Huv: (u <^^*_R v);
  by apply/esym /HigmanLtP/HigmanLtDecP; rewrite Huv.
Qed.

Lemma Higman_lt_leq_lt:
  transitive R ->
  forall u v w, u <^^*_R v -> v <=^^*_R w -> u <^^*_R w.
Proof.
  move => Htrans u v w; rewrite !HigmanLtDecE => Huv Hvw.
  apply lt_leq_lt with v => [|//|//].
  by apply HigmanLeqDec_trans.
Qed.

Lemma HigmanLeqDec_cons: forall a u v,
  (a::u) <=^^*_R v -> u <^^*_R v.
Proof.
  move => a u v; elim: v a u => [//|b v IH a [//|a' u] /=].
  move => /orP [/IH|/andP [_ ->] //].
  by rewrite HigmanLtDecE => /andP [->].
Qed.

End HigmanLtOrder.
Notation "a <^*_ R b" := ((a <=^*_R b) /\ ~ (b <=^*_R a)).
Notation "a <^^*_ R b" := (HigmanLtDec R a b).

(*|

Well-foundedness
================

|*)

Section WellFounded.

Context {T: Type}.
Variable (R: rel T).

Definition descending (l: seq T): bool :=
  pairwise (fun a b => b <_R a) l.

Lemma descending_rcons: forall l a,
  descending (rcons l a) = all (Lt R a) l && descending l.
Proof.
  by move => l a; rewrite /descending pairwise_rcons.
Qed.

Print mkseq.

Definition fun_succ (f: nat -> T): nat -> T := fun n => f n.+1.

Lemma mkseq0: forall (f: nat -> T),
  mkseq f 0 = [::].
Proof. done. Qed.

Lemma mkseqSr: forall (f: nat -> T) n,
  mkseq f n.+1 = (f 0) :: mkseq (fun_succ f) n.
Proof.
  move => f; elim => [//|n IH].
  by rewrite mkseqS IH mkseqS rcons_cons.
Qed.

Definition descending_chain_condition: Prop:=
  forall (f: nat -> T), exists n, ~~ descending (mkseq f n).

Lemma well_founded_DCC:
  well_founded (Lt R) -> descending_chain_condition.
Proof.
  move => Hwf f; move Hx: (f 0) => x.
  elim/(well_founded_ind Hwf): x f Hx => x IH f Hx.
  move Hy: (f 1) => y.
  case Hxy: (y <_R x).
  - move: (IH y Hxy (fun_succ f) Hy) => [n Hn].
    exists n.+1.
    by rewrite mkseqSr /= andbC negb_and Hn.
  - exists 2 => /=.
    by rewrite Hx Hy Hxy.
Qed.


Section ClassicalEquivalence.
From Stdlib Require Import Classical ChoiceFacts.

(* We now give a classical characterization of the negation
   of the accessibility predicate, namely:
   if a is not accessible, then there exists a strictly smaller
   element b that is also not accessible. *)
Lemma not_AccP: forall a,
  ~ Acc (Lt R) a <-> exists b, b <_R a /\ ~ Acc (Lt R) b.
Proof.
  move => a; split => [Ha|].
  - apply NNPP. (* This uses excluded middle *)
    move/not_ex_all_not => Hfalso. (* Excluded middle *)
    apply /Ha /Acc_intro => b Hb.
    move/not_and_or: (Hfalso b) => [//|]. (* Excluded middle *)
    by move /NNPP. (* Excluded middle *)
  - move => [b [Hba Hb]] [Ha].
    by apply /Hb /Ha.
Qed.

(* It follows by iterating not_AccP that a single inaccessible
   element generates an infinite descending chain of elements.
   Such a chain clearly contradicts the assumption that there are
   no infinite descending chains. *)

(* But how can we use not_AccP to construct a concrete infinite
   chain f: nat -> T? For this we need a choice axiom. *)
Print FunctionalDependentChoice_on.

(* Now we assume we have an axiom of dependent choice on T. *)
Hypothesis Hchoice: FunctionalDependentChoice_on T.

Lemma not_Acc_counter_fun: forall a,
  exists (f: nat -> T),
  f 0 = a /\
  forall n,
    (~ Acc (Lt R) (f n) ->
    (f n.+1) <_R (f n) /\ ~ Acc (Lt R) (f n.+1)).
Proof.
  move => a.
  (* The axiom of choice will give us a function, provided we can exhibit
  * an element smaller than any given element. *)
  apply (Hchoice
    (fun x y => ~ Acc (Lt R) x -> y <_R x /\ ~ Acc (Lt R) y)) => b.
  case: (classic (Acc (Lt R) b)) => Hb;
    first by exists b. (* Excluded middle *)
  move/not_AccP: Hb => [c [Hcb Hc]].
  by exists c.
Qed.

Hypothesis Htrans: transitive R.

Lemma DCC_well_founded:
  descending_chain_condition -> (well_founded (Lt R)).
Proof.
  move => Hdcc.
  apply NNPP. (* Excluded middle *)
  move/not_all_ex_not => [a Ha]. (* Excluded middle *)
  move: (not_Acc_counter_fun a) => [f [H0 HS]].
  have: (forall n, f n.+1 <_R f n) => [n|Hf {H0 HS}].
  - apply HS; elim: n => [|n];
      first by rewrite H0.
    by case/HS.
  - move: (Hdcc f) => [n] /negP Hfalso.
    apply /Hfalso.
    rewrite /descending -sorted_pairwise => [|];
      last by apply /rev_trans /lt_transitive.
    apply /(sortedP a) => i.
    rewrite size_mkseq => Hi.
    by rewrite !nth_mkseq => [//||//]; apply ltn_trans with i.+1.
Qed.

Lemma descending_chain_conditionP:
  descending_chain_condition <-> (well_founded (Lt R)).
Proof.
  split.
  - by apply DCC_well_founded.
  - by apply well_founded_DCC.
Qed.
End ClassicalEquivalence.
End WellFounded.


Section HigmanIsWellFounded.

Context {T: Type}.
Variable (R: rel T).

(* We can declare a section hypothesis, in this case we require that
   the base order R is transitive and that the
   corresponding strict order is well-founded. *)
Hypothesis Htrans: transitive R.
Hypothesis Hwf: (well_founded (Lt R)).

Lemma Acc_Higman_cons: forall b v,
  Acc (HigmanLtDec R) v ->
  Acc (HigmanLtDec R) (b::v).
Proof.
  move => b v Hv; elim: Hv b => [{}v _ IHv] b.
  elim/(well_founded_ind Hwf): b v IHv => b IHb v IHv.
  apply Acc_intro => [] [_|a u /=];
    first by apply Acc_intro; case.
  move => /orP [/orP [H |/andP [Hab Huv]]|/andP [Hab Huv]].
  - by apply IHv; apply HigmanLeqDec_cons with a.
  - apply IHb => [//|w Hw c];
    by apply /IHv; apply Higman_lt_leq_lt with u.
  - by apply IHv.
Qed.

Lemma HigmanLtDec_wf: well_founded (HigmanLtDec R).
Proof.
  elim; last by exact: Acc_Higman_cons.
  by apply Acc_intro; case.
Qed.

End HigmanIsWellFounded.

(*|

Bar induction
=============

|*)

Section BarPredicates.
(* We have now come to a point where we need to prove some
   properties about so-called bar predicates. This will be
   the simplest way to work with well-orders and properties
   of infinite sequence. *)

Context {T: Type}.

(* Idea: less than 10 example *)
Inductive Bar (P: seq T -> Prop) (l: seq T): Prop :=
| Bar_nil: P l -> Bar P l
| Bar_cons: (forall a, Bar P (rcons l a)) -> Bar P l.


Lemma Bar_mkseq: forall P l,
  Bar P l -> forall (f: nat -> T), exists n, P (l ++ mkseq f n).
Proof.
  move => P l; elim => [{}l H f|{}l _ IH f];
    first by exists 0; rewrite cats0.
  move: (IH (f 0) (fun_succ f)) => [n].
  rewrite cat_rcons -mkseqSr => H.
  by exists n.+1.
Qed.

Theorem Bar_nil_mkseq: forall P,
  Bar P [::] -> forall (f: nat -> T), exists n, P (mkseq f n).
Proof.
  move => P H f; move: (Bar_mkseq P [::] H f) => [n /=].
  by exists n.
Qed.


Section BarClassicalEquivalence.
From Stdlib Require Import Classical ChoiceFacts.

Lemma not_BarP: forall {P} {l: seq T},
   ~ (Bar P l) <-> ~ (P l) /\ exists a, ~ (Bar P (rcons l a)).
Proof.
  move => P l; split => [H|[Hl [a Ha]] [//|//]].
  split => [Hfalso | ];
    first by apply /H /Bar_nil.
  apply not_all_ex_not => Hfalso. (* This uses excluded middle *)
  by apply /H /Bar_cons.
Qed.

Definition not_Bar_rcons (P: seq T -> Prop) l l': Prop:= 
    ~ Bar P l -> exists a, l' = rcons l a /\ ~ Bar P l'.

Lemma not_Bar_counter_seq: forall {P: seq T -> Prop},
  forall l, exists l', not_Bar_rcons P l l'.
Proof.
   move => P l.
   case: (classic (Bar P l)); (* Excluded middle *)
     first by exists [::].
   move/not_BarP => [_ [a H]].
   exists (rcons l a) => _.
   by exists a.
Qed.

(* Now we assume we have an axiom of dependent choice on seq T. *)
Hypothesis Hchoice: FunctionalDependentChoice_on (seq T).

Lemma not_Bar_counter_seq_fun: forall (P: seq T -> Prop),
   exists (f: nat -> seq T),
   f 0 = [::] /\
   forall n, not_Bar_rcons P (f n) (f n.+1).
Proof.
   move => P.
   (* Use axiom to get a function mapping each n to a sequence of length n
      disproving P, so that additionally each f n is a subsequence of f n.+1.
   *)
   apply /Hchoice /not_Bar_counter_seq.
Qed.

(* Assume T is non-empty. This is not strictly necessary, but makes life
   easier, and were already assuming so much we might as well. *)
Hypothesis Hnonempty: inhabited T.

Search nth last.

Lemma not_Bar_counter_fun: forall {P: seq T -> Prop},
   ~ Bar P [::] ->
   exists f: nat -> T, forall n, ~ P (mkseq f n).
Proof.
   move => P H.
   move: (not_Bar_counter_seq_fun P) => [f [Hf0 Hfn]].
   (* In Rocq the nth function needs a default argument since we
      can't always guarantee that the function won't index out
      of founds. So we pick any element of T for this. *)
   (* Of course, because of the definition of the function f,
      size (f n.+1) = n.+1 for all n, so the n-th element is always
      defined, hence t0 will never actually be relevant. *)
   move: Hnonempty => [t0].
   move Hg: (fun n => nth t0 (f n.+1) n) => g.
   have: (forall n, size (f n) = n /\ mkseq g n = f n /\ ~ Bar P (f n)) => [|IHg].
   - elim => [|n [IHsize [IHg IHBar]]];
       first by rewrite Hf0.
     rewrite mkseqS IHg -Hg /=.
     move: (Hfn n IHBar) => [a [-> HBar]]; split;
       first by rewrite size_rcons IHsize.
     split => [|//].
     f_equal.
     have: (n = (size (rcons (f n) a)).-1) => [|{2}->];
       first by rewrite size_rcons IHsize.
     by rewrite nth_last last_rcons.
   - exists g => n.
     by move: (IHg n) => [_ [-> /not_BarP []]].
Qed.

Theorem Bar_nil_mkseqR: forall P,
  (forall (f: nat -> T), exists n, P (mkseq f n)) -> Bar P [::].
Proof.
  move => P H; apply NNPP => HN; move: H.
  apply ex_not_not_all. (* Excluded middle *)
  move: (not_Bar_counter_fun HN) => [f Hf].
  by exists f; case.
Qed.

End BarClassicalEquivalence.

End BarPredicates.

(*|

Wellness
========

|*)

Section WellQuasiOrder.

Context {T: Type}.
Variable (R: rel T).


Fixpoint has_ascending_pair (l: seq T): bool :=
  match l with
  | [::] => false
  | a::l' => (has (R a) l') || has_ascending_pair l'
  end.

Search has nth.

Lemma has_ascending_pairP: forall a0 l,
  reflect
    (exists i j, i < j /\ j < size l /\ nth a0 l i <=_R nth a0 l j)
    (has_ascending_pair l).
Proof.
  move => a0 l; apply /(iffP idP).
  - elim: l => [//|a l IH /= /orP
      [/(has_nthP a0) [j Hj Hij]
      |/IH [i [j [Hi [Hj Hij]]]]]];
      first by exists 0; exists j.+1.
    by exists i.+1; exists j.+1.
  - elim: l => [[i [[|j] [Hi [Hj //]]]]|a l IH].
    move => [[|i] [[|j] /= [Hi [Hj Hij]]]] //; apply /orP.
  -- by left; apply /(has_nthP a0); exists j.
  -- by right; apply IH; exists i; exists j.
Qed.

Definition Well: Prop := Bar has_ascending_pair [::].

Lemma Well_spec: Well ->
  forall (a0: T) (f: nat -> T), exists i j, i < j /\ f i <=_R f j.
Proof.
  move/Bar_nil_mkseq => H a0 f.
  move: (H f) => [n /(has_ascending_pairP a0) [i [j [Hi []]]]].
  rewrite size_mkseq => Hj.
  rewrite !nth_mkseq => [Hij|//|];
    last by apply ltn_trans with j.
  by exists i; exists j.

Qed.

Hypothesis Htrans: transitive R.

Lemma Well_wf': forall a0 l,
  Bar has_ascending_pair l -> descending R l -> Acc (Lt R) (last a0 l).
Proof.
  move => a0 l; elim => [{}l|].
  - move => /(has_ascending_pairP a0) [i [j [Hi [Hj Hij]]]]
            /(pairwiseP a0) H.
    exfalso.
    enough (Hfalso: nth a0 l j <_R nth a0 l i);
      first by rewrite /(_ <_R _) Hij andbC in Hfalso.
    by apply H => [|//|//]; apply ltn_trans with j.
  - elim/last_ind => [/= _ |{}l a _ _ /=] IH H;
      first by apply IH.
    rewrite last_rcons; apply Acc_intro => b Hb.
    move: (IH b) => {}IH; rewrite last_rcons in IH.
    apply IH; rewrite descending_rcons H andbC /=.
    elim/last_ind: l H {IH} => [/= _|l c IH];
      first by rewrite Hb.
    rewrite /descending !pairwise_rcons all_rcons =>
      /andP [/andP [Hac Hal] /andP [_ Hl]].
    rewrite !all_rcons andbA [_ && (_ <_R _)]andbC
            -andbA -all_rcons IH;
      last by rewrite /descending pairwise_rcons Hal Hl.
    rewrite andbC /=; apply lt_leq_lt with a => [//|//|].
    by move/andP: Hac => [].
Qed.
    
Lemma Well_wf: Well -> well_founded (Lt R).
Proof.
  move => Hwell a.
  by apply (Well_wf' a [::]).
Qed.

End WellQuasiOrder.

(* We follow
Higman’s Lemma and Its Computational Content
by 
Helmut Schwichtenberg, Monika Seisenberger and Franziskus Wiesnet
*)

Section Forest.
(*
   The idea of the constructive proof that
   Well <= implies Well <=^* is to consider a sequence
   S = [:: w_1, ..., w_n] of words w_i: seq T.
   Clearly, if some w_i is empty, then any extension of
   S of the right will contain an ascending pair, so
   S is barred and we are done.
   Otherwise, we can write w_i = a_i::v_i for some letter a_i
   and sequence v_i.

   We *would like* to say something like: the sequence
   a_i must have an ascending pair and therefore so does
   w_i, but this is not true. Instead we can try to seek a
   contradiction another way.

   TODO: this is wrong, fix, actually look at ascending sequences.
   We will consider all possible strictly decreasing subsequences
   a_{i_1} > a_{i_2} > ... > a_{i_k}, the key idea of the proof
   will be to show that the length of such sequences is
   bounded (immediate since we assume T is well-founded)
   and that the number of such distinct subsequences is also
   bounded (this is the hard part).

   We will store these sequences in a forest datastructure,
   and prove that these forests are barred, with respect to
   a certain function.

   A prior formalization along the same lines has been carried out in
   Rocq, but is not actively maintained at the moment:

   https://github.com/rocq-archive/higman-s

*)

Context {T: Type}.
Variable (R: rel T).

Inductive AscendingTree :=
| AT_node: T -> seq T -> seq AscendingTree -> AscendingTree.

Definition AT_leq (t1 t2: AscendingTree) :=
  match t1, t2 with
  | AT_node a1 _ _, AT_node a2 _ _ => a1 <=_R a2
  end.

Fixpoint AT_meld (t1 t2: AscendingTree) {struct t1}: AscendingTree :=
  match t1, t2 with
  | AT_node a1 w1 f1, AT_node a2 w2 f2 =>
    if a1 <=_R a2 then
      if (has (fun t1' => AT_leq t1' t2) f1) then
        AT_node a1 w1 [seq (AT_meld t1' t2) | t1' <- f1]
      else
        AT_node a1 w1 (rcons f1 t2)
    else
      t1
  end.

(* Each entry (w, None) indicates that either w is empty, or
   the first letter of w is an element of an earlier
   ascending tree. *)
(* Each entry (w, Some t) indicates that the first
   letter of w begins a new maximal ascending chain
   (in particular it is either incomparable or strictly less
    than every preceeding word in the sequence). *)
Definition AscendingForest := seq (seq T * option AscendingTree).

Fixpoint AF_update (make_tree: bool) (f: AscendingForest) (w: seq T) :=
  match f, w with
  | _, [::] => rcons f (w, None)
  | [::], b :: v =>
    if make_tree then 
      [:: (w, Some (AT_node b v [::]))]
    else
      [:: (w, None)]
  | (w', None) :: f', _ => (w', None) :: AF_update make_tree f' w
  | (w', Some t) :: f', b :: v => 
    match t with
    | AT_node a _ _ =>
      if a <=_R b then
        (w', Some (AT_meld t (AT_node b v [::]))) :: AF_update false f' w
      else
        (w', Some t) :: AF_update make_tree f' w
    end
  end.

Definition AF_build (ws: seq (seq T)) :=
  foldl (AF_update true) [::] ws.

End Forest.

Section HigmanIsWell.

Context {T: Type}.
Variable (R: rel T).

(* Idea begin bigcons: concatenate every element of l to
   the corresponding element of L. *)
Definition bigcons (l: seq T) (L: seq (seq T)): seq (seq T) :=
   [seq x.1::x.2 | x <- (zip l L)].

(* TODO: this is wrong, do the forest approach, see above. *)
Theorem HigmanLeqDecWell':
   forall l, Bar (has_ascending_pair R) l ->
   forall L,
      Bar (has_ascending_pair (HigmanLeqDec R)) (bigcons l L).
Proof.
   move => l; elim => [{}l H|].
Admitted.

Theorem HigmanLeqDecWell:
   Well R -> Well (HigmanLeqDec R).
Proof.
Admitted.

End HigmanIsWell.


(*|

Bibliography
============

.. [1] Benjamin C. Pierce, Arthur Azevedo de Amorim, Chris Casinghino, Marco Gaboardi, Michael Greenberg, Cătălin Hriţcu, Vilhelm Sjöberg, & Brent Yorgey. (2026).
   *Logical Foundations*. (Vol. 1) Electronic textbook.
   URL: <https://softwarefoundations.cis.upenn.edu>.

.. [2] Assia Mahboubi & Enrico Tassi. (2022).
   *Mathematical Components* (Version 1.0.2).
   DOI: `10.5281/zenodo.7118596 <https://doi.org/10.5281/zenodo.7118596>`_
   URL: <https://math-comp.github.io/mcb/>.

.. [3] S. Demri, A. Finkel, J. Goubault-Larrecq, S. Schmitz, & Ph. Schnoebelen. (2024).
   *Well-Quasi-Orders for Algorithms*. Electronic lecture notes.
   URL: <https://lsv.ens-paris-saclay.fr/~phs/lecture-notes-wqo-mar2024.pdf>.

|*)
