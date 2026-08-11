(*|

==============
Higman is well 
==============
:Author: Reinis Cirpons <reinis.cirpons@inria.fr>
:Description: A `Rocq <https://rocq-prover.org>`_ formalizaion of `Higman's lemma <https://en.wikipedia.org/wiki/Higman's_lemma>`_.

.. include:: ../assets/alectryon_style.rst

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

This Rocq file is written in a
`literate programming <https://en.wikipedia.org/wiki/Literate_programming>`_
style utilizing the `Alectryon <https://alectryon-paper.github.io/>`_ tool.

When reading the compiled web version of the document, prose should
appear interspersed with code snippets. When these code snippets have
output, it can be observed by hovering over the code. Clicking on a
code snippet with output will toggle between showing and hiding the output.

Below are two simple examples, one showing the output and one hiding it.
|*)

Compute 2 + 2. (* .unfold *)
Compute 2 + 5. (* .fold *)

(*|
When reading the
`Rocq source <https://github.com/reiniscirpons/RocqHigmanOrder/blob/main/theories/Higman.v>`_
of this file, the comments may look a bit strange due to the markup, but
should hopefully still remain legible. In particular comments of the form
:coq:`(* .foo *)` are used to control Alectryon output and should be ignored.

We start by importing some libraries we are going to use and set some
boilerplate below.
|*)

From Stdlib Require Import Btauto.
Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq choice eqtype path. (* .no-messages *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope higman_order_scope.
Delimit Scope higman_order_scope with HO.
Local Open Scope higman_order_scope.

(*|

Notations
=========

We reserve some notation for later, to make the lemmas easier to read.
Roughly speaking:

1. The notation :coq:`<=_R` will denote the non-strict base order
   :math:`\leq` on the alphabet.

2. The notation :coq:`<=^*_R` will denote the non-strict Higman order
   on words :math:`\leq^\ast` induced by the base 
   order :math:`\leq` on letters.

3. The notations :coq:`<=^^*_R` will denote a computational version of the
   non-strict Higman order.

4. The notations :coq:`<_R`, :coq:`<^*_R` and :coq:`<^^*_R` will denote the
   strict versions of the above orders.

The :coq:`Reserved Notation` command declares a notation for use later on.
|*)

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

In this section we define some properties of quasi-orders.
Rocq already has much of this formalized in the
preorder module of the math-comp library,
see e.g. the
`preorder module documentation
<https://math-comp.github.io/htmldoc/mathcomp.order.preorder.html>`_.

However, using this library requires us to do a bit of boilerplate
to correctly register our orders, which we chose to avoid for
simplicity of presentation in the first instance. 

There should be no issue to integrate with the mathcomp preorder
module later on.
|*)
Section QuasiOrder.

(*|
We start by declaring some recurring objects for this section
using the :coq:`Context` and :coq:`Variable` commands.
The general syntax of declaring a variable named :coq:`name` of type :coq:`type`
is :coq:`name: type`. Occasionally we can omit the type declaration when
it can be inferred from context.

We declare the variable :coq:`T` to be
the base type of the alphabet over which our ordering is defined.
|*)
Context {T: Type}.

(*|
We declate the variable :coq:`R` to be a relation on :coq:`T`.
While we do not yet impose any requirements (like e.g. reflexivity or
transitivity) on :coq:`R`, we think of it as a "non-strict" :math:`\leq`
order on :coq:`T`. 
|*)
Variable (R: rel T).

(*|
The type of :coq:`R` is :coq:`rel T`, which expands to :coq:`T -> T -> bool`,
i.e. :coq:`R` is a function taking in two arguments and returning a boolean.
We interpret :coq:`R a b = true` to mean that :math:`a \leq b` holds.
|*)
Check R: T -> T -> bool. (* .unfold *)
(*|
Note that this framing also requires that :coq:`R` is effective, i.e.
there is a program that can decide if :math:`a \leq b` holds or not.
More on this later.
|*)

(*|
Lets denote the order :coq:`R` on :coq:`T` by :coq:`<=`.
|*)
Notation "a <= b" := (R a b).

(*|
Lets now define the strict order associated to :coq:`R`.
Recall that :math:`a < b` holds precisely when
:math:`a \leq b` and :math:`b \not \leq a`.
We can translate this mathematical definition directly to Rocq
as:

  :coq:`(a <= b) && ~~ (b <= a)`

Here :coq:`&&` is the boolean conjunction
and :coq:`~~` is the boolean negation.
We denote the strict order by :coq:`a < b`.
|*)
Definition Lt a b := ((a <= b) && ~~ (b <= a)).
Notation "a < b" := (Lt a b).

(*|
We can now state and prove our first lemma!
Lets prove that :math:`a < b` and :math:`b \leq c`
imply that :math:`a < c`, provided that :coq:`R` is transitive:
|*)
Lemma lt_leq_lt:
  transitive R -> forall a b c, a < b -> b <= c -> a < c.

(*|
Here the arrows :coq:`->` in the code should be read as logical implications,
i.e. :coq:`X -> Y` means if :math:`X` then :math:`Y`. Chaining multiple arrows
then just means we add multiple hypotheses to the statement,
i.e. :coq:`X -> Y -> Z` just means that if :math:`X` *and* :math:`Y` both hold,
then :math:`Z` also holds.

So the statement of :coq:`lt_leq_lt` above decyphers to:

  **Lemma**: If :math:`R` is a transitive relation,
  then for all :math:`a, b` and :math:`c`, :math:`a < b` and
  :math:`b \leq c` imply that :math:`a < c`.

To see what :coq:`transitive` means in Rocq, we can :coq:`Print` its definition.
|*)

Print transitive. (* .unfold .no-goals *)

(*|
There is some boilerplate, but the crucial part is this:

  :coq:`forall y x z : T, R x y -> R y z -> R x z`

In other words, :coq:`transitive R` means that for all :math:`x, y, z \in T`
we have that :math:`x \leq y` and :math:`y \leq z` implies :math:`x \leq z`,
which is just the usual mathematical definition.
|*)

(*|
We now need to prove the lemma. We start a proof with the :coq:`Proof`
command. The output displays the current proof state, with named
variables and hypotheses shown above the line, and the goal displayed
below the line.

We will be quite verbose in this first proof to give a flavor of
how these things go. Subsequent proofs will be much more terse.
See the
`Proof mode <https://rocq-prover.org/doc/V9.2.0/refman/proofs/writing-proofs/proof-mode.html>`_.
chapter of the reference manual for more details.
|*)
Proof. (* .unfold *)
(*|
We start by using the :coq:`move =>` tactic to name the transitivity
hypothesis :coq:`Htrans` and to name the variables :coq:`a`, :coq:`b` and :coq:`c`,
moving them from the goal to the named variables and hypotheses list.
|*)
  move => Htrans a b c. (* .unfold *)
(*|
We are now left with a goal of the form:

  :coq:`a < b -> b <= c -> a < c.`

We can unfold the definition of :coq:`<` using the :coq:`rewrite` tactic.
|*)
  rewrite /(_ < _). (* .unfold *)
(*|
This exposes the fact that we defined :coq:`a < b` to mean
:math:`a \leq b` and :math:`b \not \leq a`.
We would like to split apart the hypothesis 
:coq:`(a <= b) && ~~ (b <= a)` to add both
:coq:`a <= b` and :coq:`~~ (b <= a)` as *separate* named hypotheses.
Normally this can be done with the :coq:`case` tactic.
But we can't do it at the moment since the expression
:coq:`(a <= b) && ~~ (b <= a)` is a boolean, i.e. it is either
the value :coq:`true` or the value :coq:`false`,
and it has no idea about *how* the boolean was constructed.
|*)
  case. (* .unfold .no-goals *)
(*|
We can what the type of an expression is with the :coq:`Check` command.
|*)
  Check (a <= b) && ~~ (b <= a). (* .unfold .no-goals *)
  Print bool. (* .unfold .no-goals *)
(*|
As we can see from the :coq:`Print` command, a :coq:`bool` is either
:coq:`true` or :coq:`false`.
Rocq has a different type :coq:`Prop` used to express propositions, which is
much better suited to our needs. Roughly speaking, an instance :coq:`A: Prop`
is a proposition, and an instance :coq:`a: A` is a proof that :coq:`A` holds.

In particular :coq:`Prop` has a different conjunction operation :coq:`/\ `.
If :coq:`A` and :coq:`B` are propositions in :coq:`Prop`, then :coq:`A /\ B` is
the "product type" of :coq:`A` and :coq:`B`, so that an element of
:coq:`A /\ B` is, roughly speaking, a pair :coq:`(a, b)` where :coq:`a: A` and
:coq:`b: B`. With the above interpretation about proofs, this means that
a proof of :coq:`A /\ B` is a pair consisting of a proof of :coq:`A` and
a proof of :coq:`B`.

If we :coq:`Print` the definition of :coq:`/\ ` (note: :coq:`and` is the
name of the definition behind the notation :coq:`/\ `), we see that
it is a type with a single constructor :coq:`conj`, so the pair
:coq:`(a, b)` is actually given by :coq:`conj a b`.
|*)
  Print and. (* .unfold .no-goals *)
(*|
We can split apart pairs, so if we could transform the :coq:`&&` into an
:coq:`/\ `, then we could create two named hypotheses as we wanted.
Thankfully this is possible in Rocq using *reflection* lemmas,
such as the lemma :coq:`andP` below.
|*)
  Check andP. (* .unfold .no-goals *)
(*|
Reflection lemmas allow us to move between :coq:`Prop` and :coq:`bool`,
essentially by proving that the function implementing the boolean,
such as :coq:`&&`, is correct, i.e. the result of :coq:`&&` is true if and only
if :coq:`/\ ` holds.

Given a reflection lemma :coq:`H`, we can apply it to the first
unnamed hypothesis via the :coq:`move/H` tactic.
|*)
  move/andP. (* .unfold *)
(*|
The :coq:`case` tactic can now be used to transform the goal from
:coq:`A /\ B -> C` into :coq:`A -> B -> C`.
|*)
  case. (* .unfold *)
(*| Lets name it as well. |*)
  move => Hab. (* .unfold *)
(*|
Like before :coq:`~~` is boolean negation and it will be slightly more
useful for us to transform it into a propositional negation :coq:`~`.
We can do so using the :coq:`negP` reflection lemma.
|*)
  Check negP.
  move/negP. (* .unfold *)
(*|
The way propositional negation is defined, :coq:`~ A` is equal to
:coq:`A -> False`, i.e. the implication :coq:`A` implies :coq:`False`.
Lets name the two remaining unnamed hypotheses.
|*)
  move => Hba Hbc. (* .unfold *)
(*|
We are finally left with a single goal, the *conclusion*.
As before, we can expand :coq:`<` with :coq:`rewrite`.
|*)
  rewrite /(_ < _). (* .unfold *)
(*|
Similarly, it will be easier to prove the statement if we
replace the :coq:`&&` with :coq:`/\ `. We do this via the :coq:`andP` reflection
lemma again, but because we are applying this lemma to the conclusion
instead of a hypothesis, we need to use the :coq:`apply` tactic instead.
|*)
  apply/andP. (* .unfold *)
(*|
Given a conjunction as a goal, the :coq:`split` tactic splits it into
two independent subgoals.
|*)
  split. (* .unfold *)
(*|
We can focus each goal separately with bullets like :coq:`-`, :coq:`+` and :coq:`*`.
The first subgoal asks us to prove :coq:`a <= c`. Since we know
:coq:`a <= b` and :coq:`b <= c` and :coq:`<=` is transitive, we should be done
by transitivity. We can apply :coq:`Htrans` to the goal to use transitivity,
but we need to specify the intermediate variable with :coq:`with b`,
since Rocq can't guess this.
|*)
  - apply Htrans with b. (* .unfold *)
(*|
Applying this tactic generated two extra goals:
one to prove :coq:`a <= b` and one to prove :coq:`b <= c`.
The :coq:`exact` tactic can be used when we have exactly this goal in
the context already. The :coq:`by` tactic is added to make sure the
subgoal is actually completed (it will complain if not).
|*)
    + by exact Hab. (* .unfold *)
    + by exact Hbc. (* .unfold *)
(*|
The second goal asks us to prove :coq:`~~ (c <= a)`.
Again, it will turn out to be easier to prove the non-boolean
version of this statement, so we apply the reflection lemma.
|*)  
  - apply /negP. (* .unfold *)
(*|
Since `~ A` is the same as `A -> False`, the current goal
:coq:`~ c <= a` is the  same as :coq:`c <= a -> False`, so we can
name the hypothesis :coq:`c <= a`.
|*)
    move => Hac. (* .unfold *)
(*|
The hypothesis :coq:`Hba` is :coq:`~ b <= a`, which is the same as
:coq:`b <= a -> False`. So, if we can prove :coq:`b <= a`, then
we can prove :coq:`False`. We can use the :coq:`apply` tactic to
transform the goal to the premise of the :coq:`Hab` hypothesis.
|*)
    apply Hba. (* .unfold *)
(*|
We are once again done by transitivity, since :coq:`Hbc` and :coq:`Hac`
together imply the conclusion.
We :coq:`apply` the transitivity lemma again, but instead of explicitly
considering the two subgoals, since they are simple enough, the :coq:`by`
tactic will automatically close them for us.
|*)
    by apply Htrans with c. (* .unfold *)
Qed.


(*|
The particular tactics and proof style follows the *small scale reflection*
methodology, also known as *SSReflect*, see the 
`SSReflect chapter <https://rocq-prover.org/doc/V9.2.0/refman/proof-engine/ssreflect-proof-language.html>`_
of the reference manual for more details.

The prior proof was rather long and cumbersome, but SSReflect offers quite
a lot of tools for chaining and simplifying proofs.
We now prove a symmetric lemma :coq:`leq_lt_lt` in only 4 lines by
using these tools.
|*)

Lemma leq_lt_lt: transitive R -> forall a b c, a <= b -> b < c -> a < c.
Proof. (* .unfold *)
(*|
First we can chain moves and applications of reflection lemmas.
So here the :coq:`move => Htrans a b c Hab /andP` part of the next line
will transform the goal into:

  :coq:`b <= c /\ ~~ (c <= b) -> a < c`

We can furthermore perform a :coq:`case` tactic during a :coq:`move`
by using the square brackets :coq:`[]`, so the part :coq:`[Hbc /negP Hcb]`
is roughly the same as doing :coq:`case. move => Hbc /negP Hcb.`.
|*)
  move => Htrans a b c Hab /andP [Hbc /negP Hcb]. (* .unfold *)
(*|
We now only have the conclusion to worry about.
We can chain tactics with a semicolon :coq:`;`, so the following
does :coq:`apply/andP.` followed by :coq:`split.` from before.
|*)
  apply/andP; split. (* .unfold *)
(*| First case can be dispatched with the transitivity tactic. |*)
    by apply Htrans with b. (* .unfold *)
(*| Second case we chain some lemma applications. |*)
  by apply /negP => Hca; apply Hcb; apply Htrans with a. (* .unfold *)
Qed.

(*|
In theory, every line of a good Rocq proof should correspond roughly
one to one with a proof you might write by hand. For the proof of
:coq:`leq_lt_lt` this would roughly go as follows.

Line 1:

  :coq:`move => Htrans a b c Hab /andP [Hbc /negP Hcb].`

Let :math:`\leq` be a transitive relation, let :math:`a, b, c\in T` be
arbitrary. Assume that :math:`a \leq b` and that :math:`b < c`.
By definition, the latter is equivalent to :math:`b \leq c` and
:math:`c \not \leq b`.

Line 2:

  :coq:`apply/andP; split.`

To prove :math:`a < c`, it suffices to prove that :math:`a \leq c` and
:math:`c \not \leq a`. We prove each in turn.

Line 3:

  :coq:`by apply Htrans with b.`

Since :math:`a\leq b` and :math:`b \leq c`,
transitivity of :math:`\leq` implies that :math:`a \leq c`.

Line 4:

  :coq:`by apply /negP => Hca; apply Hcb; apply Htrans with a.`

Assume by contradiction that :math:`c \leq a`. Since
:math:`c \leq a` and :math:`a \leq b` hold, transitivity implies that
:math:`c \leq b` holds.
But this is a contradiction since :math:`c \not \leq b` by assumption.
Hence :math:`c \not \leq a`, as required.

The lines are a bit overloaded here, but conceptually the parts of the
Rocq proof map onto the main parts of the human proof.
Not all of the proofs in this repository follow this maxim at the moment,
but hopefully they can be refined later on.
|*)

(*|
We can now prove that :math:`<` is transitive. You can see the proof state
after executing each line by hovering over the line or clicking on it.
|*)
Lemma lt_transitive: transitive R -> transitive Lt.
Proof.
  move => Htrans a b c /andP [Hba _] Hac.
  by apply leq_lt_lt with a.
Qed.

(*|
We will not go into as much detail about proofs in the remainder of the file.
|*)
End QuasiOrder.

(*|
Notations defined inside of sections are cleared after the section is
closed. So we redeclare some notations globally now.
We will write :coq:`a <=_R b` for the non-strict order and
:coq:`a <_R b` for the strict one. 
|*)
Notation "a <=_ R b" := (R a b).
Notation "a <_ R b" := (Lt R a b).

(*|

Higman's embedding order
========================

In this section we define the Higman embedding order arising from a base
order on some alphabet.
|*)
Section HigmanLeqOrder.

(*|
As before, :coq:`T` is the type of the alphabet and :coq:`R` is the base
order on the alphabet.
|*)
Context {T: Type}.
Variable (R: rel T).


(*|
We first consider the non-strict Higman order in an inductive fashion.
The type :coq:`seq T` is the type of sequences of elements in :coq:`T`,
i.e. words, whose alphabet is :coq:`T`.

We will give an alternative definition of :coq:`HigmanLeq` which is decidable
later on, and prove that it is equivalent to the inductive definition.
The :coq:`Inductive` command lets us define a proposition or type inductively
by specifying all of its constructors.
|*)
Inductive HigmanLeq {T} (R: rel T): seq T -> seq T -> Prop :=
| HLeq_nil: forall u,
    [::] <=^*_R u
| HLeq_cons1: forall b u v,
    u <=^*_R v ->
    u <=^*_R (b::v)
| HLeq_cons2: forall a b u v,
    a <=_R b ->
    u <=^*_R v ->
    (a::u) <=^*_R (b::v)
(*|
A little notational convenience: we declare the notation as part of
the definition, so we could write :coq:`u <=^*_R v` instead of
:coq:`HigmanLeq R u v` above.
|*)
where "u <=^*_ R v" := (HigmanLeq R u v).

(*|
Here the :coq:`[::]` denotes the empty word in Rocq and
:coq:`b::v` denotes left-concatenation of a letter to a word.
Hence each of the construcors of :coq:`HigmanLeq` corresponds to
one of the inference rules in the mathematical definition of the
Higman embedding order:

.. math::

  \begin{prooftree}
  \AxiomC{$u \in T^\ast$}
  \LeftLabel{HLeq_nil}
  \UnaryInfC{$\varepsilon \leq^\ast u$}
  \end{prooftree}
  
  \begin{prooftree}
  \AxiomC{$b\in T$}
  \AxiomC{$u, v \in T^\ast$}
  \AxiomC{$u \leq^\ast v$}
  \LeftLabel{HLeq_cons1}
  \TrinaryInfC{$u \leq^\ast bv$}
  \end{prooftree}
  
  \begin{prooftree}
  \AxiomC{$a, b\in T$}
  \AxiomC{$u, v \in T^\ast$}
  \AxiomC{$a \leq b$}
  \AxiomC{$u \leq^\ast v$}
  \LeftLabel{HLeq_cons2}
  \QuaternaryInfC{$au \leq^\ast bv$}
  \end{prooftree}

The type of :coq:`HigmanLeq` is :coq:`seq T -> seq T -> Prop`, instead
of :coq:`seq T -> seq T -> bool` like we had for :coq:`R`.
This is because inductive definitions are non-effective by default. Indeed,
there is no general purpose algorithm for deciding if a proposition holds
given a set of inference rules, so we cannot expect inductive definitions
to be computable.
|*)


(*|
However, it is not hard to see that Higman's order *is* effective,
whenever the base order on the alphabet is effective.
We will now give an alternative, computable definition of
:coq:`HigmanLeq`.

We can do so using the :coq:`Fixpoint` command, which is simply Rocq's
way of specifying a recursive function.
|*)
Fixpoint HigmanLeqDec {T} (R: rel T): rel (seq T) :=
  fun u v =>
    match u with
    | [::] => true
    | a::u' =>
      match v with
      | [::] => false
      | b::v' => (u <=^^*_R v') || ((a <=_R b) && (u' <=^^*_R v'))
      end
    end
(*|
Note the double :coq:`^^` for the notation for :coq:`HigmanLeqDec`,
as opposed to the single one for :coq:`HigmanLeq`.
|*)
where "u <=^^*_ R v" := (HigmanLeqDec R u v).

(*|
Briefly, the :coq:`fun u v =>` statement defines a function and binds
:coq:`u, v` as its arguments. The :coq:`match u with` statement performs
casework on :coq:`u`.
If :coq:`u` is empty, then the first inference rule
:coq:`HLeq_nil` tells us that :coq:`[::] <=^*_R u` holds,
so we return :coq:`true`.

Otherwise if :coq:`u` is non-empty, we do casework on :coq:`v`.
If :coq:`v` is empty, then return :coq:`false`, the empty word
is the minimum element.
If both :coq:`u` and :coq:`v` are non-empty, then one of
:coq:`HLeq_cons1` or :coq:`HLeq_cons2` must be used,
so we encode this.
Here :coq:`||` and :coq:`&&` are just boolean "or" and boolean "and".

The :coq:`u <=^^*_R v'` and :coq:`u' <=^^*_R v'` calls are
recursive. Since the size of the second argument :coq:`v'` is strictly,
smaller than that of :coq:`v`, this is guaranteed to terminate.

This last point is important! Rocq will not let us define a function
if it cannot be proven to terminate. For example, the following definition
fails, because Rocq detects that `n` is non-decreasing.
|*)

Fail Fixpoint loop: nat -> nat := fun n => loop (n * 2). (* .unfold *)

(*|
I claim that :coq:`HigmanLeq` and :coq:`HigmanLeqDec` are equivalent,
i.e. that :coq:`HigmanLeqDec` returns :coq:`true` if and only if
:coq:`HigmanLeq` holds.
Since we are in a proof assistant, we can actually make such claims precise
and prove them!

We do this by establishing the reflection lemma :coq:`HigmanLeqDecP` below.
|*)

Lemma HigmanLeqDecP: forall u v,
  reflect (u <=^*_R v) (u <=^^*_R v).
Proof.
  move => u v; apply: (iffP idP).
  - elim: v u => [[_|//]|b v IH [_|a u /= /orP [|/andP [Hab]] /IH Huv]].
    + by apply HLeq_nil.
    + by apply HLeq_nil.
    + by apply HLeq_cons1.
    + by apply HLeq_cons2.
  - elim => [[//|//]|b [//|a {}u] {}v _ /= -> //|a b {}u {}v /= -> _ -> /=];
    by rewrite orbC.
Qed.

(*|
There are two parts to the proof: showing that the computational result
implies the non-computational one and vice-versa.
The first part is done by doing casework on :coq:`u` and :coq:`v`, and applying
the corresponding constructor of :coq:`HigmanLeq`.
The second part is done by induction on the evidence using the :coq:`elim`
tactic. There are three cases: one for each constructor.
In each case we are done by doing some more casework, using the inductive hypothesis
and then performing some computation to deduce the result.

For the remainder of the section we prove some utility lemmas about
the decidable Higman order.
|*)

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

(*| Transitivity of the base order is preserved by the Higman order. |*)
Lemma HigmanLeqDec_trans: transitive R -> transitive (HigmanLeqDec R).
Proof.
  move => Htrans v u w; elim: w u v => [|c w IH] [|a u] [|b v] //.
  move => /= /orP [|/andP [Hab]] Huv /orP [|/andP [Hac]] Huw.
  - by rewrite (IH (a::u) v) //; apply HigmanLeqDec_cons1 with b.
  - by rewrite (IH (a::u) v).
  - by rewrite (IH (a::u) (b::v)) //; apply HigmanLeqDec_cons2.
  - by rewrite (IH u v) // (Htrans b) // orbC.
Qed.

(*| Higman's order refines the size order. |*)
Lemma HigmanLeqDec_size: forall {u v},
  u <=^^*_R v -> size u <= size v.
Proof.
  move => u v /HigmanLeqDecP; elim => {u v} [//|b u v _ /leqW //|//].
Qed.

End HigmanLeqOrder.
Notation "a <=^*_ R b" := (HigmanLeq R a b).
Notation "a <=^^*_ R b" := (HigmanLeqDec R a b).

(*|
In Rocq well-foundedness is the same as termination, i.e. it is a property
of the strict order, as opposed to the non-strict order. In this
section we endeavour to define the strict order and prove it is correct.
|*)
Section HigmanLtOrder.

Context {T: Type}.
Variable (R: rel T).

(*|
Recall that we defined the strict order associate to :coq:`R` by:

  :coq:`(a <=_R b) && ~~ (b <=_R a)`

using the boolean "and" and "not" operators.

We define the strict propositional Higman order similarly below,
but note that the logical and :coq:`/\ ` and logical negation :coq:`~` is
used instead of their boolean counterparts.
|*)
Definition HigmanLt (R: rel T) a b :=
  ((a <=^*_R b) /\ ~ (b <=^*_R a)).
Notation "a <^*_ R b" := (HigmanLt R a b).

(*|
Here we show that there is a decidable version of the same inequality
using the :coq:`HigmanLeqDec` function.
|*)
Lemma HigmanLtP: forall u v,
  reflect (u <^*_R v) ((u <=^^*_R v) && ~~ (v <=^^*_R u)).
Proof.
  move => u v; apply (iffP idP) =>
    [/andP [/HigmanLeqDecP Huv /HigmanLeqDecP Hvu]
    |[/HigmanLeqDecP -> /HigmanLeqDecP ->] //]; by split.
Qed.

(*|
For the computational version, we choose to give a slightly more explicit
definition, which will make our life much easier later on.
|*)
Fixpoint HigmanLtDec {T} (R: rel T): rel (seq T) :=
  fun u v =>
    match v with
    | [::] => false
    | b::v' =>
      match u with
      | [::] => true
      | a::u' =>
        (u <=^^*_R v') ||
        ((a <_R b) && (u' <=^^*_R v')) ||
        ((a <=_R b) && (u' <^^*_R v'))
      end
    end
where "u <^^*_ R v" := (HigmanLtDec R u v).

(*|
Prove correctness of the above function with a reflection lemma again.
|*)
Lemma HigmanLtDecP: forall u v,
  reflect (u <^*_R v) (u <^^*_R v).
Proof.
  move => u v; apply: (iffP idP) => [Huv |/HigmanLtP /andP [Huv Hvu]].
  - apply /HigmanLtP;
    elim: v u Huv => [[//|//]|b v IH [//|a u] /=].
    move => /orP [/orP [Huv|/andP [/andP [Hab Hba] Huv]]|/andP [Hab /IH /andP [Huv Hvu]]];
    apply /andP; split; rewrite ?Huv ?Hab // orbC // negb_or negb_and.
    + apply /andP; split; first (apply /orP; right); apply/negP;
      move/HigmanLeqDec_size; move/HigmanLeqDec_size in Huv => /=;
        first by rewrite ltn_geF.
      by rewrite leq_gtF => [|//]; apply ltnW.
    + apply/andP; split; first by apply /orP; left.
      apply /negP => /HigmanLeqDec_size /=.
      by move/HigmanLeqDec_size in Huv; rewrite ltn_geF.
    + apply/andP; split; first by apply /orP; right.
      apply /negP => /HigmanLeqDec_size /=.
      by move/HigmanLeqDec_size in Huv; rewrite ltn_geF.
  - elim: v u Huv Hvu => [[//|//]|b v' IH [//|a u'] /=].
    move => /orP [-> //|/andP [Hab Huv]].
    rewrite /(_ <_R _) negb_or negb_and => /andP [Hbvu /orP [->|Hvu]];
      first by rewrite Hab Huv -orbA orbC.
    by rewrite orbC Hab IH.
Qed.

(*| Some more utility lemmas now. |*)

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

TODO: Talk about well-foundedness in Rocq here, mention
inductive versus existential definition here.

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
Print Hchoice.

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
  apply (@Hchoice
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
      first by apply /rev_trans /lt_transitive.
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
  move => P H f.
  by apply (Bar_mkseq H).
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
    + by left; apply /(has_nthP a0); exists j.
    + by right; apply IH; exists i; exists j.
Qed.

Definition Well: Prop := Bar has_ascending_pair [::].

Lemma Well_spec: Well ->
  forall (a0: T) (f: nat -> T), exists i j, i < j /\ f i <=_R f j.
Proof.
  move/Bar_nil_mkseq => H a0 f.
  move: (H f) => [n /(has_ascending_pairP a0) [i [j [Hi []]]]].
  rewrite size_mkseq => Hj.
  rewrite !nth_mkseq => [|//|Hij];
    first by apply ltn_trans with j.
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
      first by rewrite /descending pairwise_rcons Hal Hl.
    rewrite andbC /=; apply lt_leq_lt with a => [//|//|].
    by move/andP: Hac => [].
Qed.
    
Lemma Well_wf: Well -> well_founded (Lt R).
Proof.
  move => /Well_wf' Hwell a.
  by apply Hwell.
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
