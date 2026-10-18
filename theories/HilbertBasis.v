From HB Require Import structures.
Require Import ssreflect ssrbool ssrfun.
From Equations.Prop Require Import Logic Equations.
From mathcomp Require Import ssrnat choice eqtype seq.
From mathcomp Require Import order ssralg mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory.

Section GrobnerBasis.

Open Scope ring_scope.
Variable (K:fieldType) (n: nat).
Implicit Types
  (m: 'X_{1..n}) (f g: {mpoly K[n]}) (A: seq {mpoly K[n]}).

(*|
One step reduction of :math:`f` by :math:`g` at the
monomial :math:`m`. Returns :math:`f` unchanged if
:math:`g` is the zero polynomial or
:math:`m` is not a multiple of the leading monomial of :math:`g`.
|*)
Definition red1 m f g: {mpoly K[n]} :=
  if mleadc g == 0%R then f
  else
    let: lmg := mlead g in
    let: lcg := mleadc g in
    if (lmg <= m)%MM then
      f - (f@_m / lcg) *: (g * 'X_[m - lmg])
    else f.

(*|
Importantly, single step reduction removes the monomial :math:`m`
from :math:`f`.
|*)
Lemma red1_at: forall m f g,
  (mleadc g != 0%R) ->
  (mlead g <= m)%MM ->
  (red1 m f g)@_m = 0%R.
Proof.
  move => m f g /negP Hg Hm.
  rewrite /red1.
  case: ifP => [//|_].
  rewrite Hm mcoeffD mcoeffN mcoeffZ. 
  have: (m = (m - mlead g) + mlead g)%MM => [|H];
    first by rewrite submK.
  rewrite [X in (g*_)@_X]H mcoeffMX divfK;
    first by apply /negP.
  by rewrite subrr.
Qed.

(*|
In a lead reduction step, we perform a one step reduction with
respect to the leading monomial of :math:`f`.
|*)
Definition lred1 f g: {mpoly K[n]} :=
  red1 (mlead f) f g.

(*|
For convenience we define :coq:`is_lred1` to check whether
:math:`f` is lead reducible by :math:`g`.
|*)
Definition is_lred1 f g: bool :=
  (mleadc g != 0%R) &&
  (mleadc f != 0%R) &&
  (mlead g <= mlead f)%O.


(*|
Importantly, performing lead reduction always strictly
decreases the leading term (in degrevlex ordering), assuming
it is lead reducible in the first place.
|*)
Lemma lred1_le: forall f g,
  is_lred1 f g ->
  (mlead (lred1 f g) < mlead f)%O.
Proof.
  move => f g /andP [/andP [Hg Hf] Hgf].
Admitted.

(*|
Now we define one step lead reduction by a sequence of polynomials
:math:`A`, which reduces :math:`f` by the first applicable
(i.e. lead reducible) polynomial in the sequence, or returns
:math:`f` unchanged otherwise.
The :coq:`is_lred1s` function returns :coq:`true` if any polynomial
is applicable and :coq:`false` otherwise.
|*)

Definition lred1s f A := lred1 f (nth f A (find (is_lred1 f) A)).
Definition is_lred1s f A := has (is_lred1 f) A.

Lemma lred1s_le: forall f A,
  is_lred1s f A ->
  (mlead (lred1s f A) < mlead f)%O.
Proof.
  move => f A H.
  by apply /lred1_le /nth_find.
Qed.

(*|
Finally, to define the full lead reduction, we want to repeatedly
lead reduce by a sequence of functions, until no more lead reductions
can occur. This is a bit tricky to prove the termination of, so we
use the :coq:`Equations` library to simplify the process.

First we make the degrevlex ordering on monomials an instance
of :coq:`WellFounded`, to indicate that it is well founded.
Note it was already proven to be well-founded in the
:coq:`mathcomp-monomials` library, so this is just making
it visible to the :coq:`Equations` library.
|*)

Instance ltom_well_founded:
  WellFounded (<%O: rel 'X_{1..n}) := ltom_wf.

(*|
The :coq:`Equations` library allows us to define functions via
well-founded induction with some extra tricks. Below we define
the lead reduction function :coq:`lred`. Is is terminating since it
always decreases the leading monomial of :math:`f` in each
recursive call. We write :coq:`by wf (mlead f) <%O)` to declare this,
i.e. we guarantee that the value of :coq:`mlead f` is strictly
decreasing with respect to the degrevlex ordering :coq:`<%O` in
every recursive call.

We then need to prove that this is actually the case. If we tried
doing this without some extra help we would surely fail:
our recursive call is to :coq:`lred (lred1s f A) A`, and
:coq:`lred1s f A` has a smaller leading monomial only if
it was lead reducible by at least one element of :coq:`A`.
This is what the :coq:`with inspect (is_lred1s f A)` is doing.
One one hand it lets us change what the function does depending
on whether :coq:`is_lred1s f A` returns :coq:`true` or :coq:`false`.
On the other hand, the :coq:`inspect` allows us to also remember
what the output of this function was, which means we are able to
use it in the proof. Hence the termination of this
function is easily proved.

Note, the :coq:`eqn:` notation is just to make this internal match
statement prettier.
|*)

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Equations? lred f A: {mpoly K[n]}
  by wf (mlead f) <%O :=
    lred f A with inspect (is_lred1s f A) := {
      | true eqn: H => lred (lred1s f A) A;
      | false eqn: _ => f
    }.
Proof.
  by apply lred1s_le.
Qed.

(*|
Another perk of the :coq:`Equations` library is that we can
now use the :coq:`funelim` tactic to do casework on the inductive
definition of :coq:`lred`. So for example we can prove that the result
of :coq:`lred` is not lead reducible by any element of :coq:`A`.
|*)
Lemma lred_is_lred1s: forall f A, is_lred1s (lred f A) A = false.
Proof.
  move => f A.
  by funelim (lred f A).
Qed.

(*|
In general, for testing membership in an ideal generated by a set
:math:`A` of polynomials, we must perform all possible
reductions, not just lead reductions, but this process is not
confluent. I.e. its possible to reduce the same polynomial in two
distinct ways. If we could fix this, then every polynomial in the
ideal generated by :math:`A` would reduce to 0 (since 0 belongs to
every ideal, and 0 reduces to itself by definition). Hence this
would give us a simple test for membership.

One simple observation is that, whenever some polynomial can be
reduced in two distinct ways, say by polynomials :math:`f` and
:math:`g`, it must contain a monomial which is the least common
multiple :math:`l` of the leading monomials of
:math:`f` and :math:`g`.

As such, whenever we can reduce some polynomial :math:`h` by either
:math:`f` or :math:`g`, it can be written as
:math:`h = c\cdot l + h^\prime` for some scalar :math:`c` and some
polynomial :math:`h^\prime` that does not contain the monomial
:math:`l`. Then the one step reduction by :math:`f` is
:math:`h^\prime - c\cdot \textrm{red}_1(l, f)` and the reduction by
:math:`g` is :math:`h^\prime - c\cdot \textrm{red}_1(l, g)`, where
:math:`\textrm{red}_1` is the one step reduction operator.

It follows that the difference between these two reductions is
precisely
:math:`c\dot\left(\textrm{red}_1(l, f) - \textrm{red}_1(l, g)\right)`.
The term :math:`\textrm{red}_1(l, f) - \textrm{red}_1(l, g)` is
called the _critical pair_ or _S-polynomial_ associated to a pair
of polynomials :math:`f` and :math:`g`. I.e. it is the difference
between the one step reduction of the least common multiple of
:math:`f` and :math`g` by each of :math:`f` and :math:`g`.
We define it below as :coq:`spoly`.
|*)
Definition spoly f g: {mpoly K[n]} :=
  let lcm := mlcm (mlead f) (mlead g) in
  red1 lcm 'X_[lcm] f - red1 lcm 'X_[lcm] g.

(*|
A fundamental observation is that, if the reduction is confluent
on every critical pair, then it is also confluent on all polynomials.
This is sometimes called Newman's lemma. 

A _Gröbner basis_ is a set of polynomials in which every lead
reduction of any critical pair of elements in the basis equals 0.
We define it below as the boolean predicate :coq:`is_gbasis`.
|*)
Definition is_gbasis A: bool :=
  all2 (fun f g => lred (spoly f g) A == 0%R) A A.

(*|
As it turns out, every set of polynomials can be extended to a
Gröbner basis generating the same ideal.
|*)

End GrobnerBasis.
