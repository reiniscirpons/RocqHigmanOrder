From HB Require Import structures.
Require Import ssreflect ssrbool ssrfun.
From Equations.Prop Require Import Logic Equations.
From mathcomp Require Import ssrnat choice eqtype seq fintype tuple bigop.
From mathcomp Require Import order ssralg freeg mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory.

Section Utils.

Context {T1 T2: eqType}.
Implicit Types (f: T1 -> T2) (X: seq T1) (Y: seq ((seq T1) * T2)).

Fixpoint updategroup Y (x: T1) (y: T2): seq ((seq T1) * T2) :=
  match Y with
  | [::] => [:: ([:: x], y)]
  | (l, y')::Y' =>
    if y == y' then
      (x::l, y')::Y'
    else
      (l, y')::(updategroup Y' x y)
    end.

Fixpoint groupby f X: seq ((seq T1) * T2) :=
  match X with
  | [::] => [::]
  | x::X' => updategroup (groupby f X') x (f x)
  end.

Lemma updategroup_flatten1: forall f X,
  perm_eq X (flatten [seq z.1 | z <- groupby f X]).
Proof.
Admitted.

Lemma updategroup_uniq2: forall f X,
  uniq [seq z.2 | z <- groupby f X].
Proof.
Admitted.

End Utils.

Section GeneratedIdeal.

Open Scope ring_scope.
Context {R: nzRingType}.
Variable (B: seq R).
Implicit Types (x y r: R) (C: seq R).
Let k := size B.

Definition in_genideal x: Prop := exists C,
  x = \sum_(0 <= i < k) C`_i * B`_i.

(*Check nth_map.*)
(*Lemma nth_map: forall (T1 : pzRingType) (T2 : pzRingType) *)
(*  (f : T1 -> T2) (n : nat) (s : seq T1),*)
(*  n < size s -> [seq f i | i <- s]`_n = f (s`_n).*)
(*Proof.*)
(*  move => T1 T2 f n s Hn.*)
(*  by apply nth_map.*)
(*Qed.*)

Lemma genideal_addr_closed: forall x y,
  in_genideal x -> in_genideal y -> in_genideal (x + y).
Proof.
  move => x y [Cx ->] [Cy ->].
  exists [tuple Cx`_i + Cy`_i | i < k].
Admitted.

Lemma genideal_scaler_closed: forall x r,
  in_genideal x -> in_genideal (x * r).
Proof.
  move => x r [Cx ->].
  exists [tuple Cx`_i * r | i < k].
Admitted.

(* TODO: Prove the above *)

End GeneratedIdeal.

Section MultinomialDecomposition.

Open Scope ring_scope.
Context {R: nzRingType}.
Variable (n: nat) (B: seq {mpoly R[n]}).

Record decomp_term := DecompTerm {
  dcoeff: R;
  dmonom: 'X_{1..n};
  dpolyn: {mpoly R[n]}
}.

Definition decomp_term_beq (x y: decomp_term): bool :=
  (dcoeff x == dcoeff y) && (dmonom x == dmonom y) && (dpolyn x == dpolyn y).

Lemma decomp_term_beqP: Equality.axiom decomp_term_beq.
Proof.
  move => [x1 x2 x3] [y1 y2 y3]. apply (iffP idP) => /=.
  - by rewrite /decomp_term_beq => /= /andP [/andP [/eqP -> /eqP ->]/eqP -> //].
  - by case => -> -> ->; rewrite /decomp_term_beq /= !eq_refl.
Qed.

HB.instance Definition _ := hasDecEq.Build decomp_term decomp_term_beqP.

Implicit Types (x y r: {mpoly R[n]}) (D: seq decomp_term).
Let k := size B.

Print subset.body.

Definition is_decomp D: Prop :=  {subset [seq dpolyn d | d <- D] <= B}.

Definition deval (d: decomp_term): {mpoly R[n]} :=
  [mpoly <<dcoeff d *g dmonom d >>] * dpolyn d.

Definition devals D: {mpoly R[n]} :=
  \sum_(d <- D) deval d.

Definition has_mdecomp x: Prop := exists D, x == devals D.

Lemma has_mdecompP: forall x,
  in_genideal B x <-> has_mdecomp x.
Proof.
Admitted.

Definition dlead D: 'X_{1..n} := (\join_(d <- D) mlead (deval d))%O.

Lemma mlead_le_dlead: forall D, (mlead (devals D) <= dlead D)%O.
Proof.
  elim => [|d D /=].
  - by rewrite /devals /dlead !big_nil mlead0.
  - rewrite /devals /dlead !big_cons => IH.
    apply le_trans with (mlead (deval d) `|` mlead (\sum_(j <- D) deval j))%O.
    + by apply mleadD_le.
    + by rewrite leU2.
Qed.

Variable (D: seq decomp_term).
Hypothesis HlmD: (mlead (devals D) < dlead D)%O.

Let S1 := [seq t <- D | mlead (deval t) == dlead D].
Let S2 := [seq t <- D | t \notin S1].

Local Lemma Ssum: perm_eq (S1 ++ S2) D.
Proof.
Admitted.

Local Lemma DnilN: D <> [::].
Proof.
  move => H; move: HlmD.
  by rewrite H /devals /dlead !big_nil mlead0 ltx0.
Qed.

Lemma S1nilN: S1 <> [::].
Proof.
  apply /eqP.
  rewrite -has_filter /dlead.
  (* TODO: We have \join currently, but it really is the max,
     for max its immediate (max is one of the elements for non -mepty list),
     for join is false in general. We should fix. *)
Admitted.

Lemma S1sum0: \sum_(d <- D)
  [mpoly << dcoeff d *g ((dmonom d) + (mlead (dpolyn d)))%MM >>] = 0%R.
Proof.
Admitted.

End MultinomialDecomposition.

Section GrobnerBasis.

Open Scope ring_scope.
Variable (K:fieldType) (n: nat).
Implicit Types
  (m: 'X_{1..n}) (f g: {mpoly K[n]}) (B: seq {mpoly K[n]}).

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
  Search mlead.
  move => f g /andP [/andP [Hg Hf] Hgf].
Admitted.

(*|
Now we define one step lead reduction by a sequence of polynomials
:math:`B`, which reduces :math:`f` by the first applicable
(i.e. lead reducible) polynomial in the sequence, or returns
:math:`f` unchanged otherwise.
The :coq:`is_lred1s` function returns :coq:`true` if any polynomial
is applicable and :coq:`false` otherwise.
|*)

Definition lred1s f B := lred1 f (nth 0%R B (find (is_lred1 f) B)).
Definition is_lred1s f B := has (is_lred1 f) B.

Lemma lred1s_le: forall f B,
  is_lred1s f B ->
  (mlead (lred1s f B) < mlead f)%O.
Proof.
  move => f B H.
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
our recursive call is to :coq:`lred (lred1s f B) B`, and
:coq:`lred1s f B` has a smaller leading monomial only if
it was lead reducible by at least one element of :coq:`B`.
This is what the :coq:`with inspect (is_lred1s f B)` is doing.
One one hand it lets us change what the function does depending
on whether :coq:`is_lred1s f B` returns :coq:`true` or :coq:`false`.
On the other hand, the :coq:`inspect` allows us to also remember
what the output of this function was, which means we are able to
use it in the proof. Hence the termination of this
function is easily proved.

Note, the :coq:`eqn:` notation is just to make this internal match
statement prettier.
|*)

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Equations? lred f B: {mpoly K[n]}
  by wf (mlead f) <%O :=
    lred f B with inspect (is_lred1s f B) := {
      | true eqn: H => lred (lred1s f B) B;
      | false eqn: _ => f
    }.
Proof.
  by apply lred1s_le.
Qed.

(*|
Another perk of the :coq:`Equations` library is that we can
now use the :coq:`funelim` tactic to do casework on the inductive
definition of :coq:`lred`. So for example we can prove that the result
of :coq:`lred` is not lead reducible by any element of :coq:`B`.
|*)
Lemma lred_is_lred1s: forall f B, is_lred1s (lred f B) B = false.
Proof.
  move => f B.
  by funelim (lred f B).
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
Definition is_gbasis B: bool :=
  all2 (fun f g => lred (spoly f g) B == 0%R) B B.


(* TODO: Prove Lemma 3.8 from Aliaume and Arka paper to show that 
   In ideal iff is_gbasis B -> lred f B = 0. *)

End GrobnerBasis.
