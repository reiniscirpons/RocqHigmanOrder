From HB Require Import structures.
Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat choice eqtype seq.
From mathcomp Require Import order ssralg mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory.

Section GrobnerBasis.

Open Scope ring_scope.
Variable (K:fieldType) (n: nat).

(*|
One step reduction of :math:`f` by :math:`g` at the monomial :math:`m`.
Returns :math:`f` unchanged if :math:`g` is the zero polynomial or
:math:`m` is not a multiple of the leading monomial of :math:`g`.
|*)
Definition red1 (m: 'X_{1..n}) (f g: {mpoly K[n]}): {mpoly K[n]} :=
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
Definition lred1 (f g: {mpoly K[n]}): {mpoly K[n]} :=
  red1 (mlead f) f g.

(*|
Importantly, performing lead reduction always strictly
decreases the leading term (in degrevlex ordering).
|*)
Lemma lred1_le: forall f g,
  (mleadc g != 0%R) ->
  (mlead g <= mlead f)%MM ->
  (mlead (lred1 f g) < mlead f)%O.
Proof.
  move => f g Hg Hlmg.
Admitted.

(*|
Now we define one step lead reduction by a sequence of polynomials
by just iterating the one step lead reduction over a sequence.
|*)
Fixpoint lred1s (f: {mpoly K[n]}) (A: seq {mpoly K[n]}) :=
  match A with
  | [::] => f
  | g::A' => lred1s (lred1 f g) A'
  end.

(*|
Finally, to define the full lead reduction, we will need to do some

|*)

#[program]
Fixpoint lred'
  (f: {mpoly K[n]}) (A: seq {mpoly K[n]})
  {measure (mlead f) (<%O: 'X_{1..n} -> 'X_{1..n} -> Prop)} :=
  let redf := lred1s f A in
  if (mlead redf < mlead f)%O then lreds redf A
  else f.


Definition spoly (f g: {mpoly K[n]}): {mpoly K[n]} :=
  let lcm := mlcm (mlead f) (mlead g) in
  red1 lcm 'X_[lcm] f - red1 lcm 'X_[lcm] g.

End GrobnerBasis.
