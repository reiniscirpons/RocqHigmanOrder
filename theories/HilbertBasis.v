From HB Require Import structures.
Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat choice eqtype seq.
From mathcomp Require Import nmodule order ssralg freeg mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Def Order.Theory GRing.Theory.

(*NOTE: Nmodule is a Rocq shorthand for an Abelian monoid.
  It comes from the fact that each such monoid has a module
  structure over the naturals, with scalar multiplication
  given by repeated addition. *)

(*|
We first define a type for ordered Abelian monoids.
First we define a type :coq:`nmoduleOrderType` which contains all
Abelian monoids together with a total order and a bottom element,
but we do not impose any compatibility relations.
|*)

#[short(type="nmoduleOrderType")]
HB.structure Definition NmoduleOrder (d : Order.disp_t) :=
  {T of Order.BTotal d T & Algebra.Nmodule T}.

(*|
Now we turn any :coq:`nmoduleOrderType` into an ordered Abelian
monoid by  imposing two conditions on it - namely that the order
respects right multiplication, and that an element is the minimum
of its right ideal. The type for ordered Abelian monoids is then
:coq:`onmodType`.
|*)

#[key=T, primitive]
HB.mixin Record
  NmoduleOrder_isONmodule d T & NmoduleOrder d T :=
  {
    le_mulrK : forall (z x y: T),
      ((x + z)%R <= (y + z)%R)%O = (x <= y)%O;
    mulr_le : forall (x y: T),
      (x <= (x + y)%R)%O
  }.

#[short(type="onmodType")]
HB.structure Definition ONmodule (d : Order.disp_t) :=
  {T of NmoduleOrder_isONmodule d T & NmoduleOrder d T}.

Section ONModuleTheory.
Context {d: Order.disp_t}.
Variables (G: onmodType d).

Lemma onmod0x: forall (x: G), (0%R <= x)%O.
Proof.
  move => x; move: (mulr_le 0%R x).
  by rewrite add0r.
Qed.

Lemma onmod_bot: \bot%O = 0%R :> G.
Proof.
  apply /le_anti /andP; split.
  - by exact (le0x 0%R).
  - by apply onmod0x.
Qed.
End ONModuleTheory.

(*|
The ordered Abelian monoid structure will be the structure that we 
impose on monomials later on. Initially, however, we will work
in slightly more generality by considering the group ring
:math:`K[G]`, where :math:`K` is a field and :math:`G` is an ordered
Abelian group.

The :coq:`{freeg G / K}` construct does precisely this, defining the
group ring with coefficients in :math:`K` over the base group :math:`G`.
|*)

Definition groupRing {d: Order.disp_t}
  (K: fieldType) (G: onmodType d) :=
    {freeg G / K}.

Notation "K [ G ]" := (groupRing K G) (format "K [ G ]").

Section HilbertBasis.

Context {d: Order.disp_t}.
Variables (G: onmodType d) (K: fieldType).

(*| The leading monomial is the maximum among all monomials with
respect to the monomial ordering. |*)
Definition kg_mlead (p: K[G]): G := (\max_(g <- dom p | true) g)%O.
Definition kg_clead (p: K[G]): K := coeff (kg_mlead p) p.



End HilbertBasis.
