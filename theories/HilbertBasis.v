From HB Require Import structures.
Require Import ssreflect ssrbool ssrfun.
From Equations.Prop Require Import Logic Equations.
From mathcomp Require Import ssrnat choice eqtype seq fintype tuple bigop.
From mathcomp Require Import order ssralg freeg mpoly.
From mathcomp Require Import ssrAC.

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
Variable (R: nzRingType) (n: nat) (B: seq {mpoly R[n]}).

Record decomp_term := DecompTerm {
  dcoeff: R;
  dmonom: 'X_{1..n};
  dpolyn: {mpoly R[n]}
}.

Definition DT0 := (DecompTerm 0%R 0%MM 0%R).

Definition decomp_term_beq (x y: decomp_term): bool :=
  (dcoeff x == dcoeff y) && (dmonom x == dmonom y) && (dpolyn x == dpolyn y).

Lemma decomp_term_beqP: Equality.axiom decomp_term_beq.
Proof.
  move => [x1 x2 x3] [y1 y2 y3]. apply (iffP idP) => /=.
  - by rewrite /decomp_term_beq => /= /andP [/andP [/eqP -> /eqP ->]/eqP -> //].
  - by case => -> -> ->; rewrite /decomp_term_beq /= !eq_refl.
Qed.

HB.instance Definition _ := hasDecEq.Build decomp_term decomp_term_beqP.

Definition normalize_decomps (D: seq decomp_term): seq decomp_term :=
  [seq d <- D | dcoeff d != 0].

Definition is_normalized_decomps (D: seq decomp_term): bool :=
  all (fun d => dcoeff d != 0) D.

Lemma normalize_is_normalized: forall D, is_normalized_decomps (normalize_decomps D).
Proof.
  move => D. apply /allP => d.
  by rewrite mem_filter => /andP [].
Qed.

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

(* TODO: WTF? Maybe add the d <- D form to mathcomp, probably bug. *)
Definition dlead D: 'X_{1..n} := (\max_(d <- D | true) mlead (deval d))%O.

Lemma mlead_le_dlead: forall D, (mlead (devals D) <= dlead D)%O.
Proof.
  elim => [|d D /=].
  - by rewrite /devals /dlead !big_nil mlead0.
  - rewrite /devals /dlead !big_cons => IH.
    apply le_trans with (mlead (deval d) `|` mlead (\sum_(j <- D) deval j))%O.
    + by apply mleadD_le.
    + by rewrite leU2.
Qed.


(*Definition decomp_trivial (p: {mpoly R[n]}): decomp_term :=*)
(*  [seq (DecompTerm ) | t <- msupp p].*)


Variable (D: seq decomp_term).
Hypothesis Hnorm: is_normalized_decomps D.
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

(* TODO: Add to mathcomp?? *)
Lemma max_mem {T: Type}: forall (t0: T) (f: T -> 'X_{1..n}) (S: seq T),  
  size S != 0 -> exists i, i < size S /\ (\max_(x <- S|true) f x)%O = f (nth t0 S i).
Proof.
  move => t0 f S.
  elim: S => [//|x S IH _].
  case: S IH => [_|y S /= IH].
  - exists 0.
    by rewrite big_cons big_nil /(Order.max) ltx0.
  - move: (IH is_true_true) => [i [HiS Hi]].
    rewrite big_cons /=.
    case Hx: (f x < \max_(j <- y :: S | true) f j)%O.
    + exists i.+1.
      move: Hx.
      by rewrite /Order.max Hi => -> /=.
    + exists 0.
      move: Hx.
      by rewrite /Order.max Hi => ->.
Qed.

Lemma S1nilN: S1 <> [::].
Proof.
  apply /eqP.
  rewrite -has_filter /dlead.
  enough 
    (H: exists i,
      i < size D /\ dlead D = mlead (deval (nth (DecompTerm 0%R 0%MM 0%R) D i))).
  - apply /hasP.
    case: H => i [HiS Hi].
    exists ((nth {| dcoeff := 0; dmonom := 0; dpolyn := 0 |} D i)) => [|].
    + by apply /(nthP (DecompTerm 0%R 0%MM 0%R)); exists i.
    + by rewrite -Hi.
  - rewrite /dlead. apply (max_mem _ (fun t => mlead (deval t))).
    by move: DnilN; case: D.
Qed.

(*Lemma S1sum0: \sum_(d <- S1)*)
(*  [mpoly*)
(*    << dcoeff d *g ((dmonom d) + (mlead (dpolyn d)))%MM >>] *)
(*    = 0%R*)
(*  <-> (mlead (devals S1) < dlead S1)%O.*)
(*Proof.*)
(*  split => [H|].*)
(*  - rewrite /mlead /devals.*)
(**)
(*Lemma S1sum0: \sum_(d <- S1)*)
(*  [mpoly << dcoeff d *g ((dmonom d) + (mlead (dpolyn d)))%MM >>] = 0%R.*)
(*Proof.*)
(*Qed.*)


Lemma sum_coeffC:
  (\sum_(d <- D) deval d)@_(dlead D) = 
  (\sum_(d <- D) (deval d)@_(dlead D)).
Proof.
Admitted.

Lemma S1P: forall d,
  deval d != 0 ->
  (mlead (deval d) < dlead D)%O ->
  ((deval d)@_(dlead D) != 0) = ((mlead (deval d) == dlead D)).
Proof.
  move => d Hd HD.
  move: (mlead_supp Hd).
  case H: (mlead (deval d) < dlead D)%O.
  - rewrite (mcoeff_gt_mlead H).
    case H': ((mlead (deval d) == dlead D)).
    + by move/eqP in H'; rewrite H' ltxx in H.
    + by move => _; apply /negP.
  - move => H'.
    move/negP: H => /negP H.
    rewrite ltNge negbK in H.
    case H'': ((mlead (deval d) == dlead D)).
    + move /eqP in H''.
      by rewrite -mcoeff_msupp -H'' H'.
    + exfalso.
      by rewrite leNgt HD in H.
Qed.

Lemma sum_filter0 {T: Type}:
  forall (X: (seq T)) (f: T -> R),
  \sum_(x <- X) f x = \sum_(x <- X | f x != 0%R) f x.
Proof.
Admitted.

(* Want: every polynomial can be decomposed as 
  mcoeff * mlead + foo
*)

Search mcoeff mlead.

Lemma dcoeff_dlead: forall d,
  mlead (deval d) == dlead D ->
  dcoeff d = (deval d)@_(dlead D).
Proof. 
  move => d Hd.
  rewrite /deval /=.
  (* TODO: decomposition lemma, then linearity, then
     distributes, then one part gives right answer, other
     gives 0 because it is smaller. *)
Admitted.

Lemma S1sum0: \sum_(d <- S1) dcoeff d = 0%R.
Proof.
  have: (\sum_(d <- S1) dcoeff d = (devals D)@_(dlead D)) => [//|H].
  - rewrite /devals sum_coeffC (sum_filter0 D)
      -(big_filter D).
    have: ([seq x <- D | (deval x)@_(dlead D) != 0] = S1).
    + rewrite /S1.
      apply eq_in_filter => d Hd.
      rewrite S1P => [||//].
      * admit.
      * admit. (*TODO: fix this, the case is wrong, the
          assumption is too much *)
    + move => ->.
      rewrite /S1 !big_filter.
      apply eq_bigr => d Hd.
      by rewrite dcoeff_dlead.
  - by rewrite H mcoeff_gt_mlead.
Admitted.

End MultinomialDecomposition.

Section GrobnerBasis.

Open Scope ring_scope.
Variable (K:fieldType) (n: nat).
Implicit Types
  (m: 'X_{1..n}) (f g: {mpoly K[n]}) (B: seq {mpoly K[n]})
  (d: decomp_term K n) (D: seq (decomp_term K n)).

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

Definition red1K: forall m f g,
  (mleadc g != 0%R) ->
  (mlead g <= m)%MM ->
  let: lmg := mlead g in 
  let: lcg := mleadc g in
  f = red1 m f g + (f@_m / lcg) *: (g * 'X_[m - lmg]).
Proof.
  move => m f g /negP Hc Hm.
  rewrite /red1 Hm.
  case: ifP => [//|_].
  by rewrite subrK.
Qed.

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
  (mlead g <= mlead f)%MM.

Definition lred1K: forall f g,
  is_lred1 f g ->
  let: lmg := mlead g in 
  let: lmf := mlead f in 
  let: lcg := mleadc g in
  let: lcf := mleadc f in 
  f = lred1 f g + (lcf / lcg) *: (g * 'X_[lmf - lmg]).
Proof.
  move => f g /andP [/andP [Hg Hf] Hfg].
  by apply red1K with (m := mlead f).
Qed.

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

Definition lred1sK: forall f B,
  is_lred1s f B ->
  let: g := (nth 0%R B (find (is_lred1 f) B)) in
  let: lmg := mlead g in 
  let: lmf := mlead f in 
  let: lcg := mleadc g in
  let: lcf := mleadc f in 
  f = lred1 f g + (lcf / lcg) *: (g * 'X_[lmf - lmg]).
Proof.
  move => f B H.
  apply lred1K.
  move: H.
  rewrite /is_lred1s.
  by apply nth_find.
Qed.

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
  lred1 'X_[lcm] f - lred1 'X_[lcm] g.


(*|
A fundamental observation is that, if the reduction is confluent
on every critical pair, then it is also confluent on all polynomials.
This is sometimes called Newman's lemma. 

A _Gröbner basis_ is a set of polynomials in which every lead
reduction of any critical pair of elements in the basis equals 0.
We define it below as the boolean predicate :coq:`is_gbasis`.

TODO: change explanation
|*)
Definition ssaturated B: Prop :=
  forall f g,
    f \in B ->
    g \in B ->
    lred (spoly f g) B == 0%R.

Definition is_decomp_wrt B D: bool :=
  all (fun d => dpolyn d \in B) D.

Definition is_good_decomp D: bool :=
  dlead D == mlead (devals D).

(* TODO(figure out if we can make it automatically simplify to this) *)
Lemma devals_nil: forall R N,
  @devals R N [::] = 0%R.
Proof.
  move => R N.
  by rewrite /devals big_nil.
Qed.

Lemma dlead_nil: forall R N,
  @dlead R N [::] = 0%MM.
Proof.
  move => R N.
  by rewrite /dlead big_nil.
Qed.

Lemma red0decomp B f:
  0%R \notin B ->
  lred f B == 0%R -> exists D,
    is_good_decomp D /\ is_decomp_wrt B D /\ devals D = f.
Proof.
  move => HB0.
  funelim (lred f B); last first.
  - move => /eqP ->; exists [::]; split => [|].
    + by rewrite /is_good_decomp devals_nil dlead_nil mlead0.
    + by split => [//|]; rewrite devals_nil.
  - move/H0: HB0 => {}H0.
    move => /H0 [D [Hgood [HB Hdevals]]].
    rewrite (lred1sK H).
    set b := B`_(find (is_lred1 f) B).
    set c := (mleadc f / mleadc b).
    set m := (mlead f - mlead b)%MM.
    exists ((DecompTerm c m b)::D).
    split.
    + rewrite /is_good_decomp /dlead /devals !big_cons.
      rewrite /devals in Hdevals.
      rewrite Hdevals.
      move: Hgood => /eqP; rewrite /dlead => ->.
      rewrite /devals Hdevals.
      rewrite /deval /=.
      enough (Hlt: (mlead (lred1s f B) < mlead ([mpoly << c *g m >>] * b))%O).
      * by rewrite mleadDl // max_l // le_eqVlt Hlt orbC.
      * have: (mlead ([mpoly << c *g m >>] * b) = mlead f);
          first admit.
        move => ->.
        by rewrite lred1s_le.
    + split.
      * rewrite /= HB andbC /=.
        apply mem_nth.
        rewrite -has_find.
        move: H1 => _.
        rewrite /is_lred1s in H.
        by rewrite H.
      * rewrite /devals in Hdevals.
        rewrite /devals  big_cons Hdevals /deval /= /lred1s addrC.
        f_equal.
        by rewrite -mulr_algl mulrC mulrA [_ * b]mulrC -mulrA MPolyU -mulr_algl.
Admitted.

Definition dsaturated B: Prop :=
  forall p q,
    p \in B ->
    q \in B ->
    exists (D: seq (decomp_term K n)),
      is_good_decomp D /\
      is_decomp_wrt B D /\
      devals D = spoly p q.

Lemma ssaturated_dsaturated: forall B,
  0%R \notin B -> ssaturated B -> dsaturated B.
Proof.
  move => B HB H p q Hp Hq.
  move: (H p q Hp Hq) => H0.
  move: (red0decomp HB H0) => [D HD].
  by exists D.
Qed.

Definition lcancel_pair (d1 d2: decomp_term K n): bool :=
   (mlead (deval d1 + deval d2) < mlead (deval d1))%O &&
   (mlead (deval d1 + deval d2) < mlead (deval d2))%O.

Lemma lcancel_spoly: forall d1 d2,
  lcancel_pair d1 d2 ->
  exists c m,
    c != 0 /\
    deval d1 + deval d2 = c *: ('X_[m] * spoly (dpolyn d1) (dpolyn d2)). 
Proof.
  move => d1 d2 /andP [].
Admitted.

Definition csaturated B: Prop :=
  forall d1 d2,
    dpolyn d1 \in B ->
    dpolyn d2 \in B ->
    lcancel_pair d1 d2 ->
    exists (D: seq (decomp_term K n)),
      is_good_decomp D /\
      is_decomp_wrt B D /\
      devals D = deval d1 + deval d2.

Definition scale_decomp c m D :=
  [seq (DecompTerm (c * dcoeff d) (m + dmonom d) (dpolyn d) ) | d <- D ].

Lemma devals_scale: forall D c m,
  c != 0 ->
  devals (scale_decomp c m D) = c *: ('X_[m] * devals D).
Proof.
  move => D c m Hc.
  rewrite /devals big_map /deval /=.
Admitted.

Lemma good_scale: forall D c m,
  c != 0 ->
  is_good_decomp D ->
  is_good_decomp (scale_decomp c m D).
Proof.
  move => D c m Hc /eqP HD.
  rewrite /is_good_decomp /dlead /= devals_scale // big_map /deval /=.
  rewrite /is_good_decomp in HD.
  rewrite mleadZ //.
  case HD0: (devals D == 0).
  - move/eqP in HD0.
  Search (mlead (_ *: _)).
Admitted.
  

Lemma dsaturated_csaturated: forall B,
  0%R \notin B -> dsaturated B -> csaturated  B.
Proof.
  move => B HB0 Hd d1 d2 Hd1 Hd2 /lcancel_spoly [c [m]] [Hc H].
  move: (Hd (dpolyn d1) (dpolyn d2) Hd1 Hd2) => [D [Hgood [Hdec Hdevals]]].
  exists (scale_decomp c m D).
  split;
    first by apply good_scale.
  split.
  - rewrite /is_decomp_wrt all_map.
    by apply Hdec.
  - by rewrite devals_scale // Hdevals -H.
Qed.

Print csaturated.

Lemma decomp_lead_split: forall D,
  let D1 := [seq d <- D | mlead (deval d) == dlead D] in
  let D2 := [seq d <- D | (mlead (deval d) < dlead D)%O] in
  devals D1 + devals D2 = devals D.
Proof.
Admitted.

Lemma decomp_coeff: forall D m,
  (devals D)@_m = \sum_(d <- D) (deval d)@_m.
Admitted.

Lemma decomp_bad_sum0: forall D m,
  is_good_decomp D ->
  all (fun d => mlead (deval d) == m) D ->
  (mlead (devals D) < m)%O ->
  \sum_(d <- D) (dcoeff d)*(mleadc (dpolyn d)) = 0.
Proof.
  move => D m Hgood H Hlead.
  move: (decomp_coeff D m).
  have: ((devals D)@_m = 0) => [|-> H'].
  - apply /memN_msupp_eq0 /negP.
    move => /msupp_le_mlead.
    by rewrite leNgt Hlead.
  - rewrite [X in _ = X]H'.
    move/all_filterP: H => <-.
    rewrite !big_filter.
    apply eq_bigr => d /eqP <-.
    rewrite /deval mleadcM_proper.
    + admit.
    + admit.
Admitted.

(*Definition pairwise_cancel_term d0 D :=*)
(*  let dc0 := dcoeff d0 in*)
(*  let dm0 := dmonom d0 in*)
(*  let dp0 := dpolyn d0 in*)
(*  [seq *)
(*    let dci := dcoeff d in*)
(*    let dmi := dmonom d in*)
(*    let dpi := dpolyn d in*)
(*    dci *: ('X_[dmi] * dpi - ((mleadc dpi)/(mleadc dp0)) *: 'X_[dm0] * dp0)*)
(*  | d <- D].*)

Definition pairwise_cancel_term d0 D :=
  let dc0 := dcoeff d0 in
  let dm0 := dmonom d0 in
  let dp0 := dpolyn d0 in
  [seq 
    let dci := dcoeff d in
    let dpi := dpolyn d in
    (d, 
    DecompTerm (- (dci * (mleadc dpi)/(mleadc dp0))) dm0 dp0)
  | d <- D].

Lemma pairwise_cancel_local_props D m:
  is_good_decomp D ->
  all (fun d => mlead (deval d) == m) D ->
  (mlead (devals D) < m)%O ->
  forall (p: decomp_term K n * decomp_term K n),
    p \in pairwise_cancel_term (head (DT0 K n) D) (behead D) ->
    let: (d1, d2) := p in
      lcancel_pair d1 d2 /\
      (mlead (deval d1 + deval d2) < m)%O.
Proof.
Admitted.

Lemma pairwise_cancel_sumE D m:
  is_good_decomp D ->
  all (fun d => mlead (deval d) == m) D ->
  (mlead (devals D) < m)%O ->
  let PCT := pairwise_cancel_term (head (DT0 K n) D) (behead D) in
  (\sum_(p <- PCT) 
    let: (d1, d2) := p in
    deval d1 + deval d2) = devals D.
Proof.
Admitted.


Lemma csaturated_pairwise_cancel_normalize B D m:
  csaturated B ->
  is_good_decomp D ->
  all (fun d => mlead (deval d) == m) D ->
  (mlead (devals D) < m)%O ->
    exists (D': seq (decomp_term K n)),
      is_good_decomp D' /\
      is_decomp_wrt B D' /\
      devals D' = devals D /\
      (dlead D' < m)%O.
Proof.
Admitted.

Definition weak_gbasis B: Prop := forall D: seq (decomp_term K n),
  is_decomp_wrt B D ->
  exists D',
    is_decomp_wrt B D /\
    devals D = devals D' /\
    dlead D' = mlead (devals D').

Lemma csaturated_weak_gbasis: forall B,
  csaturated B -> weak_gbasis B.
Proof.
  move => B H D.
  set ml := dlead D.
  have: (ml = dlead D) => [//|].
  move: ml => ml.
  elim/(well_founded_ind (@ltom_wf n)): ml D => ml IH D Hml.
  case Heq: (dlead D == mlead (devals D)).
  - exists D.
    by split => [//|]; split => [//|]; apply /eqP.
  - have: ((dlead D < mlead (devals D)))%O.
    + admit.
    + set m :=  mlead (devals D).


Definition gbasis B := forall f,
  reflect (in_genideal B f) (lred f B == 0%R).


(* TODO: Prove Lemma 3.8 from Aliaume and Arka paper to show that 
   In ideal iff is_gbasis B -> lred f B = 0. *)

End GrobnerBasis.
