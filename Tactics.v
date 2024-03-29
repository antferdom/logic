(** * Tactics: More Basic Tactics *)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From COC Require Export Poly.

(* ################################################################# *)
(** * The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    _exactly_ the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

(** Here, we could finish with "[rewrite -> eq2.  reflexivity.]" as we
    have done several times before.  We can finish this proof in
    a single step by using the [apply] tactic instead: *)

  apply eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] that introduces some _universally quantified
    variables_.  When Coq matches the current goal against the
    conclusion of [H], it will try to find appropriate values for
    these variables.  For example, when we do [apply eq2] in the
    following proof, the universal variable [q] in [eq2] gets
    instantiated with [n], and [r] gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

(** **** Exercise: 2 stars, standard, optional (silly_ex) 

    Complete the following proof using only [intros] and [apply]. *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 2 = true ->
     oddb 3 = true.
Proof.
  intros n eq1.
  apply eq1.
Qed.

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal exactly -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat), true = (n =? 5)  ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.

(** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)

  symmetry.
  simpl. (** (This [simpl] is optional, since [apply] will perform
             simplification first, if needed.) *)
  apply H.
Qed.

(** **** Exercise: 3 stars, standard (apply_exercise1) 

    _Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  You may find earlier lemmas like
    [app_nil_r], [app_assoc], [rev_app_distr], [rev_involutive],
    etc. helpful.  Also, remember that [Search] is your friend
    (though it may not find earlier lemmas if they were posed as
    optional problems and you chose not to finish the proofs). *)

Theorem rev_exercise1 : forall (l l' : list nat), l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

(** **** Exercise: 1 star, optional (apply_rewrite)  *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied? *)

(* When we need to use global variables, "apply" is better than "rewrite". *)

(* ################################################################# *)
(** * The [apply with] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a;b]] to [[e;f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(** Since this is a common pattern, we might like to pull it out as a
    lemma that records, once and for all, the fact that equality is
    transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

(** Now, we should be able to use [trans_eq] to prove the above
    example.  However, to do this we need a slight refinement of the
    [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

(** If we simply tell Coq [apply trans_eq] at this point, it can
    tell (by matching the goal against the conclusion of the lemma)
    that it should instantiate [X] with [[nat]], [n] with [[a,b]], and
    [o] with [[e,f]].  However, the matching process doesn't determine
    an instantiation for [m]: we have to supply one explicitly by
    adding "[with (m:=[c,d])]" to the invocation of [apply]. *)
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

(** (Actually, we usually don't have to include the name [m] in
    the [with] clause; Coq is often smart enough to figure out which
    variable we are instantiating. We could instead write [apply
    trans_eq with [c;d]].) *)

(** Coq also has a tactic [transitivity] that accomplishes the
    same purpose as applying [trans_eq]. The tactic requires us to
    state the instantiation we want, just like [apply with] does. *)

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.
Qed.

(** **** Exercise: 3 stars, standard, optional (trans_eq_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  transitivity m.
  apply H2.
  apply H1.
Qed.

(* ################################################################# *)
(** * The [injection] and [discriminate] Tactics *)

(** Recall the definition of natural numbers:

     Inductive nat : Type :=
       | O
       | S (n : nat).

    It is obvious from this definition that every number has one of
    two forms: either it is the constructor [O] or it is built by
    applying the constructor [S] to another number.  But there is more
    here than meets the eye: implicit in the definition are two more
    facts:

    - The constructor [S] is _injective_, or _one-to-one_.  That is,
      if [S n = S m], it must be that [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor
    is injective and [nil] is different from every non-empty list.
    For booleans, [true] and [false] are different.  (Since [true] and
    [false] take no arguments, their injectivity is neither here
    nor there.)  And so on. *)

(** For example, we can prove the injectivity of [S] by using the
    [pred] function defined in [Basics.v]. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  (* insert new hypothesis H2 *)
  assert (H2: n = pred (S n)). { reflexivity. }
  (* prove H1 *)
  rewrite H2. 
  rewrite H1. 
  reflexivity.
Qed.

(** This technique can be generalized to any constructor by
    writing the equivalent of [pred] -- i.e., writing a function that
    "undoes" one application of the constructor. As a more convenient
    alternative, Coq provides a tactic called [injection] that allows
    us to exploit the injectivity of any constructor.  Here is an
    alternate proof of the above theorem using [injection]: *)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** By writing [injection H as Hmn] at this point, we are asking Coq
    to generate all equations that it can infer from [H] using the
    injectivity of constructors (in the present example, the equation
    [n = m]). Each such equation is added as a hypothesis (with the
    name [Hmn] in this case) into the context. *)

  injection H as Hnm. apply Hnm.
Qed.

(** Here's a more interesting example that shows how [injection] can
    derive multiple equations at once. *)

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(** Alternatively, if you just say [injection H] with no [as] clause,
    then all the equations will be turned into hypotheses at the
    beginning of the goal. *)

Theorem injection_ex2 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (injection_ex3)  *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H1. rewrite -> H2.
  (* insert new hypothesis H3 *)
Admitted.

(** So much for injectivity of constructors.  What about disjointness?

    The principle of disjointness says that two terms beginning with
    different constructors (like [O] and [S], or [true] and [false])
    can never be equal.  This means that, any time we find ourselves
    in a context where we've _assumed_ that two such terms are equal,
    we are justified in concluding anything we want, since the
    assumption is nonsensical. *)

(** The [discriminate] tactic embodies this principle: It is used on a
    hypothesis involving an equality between different
    constructors (e.g., [S n = O]), and it solves the current goal
    immediately.  Here is an example: *)

Theorem eqb_0_l : forall n, 
  0 =? n = true -> n = 0.
Proof.
  intros n.

(** We can proceed by case analysis on [n]. The first case is
    trivial. *)

  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.

(** However, the second one doesn't look so simple: assuming [0
    =? (S n') = true], we must show [S n' = 0]!  The way forward is to
    observe that the assumption itself is nonsensical: *)

  - (* n = S n' *)
    simpl.

(** If we use [discriminate] on this hypothesis, Coq confirms
    that the subgoal we are working on is impossible and removes it
    from further consideration. *)

    intros H. discriminate H.
Qed.

(** This is an instance of a logical principle known as the _principle
    of explosion_, which asserts that a contradictory hypothesis
    entails anything (even false things!). *)

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

(** If you find the principle of explosion confusing, remember
    that these proofs are _not_ showing that the conclusion of the
    statement holds.  Rather, they are showing that, _if_ the
    nonsensical situation described by the premise did somehow arise,
    _then_ the nonsensical conclusion would also follow, because we'd
    be living in an inconsistent universe where every statement is
    true.  We'll explore the principle of explosion in more detail in
    the next chapter. *)

(** **** Exercise: 1 star, standard (discriminate_ex3)  *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra.
Qed.



(** To summarize this discussion, suppose [H] is a hypothesis in the
    context or a previously proven lemma of the form
      c a1 a2 ... an = d b1 b2 ... bm
    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] has the following effect:
    - If [c] and [d] are the same constructor, then, by the
      injectivity of this constructor, we know that [a1 = b1], [a2 =
      b2], etc.; [inversion H] adds these facts to the context, and
      tries to use them to rewrite the goal.
    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory, and the current goal doesn't have to be
      considered. In this case, [inversion H] marks the current goal
      as completed and pops it off the goal stack. *)



(** The injectivity of constructors allows us to reason that
    [forall (n m : nat), S n = S m -> n = m].  The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find convenient in a few
    places below: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. 
  intros A B f x y H. 
  rewrite H.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

(** There is also a tactic named `f_equal` that can prove such
    theorems.  Given a goal of the form [f a1 ... an = g b1 ... bn],
    the tactic [f_equal] will produce subgoals of the form [f = g],
    [a1 = b1], ..., [an = bn]. At the same time, any of these subgoals
    that are simple enough (e.g., immediately provable by
    [reflexivity]) will be automatically discharged by [f_equal]. *)

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic "[simpl in H]" performs simplification on
    the hypothesis [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.


(** Similarly, [apply L in H] matches some conditional statement
    [L] (of the form [X -> Y], say) against a hypothesis [H] in the
    context.  However, unlike ordinary [apply] (which rewrites a goal
    matching [Y] into a subgoal [X]), [apply L in H] matches [H]
    against [X] and, if successful, replaces it with [Y].

    In other words, [apply L in H] gives us a form of "forward
    reasoning": from [X -> Y] and a hypothesis matching [X], it
    produces a hypothesis matching [Y].  By contrast, [apply L] is
    "backward reasoning": it says that if we know [X -> Y] and we
    are trying to prove [Y], it suffices to prove [X].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5)  ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. apply H.
Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_ and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.

    The informal proofs that you've seen in math or computer science
    classes probably tended to use forward reasoning.  In general,
    idiomatic use of Coq favors backward reasoning, but in some
    situations the forward style can be easier to think about. *)

(* ################################################################# *)
(** * Varying the Induction Hypothesis *)

(** * Varying the Induction Hypothesis *)

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we sometimes need to be careful about which of the
    assumptions we move (using [intros]) from the goal to the context
    before invoking the [induction] tactic.  For example, suppose
    we want to show that [double] is injective -- i.e., that it maps
    different arguments to different results:

       Theorem double_injective: forall n m,
         double n = double m -> n = m.

    The way we start this proof is a bit delicate: if we begin it with

       intros n. induction n.

    all is well.  But if we begin it with

       intros n m. induction n.

    we get stuck in the middle of the inductive case... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) 
  simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) 
    reflexivity.
    + (* m = S m' *)
    discriminate eq.
  - (* n = S n' *) 
  intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *)
    discriminate eq.
    + (* m = S m' *)
    apply f_equal.

(** At this point, the induction hypothesis ([IHn']) does _not_ give us
    [n' = m'] -- there is an extra [S] in the way -- so the goal is
    not provable. *)

Abort.

(** What went wrong? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context --
    intuitively, we have told Coq, "Let's consider some particular [n]
    and [m]..." and we now have to prove that, if [double n = double
    m] for _those particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove, for
    _all_ [n], that the proposition

      - [P n] = "if [double n = double m], then [n = m]"

    holds, by showing

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") and

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular (arbitrary,
    but fixed) [m] -- say, [5].  The statement is then saying that,
    if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help at all with proving
    [R]!  If we tried to prove [R] from [Q], we would start with
    something like "Suppose [double (S n) = 10]..." but then we'd be
    stuck: knowing that [double (S n)] is [10] tells us nothing
    helpful about whether [double n] is [10] (indeed, it strongly
    suggests that [double n] is _not_ [10]!!), so [Q] is useless. *)

(** Trying to carry out this proof by induction on [n] when [m] is
    already in the context doesn't work because we are then trying to
    prove a statement involving _every_ [n] but just a _single_ [m]. *)

(** A successful proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *) simpl.

(** Notice that both the goal and the induction hypothesis are
    different this time: the goal asks us to prove something more
    general (i.e., to prove the statement for _every_ [m]), but the IH
    is correspondingly more flexible, allowing us to choose whichever
    [m] we like when we apply the IH. *)

    intros m eq.

(** Now we've chosen a particular [m] and introduced the assumption
    that [double n = double m].  Since we are doing a case analysis on
    [n], we also need a case analysis on [m] to keep the two "in sync." *)

    destruct m as [| m'] eqn:E.
    + (* m = O *)

(** The 0 case is trivial: *)

    discriminate eq.
    + (* m = S m' *)
      apply f_equal.

(** At this point, since we are in the second branch of the [destruct
    m], the [m'] mentioned in the context is the predecessor of the
    [m] we started out talking about.  Since we are also in the [S]
    branch of the induction, this is perfect: if we instantiate the
    generic [m] in the IH with the current [m'] (this instantiation is
    performed automatically by the [apply] in the next step), then
    [IHn'] gives us exactly what we need to finish the proof. *)

      apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.

(** What you should take away from all this is that we need to be
    careful, when using induction, that we are not trying to prove
    something too specific: When proving a property involving two
    variables [n] and [m] by induction on [n], it is sometimes
    crucial to leave [m] generic. *)

(** The following exercise follows the same pattern. *)

(** **** Exercise: 2 stars, standard (eqb_true)  *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *)
    intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) simpl. reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *)
     intros m eq.  destruct m as [| m'] eqn:E.
    + (* m = O *)  discriminate eq.
    + (* m = S m' *) apply f_equal. apply IHn'.
    simpl in eq. apply eq.
Qed.

(** The strategy of doing fewer [intros] before an [induction] to
    obtain a more general IH doesn't always work by itself; sometimes
    some _rearrangement_ of quantified variables is needed.  Suppose,
    for example, that we wanted to prove [double_injective] by
    induction on [m] instead of [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (And if we simply say [induction m] without
    introducing anything first, Coq will automatically introduce [n]
    for us!)  *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them!  Rather we want to state them in the clearest and
    most natural way. *)

(** What we can do instead is to first introduce all the quantified
    variables and then _re-generalize_ one or more of them,
    selectively taking variables out of the context and putting them
    back at the beginning of the goal.  The [generalize dependent]
    tactic does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal.
Qed.

(* ################################################################# *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a name that
    has been introduced by a [Definition] so that we can manipulate
    the expression it denotes.  For example, if we define... *)

Definition square n := n * n.

(** ... and try to prove a simple fact about [square]... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ... we appear to be stuck: [simpl] doesn't simplify anything, and
    since we haven't proved any other facts about [square], there is
    nothing we can [apply] or [rewrite] with. *)

(**  To make progress, we can manually [unfold] the definition of
    [square]: *)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these it is not hard
    to finish the proof. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite -> H. rewrite -> mult_assoc. reflexivity.
Qed.

(** At this point, some discussion of unfolding and simplification is
    in order.

    We already have observed that tactics like [simpl], [reflexivity],
    and [apply] will often unfold the definitions of functions
    automatically when this allows them to make progress.  For
    example, if we define [foo m] to be the constant [5]... *)

Definition foo (x: nat) := 5.

(** .... then the [simpl] in the following proof (or the
    [reflexivity], if we omit the [simpl]) will unfold [foo m] to
    [(fun x => 5) m] and then further simplify this expression to just
    [5]. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** However, this automatic unfolding is somewhat conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** The reason that [simpl] doesn't make progress here is that it
    notices that, after tentatively unfolding [bar m], it is left with
    a match whose scrutinee, [m], is a variable, so the [match] cannot
    be simplified further.  It is not smart enough to notice that the
    two branches of the [match] are identical, so it gives up on
    unfolding [bar m] and leaves it alone.  Similarly, tentatively
    unfolding [bar (m+1)] leaves a [match] whose scrutinee is a
    function application (that cannot itself be simplified, even
    after unfolding the definition of [+]), so [simpl] leaves it
    alone. *)

(** At this point, there are two ways to make progress.  One is to use
    [destruct m] to break the proof into two cases, each focusing on a
    more concrete choice of [m] ([O] vs [S _]).  In each case, the
    [match] inside of [bar] can now make progress, and the proof is
    easy to complete. *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** This approach works, but it depends on our recognizing that the
    [match] hidden inside [bar] is what was preventing us from making
    progress. *)

(** A more straightforward way forward is to explicitly tell Coq to
    unfold [bar]. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** Now it is apparent that we are stuck on the [match] expressions on
    both sides of the [=], and we can use [destruct] to finish the
    proof without thinking too hard. *)

  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where [destruct] is used to
    perform case analysis of the value of some variable.  Sometimes we
    need to reason by cases on the result of some _expression_.  We
    can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.
Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (n =? 3) then ... else ...].  But either
    [n] is equal to [3] or it isn't, so we can use [destruct (eqb
    n 3)] to let us reason about the two cases.

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c]. *)

(** **** Exercise: 3 stars, optional (combine_split)  *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H. generalize dependent l. generalize l1.
  induction l2 as [| h2 l2'].
  - intros l0 l. generalize dependent l0. induction l as [|h l'].
    + intros l0 H. assert (l0 = []). { inversion H. reflexivity. } rewrite H0. reflexivity.
    + intros l0 H. inversion H. unfold app_list_pair in H1. Abort.

(** The [eqn:] part of the [destruct] tactic is optional: So far,
    we've chosen to include it most of the time, just for the sake of
    documentation.

    However, when [destruct]ing compound expressions, the information
    recorded by the [eqn:] can actually be critical: if we leave it
    out, then [destruct] can erase information we need to complete a
    proof.

    For example, suppose we define a function [sillyfun1] like
    this: *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

(** Now suppose that we want to convince Coq that [sillyfun1 n]
    yields [true] only when [n] is odd.  If we start the proof like
    this (with no [eqn:] on the [destruct])... *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

(** ... then we are stuck at this point because the context does
    not contain enough information to prove the goal!  The problem is
    that the substitution performed by [destruct] is quite brutal --
    in this case, it throws away every occurrence of [n =? 3], but we
    need to keep some memory of this expression and how it was
    destructed, because we need to be able to reason that, since [n =?
    3 = true] in this branch of the case analysis, it must be that [n
    = 3], from which it follows that [n] is odd.

    What we want here is to substitute away all existing occurences of
    [n =? 3], but at the same time add an equation to the context that
    records which case we are in.  This is precisely what the [eqn:]
    qualifier does. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        [eqn:] again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.
Qed.




