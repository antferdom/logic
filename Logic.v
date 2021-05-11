(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing".
From COC Require Export Tactics.

(** We have seen many examples of factual claims (_propositions_)
    and ways of presenting evidence of their truth (_proofs_).  In
    particular, we have worked extensively with _equality
    propositions_ ([e1 = e2]), implications ([P -> Q]), and quantified
    propositions ([forall x, P]).  In this chapter, we will see how
    Coq can be used to carry out other familiar forms of logical
    reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)

Check 3 = 3 : Prop.

Check forall n m : nat, n + m = m + n : Prop.

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true. *)

(** Simply _being_ a proposition is one thing; being _provable_ is
    something else! *)

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

(** Indeed, propositions not only have types: they are
    _first-class_ entities that can be manipulated in all the same
    ways as any of the other things in Coq's world. *)

(** So far, we've seen one primary place that propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to other kinds of expressions. *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments. For instance, here's a
    (polymorphic) property defining the familiar notion of an
    _injective function_. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.


(** The equality operator [=] is also a function that returns a
    [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined in
    Coq's standard library using the [Notation] mechanism). Because
    [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq : forall A : Type, A -> A -> Prop.

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, and we need to turn
    off the inference of this implicit argument to see the full type
    of [eq].) *)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B]
    is written [A /\ B], representing the claim that both [A] and [B]
    are true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true
    and that [B] is true, we can conclude that [A /\ B] is also
    true. *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can apply [and_intro] to achieve the same effect
    as [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 
    -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  apply and_intro.
  - (* n = 0 *) induction n as [| n'].
    + reflexivity.
    + discriminate H.
  - (* m = 0 *) induction m as [| m'].
    + reflexivity.
    + rewrite plus_comm in H. discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite -> Hn. rewrite -> Hm. simpl.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For this specific theorem, both formulations are fine.  But
    it's important to understand how to work with conjunctive
    hypotheses because conjunctions often arise from intermediate
    steps in proofs, especially in larger developments.  Here's a
    simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite -> Hn. simpl. reflexivity.
Qed.

(** Another common situation with conjunctions is that we know
    [A /\ B] but in some context we need just [A] or just [B].
    In such cases we can do a [destruct] (possibly as part of
    an [intros]) and use an underscore pattern [_] to indicate
    that the unneeded conjunct should just be thrown away. *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  (** destruct HPQ as [_ HQ]. to return Q instead of P **)
  apply HP.
Qed.

(** **** Exercise: 1 star, standard, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q HPQ.
  destruct HPQ as [_ HQ].
  apply HQ.
Qed.

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions.  The following
    commutativity and associativity theorems are handy in such
    cases. *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

(** **** Exercise: 2 stars, standard (and_assoc) 

    (In the following proof of associativity, notice how the _nested_
    [intros] pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof from
    there.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - (* inner *) split.
    + apply HP.
    + apply HQ.
  - (* outer *) apply HR.
Qed.

(** By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)

Check and : Prop -> Prop -> Prop.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (This infix notation stands for [or A B], where [or : Prop ->
    Prop -> Prop].) *)

(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis (which, as with other data types like [nat], can be done
    explicitly with [destruct] or implicitly with an [intros]
    pattern): *)

Lemma eq_mult_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite -> Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite -> Hm. rewrite -> mult_n_O. reflexivity.
Qed.

(** Conversely, to show that a disjunction holds, it suffices to show
    that one of its sides holds. This is done via two tactics, [left]
    and [right].  As their names imply, the first one requires proving
    the left side of the disjunction, while the second requires
    proving its right side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [|n'].
  - (* left *)
  left. reflexivity.
  - (* right *)
  right. simpl. reflexivity.
Qed.

Search ( _ * _ = _ ).
(** **** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 : forall n m,
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n. induction n as [|n'].
  - (* n = O *)
  intros m H. rewrite mult_O_1 in H. left. apply H.
  - (* n = S n' *) intros m. induction m as [| m].
    + intros H. simpl in H. rewrite mult_n_O in H. right. apply H.
    + intros H. discriminate H.
Qed.

(** **** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP|HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(* ================================================================= *)
(** ** Falsehood and Negation

    So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    negative results, demonstrating that some given proposition is
    _not_ true. Such statements are expressed with the logical
    negation operator [~]. *)

(** To see how negation works, recall the _principle of explosion_
    from the [Tactics] chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived. 
    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q].

    Coq actually makes a slightly different (but equivalent) choice,
    defining [~ P] as [P -> False], where [False] is a specific
    contradictory proposition defined in the standard library. *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End MyNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.
Qed.

(** **** Exercise: 2 stars, standard, optional (not_implies_our_not) 

    Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HPnot Q HP.
  contradiction.
Qed.

(** Inequality is a frequent enough example of negated statement
    that there is a special notation for it, [x <> y]: **)

Notation "x <> y" := (~(x = y)).

(** We can use [not] to state that [0] and [1] are different elements
    of [nat]: *)

Theorem zero_not_one : 0 <> 1.
Proof.
  (** The proposition [0 <> 1] is exactly the same as
      [~(0 = 1)], that is [not (0 = 1)], which unfolds to
      [(0 = 1) -> False]. (We use [unfold not] explicitly here
      to illustrate that point, but generally it can be omitted.) *)
  unfold not.
  (** To prove an inequality, we may assume the opposite
      equality... *)
  intros contra.
  (** ... and deduce a contradiction from it. Here, the
      equality [O = S O] contradicts the disjointness of
      constructors [O] and [S], so [discriminate] takes care
      of it. *)
  discriminate contra.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    make Coq understand it!  Here are proofs of a few familiar facts
    to get you warmed up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.
Qed.

(** **** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HQnot.
  unfold not. unfold not in HQnot. intros P'. apply HQnot. apply H. apply P'.
Qed.

(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros [HP HPnot].
  apply HPnot. apply HP.
Qed.

(** Since inequality involves a negation, it also requires a little
    practice to be able to work with it fluently.  Here is one useful
    trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.          (* note implicit [destruct b] here *)
  - (* b = true *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis.

    But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see examples later on. *)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is simply the conjunction
    of two implications. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P. split.
  - (* -> *) intros P'. apply P'.
  - (* <- *) intros P'. apply P'.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HPQ HQP] [HQR HRQ]. split.
  - (* -> *) intros P'. apply HPQ in P'. apply HQR in P'. apply P'.
  - (* <- *) intros R'. apply HRQ in R'. apply HQP in R'. apply R'.
Qed.

(** **** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - (* -> *) intros H. inversion H.
    + split.
      { left. apply H0. }
      { left. apply H0. }
    + split.
      { apply proj1 in H0. right. apply H0. }
      { apply proj2 in H0. right. apply H0. }
  - (* <- *) intros H. inversion H.
    + destruct H1.
      { left. apply H1. }
      { destruct H0.
        { left. apply H0. }
        { right. split.
          { apply H0. }
          { apply H1. } } }
Qed.

(* ================================================================= *)
(** ** Setoids and Logical Equivalence *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we have
    to import the Coq library that supports it: *)

From Coq Require Import Setoids.Setoid.

(** A "setoid" is a set equipped with an equivalence relation,
    that is, a relation that is reflexive, symmetric, and transitive.
    When two elements of a set are equivalent according to the
    relation, [rewrite] can be used to replace one element with the
    other. We've seen that already with the equality relation [=] in
    Coq: when [x = y], we can use [rewrite] to replace [x] with [y],
    or vice-versa.

    Similarly, the logical equivalence relation [<->] is reflexive,
    symmetric, and transitive, so we can use it to replace one part of
    a proposition with another: if [P <-> Q], then we can use
    [rewrite] to replace [P] with [Q], or vice-versa. *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences. *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - (* -> *) apply mult_eq_0.
  - (* <- *) apply eq_mult_0.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - (* -> *) intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - (* <- *) intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity]
    to give smooth proofs of statements involving equivalences.  For
    example, here is a ternary version of the previous [mult_0]
    result: *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite -> mult_0. rewrite -> mult_0. rewrite -> or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which direction of
    the equivalence will be useful. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T,
    P]. As with [forall], the type annotation [: T] can be omitted if
    Coq is able to infer from the context what the type of [x] should
    be. *)

(** To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t].  Then we prove that [P] holds after
    all occurrences of [x] are replaced by [t]. *)

Definition even x := exists n : nat, x = double n.

Lemma four_is_even : even 4.
Proof.
  (* witness_ of the existential is given as 2 in this context *)
  unfold even. exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.
Qed.

(** **** Exercise: 1 star, standard, especially useful (dist_not_exists) 

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P Hall Hexist.
  destruct Hexist as [x HPnot].
  unfold not in HPnot. apply HPnot. apply Hall.
Qed.

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - (* -> *) intros H. destruct H as [X' H]. destruct H as [HP | HQ].
    + left. exists X'. apply HP.
    + right. exists X'. apply HQ.      
  - (* <- *) intros H. destruct H as [HP | HQ].
    + destruct HP as [X' HP]. exists X'. left. apply HP.
    + destruct HQ as [X' HQ]. exists X'. right. apply HQ.
Qed.


(* ################################################################# *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if either it is equal to [x'] or it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition (!): *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].

    Note, in the first, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** This way of defining propositions recursively, though convenient
    in some cases, also has some drawbacks.  In particular, it is
    subject to Coq's usual restrictions regarding the definition of
    recursive functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 2 stars (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - (* -> *) intros H. induction l as [| x' l' IHl'].
    + (* l = [] *)
      simpl in H. contradiction.
    + (* l = x' :: l' *)
      simpl in H. destruct H as [H1 | H2].
      { exists x'. split.
        - apply H1.
        - simpl. left. reflexivity. }
      { apply IHl' in H2. destruct H2 as [x2 H2]. exists x2. split.
        - apply proj1 in H2. apply H2.
        - simpl. right. apply proj2 in H2. apply H2. }
  - (* <- *) intros H. induction l as [| x' l' IHl'].
    + (* l = [] *)
      simpl in H. destruct H as [x' H]. apply proj2 in H. contradiction.
    + (* l = x' :: l' *)
      simpl. simpl in H. destruct H as [x'' H]. inversion H. destruct H1 as [H2 | H3].
      { left. rewrite H2. apply H0. }
      { right. apply IHl'. exists x''. split.
        - apply H0.
        - apply H3. }
Qed.

(** **** Exercise: 2 stars (in_app_iff)  *)
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' x. split.
  - intros H. induction l.
    + simpl. simpl in H. right. apply H.
    + simpl. simpl in H. destruct H.
      { left. left. apply H. }
      { apply IHl in H. apply or_assoc. right. apply H. }
  - intros H. induction l.
    + simpl. simpl in H. destruct H.
      { contradiction. }
      { apply H. }
    + simpl. simpl in H. apply or_assoc in H. destruct H as [H1 | [H2 | H3]].
      { left. apply H1. }
      { right. apply IHl. left. apply H2. }
      { right. apply IHl. right. apply H3. }
Qed.

(** **** Exercise: 3 stars (All)  *)
(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].
    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In : forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l. split.
  - (* -> *) intros H. induction l as [| n l' IHl'].
    + (* l = nil *) simpl. auto.
    + (* l = n :: l' *) simpl. split.
      (* left *) { apply H. simpl. left. reflexivity. }
      (* right *) { apply IHl'. intros x0 H0. apply H. simpl. right. apply H0. }
  - (* <- *) intros H. induction l.
    + (* l = nil *) simpl. intros x0 H0. contradiction.
    + (* l = cons n l' *) simpl. intros x0 H0. destruct H0 as [|H1 H2].
      (* left *) { simpl in H. apply proj1 in H. rewrite H0 in H. apply H. }
      (* right *) { simpl in H. apply proj2 in H. apply IHl with x0 in H. apply H. apply H1. }
Qed.

(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (n : nat) => if oddb n then Podd n else Peven n.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n Hodd Heven.
  unfold combine_odd_even. destruct (oddb n) eqn: H.
  - apply Hodd. reflexivity.
  - apply Heven. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n Hcomb Hodd.
  unfold combine_odd_even in Hcomb.
  rewrite Hodd in Hcomb. assumption.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n Hcomb Heven.
  unfold combine_odd_even in Hcomb.
  rewrite Heven in Hcomb. assumption.
Qed.

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** One feature that distinguishes Coq from some other popular
    proof assistants (e.g., ACL2 and Isabelle) is that it treats
    _proofs_ as first-class objects.

    There is a great deal to be said about this, but it is not
    necessary to understand it all in detail in order to use Coq.
    This section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)

(** We have seen that we can use [Check] to ask Coq to print the type
    of an expression.  We can also use it to ask what theorem a
    particular identifier refers to. *)

Check plus_comm.

(** Coq checks the _statement_ of the [plus_comm] theorem (or prints
    it for us, if we leave off the part beginning with the colon) in
    the same way that it checks the _type_ of any term that we ask it
    to [Check]. Why? *)

(** The reason is that the identifier [plus_comm] actually refers to a
    _proof object_, which represents a logical derivation establishing
    of the truth of the statement [forall n m : nat, n + m = m + n].  The
    type of this object is the proposition which it is a proof of. *)

(** Intuitively, this makes sense because the statement of a
    theorem tells us what we can use that theorem for, just as the
    type of a "computational" object tells us what we can do with that
    object -- e.g., if we have a term of type [nat -> nat -> nat], we
    can give it two [nat]s as arguments and get a [nat] back. 
    Similarly, if we have an object of type [n = m -> n + n = m + m]
    and we provide it an "argument" of type [n = m], we can derive
    [n + n = m + m]. *)

(** Operationally, this analogy goes even further: by applying a
    theorem as if it were a function, i.e., applying it to hypotheses
    with matching types, we can specialize its result without having
    to resort to intermediate assertions.  For example, suppose we
    wanted to prove the following result: *)

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [plus_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  (* WORKED IN CLASS *)
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

(** We saw similar problems back in Chapter [Induction], and saw one
    way to work around them by using [assert] to derive a specialized
    version of [plus_comm] that can be used to rewrite exactly where
    we want. *)

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [plus_comm] directly
    to the arguments we want to instantiate it with, in much the same
    way as we apply a polymorphic function to a type argument. *)

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite <- (plus_comm y z).
  reflexivity.
Qed.

(** Let's see another example of using a theorem like a
    function. The following theorem says: any list [l]
    containing some element must be nonempty. *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** What makes this interesting is that one quantified variable
    ([x]) does not appear in the conclusion ([l <> []]). *)

(** We should be able to use this theorem to prove the special case
    where [x] is [42]. However, naively, the tactic [apply in_not_nil]
    will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(** You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. (The details of how this proof
    works are not critical -- the goal here is just to illustrate what
    can be done.) *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite -> mult_n_O in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But,
    since Coq's equality operator is polymorphic, we can use it at
    _any_ type -- in particular, we can write propositions claiming
    that two _functions_ are equal to each other: *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** Informally, an "extensional property" is one that pertains to an
    object's observable behavior.  Thus, functional extensionality
    simply means that a function's identity is completely determined
    by what we can observe from it -- i.e., the results we obtain
    after applying it. *)

(** However, functional extensionality is not part of Coq's built-in
    logic.  This means that some apparently "obvious" propositions are
    not provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** However, we can add functional extensionality to Coq's core using
    the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False],
    [2+2=5], etc.!

    Unfortunately, there is no simple way of telling whether an axiom
    is safe to add: hard work by highly trained mathematicians is
    often required to establish the consistency of any particular
    combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command.  *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

Print Assumptions functional_extensionality.

(* recursion with acumulation *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version of [rev] is said to be _tail-recursive_, because the
    recursive call to the function is the last operation that needs to
    be performed (i.e., we don't have to execute [++] after the
    recursive call); a decent compiler will generate very efficient
    code in this case.

    Prove that the two definitions are indeed equivalent. *)

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
(* FILL IN HERE *) Admitted.


(* ================================================================= *)
(** ** Propositions vs. Booleans *)

(** We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    For instance, to claim that a number [n] is even, we can say
    either... *)

(** ... that [evenb n] evaluates to [true]... *)
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : even 42.
Proof. unfold even. exists 21. reflexivity. Qed.

(** Of course, it would be pretty strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!  Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Lemma evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Print evenb_S.

(** **** Exercise: 3 stars, standard (evenb_double_conv)  *)
Lemma evenb_double_conv : forall n, exists k,
  n = if evenb n then double k else S (double k).
Proof.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
  intros n. induction n as [| n'].
  - (* n = O *) simpl. exists 0. reflexivity.
  - (* n = S n' *) destruct (evenb n') eqn: Heq.
    + (* evenb n' = true *) rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
      exists n''. rewrite IHn'. reflexivity.
    + (* evenb n' = false *) rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
      exists (n''+1). rewrite IHn'. rewrite double_plus. rewrite double_plus.
      rewrite plus_n_Sm. rewrite <- plus_1_l. rewrite <- plus_n_Sm. rewrite <- (plus_1_l (n'' + n'')).
      rewrite plus_comm. rewrite plus_assoc.  rewrite (plus_comm 1).
      rewrite plus_assoc. reflexivity.
Qed.

(** Now the main theorem: *)
Theorem even_bool_prop : forall n,
  evenb n = true <-> even n.
Proof.
  intros n. split.
  - (* -> *)intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite -> Hk. rewrite H. exists k. reflexivity.
  - (* <- *) intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** In view of this theorem, we say that the boolean computation
    [evenb n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent. *)

Print eqb_refl.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - (* -> *) apply eqb_true.
  - (* <- *) intros H. rewrite -> H. rewrite <- eqb_refl. reflexivity.
Qed.

(** However, even when the boolean and propositional formulations of a
    claim are equivalent from a purely logical perspective, they are
    often not equivalent from the point of view of convenience for
    some specific purpose. *)

(** In the case of even numbers above, when proving the
    backwards direction of [even_bool_prop] (i.e., [evenb_double],
    going from the propositional to the boolean claim), we used a
    simple induction on [k].  On the other hand, the converse (the
    [evenb_double_conv] exercise) required a clever generalization,
    since we can't directly prove [(evenb n = true) -> even n]. *)

(** For these examples, the propositional claims are more useful than
    their boolean counterparts, but this is not always the case.  For
    instance, we cannot test whether a general proposition is true or
    not in a function definition; as a consequence, the following code
    fragment is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects
    an element of [bool] (or some other inductive type with two
    elements).  The reason has to do with the _computational_ nature
    of Coq's core language, which is designed so that every function
    it can express is computable and total.  One reason for this is to
    allow the extraction of executable programs from Coq developments.
    As a consequence, [Prop] in Coq does _not_ have a universal case
    analysis operation telling whether any given proposition is true
    or false, since such an operation would allow us to write
    non-computable functions.

    Beyond the fact that non-computable properties are impossible in
    general to phrase as boolean computations, even many _computable_
    properties are easier to express using [Prop] than [bool], since
    recursive function definitions in Coq are subject to significant
    restrictions.  For instance, the next chapter shows how to define
    the property that a regular expression matches a given string
    using [Prop].  Doing the same with [bool] would amount to writing
    a regular expression matching algorithm, which would be more
    complicated, harder to understand, and harder to reason about than
    a simple (non-algorithmic) definition of this property.

    Conversely, an important side benefit of stating facts using
    booleans is enabling some proof automation through computation
    with Coq terms, a technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : even 1000.


(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is even
    simpler (because we don't have to invent the witness: Coq's
    computation mechanism does it for us!). 
    
    In this case the witness is the nat term with value 500 *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning the value 500 explicitly: *)

Example even_1000'' : even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.


(** Although we haven't gained much in terms of proof-script
    size in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Coq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** Another notable difference is that the negation of a "boolean
    fact" is straightforward to state and prove: simply flip the
    expected boolean result. *)

Example not_even_1001 : evenb 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

(** In contrast, propositional negation can be more difficult
    to work with directly. *)

Example not_even_1001' : ~(even 1001).
Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** Equality provides a complementary example, where it is sometimes
    easier to work in the propositional world. Knowing that
    [n =? m = true] is generally of little direct help in the middle of a
    proof involving [n] and [m]; however, if we convert the statement
    to the equivalent form [n = m], we can rewrite with it. *)

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite -> H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** **** Exercise: 2 stars (logical_connectives)  *)
(** The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - (* -> *) intros H. split.
    + (* b1 = true *) rewrite andb_commutative in H. apply andb_true_elim2 in H. apply H.
    + (* b2 = true *) apply andb_true_elim2 in H. apply H.
  - (* <- *) intros H. inversion H. rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - (* -> *) intros H. destruct H. destruct b1.
    + simpl. left. reflexivity.
    + simpl. right. reflexivity.
  - (* -> *) intros H. destruct H as [H1 | H2].
    + rewrite H1. simpl. reflexivity.
    + rewrite H2. destruct b1.
      { reflexivity. }
      { reflexivity. }
Qed.

(** **** Exercise: 1 star (beq_nat_false_iff)  *)
(** The following theorem is an alternate "negative" formulation of
    [beq_nat_true_iff] that is more convenient in certain
    situations (we'll see examples in later chapters). *)


Theorem eqb_nat_false_iff : forall x y : nat,
  eqb x y = false <-> x <> y.
Proof.
  intros x y. unfold not. split.
  - (* -> *) intros H0 H1. apply eqb_eq in H1. rewrite H1 in H0. inversion H0.
  - (* <- *) intros H. induction x as [| x'].
    + induction y as [| y'].
      { exfalso. apply H. reflexivity. }
      { generalize dependent y'. auto. }
    + induction y as [| y'].
      { generalize dependent x'. auto. }
      { simpl. destruct (eqb x' y') eqn:Heq.
        - exfalso. apply H. apply f_equal. apply eqb_eq. apply Heq.
        - reflexivity. }
Qed.


(** **** Exercise: 3 stars (beq_list)  *)
(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Fixpoint eqb_list {A} (eqb : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [] , [] => true
  | _  , [] => false
  | [] , _  => false
  | h1 :: t1 , h2 :: t2 => if(eqb h1 h2) then eqb_list eqb t1 t2 else false
  end.
  
Lemma beq_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H l1 l2. split.
  - (* -> *) generalize dependent l2. induction l1 as [| h1 l1' IHl1'].
    + induction l2 as [| h2 l2' IHl2'].
      { reflexivity. }
      { simpl. intros H1. inversion H1. }
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. intros H1. inversion H1. }
      { simpl. intros H1. destruct (eqb h1 h2) eqn:Heq.
        + apply H in Heq. rewrite <- Heq.
          assert (l1' = l2' -> h1 :: l1' = h1 :: l2') as H2.
          { intros H3. rewrite H3. reflexivity. } apply H2. apply IHl1'. apply H1.
        + inversion H1. }
  - (* <- *) generalize dependent l2. induction l1 as [| h1 l1' IHl1'].
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. reflexivity. }
      { simpl. intros H1. inversion H1. }
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. intros H1. inversion H1. }
      { simpl. intros H1. destruct (eqb h1 h2) eqn:Heq.
        + apply IHl1'. apply H in Heq. rewrite Heq in H1.
          assert (h1 :: l1' = h1 :: l2' -> l1' = l2') as H2.
          { intros H3. inversion H1. reflexivity. } apply H2. rewrite Heq. apply H1.
        + inversion H1. apply H in H2. rewrite H2 in Heq. symmetry. apply Heq. }
Qed.

(** **** Exercise: 2 stars, recommended (All_forallb)  *)
(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros. split.
  - (* -> *) intros. induction l.
    + simpl. auto.
    + simpl. split.
      { unfold forallb in H. rewrite andb_true_iff in H. apply proj1 in H. assumption. }
      { apply IHl. inversion H. rewrite andb_true_iff in H1. destruct H1 as [H2 H3]. rewrite H2.
        rewrite H3. auto. }
  - (* <- *) intros. induction l.
    + reflexivity.
    + simpl. rewrite andb_true_iff. split.
      { simpl in H. apply proj1 in H. assumption. }
      { simpl in H. apply proj2 in H. apply IHl in H. assumption. }
Qed.







