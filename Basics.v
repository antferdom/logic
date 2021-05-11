Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

(** Coq can record what it's _expected_ the result to be in the form of a _example_ *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** This declaration does two things: 
    . It makes an assertion (that the second weekday after [saturday] is [tuesday]
    . It gives the assertion a name that can be used to refer to it later.
Having made the assertion, it can be verified it like this: *)

Proof. simpl. reflexivity.  Qed.

From Coq Require Export String.

(* ================================================================= *)
(** ** Booleans *)

(** In a similar way, the standard type [bool] of
    booleans can be defined, whose members are [true] and [false]. *)

Inductive bool : Type :=
  | true
  | false.
(** Functions over booleans can be defined in the same way as
    above: *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
(** (Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans, together with a
    multitude of useful functions and lemmas.  Whenever possible,
    we'll name our own definitions and theorems so that they exactly
    coincide with the ones in the standard library.) *)
(** The last two of these illustrate Coq's syntax for
    multi-argument function definitions.  The corresponding
    multi-argument application syntax is illustrated by the following
    "unit tests," which constitute a complete specification -- 
    truth table -- for the [orb] function: *)
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.
(** It can be introduced some familiar infix syntax for the
    boolean operations which have been just defined. The [Notation] command
    defines a new symbolic notation for an existing definition. *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** _A note on notation_: In [.v] files, square brackets
    are used to delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the HTML version of the
    files, these pieces of text appear in a [different font]. *)

(** **** Exercise: 1 star, standard (nandb) 

    The command [Admitted] can be used as a placeholder for an
    incomplete proof.  We use it in exercises to indicate the parts
    that we're leaving for you -- i.e., your job is to replace
    [Admitted]s with real proofs.

    Remove "[Admitted.]" and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (I.e., fill in each proof, following the
    model of the [orb] tests above, and make sure Coq accepts it.) The
    function should return [true] if either or both of its inputs are
    [false]. *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb(andb b1 b2).
Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 1 star, standard (andb3) 

    This function should return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.
Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* ================================================================= *)
(** ** Types *)

(** Every expression in Coq has a type, describing what sort of
    thing it computes. The [Check] command asks Coq to print the type
    of an expression. *)

Check true.
(* ===> true : bool *)

(** If the expression after [Check] is followed by a colon and a type,
    Coq will verify that the type of the expression matches the given
    type and halt with an error if not. *)

Check true 
    : bool.
Check (negb true) : bool.

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb
    : bool -> bool.

(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, each of type [bool], this function
    produces an output of type [bool]." *)



(* ================================================================= *)
(** ** New Types from Old *)

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements, called _constructors_.  Here is a more interesting type
    definition, where one of the constructors takes an argument: *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p:rgb).

(** Let's look at this in a little more detail.

    Every inductively defined type ([day], [bool], [rgb], [color],
    etc.) describes a set of _constructor expressions_ built from
    _constructors_.

    - We start with an infinite set of _constructors_. E.g., [red],
      [primary], [true], [false], [monday], etc. are constructors.

    - _Constructor expressions_ are formed by applying a constructor
      to zero or more other constructors or constructor expressions.
      E.g.,
         - [red]
         - [true]
         - [primary]
         - [primary red]
         - [red primary]
         - [red true]
         - [primary (primary primary)]
         - etc.

    - An [Inductive] definition carves out a subset of the whole space
      of constructor expressions and gives it a name, like [bool],
      [rgb], or [color]. *)

(** In particular, the definitions of [rgb] and [color] say
    which constructor expressions belong to the sets [rgb] and
    [color]:

    - [red], [green], and [blue] belong to the set [rgb];
    - [black] and [white] belong to the set [color];
    - if [p] is a constructor expression belonging to the set [rgb],
      then [primary p] (pronounced "the constructor [primary] applied
      to the argument [p]") is a constructor expression belonging to
      the set [color]; and
    - constructor expressions formed in these ways are the _only_ ones
      belonging to the sets [rgb] and [color]. *)

(** We can define functions on colors using pattern matching just as
    we did for [day] and [bool]. *)

Definition monochrome (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Example test_monochrome: (monochrome black) = true.
Proof. simpl. reflexivity. Qed.


(** Since the [primary] constructor takes an argument, a pattern
    matching [primary] should include either a variable (as above --
    note that we can choose its name freely) or a constant of
    appropriate type (as below). *)

Definition isRed (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(** The pattern "[primary _]" here is shorthand for "the constructor
    [primary] applied to any [rgb] constructor except [red]."  (The
    wildcard pattern [_] has the same effect as the dummy pattern
    variable [p] in the definition of [monochrome].) *)

(* ================================================================= *)
(** ** Modules *)

(** Coq provides a _module system_ to aid in organizing large
    developments.  We won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to limit the scope of definitions, so that we are free to
    reuse names. *)

Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

(* ================================================================= *)
(** ** Tuples *)

Module TuplePlayground.

(** A single constructor with multiple parameters can be used
    to create a tuple type. As an example,consider representing
    the four bits in a nybble (half a byte). We first define
    a datatype [bit] that resembles [bool] (using the constructors
    [B0] and [B1] for the two possible bit values)
    and then define the datatype [nybble], which is essentially 
    a tuple of four bits. *)

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0) : nybble.

(** The [bits] constructor acts as a wrapper for its contents.
    Unwrapping can be done by pattern-matching, as in the [all_zero]
    function which tests a nybble to see if all its bits are [B0].
    We use underscore (_) as a _wildcard pattern_ to avoid inventing
    variable names that will not be used. *)

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

End TuplePlayground.

(* ================================================================= *)
(** ** Numbers *)

(** We put this section in a module so that the following definition of
    natural numbers does not interfere with the one from the
    standard library.  In the rest of the book, the standard library's
    natural numbers will be used. *)

(** Finite types : "enumerated types" *)

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n:nat).

End NatPlayground.

Check (S (S (S (S O)))).
(* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)

Check S : nat -> nat.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).
(* ===> 5 : nat *)

(** The steps of simplification that Coq performs can be
    visualized as follows: *)

(*      [plus 3 2]
   i.e. [plus (S (S (S O))) (S (S O))]
    ==> [S (plus (S (S O)) (S (S O)))]
          by the second clause of the [match]
    ==> [S (S (plus (S O) (S (S O))))]
          by the second clause of the [match]
    ==> [S (S (S (plus O (S (S O)))))]
          by the second clause of the [match]
    ==> [S (S (S (S (S O))))]
          by the first clause of the [match]
   i.e. [5]  *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(** You can match two expressions at once by putting a comma
    between them: *)

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end. 

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Example test_exp1: (exp 2 4) = 16.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 1 star, standard (factorial) 

    Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => n*factorial(n')
  end.

Example test_factorial1: factorial 3 = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: factorial 5 = 10*12.
Proof. simpl. reflexivity. Qed.
Example test_factorial3: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(** Again, we can make numerical expressions easier to read and write
    by introducing notations for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1) : nat.

(** Here is a function [eqb], which tests natural numbers for
    [eq]uality, yielding a [b]oolean.  Note the use of nested
    [match]es (we could also have used a simultaneous match, as we did
    in [minus].) *)

Fixpoint eqb (n m:nat) : bool :=
  match n, m with
  | O, O => true
  | O, S m' => false
  | S n', O => false
  | S n', S m'=> eqb n' m'
  end.

Example test_eqb1: (eqb 1 1) = true.
Proof. simpl. reflexivity. Qed.
Example test_eqb2: (eqb 0 1) = false.
Proof. simpl. reflexivity. Qed.

(** Similarly, the [leb] function tests whether its first argument is
    less than or equal to its second argument, yielding a boolean. *)

Fixpoint leb (n m:nat) : bool :=
  match n, m with
  | O, O => true
  | O, _ => true
  | _, O => false
  | S n', S m' => leb n' m'
  end.

Example test_leb1: (leb 0 1) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 0 0) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3:                leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb4:                leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

(** We'll be using these (especially [eqb]) a lot, so let's give
    them infix notations. *)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb5: 1 <=? 0 = false.
Proof. simpl. reflexivity. Qed.

(** We now have two symbols that look like equality: [=] and
    [=?].  We'll have much more to say about the differences and
    similarities between them later. For now, the main thing to notice
    is that [x = y] is a logical _claim_ -- a "proposition" -- that we
    can try to prove, while [x =? y] is an _expression_ whose
    value (either [true] or [false]) we can compute. *)

(** **** Exercise: 1 star, standard (ltb) 

    The [ltb] function tests natural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined
    function.  (It can be done with just one previously defined
    function, but you can use two if you want.) *)

Definition ltb (n m:nat) : bool :=
  andb (leb n m) (negb (eqb n m)).

Example test_ltb1: ltb 0 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: ltb 1 1 = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: ltb 1 0 = false.
Proof. simpl. reflexivity. Qed.

(* ################################################################# *)
(** * Proof by Simplification *)

Theorem plus_0_n: forall n:nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(** [reflexivity] can perform some simplification automatically when
    checking that two sides are equal. 
    [simpl] visualizes the intermediate state after simplification but 
    before finishing the proof. *)

(* Shorter proof of the previous theorem *)
Theorem plus_O_n': forall n:nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** [reflexivity] does somewhat _more_ simplification than [simpl] does 
    if [reflexivity] succeeds, the whole goal is finished and we don't need
    to look at whatever expanded expressions [reflexivity] has created
    by all this simplification and unfolding.
    By contrast, [simpl] is used in situations where we may have to read
    and understand the new goal that it creates, so we would not want it blindly

    expanding definitions and leaving the goal in a messy state.
    First, we've used the keyword [Theorem] instead of [Example].
    This difference is mostly a matter of style; the keywords
    [Example] and [Theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean pretty much the same thing to Coq.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions. Note that we could have used
    another identifier instead of [n] in the [intros] clause, (though
    of course this might be confusing to human readers of the proof):*)

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

(** The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.
    A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    many more in future chapters. *)

(** Other similar theorems can be proved with the same pattern. *)

Theorem plus_1_1 : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_O_1 : forall n:nat, 0*n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(** It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [reflexivity] to see the simplifications that Coq performs
    on the terms before checking that they are equal. *)

(* ################################################################# *)
(** * Proof by Rewriting *)

(** The following theorem is a bit more interesting than the
    ones we've seen: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when
    [n = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  simpl.
  reflexivity.
Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.) *)

(** **** Exercise: 1 star, standard (plus_id_exercise) 

    Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m o:nat,
  n = m -> 
  m = o -> 
  n + m = m + o.

Proof.
  (* move terms into the context: *)
  intros n m o.
  (* move both hypothesis into the context: *)
  intros H1 H2.
  (* rewrite the goal using both hypothesis: *)
  rewrite -> H1.
  rewrite <- H2.
  simpl.
  reflexivity.
Qed.

Check plus_O_n.
(* ===> forall n : nat, 0 + n = n*)
Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

Theorem mult_n_0_m_0 : forall n m:nat,
  (n * 0) + (m * 0) = 0.
Proof.
  intros n m.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (mult_n_1) 

    Use those two lemmas about multiplication that we just checked to
    prove the following theorem.  Hint: recall that [1] is [S O]. *)
Theorem mult_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  Admitted.

Theorem mult_0_plus : forall n m:nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  
Qed.

(** **** Exercise: 2 stars (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m. 
  intros H. 
  rewrite -> plus_1_1. 
  rewrite <- H. 
  reflexivity.
Qed.

(* ################################################################# *)
(** * Proof by Case Analysis *)

(** Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck.  (We then
    use the [Abort] command to give up on it for the moment.)*)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

(** The reason for this is that the definitions of both [eqb]
    and [+] begin by performing a [match] on their first argument.
    But here, the first argument to [+] is the unknown number [n] and
    the argument to [eqb] is the compound expression [n + 1]; neither
    can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [(n + 1) =? 0] and check that it is, indeed, [false].  And if
    [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] represents, we can calculate that, at least,
    it will begin with one [S], and this is enough to calculate that,
    again, [(n + 1) =? 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n:nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem.

    The annotation "[as [| n']]" is called an _intro pattern_.  It
    tells Coq what variable names to introduce in each subgoal.  In
    general, what goes between the square brackets is a _list of
    lists_ of names, separated by [|].  
    In this case, the first component is empty, since the [O] constructor 
    is nullary (it doesn't have any arguments).  
    The second component gives a single name, [n'], since [S] is a unary constructor.

    In each subgoal, Coq remembers the assumption about [n] that is
    relevant for this subgoal -- either [n = 0] or [n = S n'] for some
    n'.  The [eqn:E] annotation tells [destruct] to give the name [E]
    to this equation.  Leaving off the [eqn:E] annotation causes Coq
    to elide these assumptions in the subgoals.  This slightly
    streamlines proofs where the assumptions are not explicitly used,
    but it is better practice to keep them for the sake of
    documentation, as they can help keep you oriented when working
    with the subgoals.

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to the two
    generated subgoals.  The part of the proof script that comes after
    a bullet is the entire proof for the corresponding subgoal.  In
    this example, each of the subgoals is easily proved by a single
    use of [reflexivity], which itself performs some simplification --
    e.g., the second one simplifies [(S n' + 1) =? 0] to [false] by
    first rewriting [(S n' + 1)] to [S (n' + 1)], then unfolding
    [eqb], and then simplifying the [match].

    Marking cases with bullets is optional: if bullets are not
    present, Coq simply asks you to prove each subgoal in sequence,
    one at a time. But it is a good idea to use bullets.  For one
    thing, they make the structure of a proof apparent, improving
    readability. Also, bullets instruct Coq to ensure that a subgoal
    is complete before trying to verify the next one, preventing
    proofs for different subgoals from getting mixed up. These issues
    become especially important in large developments, where fragile
    proofs lead to long debugging sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- e.g., where lines should be broken and how
    sections of the proof should be indented to indicate their nested
    structure.  However, if the places where multiple subgoals are
    generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on a single line.  Good style lies
    somewhere in the middle.  One reasonable guideline is to limit
    yourself to 80-character lines.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)

Theorem negb_involutive : forall b:bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  In fact, we can omit
    the [as] clause from _any_ [destruct] and Coq will fill in
    variable names automatically.  This is generally considered bad
    style, since Coq often makes confusing choices of names when left
    to its own devices.

    It is sometimes useful to invoke [destruct] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example: *)

Theorem andb_commutative : forall b1 b2:bool,
  andb b1 b2 = andb b2 b1.
Proof.
  intros b1 b2. destruct b1 eqn:Eb1.
  - destruct b2 eqn:Eb2.
    + reflexivity.
    + reflexivity.
  - destruct b2 eqn:Eb2.
    + reflexivity.
    + reflexivity.
Qed.

(** Each pair of calls to [reflexivity] corresponds to the
    subgoals that were generated after the execution of the [destruct b2]
    line right above it. *)

(** Besides [-] and [+], we can use [*] (asterisk) or any repetition
    of a bullet symbol (e.g. [--] or [***]) as a bullet.
    We can also enclose sub-proofs in curly braces: *)

Theorem andb_commutative' : forall b1 b2,
  b1 && b2 = b2 && b1.
Proof.
  intros b1 b2. destruct b1 eqn:Eb1.
  { destruct b2 eqn:Eb2.
    { reflexivity. }
    { reflexivity. } }
  { destruct b2 eqn:Eb2.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange : forall b1 b2 b3:bool,
  andb (andb b1 b2) b3 = andb b1 (andb b2 b3).
Proof.
  intros b1 b2 b3. destruct b1 eqn:Eb1.
  - destruct b2 eqn:Eb2.
    { destruct b3 eqn:Eb3.
      - reflexivity. 
      - reflexivity. 
    }
    { destruct b3 eqn:Eb3.
      - reflexivity. 
      - reflexivity. 
    }
  - destruct b2 eqn:Eb2.
    { destruct b3 eqn:Eb3.
      - reflexivity.
      - reflexivity.
    }
    { destruct b3 eqn:Eb3.
      - reflexivity.
      - reflexivity.
    }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
  - reflexivity.
  - destruct b.
    * simpl in H. discriminate.
    * simpl in H. discriminate.
Qed.

(** If there are no constructor arguments that need names, we can just
    write [[]] to get the case analysis. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_neq_plus_1 : forall n:nat,
  0 =? (n + 1) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


(* ================================================================= *)
(** ** More on Notation (Optional) *)

(** (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times: *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(** For each notation symbol in Coq, we can specify its _precedence
    level_ and its _associativity_.  The precedence level [n] is
    specified by writing [at level n]; this helps Coq parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for [+] and
    [*] say that the expression [1+2*3*4] is shorthand for
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and
    _left_, _right_, or _no_ associativity.  We will see more examples
    of this later, e.g., in the [Lists]
    chapter.

    Each notation symbol is also associated with a _notation scope_.
    Coq tries to guess what scope is meant from context, so when it
    sees [S(O*O)] it guesses [nat_scope], but when it sees the product
    type [bool*bool] (which we'll see in later chapters) it guesses
    [type_scope].  Occasionally, it is necessary to help it out with
    percent-notation by writing [(x*y)%nat], and sometimes in what Coq
    prints it will use [%nat] to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation ([3], [4], [5], [42],
    etc.), so you may sometimes see [0%nat], which means [O] (the
    natural number [0] that we're using in this chapter), or [0%Z],
    which means the integer zero (which comes from a different part of
    the standard library).

    Pro tip: Coq's notation mechanism is not especially powerful.
    Don't expect too much from it. *)

(* ================================================================= *)
(** ** Fixpoints and Structural Recursion (Optional) *)

(** Here is a copy of the definition of addition: *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(** When Coq checks this definition, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is "decreasing."

    This requirement is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. *)

(** **** Exercise: 1 star, standard (identity_fn_applied_twice) 

    Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x. 
  rewrite -> x. 
  reflexivity.
Qed.

(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b. 
  rewrite -> x. 
  rewrite -> x. 
  rewrite -> negb_involutive. 
  reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (andb_eq_orb) 

    Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
Qed.

Print nat.

(** **** Exercise: 3 stars, standard (binary) 

    We can generalize our unary representation of natural numbers to
    the more efficient binary representation by treating a binary
    number as a sequence of constructors [B0] and [B1] (representing 0s
    and 1s), terminated by a [Z]. For comparison, in the unary
    representation, a number is a sequence of [S] constructors terminated
    by an [O].

    For example:

        decimal            binary                           unary
           0                       Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

    Note that the low-order bit is on the left and the high-order bit
    is on the right -- the opposite of the way binary numbers are
    usually written.  This choice makes them easier to manipulate. *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (n:bin) : bin :=
  match n with
  | Z => B1 n
  | B0 n'=> B1 n'
  | B1 n' => B0 (incr n')
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.




























