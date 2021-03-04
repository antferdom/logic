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





























