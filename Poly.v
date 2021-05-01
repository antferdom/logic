(** * Poly: Polymorphism and Higher-Order Functions *)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From COC Require Export Lists.

(* ################################################################# *)
(** * Polymorphism *)

(** In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).  We begin with polymorphism. *)

(* ================================================================= *)
(** ** Polymorphic Lists *)

(** For the last chapter, we've been working with lists
    containing just numbers.  Obviously, interesting programs also
    need to be able to manipulate lists with elements from other
    types -- lists of booleans, lists of lists, etc.  We _could_ just
    define a new inductive datatype for each of these, for
    example... *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(** ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.) and all
    their properties ([rev_length], [app_assoc], etc.) for each
    new datatype definition. *)

(** To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(** This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the function header on the first line,
    and the occurrences of [natlist] in the types of the constructors
    have been replaced by [list X].

    What sort of thing is [list] itself?  A good way to think about it
    is that the definition of [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it more concisely, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is the [Inductive]ly defined set of lists whose
    elements are of type [X]. *)

Check list : Type -> Type.

(** The parameter [X] in the definition of [list] automatically
    becomes a parameter to the constructors [nil] and [cons] -- that
    is, [nil] and [cons] are now polymorphic constructors; when we use
    them, we must now provide a first argument that is the type of the
    list they are building. For example, [nil nat] constructs the
    empty list of type [nat]. *)

Check (nil nat) : list nat.

(** Similarly, [cons nat] adds an element of type [nat] to a list of
    type [list nat]. Here is an example of forming a list containing
    just the natural number 3. *)
Check (cons nat 3 (nil nat)) : list nat.

(** What might the type of [nil] be? We can read off the type
    [list X] from the definition, but this omits the binding for [X]
    which is the parameter to [list]. [Type -> list X] does not
    explain the meaning of [X]. [(X : Type) -> list X] comes
    closer. Coq's notation for this situation is [forall X : Type,
    list X]. *)

Check nil : forall X : Type, list X.

(** Similarly, the type of [cons] from the definition looks like
    [X -> list X -> list X], but using this convention to explain the
    meaning of [X] results in the type [forall X, X -> list X -> list
    X]. *)

Check cons : forall X : Type, X -> list X -> list X.

(** Having to supply a type argument for every single use of a
    list constructor would be rather burdensome; we will soon see ways
    of reducing this annotation burden. *)

Check (cons nat 2 (cons nat 1 (nil nat))) : list nat.

(** We can now go back and make polymorphic versions of all the
    list-processing functions that we wrote before.  Here is [repeat],
    for example: *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeate1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. simpl. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 2 stars, standard (mumble_grumble) 

    Consider the following two inductively defined types. *)

Module MumbleGrumble.

(** 
  Inductive mumble : Type :=
    | a : mumble
    | b : mumble -> nat -> mumble
    | c : mumble.

  Inductive grumble (X:Type) : Type :=
    | d : mumble -> grumble X
    | e : X -> grumble X. **)

  Inductive mumble : Type :=
    | a
    | b (x : mumble) (y : nat)
    | c.

  Inductive grumble (X:Type) : Type :=
    | d (m : mumble)
    | e (x : X).

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?  (Add YES or NO to each line.)
      - [d (b a 5)] NO
      - [d mumble (b a 5)] YES
      - [d bool (b a 5)] YES
      - [e bool true] YES
      - [e mumble (b c 0)] YES
      - [e bool (b c 0)] NO
      - [c]  NO*) 
(* FILL IN HERE *)

(** Check d (b a 5). **)
(** Check e bool (b c 0). -> mumble, but expected bool **)
Check d bool (b a 5).
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Check c.

End MumbleGrumble.

(* Do not modify the following line: *)
Definition manual_grade_for_mumble_grumble : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments.  Will Coq still
    accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** Indeed it will.  Let's see what type Coq has assigned to [repeat']: *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** It has exactly the same type as [repeat].  Coq was able to
    use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used.  For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations can still be quite useful as documentation and sanity
    checks, so we will continue to use them much of the time. *)

(* ----------------------------------------------------------------- *)
(** *** Type Argument Synthesis *)

(** To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the [repeat] function above must
    pass along the type [X].  But since the second argument to
    [repeat] is an element of [X], it seems entirely obvious that the
    first argument can only be [X] -- why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write a "hole" [_], which can be
    read as "Please try to figure out for yourself what belongs here."
    More precisely, when Coq encounters a [_], it will attempt to
    _unify_ all locally available information -- the type of the
    function being applied, the types of the other arguments, and the
    type expected by the context in which the application appears --
    to determine what concrete type should replace the [_].

    This may sound similar to type annotation inference -- and, indeed,
    the two procedures rely on the same underlying mechanisms.  Instead
    of simply omitting the types of some arguments to a function, like

      repeat' X x count : list X :=

    we can also replace the types with holes

      repeat' (X : _) (x : _) (count : _) : list X :=

    to tell Coq to attempt to infer the missing information.

    Using holes, the [repeat] function can be written like this: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers [1], [2], and [3].  Instead of
    this... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use holes to write this: *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** Implicit Arguments *)

(** In fact, we can go further and even avoid writing [_]'s in most
    cases by telling Coq _always_ to infer the type argument(s) of a
    given function.

    The [Arguments] directive specifies the name of the function (or
    constructor) and then lists its argument names, with curly braces
    around any arguments to be treated as implicit.  (If some
    arguments of a definition don't have a name, as is often the case
    for constructors, they can be marked with a wildcard pattern
    [_].) *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** Now, we don't have to supply type arguments at all: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces instead of parens.  For example: *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** (Note that we didn't even have to provide a type argument to the
    recursive call to [repeat'''].  Indeed, it would be invalid to
    provide one, because Coq is not expecting it.)

    We will use the latter style whenever possible, but we will
    continue to use explicit [Argument] declarations for [Inductive]
    constructors.  The reason for this is that marking the parameter
    of an inductive type as implicit causes it to become implicit for
    the type itself, not just for its constructors.  For instance,
    consider the following alternative definition of the [list]
    type: *)

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

(** Because [X] is declared as implicit for the _entire_ inductive
    definition including [list'] itself, we now have to write just
    [list'] whether we are talking about lists of numbers or booleans
    or anything else, rather than [list' nat] or [list' bool] or
    whatever; this is a step too far. *)

(** Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

(** One small problem with declaring arguments [Implicit] is
    that, once in a while, Coq does not have enough local information
    to determine a type argument; in such cases, we need to tell Coq
    that we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)

Fail Definition mynil := nil.

(** (The [Fail] qualifier that appears before [Definition] can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of [nil]): *)

Definition mynil : list nat := nil.

(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1;2;3].
Print list123'''.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard, optional (poly_exercises) 

    Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - (* l = nil *)
  simpl.
  reflexivity.
  - (* l = cons n l' *)
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| h l' IHl'].
  - (* l = nil *)
  simpl.
  reflexivity.
  - (* l = cons h l' *)
  simpl.
  rewrite <- IHl'.
  reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [| n l' IHl'].
  - (* l1 = nil *)
  simpl.
  reflexivity.
  - (* l1 = n l' *)
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (more_poly_exercises) 

    Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| n l' IHl'].
  - (* l1 = nil *)
  simpl.
  rewrite -> app_nil_r.
  reflexivity.
  - (* l1 = cons n l' *)
  simpl.
  rewrite -> IHl'.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - (* l = nil *)
  simpl.
  reflexivity.
  - (* l = cons n l' *)
  simpl.
  rewrite -> rev_app_distr.
  rewrite -> IHl'.
  simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Polymorphic Pairs *)

(** Following the same pattern, the definition for pairs of
    numbers that we gave in the last chapter can be generalized to
    _polymorphic pairs_, often called _products_: *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

(** As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)

Notation "( x , y )" := (pair x y).

(** We can also use the [Notation] mechanism to define the standard
    notation for product _types_: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types, not when parsing
    expressions.  This avoids a clash with the multiplication
    symbol.) *)

(** It is easy at first to get [(x,y)] and [X*Y] confused.
    Remember that [(x,y)] is a _value_ built from two other values,
    while [X*Y] is a _type_ built from two other types.  If [x] has
    type [X] and [y] has type [Y], then [(x,y)] has type [X*Y]. *)

(** The first and second projection functions now look pretty
    much as they would in any functional programming language. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** The following function takes two lists and combines them
    into a list of pairs.  In other functional languages, it is often
    called [zip]; we call it [combine] for consistency with Coq's
    standard library. *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
          : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** Exercise: 1 star, standard, optional (combine_checks) 

    Try answering the following questions on paper and
    checking your answers in Coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does

        Compute (combine [1;2] [false;false;true;true]).

      print? **)

Check @combine.
Compute (combine [1;2] [false;false;true;true]).


Definition app_list_pair {X Y : Type} (lp1 : (list X) * (list Y)) (lp2 : (list X) * (list Y)) 
        : (list X) * (list Y) :=
  (app (fst lp1) (fst lp2), app (snd lp1) (snd lp2)).


(** **** Exercise: 2 stars, standard, especially useful (split) 

    The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
          : (list X)*(list Y) :=
  match l with
  | [] => ([], [])
  | (h1, h2) :: p => app_list_pair ([h1], [h2]) (split p)
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.



