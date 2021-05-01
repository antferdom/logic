(** * Lists: Working with Structured Data *)

From COC Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * Pairs of Numbers *)

(** In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one (as with [nybble], and here): *)

Inductive natprod : Type :=
  | pair (n1 n2:nat).

(** This declaration can be read: "The one and only way to
    construct a pair of numbers is by applying the constructor [pair]
    to two arguments of type [nat]." *)

Check (pair 3 5) : natprod.

(** Here are simple functions for extracting the first and
    second components of a pair. *)

Definition fst (p:natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p:natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)
Compute (snd (pair 3 5)).
(* ===> 5 *)

(** Since pairs will be used heavily in what follows, it is nice
    to be able to write them with the standard mathematical notation
    [(x,y)] instead of [pair x y].  We can tell Coq to allow this with
    a [Notation] declaration. *)

Notation "( x , y )" := (pair x y).

(** The new notation can be used both in expressions and in pattern
    matches. *)

Compute (3,5).
Compute (fst (3,5)).

Definition fst' (p:natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p:natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Compute (fst'(3,5)).
Compute (snd'(3,5)).

Definition swap_pair (p:natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Compute (swap_pair(3,5)).
(* ===> (5, 3) *)

(** Note that pattern-matching on a pair (with parentheses: [(x, y)])
    is not to be confused with the "multiple pattern" syntax (with no
    parentheses: [x, y]) that we have seen previously.  The above
    examples illustrate pattern matching on a pair with elements [x]
    and [y], whereas, for example, the definition of [minus] in
    [Basics] performs pattern matching on the values [n] and [m]:

       Fixpoint minus (n m : nat) : nat :=
         match n, m with
         | O   , _    => O
         | S _ , O    => n
         | S n', S m' => minus n' m'
         end.

    The distinction is minor, but it is worth knowing that they
    are not the same. For instance, the following definitions are
    ill-formed:

        (* Can't match on a pair with multiple patterns: *)
        Definition bad_fst (p : natprod) : nat :=
          match p with
          | x, y => x
          end.

        (* Can't match on multiple values with pair patterns: *)
        Definition bad_minus (n m : nat) : nat :=
          match n, m with
          | (O   , _   ) => O
          | (S _ , O   ) => n
          | (S n', S m') => bad_minus n' m'
          end.
*)

(** Now let's try to prove a few simple facts about pairs.

    If we state properties of pairs in a slightly peculiar way, we can
    sometimes complete their proofs with just reflexivity (and its
    built-in simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  simpl.
  reflexivity. 
Qed.

(** But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** Instead, we need to expose the structure of [p] so that
    [simpl] can perform the pattern match in [fst] and [snd].  We can
    do this with [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. 
  simpl. 
  reflexivity. 
Qed.

(** Notice that, unlike its behavior with [nat]s, where it
    generates two subgoals, [destruct] generates just one subgoal
    here.  That's because [natprod]s can only be constructed in one
    way. *)

(** **** Exercise: 1 star, standard (snd_fst_is_swap)  *)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard, optional (fst_swap_is_snd)  *)

Theorem fst_swap_is_snd : forall (n m : nat),
  fst (swap_pair (n,m)) = snd (n,m).
Proof.
  intros n m.
  simpl.
  reflexivity.
Qed.

(* ################################################################# *)
(** * Lists of Numbers *)

(** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(** For example, here is a three-element list. **)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).  
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1 ; 2; 3].

(** The "[at level 60]" part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

    the [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
    will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than
    [1 + (2 :: [3])].

    (Expressions like "[1 + 2 :: [3]]" can be a little confusing when
    you read them in a [.v] file.  The inner brackets, around 3, indicate
    a list, but the outer brackets, which are invisible in the HTML
    rendering, are there to instruct the "coqdoc" tool that the bracketed
    part should be displayed as Coq code rather than running text.)

    The second and third [Notation] declarations above introduce the
    standard square-bracket notation for lists; the right-hand side of
    the third one illustrates Coq's syntax for declaring n-ary
    notations and translating them to nested sequences of binary
    constructors. *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(** Next let's look at several functions for constructing and
    manipulating lists.  First, the [repeat] function takes a number
    [n] and a [count] and returns a list of length [count] in which
    every element is [n]. *) 

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute repeat 0 5.

(* ----------------------------------------------------------------- *)
(** *** Length *)

(** The [length] function calculates the length of a list. *)

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** [1;2;3]. **)
Compute length mylist3.
(** ===> 3 **)

(* ----------------------------------------------------------------- *)
(** *** Append *)

(** The [app] function concatenates (appends) two lists. *)

Fixpoint app(l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

(** l1 := [1;2;3], l2 := [4,5] **)
Definition l1 := [1;2;3].
Definition l2 := [4;5].
Compute app l1 l2.

(** Since [app] will be used extensively, it is again convenient
    to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity , at level 60).

Example test_app1:    [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. simpl. reflexivity. Qed.
Example test_app2:    nil ++ [4;5] = [4;5].
Proof. simpl. reflexivity. Qed.
Example test_app3:    [1;2;3] ++ nil = [1;2;3].
Proof. simpl. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Head and Tail *)

(** Here are two smaller examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] returns everything but the first element (the
    "tail").  Since the empty list has no first element, we pass
    a default value to be returned in that case.  *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:     hd 0 [1;2;3] = 1.
Proof. simpl. reflexivity. Qed.
Example test_hd2:     hd 0 [] = 0.
Proof. simpl. reflexivity. Qed.
Example test_tl:      tl [1;2;3] = [2;3].
Proof. simpl. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard, especially useful (list_funs) 

    Complete the definitions of [nonzeros], [oddmembers], and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist := 
  match l with
  | nil => nil
  | O :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.


Definition ones_zeros := [0;1;0;1;0;1].
Compute nonzeros ones_zeros.

(** weird and ugly function definition **)
Fixpoint nonzeros' (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if(eqb h 0) then 
                nonzeros' t 
              else h :: nonzeros' t 
              end.

(** simpl. -> compute ? **)
Example test_nonzeros:  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Example test_nonzeros':  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

(** Verify this exhaustive use of pattern matching. **)
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
              | true => h :: oddmembers t
              | false => oddmembers t
             end
  end.

Example test_oddmembers:  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length( oddmembers l).

(** ====> countoddmembers nums = 4 **)
Definition nums := [1;0;3;1;4;5].
Compute countoddmembers nums.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 3 stars, advanced (alternate) 

    Complete the following definition of [alternate], which
    interleaves two lists into one, alternating between elements taken
    from the first list and elements from the second.  See the tests
    below for more specific examples.

    (Note: one natural and elegant way of writing [alternate] will
    fail to satisfy Coq's requirement that all [Fixpoint] definitions
    be "obviously terminating."  If you find yourself in this rut,
    look for a slightly more verbose solution that considers elements
    of both lists at the same time.  One possible solution involves
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, nil => nil
  | nil, _ => l2
  | _, nil => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Bags via Lists *)

(** A [bag] (or [multiset]) is like a set, except that each element
    can appear multiple times rather than just once.  One possible
    representation for a bag of numbers is as a list. *)

Definition bag := natlist.

(** **** Exercise: 3 stars, standard, especially useful (bag_functions) 

    Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | nil => 0
    | h :: t => if(eqb v h) then 1 + (count v t)
                 else count v t 
  end.

Example test_count1 : count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2 : count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  fun l1 l2 => app l1 l2.

Example test_sum1:  count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  app [v] s.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  negb(eqb O (count v s)).

Compute member 1 [0;1].

Example test_member1:             member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2:             member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.
Example test_member3:             member 2 nil = false.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 3 stars, standard, optional (bag_more_functions) 

    Here are some more [bag] functions for you to practice with. *)

(** When [remove_one] is applied to a bag without the number to
    remove, it should return the same bag unchanged.  (This exercise
    is optional, but students following the advanced track will need
    to fill in the definition of [remove_one] for a later
    exercise.) *)

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if(negb (eqb v h)) then h :: remove_one v t
                else t
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2: remove_one 5 [2;1;4;1] = [2;1;4;1].
Proof. simpl. reflexivity. Qed.
Example test_remove_one3: remove_one 5 [2;1;4;5;1;4] = [2;1;4;1;4].
Proof. simpl. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if(negb (eqb v h)) then h :: remove_all v t
                else remove_all v t
  end.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => if(member h s2) then subset t (remove_one h s2) else false 
  end.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* ################################################################# *)
(** * Reasoning About Lists *)

(** As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, just the simplification performed by [reflexivity] is
    enough for this theorem... *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. simpl. reflexivity. Qed.

(** ...because the [[]] is substituted into the
    "scrutinee" (the expression whose value is being "scrutinized" by
    the match) in the definition of [app], allowing the match itself
    to be simplified. *)

(** Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l'*)
    simpl.
    reflexivity.
Qed.

(** Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)

(** Usually, though, interesting theorems about lists require
    induction for their proofs.  We'll see how to do this next. *)

(** (Micro-Sermon: As we get deeper into this material, simply
    _reading_ proof scripts will not get you very far!  It is
    important to step through the details of each one using Coq and
    think about what each step achieves.  Otherwise it is more or less
    guaranteed that the exercises will make no sense when you get to
    them.  'Nuff said.) *)

(* ================================================================= *)
(** ** Induction on Lists *)

(** Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors.  For example, a boolean can be either [true] or
    [false]; a number can be either [O] or [S] applied to another
    number; and a list can be either [nil] or [cons] applied to a
    number and a list.   Moreover, applications of the declared
    constructors to one another are the _only_ possible shapes
    that elements of an inductively defined set can have.

    This last fact directly gives rise to a way of reasoning about
    inductively defined sets: a number is either [O] or else it is [S]
    applied to some _smaller_ number; a list is either [nil] or else
    it is [cons] applied to some number and some _smaller_ list;
    etc. So, if we have in mind some proposition [P] that mentions a
    list [l] and we want to argue that [P] holds for _all_ lists, we
    can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can always be broken down into smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l' IHl1].
  - (* l1 = nil *)
    simpl.
    reflexivity.
  - (* l1 = cons n l' *)
    simpl.
    rewrite -> IHl1.
    reflexivity.
Qed.

(** Notice that, as when doing induction on natural numbers, the
    [as...] clause provided to the [induction] tactic gives a name to
    the induction hypothesis corresponding to the smaller list [l1']
    in the [cons] case.

    Once again, this Coq proof is not especially illuminating as a
    static document -- it is easy to see what's going on if you are
    reading the proof in an interactive Coq session and you can see
    the current goal and context at each point, but this state is not
    visible in the written-down parts of the Coq proof.  So a
    natural-language proof -- one written for human readers -- will
    need to include more explicit signposts; in particular, it will
    help the reader stay oriented if we remind them exactly what the
    induction hypothesis is in the second case. *)

(** For comparison, here is an informal proof of the same theorem. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with

       (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)

     (the induction hypothesis). We must show

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     By the definition of [++], this follows from

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     which is immediate from the induction hypothesis.  [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing
    function [rev]: *)

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Compute rev [1;2;3].

Example test_rev1:      rev [1;2;3] = [3;2;1].
Proof. simpl. reflexivity. Qed.
Example test_rev2:      rev nil = nil.
Proof. simpl. reflexivity. Qed.

(** For something a bit more challenging than the proofs
    we've seen so far, let's prove that reversing a list does not
    change its length.  Our first attempt gets stuck in the successor
    case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress at the point where we got
    stuck and state it as a separate lemma. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l' IHl1'].
  - (* l1 = nil *)
    simpl.
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'.
    rewrite plus_comm.
    simpl.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** [Search] *)

(** We've seen that proofs can make use of other theorems we've
    already proved, e.g., using [rewrite].  But in order to refer to a
    theorem, we need to know its name!  Indeed, it is often hard even
    to remember what theorems have been proven, much less what they
    are called.

    Coq's [Search] command is quite helpful with this.  Let's say
    you've forgotten the name of a theorem about [rev].  The command
    [Search rev] will cause Coq to display a list of all theorems
    involving [rev]. *)

Search rev.

(** Or say you've forgotten the name of the theorem showing that plus
    is commutative.  You can use a pattern to search for all theorems
    involving the equality of two additions. *)

Search (_ + _ = _ + _).

(** You'll see a lot of results there, nearly all of them from the
    standard library.  To restrict the results, you can search inside
    a particular module: *)

Search (_ + _ = _ + _) inside Induction.

(** You can also make the search more precise by using variables in 
  the search pattern instead of wildcards: **)

Search (?x + ?y = ?y + ?x).

(** The question mark in front of the variable is needed to indicate
    that it is a variable in the search pattern, rather than a
    variable that is expected to be in scope currently. *)

(** Keep [Search] in mind as you do the following exercises and
    throughout the rest of the book; it can save you a lot of time! *)

(* ================================================================= *)
(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars, standard (list_exercises) 

    More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Search ((_ ++ _) = _ ++ _ ).

Theorem rev_app_assoc : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l' IHl1'].
  - (* l1 = nil *)
    simpl.
    rewrite -> app_nil_r.
    reflexivity.
  - (* l1 = cons n l' *)
    simpl.
    rewrite -> IHl1'.
    rewrite -> app_assoc. 
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = n l' *)
    simpl.
    rewrite -> rev_app_assoc.
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Search nonzeros.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++(l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2.
Proof.
  intros l1 l2. induction l1 as [| n l' IHl1'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl. { induction n.
    - (* n = O *)
      rewrite -> IHl1'.
      reflexivity.
    - (* n = S n' *)
      simpl.
      rewrite -> IHl1'.
      reflexivity.
   }
Qed.

(** **** Exercise: 2 stars, standard (eqblist) 

    Fill in the definition of [eqblist], which compares
    lists of numbers for equality.  Prove that [eqblist l l]
    yields [true] for every list [l]. *)
Search eqb inside Basics.

Fixpoint eqblist  (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | _, nil => false
  | nil, _ => false
  | h1 :: t1, h2 :: t2 => if(eqb h1 h2) then eqblist t1 t2
                          else false 
  end.

Example test_eqblist1 : eqblist nil nil = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Search nat inside Induction.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl.
    rewrite <- IHl'.
    rewrite <- eqb_refl.
    reflexivity.
Qed.

(** **** Exercise: 4 stars, advanced (rev_injective) 

    Prove that the [rev] function is injective. There is a hard way
    and an easy way to do this. *)

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive. 
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(* ################################################################# *)
(** * Options *)

(** Suppose we want to write a function that returns the [n]th
    element of some list.  If we give it type [nat -> natlist -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

(** This solution is not so good: If [nth_bad] returns [42], we
    can't tell whether that value actually appears on the input
    without further processing. A better alternative is to change the
    return type of [nth_bad] to include an error value as a possible
    outcome. We call this type [natoption]. *)

Inductive natoption : Type :=
  | Some (n:nat)
  | None.

(** We can then change the above definition of [nth_bad] to
    return [None] when the list is too short and [Some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. As we see here, constructors of inductive definitions can
    be capitalized. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | 0 => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(**  This example is also an opportunity to introduce one more small
    feature of Coq's programming language: conditional
    expressions... *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? 0 then Some a
               else nth_error' l' (pred n)
  end.

(* ################################################################# *)
(* Highly important fact of the core nature of this language *)

(** Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the [bool] type
    is not built in, Coq actually supports conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)

(** The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)

Definition hd_error (l:natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. simpl. reflexivity. Qed.

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

(** First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)

Inductive id : Type :=
  | Id (n:nat).

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us more flexibility. *)

(** We'll also need an equality test for [id]s: *)

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(* Compute eqb_id Id(S 1) Id(S 1). missunderstanding of constructors *)

Theorem eqb_id_refl : forall x, 
  true = eqb_id x x.
Proof.
  intros x. 
  destruct x as [n]. 
  simpl. 
  rewrite <- eqb_refl. 
  reflexivity.
Qed.


(** Now we define the type of partial maps: *)

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(** This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)

(** The [update] function overrides the entry for a given key in a
    partial map by shadowing it with a new one (or simply adds a new
    entry if the given key is not already present). *)

Definition update (d : partial_map)
                  (key : id) (value : nat)
                  : partial_map :=
  record key value d.

(** Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(** **** Exercise: 1 star, standard (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d k v. 
  simpl. 
  rewrite <- eqb_id_refl. 
  reflexivity.
Qed.

End PartialMap.











