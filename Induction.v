(** * Induction: Proof by Induction *)

(* ################################################################# *)
(** * Separate Compilation *)

(** Before getting started on this chapter, we need to import
    all of our definitions from the previous chapter: *)

From COC Require Export Basics.

(* ################################################################# *)
(** * Proof by Induction *)

(** We can prove that [0] is a neutral element for [+] on the left
    using just [reflexivity].  But the proof that it is also a neutral
    element on the _right_ ... *)

Theorem plus_n_O_firsttry : 
  forall n:nat,
  n = n + 0.
(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* does nothing *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)

Theorem plust_n_O_secondtry : 
  forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.
Abort.

(** We could use [destruct n'] to get one step further, but,
    since [n] can be arbitrarily large, we'll never get all the there
    if we just go on like this. *)

(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we often need a more powerful reasoning
    principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    _principle of induction over natural numbers_: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same: we begin with the goal of proving
    [P(n)] for all [n] and break it down (by applying the [induction]
    tactic) into two separate subgoals: one where we must show [P(O)]
    and another where we must show [P(n') -> P(S n')].  Here's how
    this works for the theorem at hand: *)

Theorem plus_n_O : 
  forall n:nat, 
  n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *) 
    simpl. 
    rewrite <- IHn'. 
    reflexivity.
Qed.

(** The [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals. Since there are two subgoals, the [as...] clause
    has two parts, separated by [|].

    The assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']). **)

Theorem minus_n_n : 
  forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(** When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed. *)

(** **** Exercise: 2 stars, standard, especially useful (basic_induction) **)

Theorem mult_n_O : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m:nat,
  S (n + m) = n + S (m).
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    intros m.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m:nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - (* n = S n' *)
    rewrite <- plus_n_Sm.
    rewrite <- IHn'.
    simpl.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p:nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (double_plus) 

    Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, 
  double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem evenb_S : forall n:nat,
  evenb(S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    simpl.
    reflexivity.
Qed.

(** Large proofs are often broken into a sequence of theorems, with later 
    proofs referring to earlier theorems.
    But sometimes a proof will require some miscellaneous fact that is too
    trivial and of too little general interest to bother giving it its own 
    top-level name.

    It is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  
    The [assert] tactic. *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    rewrite -> H.
    reflexivity.
Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (0 + n
    = n) as H].)  Note that we surround the proof of this assertion
    with curly braces [{ ... }], both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke [assert] except that, in the context,
    we now have the assumption [H] that [0 + n = n].  That is,
    [assert] generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. *)

(** For example, suppose we want to prove that [(n + m) + (p + q)
    = (m + n) + (p + q)]. The only difference between the two sides of
    the [=] is that the arguments [m] and [n] to the first inner [+]
    are swapped, so it seems we should be able to use the
    commutativity of addition ([plus_comm]) to rewrite one into the
    other.  However, the [rewrite] tactic is not very smart about
    _where_ it applies the rewrite.  There are three uses of [+] here,
    and it turns out that doing [rewrite -> plus_comm] will affect
    only the _outer_ one... *)
Theorem plus_rearrange_firsttry : forall n m p q:nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
Abort.

(** To use [plus_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the _particular_ [m]
    and [n] that we are talking about here), prove this lemma using
    [plus_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q:nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm.
    reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite <- plus_n_Sm.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). { rewrite -> plus_comm. reflexivity. } rewrite -> H.
  rewrite -> plus_assoc. reflexivity.
Qed.

(** Now prove commutativity of multiplication.  You will probably
    want to define and prove a "helper" theorem to be used
    in the proof of this one. Hint: what is [n * (1 + k)]? *)
Lemma mult_n_Sm : forall n m:nat,
  n * (S m) = n + n * m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall n m:nat,
  n * m = m * n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    rewrite -> mult_n_O.
    reflexivity.
  - (* n = S n' *)
    rewrite -> mult_n_Sm.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (more_exercises) 

    a) it can be proved using only simplification and rewriting.
    b) it also requires case analysis [destruct].
    c) it also requires induction. **)

Check leb.

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b:bool,
  andb b false = false.
Proof.
  intros b. destruct b eqn:Eb.
  - (* b = true *)
    simpl.
    reflexivity.
  - (* b = false *)
    simpl.
    reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p:nat,
  n <=? m = true -> 
  (p + n) <=? (p + m) = true.
Proof.
  intros n m p H. induction p as [| p' IHp'].
  - (* p = 0 *)
    simpl.
    rewrite -> H.
    reflexivity.
  - (* p = S p' *)
    simpl.
    rewrite -> IHp'.
    reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 
  1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Theorem all3_spec : forall b1 b2:bool,
    orb (andb b1 b2) (orb (negb b1) (negb b2)) = true.
Proof.
  intros [] [].
  - (* b1 = true, b2 = true *)
    simpl.
    reflexivity.
  - (* b1 = true, b2 = false *)
    simpl.
    reflexivity.
  - (* b1 = false, b2 = true *)
    simpl.
    reflexivity.
  - (* b1 = false, b2 = false *)
    simpl.
    reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p:nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p:nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem eqb_refl : forall n:nat,
  true = (n =? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (binary_commute) 

    Recall the [incr] and [bin_to_nat] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.
    Name your theorem [bin_to_nat_pres_incr] ("pres" for "preserves").

    Before you start working on this exercise, copy the definitions of
    [incr] and [bin_to_nat] from your solution to the [binary]
    exercise here so that this file can be graded on its own.  If you
    want to change your original definitions to make the property
    easier to prove, feel free to do so! 


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
  | Z => B1 Z
  | B0 n' => B1 n'
  | B1 n' => B0 (incr n')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
  | Z => O
  | B0 b' => 2 * (bin_to_nat b')
  | B1 b' => 1 + 2 * (bin_to_nat b')
  end.

Example test_bin_to_nat1 :
  bin_to_nat(incr (B0 (B0 (B1 Z)))) = 5.
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat2 :
  bin_to_nat(B1 Z) = 1.
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat3 :
  bin_to_nat(B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.





