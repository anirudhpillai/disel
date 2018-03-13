From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From DiSeL.Heaps
Require Import pred prelude ordtype finmap pcm unionmap heap coding domain.
From DiSeL.Core
Require Import State Protocols Worlds NetworkSem Rely.
From DiSeL.Core
Require Import HoareTriples InferenceRules While.
From DiSeL.Examples
Require Import PaxosProtocol PaxosProposer PaxosAcceptor.
From DiSeL.Examples
Require PaxosInductiveInv.

Section SimplePaxosApp.

(*

A simple application to run on the shim implementation.

Check for [Run] tags to find the initial state and the code for the
proposers and the acceptors.

*)

Definition l := 0.
(* Proposer nodes *)
Definition p1 := 1.
Definition p2 := 2.

(* Acceptor nodes *)
Definition a1 := 3.
Definition a2 := 4.
Definition a3 := 5.

Definition proposers := [:: p1].
Definition acceptors := [::a1; a2; a3].

(* Necessary coherence facts *)
Fact AcceptorsNonEmpty : acceptors != [::]. Proof. by []. Qed.

(* Proposers *)
Definition proposer p (pf: acceptors != [::]) psal:=
  proposer_round l proposers acceptors p pf psal.

(* Acceptors *)
Program Definition acceptor a :=
  acceptor_round l proposers acceptors a.

(* Initial distributed state *)
Definition st_ptr := PaxosProtocol.States.st.

Definition init_heap_p psal:= st_ptr :-> (0, PInit psal).
Definition init_heap_a := st_ptr :-> (0, AInit).

Definition init_dstate :=
  p1 \\-> init_heap_p [:: 1; 1] \+
  a1 \\-> init_heap_a \+
  a2 \\-> init_heap_a \+
  a3 \\-> init_heap_a.

Lemma valid_init_dstate : valid init_dstate.
Proof.
  admit.
Admitted.

Notation init_dstatelet := (DStatelet init_dstate Unit).

(* [Run] Initial state to run *)
Definition init_state : state := l \\-> init_dstatelet.


(* Final Safety Facts *)
Notation W := (mkWorld (PaxosProposer.paxos l proposers acceptors)).

Lemma hook_complete_unit (c : context) : hook_complete (c, Unit).
Proof. by move=>????; rewrite dom0 inE. Qed.

Lemma hooks_consistent_unit (c : context) : hooks_consistent c Unit.
Proof. by move=>????; rewrite dom0 inE. Qed.

Lemma init_coh : init_state \In Coh W.
Proof. admit. Admitted.

(* [Run] Runnable proposer code *)
Program Definition run_proposer p (AcceptorsNonEmpty: acceptors != [::]) psal:
  DHT [p, _] (
    fun i => network_rely W p init_state i,
    fun _ m => exists (r : nat),
    getLocal p (getStatelet m l) = st :-> (r, PInit psal))
  := Do (with_inv (PaxosInductiveInv.ii _ _ _) (proposer p AcceptorsNonEmpty psal)).
Next Obligation.
  admit.
Admitted.
Check run_proposer.
(* [Run] Runnable acceptor code *)
Program Definition run_acceptor a:
  DHT [a, _] (
    fun i => network_rely W a init_state i,
    fun _ m => exists (r : nat),
    getLocal a (getStatelet m l) = st :-> (r, AInit))
  := Do (with_inv (PaxosInductiveInv.ii _ _ _) (acceptor a)).
Next Obligation.
  admit.
Admitted.

Variables (psal_1 psal_2 : proposal).
Variables (p_1 a_1 a_2 a_3: nat).
(* [Run] Runnable nodes *)
Program Definition run_proposer1 := run_proposer p1 AcceptorsNonEmpty psal_1.
Program Definition run_proposer2 := run_proposer p2 AcceptorsNonEmpty psal_2.
Program Definition run_acceptor1 := run_acceptor a_1.
Program Definition run_acceptor2 := run_acceptor a_2.
Program Definition run_acceptor3 := run_acceptor a_3.

End SimplePaxosApp.

(* [Run] Final programs to run with actual arguments supplied *)

Definition p_runner1 (u : unit) := run_proposer1 [:: 1; 1].
Definition p_runner2 (u : unit) := run_proposer1 [:: 2; 2].

Definition a_runner1 (u : unit) := run_acceptor1 a1.
Definition a_runner2 (u : unit) := run_acceptor2 a2.
Definition a_runner3 (u : unit) := run_acceptor3 a3.
