From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From DiSeL.Heaps
Require Import pred prelude idynamic ordtype finmap pcm unionmap.
From DiSeL.Heaps
Require Import heap coding domain.
From DiSeL.Core
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
From DiSeL.Core
Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL.Core
Require Import InductiveInv StatePredicates.
From DiSeL.Examples
Require Import PaxosProtocol.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section PaxosInductiveInv.

Variable l: Label.

Variable (proposers: seq nid) (acceptors: seq nid).

Definition paxos := PaxosProtocol proposers acceptors l.

(* Take the transitions *)
Notation sts := (snd_trans paxos).
Notation rts := (rcv_trans paxos).

Notation loc z d := (getLocal z d).

Definition role_state (d: dstatelet) (s: StateT) (n: nid): Prop :=
  loc n d = st :-> s.

(*****************************************************)

(* Phase Zero *)
Definition EverythingInit (d : dstatelet) (round : nat): Prop :=
  forall n, n \in (proposers ++ acceptors) -> (
    (exists psal, role_state d (round, PInit psal) n)
    \/ role_state d (round, AInit) n).


(* Phase One *)
Definition Phase1a (d: dstatelet) (round: nat) (n: nid): Prop :=
  (role_state d (round, AInit) n)
  \/ exists psal, (role_state d (round, PInit psal) n)
     \/ (exists sent_to, role_state d (round, PSentPrep psal sent_to) n)
     \/ (exists promises, role_state d (round, PWaitPrepResp promises psal) n).

Definition Phase1b (d: dstatelet) (round: nat) (n: nid): Prop :=
  exists psal, (role_state d (round, APromised psal) n)
    \/ (exists promises, role_state d (round, PWaitPrepResp promises psal) n).

Definition Phase2a (d: dstatelet) (round: nat) (n: nid): Prop :=
  (role_state d (round, PAbort) n)
  \/ exists psal, (role_state d (round, APromised psal) n)
     \/ (exists sent_to, role_state d (round, PSentAccReq sent_to psal) n).

Definition Phase2b (d: dstatelet) (round: nat) (n: nid): Prop :=
  (role_state d (round, PAbort) n)
  \/ exists psal, (role_state d (round, AAccepted psal) n).

(* TODO: Fix the conditions. This Inv currently isn't checking for anything. *)
Definition Inv (d: dstatelet) :=
  exists round,
    EverythingInit d round
    \/ (forall n, n \in (proposers ++ acceptors) ->
         (Phase1a d round n \/ Phase1b d round n
          \/ Phase2a d round n \/ Phase2b d round n)).

(*********************************************************)

Notation Sinv := (@S_inv paxos (fun d _ => Inv d)).
Notation Rinv := (@R_inv paxos (fun d _ => Inv d)).
Notation coh d := (coh paxos d).
Notation PI := proof_irrelevance.

(*************************************************************)
(*                  Send-transitions                         *)
(*************************************************************)

Program Definition s1: Sinv (send_prepare_req_trans proposers acceptors).
Proof.
  admit.
Admitted.

Program Definition s2: Sinv (send_accept_req_trans proposers acceptors).
Proof.
  admit.
Admitted.

Program Definition s3: Sinv (send_promise_resp_trans proposers acceptors).
Proof.
  admit.
Admitted.

Program Definition s4: Sinv (send_nack_resp_trans proposers acceptors).
Proof.
  admit.
Admitted.


(*************************************************************)
(*                  Receive-transitions                      *)
(*************************************************************)

Program Definition r1: Rinv (receive_prepare_req_trans proposers acceptors).
Proof.
  admit.
Admitted.

Program Definition r2: Rinv (receive_accept_req_trans proposers acceptors).
Proof.
  admit.
Admitted.

Program Definition r3: Rinv (receive_promise_resp_trans proposers acceptors).
Proof.
  admit.
Admitted.

Program Definition r4: Rinv (receive_nack_resp_trans proposers acceptors).
Proof.
  admit.
Admitted.


Definition sts' := [:: SI s1; SI s2; SI s3; SI s4].
Definition rts' := [:: RI r1; RI r2; RI r3; RI r4].

Program Definition ii := @ProtocolWithInvariant.II _ _ sts' rts' _ _.

Definition paxos_with_inv := ProtocolWithIndInv ii.

End PaxosInductiveInv.
