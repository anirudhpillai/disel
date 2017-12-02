From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From DiSeL.Heaps
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding domain.
From DiSeL.Core
Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL.Core
Require Import Actions Injection Process Always HoareTriples InferenceRules.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Definition nid := nat.
Definition data := seq nid.

Inductive Proposal :=
| proposal of nat & nat
| nack.

(* Proposer states *)
Inductive RoleState :=
(* Proposer States *)
(* Initialised with a proposal number and random value*)
| PInit of Proposal
(* Sent prepare message to some Acceptors at a current stage *)
| PSentPrep of data & Proposal
(* Received promises/NACKs from Acceptors *)
| PWaitPrepResponse of data & seq Proposal & Proposal
(* Send AcceptRequest *)
| PSentAccReq of data & Proposal
(* Acceptor states *)
| AInit
| APromised of Proposal
| AAccepted of Proposal.

(* Pointer to the state *)
Definition st := ptr_nat 1.

(* Pairing with the current stage of type nat *)
Definition StateT := (nat * RoleState)%type.

(* Proposer nodes *)
Variable proposers : seq nid.
(* Acceptor nodes *)
Variable acceptors : seq nid.

(** ??
Still don't completely understand the coherence, need to read up.
The coherence predicate constraints the local state of each node.
*)
Definition localCoh (n : nid) : Pred heap :=
  [Pred h | valid h /\ exists (s : StateT), h = st :-> s].


(* Involved nodes *)
Definition nodes := proposers ++ acceptors.


Definition prepare_req : nat := 0.
Definition promise_resp : nat := 1.
Definition nack_resp : nat := 2.
Definition accept_req : nat := 3.
Definition accepted_resp : nat := 4.


(** ??
Don't know if or why this is needed
Interaction with the clients 
*)
Definition eval_req : nat := 5.
Definition eval_resp : nat := 6.


Definition ttag := nat.
Definition payload := seq nat.

Definition tags : seq ttag :=
  [:: prepare_req;
     promise_resp;
     nack_resp;
     accept_req;
     accepted_resp;
     eval_req;
     eval_resp].

Definition tagFromAcceptor (t : nat) : bool :=
  (t \in [:: promise_resp; nack_resp; accepted_resp]).


(** ??
Why is this needed? What does tms_count do?
Messages from Acceptor contain a Proposal/Nack
Need to change (y : nat) to (y : Proposal)
*)
Definition msgFromAcceptor (tms : TaggedMessage) (y : nat) : bool :=
    tagFromAcceptor (tag tms) && (tms_cont tms == [:: y]).

Definition tagFromProposer (t : nat) : bool :=
  (t \in [:: prepare_req; accept_req]).

(* ??
Same as above for Acceptor
Messages from Propser contain a proposal
*)
Definition msgFromProposer (tms : TaggedMessage) (y : nat) : Prop :=
  let: body := tms_cont tms in exists data, body = y :: data.


(* ??
This is saying that a proposer can only send a message to an acceptor and vice versa.
Not sure if we need to impose this for Paxos.
*)
Definition cohMsg (ms: msg TaggedMessage) (y : nat) : Prop :=
  if from ms \in proposers
  then to ms \in acceptors /\ msgFromProposer (content ms) y
  else if from ms \in acceptors
       then to ms \in proposers /\ msgFromAcceptor (content ms) y
       else True.

(** ??
A bit lost now. Need to read up about all the uses of coherence.
Is this the coherence that holds over the message soup?
Not sure what's happening here.
*)
Definition soupCoh : Pred soup :=
  [Pred s | valid s /\
            forall m ms, find m s = Some ms -> exists y, cohMsg ms y].

(** ??
What is =i?
*)
Definition paxos_coh d : Prop :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soupCoh ds, dom dl =i nodes,
   valid dl &
   forall n, n \in nodes -> localCoh n (getLocal n d)].

(* Axioms of the coherence predicate *)
Lemma l1 d: paxos_coh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: paxos_coh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: paxos_coh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

(* Wrapping up the coherence predicate *)
Definition PaxosCoh := CohPred (CohPredMixin l1 l2 l3).






