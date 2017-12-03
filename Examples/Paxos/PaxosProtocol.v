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

Definition proposal := (nat * nat)%type.
(* Promise -> seq (node * promise/nack * accepted_proposal) *)
Definition promises := seq (nid * bool * proposal).

(* States of the nodes *)
Inductive RoleState :=
(* Proposer States *)
(* Initialised with a proposal (p_no * p_val) *)
| PInit of proposal
(* Sent prepare message to some Acceptors at a current stage *)
(* seq nid holds nodes which were sent the message *)
| PSentPrep of data & seq nid & proposal
(* Received promises/NACKs from Acceptors *)
| PWaitPrepResponse of data & promises & proposal
(* Send AcceptRequest *)
| PSentAccReq of data & seq nid & proposal
(* Finished executing after sending AccReq or not receiving majority*)
| PAbort
(* Acceptor states *)
| AInit
(* Holds the highest number promised *)
| APromised of nat
(* Holds the highest number proposal accepted *)
| AAccepted of proposal.

(* Pointer to the state *)
Definition st := ptr_nat 1.

(* Pairing with the current stage of type nat *)
Definition StateT := (nat * RoleState)%type.

(* Proposer nodes *)
Variable proposers : seq nid.
(* Acceptor nodes *)
Variable acceptors : seq nid.
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



(*** Defining Coherence ***)

(**
Coherence predicate defines the shape of the statelet.
i.e. it components of the local state and message soup properties.
Therefore, we need to write coherence functions for both the
local state and message soup and then combine them to create PaxosCoh.
 *)


(** ??
Don't know how this function works and how reading from the heap works.
localCoh constraints the local state of each node.
*)
Definition localCoh (n : nid) : Pred heap :=
  [Pred h | valid h /\ exists (s : StateT), h = st :-> s].


(** ??
What does tms_count do?
Messages from Acceptor contain a Proposal/Nack
Need to change (y : nat) to (y : Proposal)
*)
Definition msgFromAcceptor (tms : TaggedMessage) (y : nat) : bool :=
    tagFromAcceptor (tag tms) && (tms_cont tms == [:: y]).

Definition tagFromProposer (t : nat) : bool :=
  (t \in [:: prepare_req; accept_req]).

Definition msgFromProposer (tms : TaggedMessage) (y : nat) : Prop :=
  let: body := tms_cont tms in exists data, body = y :: data.


(* ??
This is saying that a proposer can only send a message to an acceptor and vice versa.
Not sure if we need to impose this for Paxos especially since we have just one 
RoleState..
*)
Definition cohMsg (ms: msg TaggedMessage) (y : nat) : Prop :=
  if from ms \in proposers
  then to ms \in acceptors /\ msgFromProposer (content ms) y
  else if from ms \in acceptors
       then to ms \in proposers /\ msgFromAcceptor (content ms) y
       else True.

(** ??
Coherence for the message soup.
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


(* TODO: Transition Lemmas *)


(* TODO: Getter lemmas for local state *)



(*** State Transitions ***)


Fixpoint choose_highest_numbered_proposal (p: proposal) (xs: promises): proposal :=
  let (p_no, p_val) := p in
  match xs with
  | cons (_, _, (p_no1, p_val1)) rest =>
         if p_no1 > p_no
         then choose_highest_numbered_proposal (p_no1, p_val1) rest
         else choose_highest_numbered_proposal (p_no, p_val) rest
  | _ => p
  end.

(* Choose value of highest numbered proposal received from acceptors *)
Fixpoint create_proposal_for_acc_req (recv_promises: promises) (p: proposal):
  proposal :=
  let (p_no, p_val) := p in
  match recv_promises with
  | cons (_, _, (p_no1, p_val1)) xs =>
    let max_proposal := choose_highest_numbered_proposal (p_no1, p_val1) xs in
    let (_, choosen_value) := max_proposal in
    (p_no, choosen_value)
  | nil => p
  end.

(* Test for highest numbered proposal
Compute create_proposal_for_acc_req [:: (1, true, (1, 1));
                                    (3, false, (3, 4));
                                    (2, true, (2, 8))
                                    ] (9, 1).
 *)

Definition fst' (tup: (nat * bool * proposal)%type): nat :=
  match tup with
  | (x, b, props) => x
  end.

Definition snd' (tup: (nat * bool * proposal)%type): bool :=
  match tup with
  | (x, b, props) => b
  end.

(**
Step function dictactes how the state of the node changes 
after performing the send transition.
*)

(* Changes in the Node state triggered upon send *)
Definition step_send (s: StateT) (to : nid) (d : data) (p: proposal): StateT :=
    let: (e, rs) := s in
    match rs with
    (* Proposer state transitions *)
    | PInit p' =>
      if acceptors == [:: to]
      then (e, PWaitPrepResponse d [::] p')
      else (e, PSentPrep d [:: to] p')
    (* Sending prepare messages *)
    | PSentPrep d' tos p' =>
      (* Do not duplicate prepare-requests *)
      if perm_eq (to :: tos) acceptors
      (* If all sent, switch to the receiving state *)
      then (e, PWaitPrepResponse d' [::] p')
      else (e, PSentPrep d' (to :: tos) p') (* Keep sending *)
    (* Waiting for promises *)
    | PWaitPrepResponse d' recv_promises p' =>
      (* If majority (all promises) received *)
      if (perm_eq (map fst' recv_promises) acceptors)
      then if all (fun r => r) (map snd' recv_promises) (* If no nacks *)
           then let: new_p := create_proposal_for_acc_req recv_promises p' in
                (e, PSentAccReq d' [:: to] new_p)
           else (e, PAbort) (* Nack recieved so abort *)
      else (e, rs) (* Keep waiting *)
    (* Sending Accept Request *)
    | PSentAccReq d' tos p' =>
      if perm_eq (to :: tos) acceptors
      then (e, PAbort) (* Finished sending accept requests *)
      else (e, PSentAccReq d' (to :: tos) p') (* Keep sending *)
    (* Acceptor state transitions *)
    | _ => (e, rs)
    end.