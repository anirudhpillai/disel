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


Module PaxosProtocol.

  
Module States.

    
Definition nid := nat.
Definition data := seq nid.

(* seq of two elements p_no, p_val *)
Definition proposal := seq nat.
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
(* Holds the highest number promised in the proposal *)
(* Storing a proposal and not just a nat as this makes it easier to catch the payload
later on in the transitions *)
| APromised of proposal
(* Holds the highest number proposal accepted *)
| AAccepted of proposal.

(* Pointer to the state *)
Definition st := ptr_nat 1.

(* Pairing with the current stage of type nat *)
Definition StateT := (nat * RoleState)%type.


End States.

Import States.

Section PaxosProtocol.

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


(** ??
Don't know if or why this is needed
Interaction with the clients 
*)
Definition eval_req : nat := 4.
Definition eval_resp : nat := 5.


Definition ttag := nat.

Definition tags : seq ttag :=
  [:: prepare_req;
     promise_resp;
     nack_resp;
     accept_req;
     eval_req;
     eval_resp].

Definition tagFromAcceptor (t : nat) : bool :=
  (t \in [:: promise_resp; nack_resp]).



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

(* NOTE: These are temporary, no idea what I've done here *)
Lemma cohSt n d (C : PaxosCoh d) (H : n \in nodes) s:
  find st (getLocal n d) = Some s ->
  idyn_tp s = StateT. 
Proof.
  admit.
Admitted.

Program Definition getSt n d (C : PaxosCoh d) (pf : n \in nodes) : StateT.
Proof.
case X: (n \in nodes); last by exact: (0, AInit).
exact: (match find st (getLocal n d) as f return _ = f -> _ with
          Some v => fun epf => icoerce id (idyn_val v) (cohSt C X epf)
        | _ => fun epf => (0, AInit)
        end (erefl _)).
Defined.

(*** State Transitions ***)


Fixpoint choose_highest_numbered_proposal (p: proposal) (xs: promises): proposal :=
  let: p_no := head 0 p in 
  let: p_val := last 0 p in 
  match xs with
  | cons (_, _, p') rest =>
    let: p_no1 := head 0 p' in
    let: p_val1 := last 0 p' in 
    if p_no1 > p_no
    then choose_highest_numbered_proposal [:: p_no1; p_val1] rest
    else choose_highest_numbered_proposal [:: p_no; p_val] rest
  | _ => p
  end.

(* Choose value of highest numbered proposal received from acceptors *)
Fixpoint create_proposal_for_acc_req (recv_promises: promises) (p: proposal):
  proposal :=
  let: p_no := head 0 p in 
  let: p_val := last 0 p in 
  match recv_promises with
  | cons (_, _, p') xs =>
    let: p_no1 := head 0 p' in
    let: p_val1 := last 0 p' in 
    let: max_proposal := choose_highest_numbered_proposal [:: p_no1; p_val1] xs in
    let: choosen_value := last 0 max_proposal in 
    [:: p_no; choosen_value]
  | nil => p
  end.

(* Test for highest numbered proposal
Compute create_proposal_for_acc_req [:: (1, true, [:: 1; 1]);
                                    (3, false, [:: 3; 4]);
                                    (2, true, [:: 2; 8])
                                    ] [:: 9; 1].
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
Send Transitions:
- Proposer: sPrep, sAccReq
- Acceptor: sPromise, sNack
*)

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
    | APromised p' =>
      let: p_no := head 0 p in 
      let: p_val := last 0 p in
      let: curr_p_no := head 0 p' in 
      let: curr_p_val := last 0 p' in
      if p_no > curr_p_no (* If promising higher number *)
      then (e, APromised p) (* Update promised number by storing new proposal *)
      else (e, APromised p') (* We'll send NACK so don't need to update *)
    (* Don't think I need transitions from AAccepted state *)
    | _ => (e, rs)
    end.


(** ?? Do I need the ?_matches_tag s mtag : bool function? *)

(**
Receive Transitions:
- Proposer: rPromise, rNack
- Acceptor: rPrep, rAccReq
 *)

Definition payload := proposal.

(* Changes in the Node state triggered upon receive *)
Definition step_recv (s : StateT) (from : nid) (mtag : ttag) (p: proposal)
           (mbody : payload): StateT :=
  let: (e, rs) := s in
  let: p_no := head 0 p in 
  let: p_val := last 0 p in 
  match rs with
  (* Proposer states *)
  | PWaitPrepResponse d' recv_promises p' =>
    (* All responses already collected or 
       already received from this participant  *)
    if (from \in (map fst' recv_promises))
    then s
    (* Save result *)
    else if mtag == nack_resp
         then (e, PAbort) (* Abort if we see nack *)
         else (e, PWaitPrepResponse d' ((from, mtag == promise_resp, mbody) :: recv_promises) p')
(** ??
Do I need to add receive transition for PWaitPrepResp -> PSentAcceptReq?
The state change is in step_send but it's a receive transition that causes the state
to change not a send transition. *)
  (* Acceptor States *)
  (* Haven't promised anything so need to promise the first prepare message *)
  | AInit => (e, APromised p)
(** ??
Do I need to add receive transition for APromised -> APromised when it receives
a new prepare message? *)
  | APromised p' =>
    if mtag == accept_req
    then let: curr_p_no := head 0 p' in
         if p_no > curr_p_no
         then (e, AAccepted p) (* Accept AccReq *)
         else (e, APromised p')
    else s (* NOTE: Can add another if statement here to check mtag == prep_req 
and then move to APromised with a higher promised number if successful *)
  | _ => s
  end.

(* 
There should be 4 send-transitions for the node:
- send-prepare
- send-accept-request
- send-promise
- send-nack

There should be 4 receive-transitions for the node:
- receive-promise
- receive-nack
- receive-prepare
- receive-accept-request
 *)

Section GenericSendTransitions.

Notation coh := PaxosCoh.

Definition HPn this to := (this \in nodes /\ to \in nodes).
Definition mkLocal {T} (sl : T) := st :-> sl.
Check mkLocal.

Variable ptag : ttag.

(* Precondition -- this is the way one can define multiple send-transitions *)
(* TODO: change seq nat to payload *)
Variable prec : StateT -> payload -> Prop.

(* Making sure that the precondition is legit *)
Lemma this_in this to : HPn this to -> this \in nodes.
Proof.
  admit.
Admitted.

Definition node_safe (this n : nid)
           (d : dstatelet) (msg : payload) :=
  HPn this n /\ 
  exists (Hp : HPn this n) (C : coh d), prec (getSt C (this_in Hp)) msg.

Lemma node_safe_coh this to d m : node_safe this to d m -> coh d.
Proof.
  admit.
Admitted.

Check node_safe_coh.

Lemma node_safe_in this to d m : node_safe this to d m ->
                               this \in nodes /\ to \in nodes.
Proof.
  admit.
Admitted.

Variable commit : bool.

Definition node_step (this to : nid) (d : dstatelet)
           (msg : payload)
           (pf : node_safe this to d msg) :=
  let C := node_safe_coh pf in
  let s := getSt C (this_in (proj1 pf)) in
  Some (mkLocal (step_send s commit)).

Check s_step_coh_t coh.

Lemma node_step_coh : s_step_coh_t coh ptag node_step.
Proof.
  admit.
Admitted.

Lemma node_safe_def this to d msg :
      node_safe this to d msg <->
      exists b pf, @node_step this to d msg pf = Some b.
Proof.
  admit.
Admitted.

Definition node_send_trans :=
  SendTrans node_safe_coh node_safe_in node_safe_def node_step_coh.

End GenericSendTransitions.

Section SendTransitions.

(* Send prepare request transition *)
Definition send_prepare_req_prec (p: StateT) (m: payload) :=
  (exists n psal, p = (n, PInit psal)) \/
  (exists n d tos psal, p = (n, PSentPrep d tos psal)).

Program Definition send_prepare_req_trans : send_trans PaxosCoh :=
  @node_send_trans prepare_req send_prepare_req_prec _.
Next Obligation.
  admit.
Admitted.

(* Send accept request transition *)
Definition send_acc_req_prec (p: StateT) (m: payload) :=
  (exists n d promises psal,
    [/\ p = (n, PWaitPrepResponse d promises psal),
     perm_eq (map fst' promises) acceptors & all (fun r => r) (map snd' promises)]).

Program Definition send_acc_req_trans : send_trans PaxosCoh :=
  @node_send_trans accept_req send_acc_req_prec _.
Next Obligation.
  admit.
Admitted.

Definition proposal_gt (p p': proposal): Prop :=
  let: p_no := head 0 p in
  let: p_no' := head 0 p in
  p_no > p_no'.

(* Send promise response transition *)
(* received proposal in message must have higher number than current proposal *)
Definition send_promise_resp_prec (p: StateT) (m: payload) :=
  (exists n, p = (n, AInit)) \/
  (exists n psal, p = (n, APromised psal) \/ proposal_gt m psal).

Program Definition send_promise_resp_trans : send_trans PaxosCoh :=
  @node_send_trans accept_req send_promise_resp_prec _.
Next Obligation.
  admit.
Admitted.

(* Send nack response transition *)
(* received proposal in message must have lower number than current proposal *)
Definition send_nack_resp_prec (p: StateT) (m: payload) :=
  (exists n, p = (n, AInit)) \/
  (exists n psal, p = (n, APromised psal) \/ not (proposal_gt m psal)).

Program Definition send_nack_resp_trans : send_trans PaxosCoh :=
  @node_send_trans accept_req send_nack_resp_prec _.
Next Obligation.
  admit.
Admitted.

End SendTransitions.

Section GenericReceiveTransitions.

Notation coh := PaxosCoh.

Variable r_tag : ttag.
Variable r_wf : forall d, coh d -> nid -> nid -> pred payload.

Definition r_step : receive_step_t coh :=
  fun this (from : nid) (m : proposal) d (pf : coh d) (pt : this \in nodes) =>
    let s := getSt pf pt in
    mkLocal (step_recv s from r_tag m).

Lemma r_step_coh : r_step_coh_t r_wf r_tag r_step.
Proof.
  admit.
Admitted.

Definition recv_trans := ReceiveTrans r_step_coh.

End GenericReceiveTransitions.

Section ReceiveTransitions.

Definition msg_wf d (_ : PaxosCoh d) (this from : nid) :=
  [pred p : payload | true].

(* Got prepare request *)
Definition receive_prepare_req_trans := recv_trans prepare_req msg_wf.

(* Got accept request *)
Definition receive_acc_req_trans := recv_trans accept_req msg_wf.

(* Got promise response *)
Definition receive_promise_resp_trans := recv_trans promise_resp msg_wf.

(* Got nack response *)
Definition receive_nack_resp_trans := recv_trans nack_resp msg_wf.

End ReceiveTransitions.


Section Protocol.

(* Putting it all together *)
Variable l : Label.

(* All send-transitions *)
Definition paxos_sends :=
  [::
     send_prepare_req_trans;
     send_acc_req_trans;
     send_promise_resp_trans;
     send_nack_resp_trans
  ].

(* All receive-transitions *)
Definition paxos_receives :=
  [::
     receive_prepare_req_trans;
     receive_acc_req_trans;
     receive_promise_resp_trans;
     receive_nack_resp_trans
  ].


Program Definition PaxosProtocol : protocol :=
  @Protocol _ l _ paxos_sends paxos_receives _ _.
Next Obligation.
  admit.
Admitted.


End Protocol.
End PaxosProtocol.

Module Exports.
Section Exports.
      
Definition PaxosProtocol := PaxosProtocol.

Definition send_prepare_req_trans := send_prepare_req_trans.
Definition send_acc_req_trans := send_acc_req_trans.
Definition send_promise_resp_trans := send_promise_resp_trans.
Definition send_nack_resp_trans := send_nack_resp_trans.

Definition receive_prepare_req_trans := receive_prepare_req_trans.
Definition receive_acc_req_trans := receive_acc_req_trans.
Definition receive_promise_resp_trans := receive_promise_resp_trans.
Definition receive_nack_resp_trans := receive_nack_resp_trans.

(* Paxos Tags *)
Definition prepare_req := prepare_req.
Definition accept_req := accept_req.
Definition promise_resp := promise_resp.
Definition nack_resp := nack_resp.

(* Getter *)
Definition getSt := getSt.

End Exports.
End Exports.

End PaxosProtocol.

Export PaxosProtocol.States.
Export PaxosProtocol.Exports.
