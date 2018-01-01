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
| PSentPrep of seq nid & proposal
(* Received promises/NACKs from Acceptors *)
| PWaitPrepResp of promises & proposal
(* Send AcceptRequest *)
| PSentAccReq of seq nid & proposal
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


Definition ttag := nat.

Definition tags : seq ttag :=
  [:: prepare_req; promise_resp; nack_resp; accept_req].


(*** Defining Coherence ***)

(**
Coherence predicate defines the shape of the statelet.
i.e. it components of the local state and message soup properties.
Therefore, we need to write coherence functions for both the
local state and message soup and then combine them to create PaxosCoh.
 *)


(** localCoh constraints the local state of each node. **)
Definition localCoh (n : nid) : Pred heap :=
  [Pred h | valid h /\ exists (s : StateT), h = st :-> s].


(** ??
What does tms_count do?
Messages from Acceptor contain a Proposal/Nack
Need to change (y : nat) to (y : Proposal)
 *)

Definition tagFromAcceptor (t : nat) : bool :=
  (t \in [:: promise_resp; nack_resp]).

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
Lemma cohSt n d (C : PaxosCoh d) s:
  find st (getLocal n d) = Some s ->
  idyn_tp s = StateT.
Proof.
  admit.
Admitted.

Definition getSt n d (C : PaxosCoh d) : StateT :=
  match find st (getLocal n d) as f return _ = f -> _ with
  | Some v => fun epf => icoerce id (idyn_val v) (cohSt C epf)
  | _ => fun epf => (0, AInit)
  end (erefl _).
Check getSt.

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
Step Functions

Step function dictactes how the state of the node changes 
after performing the send/receive transitions.
*)

(**
Send Transitions:
- Proposer: sPrep, sAccReq
- Acceptor: sPromise, sNack
*)

(* Changes in the Node state triggered upon send *)
Definition step_send (s: StateT) (to : nid) (p: proposal): StateT :=
    let: (e, rs) := s in
    match rs with
    | PInit p' =>
      if acceptors == [:: to] (* if only one acceptor *)
      then (e, PWaitPrepResp [::] p')
      else (e, PSentPrep [:: to] p')
    | PSentPrep tos p' =>
      if perm_eq (to :: tos) acceptors
      (* If all prepare reqs sent *)
      then (e, PWaitPrepResp [::] p') (* switch to the receiving state *)
      else (e, PSentPrep (to :: tos) p') (* Keep sending *)
    | PSentAccReq tos p' =>
      if perm_eq (to :: tos) acceptors
      (* If all accept reqs sent *)
      then (e, PAbort)
      else (e, PSentAccReq (to :: tos) p') (* Keep sending *)
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
Definition step_recv (s : StateT) (from : nid) (mtag : ttag) (mbody : payload):
  StateT :=
  let: (e, rs) := s in
  let: p_no := head 0 mbody in 
  let: p_val := last 0 mbody in 
  match rs with
  | PWaitPrepResp recv_promises p' =>
    if (from \in (map fst' recv_promises)) (* If duplicate *)
    then s (* then ignore *)
    else if mtag == nack_resp
         then (e, PAbort) (* Abort if we see nack *)
         else
           let: r_promises := (from, mtag == promise_resp, mbody) :: recv_promises in
           (* if all promises received, we know we don't have nacks *)
           if (perm_eq (map fst' r_promises) acceptors)
           then let: new_p := create_proposal_for_acc_req r_promises p' in
                (e, PSentAccReq [::] new_p)
           else (e, PWaitPrepResp r_promises p') (* keep waiting for promises *)
  | AInit => (* Promise/Accept first received transition *)
    if mtag == prepare_req
    then (e, APromised mbody)
    else (e, AAccepted mbody)
  | APromised p' =>
      let: curr_p_no := head 0 p' in 
      let: curr_p_val := last 0 p' in
      if mtag == prepare_req
      then if p_no > curr_p_no (* If received higher number *)
           (* Update promised number by storing new proposal *)
           then (e, APromised mbody)
           else (e, APromised p')
      else (* It's an accept request *)
           if p_no > curr_p_no (* If received higher number *)
           then (e, AAccepted mbody) (* Accept the proposal *)
           else (e, APromised p') (* we'll send nack *)
  | _ => s
  end.

(* 
There should be 4 send-transitions for the node:
- send-prepare-request
- send-accept-request
- send-promise
- send-nack

There should be 4 receive-transitions for the node:
- receive-promise
- receive-nack
- receive-prepare-request
- receive-accept-request
 *)

Section GenericSendTransitions.

Notation coh := PaxosCoh.

Definition Hin this to := (this \in nodes /\ to \in nodes).
Definition mkLocal {T} (sl : T) := st :-> sl.
Check mkLocal.

Variable ptag : ttag.

(* Precondition -- this is the way one can define multiple send-transitions *)
Variable prec : StateT -> payload -> Prop.

(* Making sure that the precondition is legit *)
Lemma this_in this to : Hin this to -> this \in nodes.
Proof.
  by case.
Qed.

Definition node_safe (this n : nid)
           (d : dstatelet) (msg : payload) :=
  Hin this n /\ 
  exists (Hp : Hin this n) (C : coh d), prec (getSt this C) msg.

Lemma node_safe_coh this to d m : node_safe this to d m -> coh d.
Proof.
  case.
  move => in_nodes.
  case.
  move => in_nodes2.
  case => coh_d H_coh_d => //.
Qed.

Lemma node_safe_in this to d m : node_safe this to d m ->
                               this \in nodes /\ to \in nodes.
Proof.
  case.
  move => Hin e_clause => //.
Qed.

Definition node_step (this to : nid) (d : dstatelet)
           (msg : payload)
           (pf : node_safe this to d msg) :=
  let C := node_safe_coh pf in
  let s := getSt this C in
  Some (mkLocal (step_send s to msg)).

Lemma node_step_coh : s_step_coh_t coh ptag node_step.
Proof.
  move=>this to d msg pf h[]->{h}.
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


(** TODO: Strengthen all pre conditions by putting conditions on (to: nid) **)
  
(* Send prepare request transition *)
Definition send_prepare_req_prec (p: StateT) (m: payload) :=
  (exists n psal, p = (n, PInit psal)) \/
  (exists n tos psal, p = (n, PSentPrep tos psal)).

Definition send_prepare_req_trans : send_trans PaxosCoh :=
  @node_send_trans prepare_req send_prepare_req_prec.

(* Send accept request transition *)
Definition send_accept_req_prec (p: StateT) (m: payload) :=
  (exists n psal, p = (n, PSentAccReq [::] psal)).

Definition send_accept_req_trans : send_trans PaxosCoh :=
  @node_send_trans accept_req send_accept_req_prec.

(* Send promise response transition *)
Definition send_promise_resp_prec (p: StateT) (m: payload) :=
  (exists n, p = (n, AInit)) \/ (exists n psal, p = (n, APromised psal)).

Definition send_promise_resp_trans : send_trans PaxosCoh :=
  @node_send_trans promise_resp send_promise_resp_prec.

(* Send nack response transition *)
Definition send_nack_resp_prec (p: StateT) (m: payload) :=
  exists n psal, p = (n, APromised psal).

Definition send_nack_resp_trans : send_trans PaxosCoh :=
  @node_send_trans nack_resp send_nack_resp_prec.

End SendTransitions.

Section GenericReceiveTransitions.

Notation coh := PaxosCoh.

Variable r_tag : ttag.
Variable r_wf : forall d, coh d -> nid -> nid -> pred payload.

Definition r_step : receive_step_t coh :=
  fun this (from : nid) (m : proposal) d (pf : coh d) (pt : this \in nodes) =>
    let s := getSt this pf in
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
Definition receive_accept_req_trans := recv_trans accept_req msg_wf.

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
     send_accept_req_trans;
     send_promise_resp_trans;
     send_nack_resp_trans
  ].

(* All receive-transitions *)
Definition paxos_receives :=
  [::
     receive_prepare_req_trans;
     receive_accept_req_trans;
     receive_promise_resp_trans;
     receive_nack_resp_trans
  ].

Program Definition PaxosProtocol : protocol :=
  @Protocol _ l _ paxos_sends paxos_receives _ _.

End Protocol.
End PaxosProtocol.

Module Exports.
Section Exports.
      
Definition PaxosProtocol := PaxosProtocol.

Definition send_prepare_req_trans := send_prepare_req_trans.
Definition send_accept_req_trans := send_accept_req_trans.
Definition send_promise_resp_trans := send_promise_resp_trans.
Definition send_nack_resp_trans := send_nack_resp_trans.

Definition receive_prepare_req_trans := receive_prepare_req_trans.
Definition receive_accept_req_trans := receive_accept_req_trans.
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
