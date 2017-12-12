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
From DiSeL.Core
Require Import InductiveInv While.
From DiSeL.Examples
Require Import PaxosProtocol.


Module PaxosProposer.
Section PaxosProposer.

Variable l : Label.
Variables (proposers: seq nid) (acceptors: seq nid) (others: seq nid).

Variable p: nid.

Hypothesis Auniq : uniq acceptors.
Hypothesis AcceptorsNonEmpty : acceptors != [::].

Check PaxosProtocol.

Definition paxos := PaxosProtocol proposers acceptors l.
Notation W := (mkWorld paxos).

Section ProposerImplementation.

(************** Atomic actions **************)

(* Two send-actions, e -- id of the current era *)
(* TODO: 
- Factor in how to encode round number 
- Probably something like [::e; psal]?
- Better would be to have a proposal as [round_no, p_no, p_val]
but p_no is supposed to work as round no, need to rethink probably
as we exit and go to PAbort instead of retrying.
*)
Program Definition send_prepare_req psal to :=
  act (@send_action_wrapper W paxos p l (prEq paxos)
       (send_prepare_req_trans proposers acceptors) _ psal to).
Next Obligation.
  admit.
Admitted.

Program Definition send_acc_req psal to :=
  act (@send_action_wrapper W paxos p l (prEq paxos)
       (send_acc_req_trans proposers acceptors) _ psal to).
Next Obligation.
  admit.
Admitted.

(* Two receive-actions *)
Program Definition tryrecv_prepare_resp := act (@tryrecv_action_wrapper W p
      (* filter *)
      (fun k _ t b => (k == l) && ((t == promise_resp) || (t == nack_resp))) _).
Next Obligation.
  admit.
Admitted.


(************** Proposer code **************)

(*** Reading internal state ***)
Implicit Arguments PaxosProtocol.PaxosCoh [proposers acceptors].
Notation coh := (@PaxosProtocol.PaxosCoh proposers acceptors).
Notation getS s := (getStatelet s l).
(* ?? not sure if to use p or proposers *)
Notation loc i := (getLocal p (getStatelet i l)).

Export PaxosProtocol.

Program Definition read_round:
  {(ecl : (nat * RoleState))}, DHT [p, W]
  (fun i => loc i = st :-> ecl, 
   fun r m => loc m = st :-> ecl /\
              exists (pf : coh (getS m)), r = (getSt p pf).1) :=
  Do (act (@skip_action_wrapper W p l paxos (prEq paxos) _
                                (fun s pf => (getSt p pf).1))).
Next Obligation.
  admit.
Admitted.

(*******************************************)
(***   Sending out proposals in a loop   ***)
(*******************************************)

Definition send_prepare_req_loop_spec (e : nat) psal:= forall to_send,
  DHT [p, W]
  (fun i =>
     loc i = st :-> (e, PInit psal) /\ perm_eq acceptors to_send \/
     if to_send == [::]
     then loc i = st :-> (e, PWaitPrepResponse [::] psal)
     else exists (acptrs : seq nid),
         loc i = st :-> (e, PSentPrep acptrs psal) /\
         perm_eq acceptors (acptrs ++ to_send),
     fun r m => r = tt /\ loc m = st :-> (e, PWaitPrepResponse [::] psal)).

Program Definition send_prepare_req_loop e psal:
  DHT [p, W] 
  (fun i => loc i = st :-> (e, PInit psal),
   fun r m => r = tt /\
              loc m = st :-> (e, PWaitPrepResponse [::] psal)) :=
  Do (ffix (fun (rec : send_prepare_req_loop_spec e psal) to_send => 
              Do (match to_send with
                  | to :: tos => send_prepare_req psal to ;; rec tos
                  | [::] => ret _ _ tt
                  end)) acceptors).
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.

(*******************************************)
(*** Receiving responses to the proposal ***)
(*******************************************)

(* Ending condition *)
Definition rc_prepare_resp_cond (acc : promises) := ~~ perm_eq (map fst' acc) acceptors.

(* Invariant relates the argument and the shape of the state *)
Definition rc_prepare_resp_inv (e : nat) (psal: proposal): cont (promises) :=
  fun acc i => loc i = st :-> (e, PWaitPrepResponse acc psal).

(* TODO: 
- check use of Hoare spec here 
- check what function construct is created by rc_prepare_resp_in e 
*)
Program Definition receive_prepare_resp_loop (e : nat) (psal: proposal):
  {(p' : proposal)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PWaitPrepResponse [::] psal),
   fun res m => 
       loc m = st :-> (e, PWaitPrepResponse res psal) /\
       (perm_eq (map fst' res) acceptors))
  :=
  Do _ (@while p W _ _ rc_prepare_resp_cond (rc_prepare_resp_inv e) _
        (fun recv_promises => Do _ (
           r <-- tryrecv_prepare_resp;
           match r with
           | Some (from, tg, body) =>
             (* TODO: need to check if received msg is for this round
               might need to change proposal to be like [e, p_no, p_val] *)
             if (from \in acceptors) &&
                 (from \notin (map fst' recv_promises))
             then ret _ _ ((from, tg == promise_resp, body) :: recv_promises)
             else ret _ _ recv_promises
           | None => ret _ _ recv_promises
           end              
        )) [::]).
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.

Definition read_res (st : StateT) :=
  let: (_, rs) := st in
  match rs with
  | PWaitPrepResponse res _ => res
  | _ => [::]
  end.

(* Reading the accumulated responses from the state *)
Program Definition read_resp_result :
  {(e : nat) (psal : proposal) res}, DHT [p, W]
  (fun i => loc i = st :-> (e, PWaitPrepResponse res psal),
   fun r m => loc m = st :-> (e, PWaitPrepResponse res psal) /\
              r = all (fun i => i) (map snd' res)) :=
  Do (act (@skip_action_wrapper W p l paxos (prEq paxos) _
          (fun s pf => all (fun i => i) (map snd' (read_res (getSt p pf)))))).
Next Obligation.
  admit.
Admitted.

(*************************)
(* Coordinator's prelude *)
(*************************)

Program Definition coordinator_prelude (psal: proposal): DHT [p, W]
  (fun i => exists (e : nat), loc i = st :-> (e, PInit psal),
   fun r m => let: (res, b) := r in
       exists (e : nat),
       [/\ loc m = st :-> (e, PWaitPrepResponse res psal),
           perm_eq (map fst' res) acceptors &
           b = all id (map snd' res)]) :=
  Do (e <-- read_round;
      send_prepare_req_loop e psal;;
      res <-- receive_prepare_resp_loop e psal;
      b <-- read_resp_result;
      ret _ _ (res, b)).
Next Obligation.
  admit.
Admitted.

(*******************************************)
(***    Sending accept requests          ***)
(*******************************************)

Definition send_acc_req_loop_spec (e : nat) psal := forall to_send,
  DHT [p, W]
  (fun i =>
     (exists res,
         [/\ loc i = st :-> (e, PWaitPrepResponse res psal),
          to_send = acceptors, perm_eq (map fst' res) acceptors &
          all id (map snd' res)]) \/
     if to_send == [::]
     then loc i = st :-> (e, PSentAccReq [::] psal)
     else exists (acptrs : seq nid),
         loc i = st :-> (e, PSentAccReq acptrs psal) /\
         perm_eq acceptors (acptrs ++ to_send),
   fun (r : unit) m => loc m = st :-> (e, PSentAccReq [::] psal)).

Program Definition send_acc_req_loop e psal: send_acc_req_loop_spec e psal :=
  fun to_send  =>
    Do (fix rec to_send :=
          (match to_send with
           | to :: tos => send_acc_req psal to ;; rec tos
           | [::] => ret _ _ tt
           end)) to_send.
Next Obligation.
  admit.
Admitted.

Program Definition send_acc_reqs e psal:
  DHT [p, W]
  (fun i => exists recv_promises,
         [/\ loc i = st :-> (e, PWaitPrepResponse recv_promises psal),
          perm_eq (map fst' recv_promises) acceptors &
          all id (map snd' recv_promises)],
   fun (r : unit) m => loc m = st :-> (e, PSentAccReq [::] psal))
  := Do (send_acc_req_loop e psal acceptors).
Next Obligation.
  admit.
Admitted.

(*****************************************************)
(*      Full Proposer Implementation                 *)
(*****************************************************)


(* TODO: 
- change to send the proposal that was read from read_resp_result 
- change else clause
*)
Program Definition proposer_round (psal: proposal):
  {(e : nat)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PInit psal),
   fun res m => loc m = st :-> (e.+1, PAbort))
  :=
  Do (e <-- read_round;
      send_prepare_req_loop e psal;;
      res <-- receive_prepare_resp_loop e psal;
      b <-- read_resp_result;
      (if b
       then send_acc_reqs e psal
       else send_acc_reqs e psal);;
      ret _ _ b).
Next Obligation.
  admit.
Admitted.

(* 
Don't we need this part of Paxos as we'll intialise each Proposer with a proposal.
So we can use proposer_round to do that and run the proposer.
This also ensures that a proposer only tries once and then goes into PAbort.


(*****************************************************)
(*    Announcing a list of data transactions         *)
(*****************************************************)

Definition proposer_loop_spec := forall (dts: seq nat),
  {(ep: nat * proposal)}, DHT [p, W]
  (fun i =>  loc i = st :-> (ep.1, PInit ep.2),
   fun (_ : unit) m => exists (chs : seq bool),
     loc m = st :-> (ep.1 + (size dts), PInit ep.2)).

Program Definition proposer_loop (psal: proposal) : proposer_loop_spec :=
  fun dts =>
    Do (fix rec dts :=
          (match dts with
           | d :: dts => proposer_round psal;; rec dts
           | [::] => ret _ _ tt
           end)) dts.
Next Obligation.
  admit.
Admitted.
 *)

End ProposerImplementation.
End PaxosProposer.

Module Exports.
Section Exports.

Definition proposer_round := proposer_round.

End Exports.
End Exports.

End PaxosProposer.

Export PaxosProposer.Exports.
