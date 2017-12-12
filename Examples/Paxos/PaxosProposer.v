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
Program Definition send_prepare_req e data to :=
  act (@send_action_wrapper W paxos p l (prEq paxos)
       (send_prepare_req_trans proposers acceptors) _ (e :: data) to).
Next Obligation.
  admit.
Admitted.

Program Definition send_acc_req e to :=
  act (@send_action_wrapper W paxos p l (prEq paxos)
       (send_acc_req_trans proposers acceptors) _ [:: e] to).
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

Check getSt.

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

Definition send_prepare_req_loop_spec (e : nat) d psal:= forall to_send,
  DHT [p, W]
  (fun i =>
     loc i = st :-> (e, PInit psal) /\ perm_eq acceptors to_send \/
     if to_send == [::]
     then loc i = st :-> (e, PWaitPrepResponse d [::] psal)
     else exists (acptrs : seq nid),
         loc i = st :-> (e, PSentPrep d acptrs psal) /\
         perm_eq acceptors (acptrs ++ to_send),
     fun r m => r = tt /\ loc m = st :-> (e, PWaitPrepResponse d [::] psal)).

Program Definition send_prepare_req_loop e d psal:
  DHT [p, W] 
  (fun i => loc i = st :-> (e, PInit psal),
   fun r m => r = tt /\
              loc m = st :-> (e, PWaitPrepResponse d [::] psal)) :=
  Do (ffix (fun (rec : send_prepare_req_loop_spec e d psal) to_send => 
              Do (match to_send with
                  | to :: tos => send_prepare_req e d to ;; rec tos
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
Definition rc_prepare_resp_inv (e : nat) (d : data) (psal: proposal): cont (promises) :=
  fun acc i => loc i = st :-> (e, PWaitPrepResponse d acc psal).


Program Definition receive_prepare_resp_loop (e : nat) (psal: proposal):
  {(dp : data * proposal)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PWaitPrepResponse dp.1 [::] psal),
   fun res m => 
       loc m = st :-> (e, PWaitPrepResponse dp.1 res dp.2) /\
       (perm_eq (map fst' res) acceptors))
  :=
  Do _ (@while p W _ _ rc_prepare_resp_cond (rc_prepare_resp_inv e psal) _
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
  | PWaitPrepResponse _ res _ => res
  | _ => [::]
  end.

(* Reading the accumulated responses from the state *)
Program Definition read_resp_result :
  {(e : nat) (d : data) (psal : proposal) res}, DHT [p, W]
  (fun i => loc i = st :-> (e, PWaitPrepResponse d res psal),
   fun r m => loc m = st :-> (e, PWaitPrepResponse d res psal) /\
              r = all (fun i => i) (map snd' res)) :=
  Do (act (@skip_action_wrapper W p l paxos (prEq paxos) _
          (fun s pf => all (fun i => i) (map snd' (read_res (getSt p pf)))))).
Next Obligation.
  admit.
Admitted.

(*************************)
(* Coordinator's prelude *)
(*************************)

Program Definition coordinator_prelude (d : data) (psal: proposal): DHT [p, W]
  (fun i => exists (e : nat), loc i = st :-> (e, PInit psal),
   fun r m => let: (res, b) := r in
       exists (e : nat),
       [/\ loc m = st :-> (e, PWaitPrepResponse d res psal),
           perm_eq (map fst' res) acceptors &
           b = all id (map snd' res)]) :=
  Do (e <-- read_round;
      send_prepare_req_loop e d psal;;
      res <-- receive_prepare_resp_loop e psal;
      b <-- read_resp_result;
      ret _ _ (res, b)).
Next Obligation.
  admit.
Admitted.

(*******************************************)
(***    Sending accept requests          ***)
(*******************************************)

Definition send_acc_req_loop_spec (e : nat) d psal := forall to_send,
  DHT [p, W]
  (fun i =>
     (exists res,
         [/\ loc i = st :-> (e, PWaitPrepResponse d res psal),
          to_send = acceptors, perm_eq (map fst' res) acceptors &
          all id (map snd' res)]) \/
     if to_send == [::]
     then loc i = st :-> (e, PSentAccReq d [::] psal)
     else exists (acptrs : seq nid),
         loc i = st :-> (e, PSentAccReq d acptrs psal) /\
         perm_eq acceptors (acptrs ++ to_send),
   fun (r : unit) m => loc m = st :-> (e, PSentAccReq d [::] psal)).

Program Definition send_acc_req_loop e d psal: send_acc_req_loop_spec e d psal :=
  fun to_send  =>
    Do (fix rec to_send :=
          (match to_send with
           | to :: tos => send_acc_req e to ;; rec tos
           | [::] => ret _ _ tt
           end)) to_send.
Next Obligation.
  admit.
Admitted.

Program Definition send_acc_reqs e d psal:
  DHT [p, W]
  (fun i => exists recv_promises,
         [/\ loc i = st :-> (e, PWaitPrepResponse d recv_promises psal),
          perm_eq (map fst' recv_promises) acceptors &
          all id (map snd' recv_promises)],
   fun (r : unit) m => loc m = st :-> (e, PSentAccReq d [::] psal))
  := Do (send_acc_req_loop e d psal acceptors).
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
Program Definition proposer_round (d : data) (psal: proposal):
  {(e : nat)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PInit psal),
   fun res m => loc m = st :-> (e.+1, PAbort))
  :=
  Do (e <-- read_round;
      send_prepare_req_loop e d psal;;
      res <-- receive_prepare_resp_loop e psal;
      b <-- read_resp_result;
      (if b
       then send_acc_reqs e d psal
       else send_acc_reqs e d psal);;
      ret _ _ b).
Next Obligation.
  admit.
Admitted.

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
           | d :: dts => proposer_round d psal;; rec dts
           | [::] => ret _ _ tt
           end)) dts.
