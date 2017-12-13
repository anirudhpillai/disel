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


Module PaxosAcceptor.
Section PaxosAcceptor.

Variable l : Label.
Variables (proposers: seq nid) (acceptors: seq nid).

Variable a: nid.

Check PaxosProtocol.

Definition paxos := PaxosProtocol proposers acceptors l.
Notation W := (mkWorld paxos).

Section AcceptorImplementation.

(************** Atomic actions **************)
  
(* Two receive-actions *)

(* This action actually encompasses two receive-transitions *)
Program Definition tryrecv_prepare_req := act (@tryrecv_action_wrapper W a
      (fun k _ t b => (k == l) && (t == prepare_req)) _).
Next Obligation.
  admit.
Admitted.

Program Definition tryrecv_accept_req :=
  act (@tryrecv_action_wrapper W a
  (fun k _ t b => (k == l) && (t == accept_req)) _).
Next Obligation.
  admit.
Admitted.

(* Two send-actions, e -- id of the current era *)
Check send_promise_resp_trans.
Program Definition send_promise_resp e to :=
  act (@send_action_wrapper W paxos a l (prEq paxos) (send_promise_resp_trans proposers acceptors) _ [:: e] to).
Next Obligation.
  admit.
Admitted.

Program Definition send_nack_resp e to :=
  act (@send_action_wrapper W paxos a l (prEq paxos) (send_nack_resp_trans proposers acceptors) _ [:: e] to).
Next Obligation.
  admit.
Admitted.


(************** Acceptor code **************)

(*** Reading internal state ***)
Implicit Arguments PaxosProtocol.PaxosCoh [proposers acceptors].
Notation coh := (@PaxosProtocol.PaxosCoh proposers acceptors).
Notation getS s := (getStatelet s l).
(* ?? not sure if to use p or proposers *)
Notation loc i := (getLocal a (getStatelet i l)).

Export PaxosProtocol.

Program Definition read_round:
  {(ecl : (nat * RoleState))}, DHT [a, W]
  (fun i => loc i = st :-> ecl, 
   fun r m => loc m = st :-> ecl /\
              exists (pf : coh (getS m)), r = (getSt a pf).1) :=
  Do (act (@skip_action_wrapper W a l paxos (prEq paxos) _
                                (fun s pf => (getSt a pf).1))).
Next Obligation.
  admit.
Admitted.

(* Step 2: Receive prepare req *)

(* Ending condition *)
Definition r_prepare_req_cond (res : option proposal) := res == None.

(* ??  Do I need to check the higher proposal number according to the state? *)
(* Invariant relates the argument and the shape of the state *)
Definition r_prepare_req_inv (e : nat) : cont (option proposal) :=
  fun res i =>
    if res is Some psal
    then loc i = st :-> (e, APromised psal)
    else loc i = st :-> (e, AInit).

Program Definition receive_prepare_req_loop (e : nat):
  DHT [a, W]
  (fun i => loc i = st :-> (e, AInit),
   fun res m => exists psal, res = Some psal /\
       loc m = st :-> (e, APromised psal))
  :=
  (* TODO: Check the functional construct formed by r_prepare_req_in *)
  Do _ (@while a W _ _ r_prepare_req_cond (r_prepare_req_inv) _
        (fun _ => Do _ (
           r <-- tryrecv_prepare_req;
           match r with
           | Some (from, tg, body) =>
             if (from \in proposers)
                  (* TODO: need to check round no.? *)
                  (* && (head 0 body == e) *)
             then ret _ _ (Some body)
             else ret _ _ None
           | None => ret _ _ None
           end              
        )) None).
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

(* Step 2: Respond promise or nack to the proposer *)
Program Definition resp_to_req (e : nat) (p': ):
  {psal : proposal}, DHT [a, W]
  (fun i => loc i = st :-> (e, APromised psal), (* TODO: state can also be AInit? *)
   fun (_ : seq nat) m =>
     loc m = st :-> (e, APromised psal))
  := Do (send_promise_resp e).
