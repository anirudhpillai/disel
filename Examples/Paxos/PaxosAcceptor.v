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


Definition paxos := PaxosProtocol proposers acceptors l.
Notation W := (mkWorld paxos).

Section AcceptorImplementation.

(************** Atomic actions **************)
  
(* Two receive-actions *)
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
Program Definition send_promise_resp to :=
  act (@send_action_wrapper W paxos a l (prEq paxos) (send_promise_resp_trans proposers acceptors) _ [::] to).
Next Obligation.
  admit.
Admitted.

Program Definition send_nack_resp to :=
  act (@send_action_wrapper W paxos a l (prEq paxos) (send_nack_resp_trans proposers acceptors) _ [::] to).
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

Program Definition read_state:
  {(ecl : (nat * RoleState))}, DHT [a, W]
  (fun i => loc i = st :-> ecl, 
   fun r m => loc m = st :-> ecl /\
              exists (pf : coh (getS m)), r = (getSt a pf).2) :=
  Do (act (@skip_action_wrapper W a l paxos (prEq paxos) _
                                (fun s pf => (getSt a pf).2))).
Next Obligation.
  admit.
Admitted.

(* Step 1: Receive prepare req *)

(* Ending condition *)
Definition r_prepare_req_cond (res : option proposal) := res == None.

(* ??  Do I need to check the higher proposal number according to the state? *)
(* Invariant relates the argument and the shape of the state *)
Definition r_prepare_req_inv (e : nat) : cont (option proposal) :=
  fun res i =>
    if res is Some psal
    then loc i = st :-> (e, APromised psal)
    else loc i = st :-> (e, AInit).

(* Loops until it receives a prepare req *)
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
           | Some (from, tg, body) => ret _ _ body
           | None => ret _ _ [::]
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
Next Obligation.
  admit.
Admitted.



(* Finds the promised number from current state *)
Definition read_promised_number (rs: RoleState) :=
  match rs with
  | APromised psal => head 0 psal
  | _ => 0
  end.

(* Step 2: Respond promise or nack to the proposer *)
Program Definition resp_to_prepare_req (e: nat) (prepare_no: nat):
  {(pinit pfinal: proposal)}, DHT [a, W]
   (fun i => loc i = st :-> (e, APromised pinit) \/ loc i = st :-> (e, AInit),
    fun (_ : seq nat) m => loc m = st :-> (e, APromised pinit) \/
        loc m = st :-> (e, APromised pfinal))
  := Do (rs <-- read_state;
         if prepare_no > read_promised_number rs
         then send_promise_resp prepare_no
         else send_nack_resp prepare_no).
Next Obligation.
  admit.
Admitted.


(* Using resp_to_prepare_req 0 as a 'do nothing' transition for now.
As 0 will never be > 0 so the acceptor won't send a promise *)
Program Definition acceptor_round:
  {(e: nat) (psal: proposal)}, DHT [a, W] 
  (fun i =>  loc i = st :-> (e, AInit) \/ loc i = st :-> (e, APromised psal),
   fun (_ : unit) m => loc m = st :-> (e, APromised psal) \/ loc m = st :-> (e, AInit))
  := 
    Do _ (e <-- read_round;
          msg <-- receive_prepare_req_loop e;
          match msg with
          | Some (cons p_no p_val) => resp_to_prepare_req e p_no
          | _  => resp_to_prepare_req e 0
          end).
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.
