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
(* Two send-actions, e -- id of the current era *)
Program Definition send_promise_resp psal to :=
  act (@send_action_wrapper W paxos a l (prEq paxos)
       (send_promise_resp_trans proposers acceptors) _ psal to).
Next Obligation.
  rewrite !InE. right. right. left. done.
Qed.

Program Definition send_nack_resp psal to :=
  act (@send_action_wrapper W paxos a l (prEq paxos)
       (send_nack_resp_trans proposers acceptors) _ psal to).
Next Obligation.
  rewrite !InE. right. right. right. done.
Qed.  

  
(* Two receive-actions *)
Program Definition tryrecv_prepare_req := act (@tryrecv_action_wrapper W a
      (fun k _ t b => (k == l) && (t == prepare_req)) _).
Next Obligation.
  by case/andP: H=>/eqP->_; rewrite /ddom gen_domPt inE/=.
Qed.

Program Definition tryrecv_accept_req :=
  act (@tryrecv_action_wrapper W a
  (fun k _ t b => (k == l) && (t == accept_req)) _).
Next Obligation.
  by case/andP: H=>/eqP->_; rewrite /ddom gen_domPt inE/=.
Qed.


(************** Acceptor code **************)

(*** Reading internal state ***)
Implicit Arguments PaxosProtocol.PaxosCoh [proposers acceptors].
Notation coh := (@PaxosProtocol.PaxosCoh proposers acceptors).
Notation getS s := (getStatelet s l).
(* ?? not sure if to use p or proposers *)
Notation loc i := (getLocal a (getStatelet i l)).

Export PaxosProtocol.

Program Definition read_round:
  {(e: nat) (rs: RoleState)}, DHT [a, W]
  (fun i => loc i = st :-> (e, rs), 
   fun r m => loc m = st :-> (e, rs) /\
              exists (pf : coh (getS m)), r = (getSt a pf).1) :=
  Do (act (@skip_action_wrapper W a l paxos (prEq paxos) _
                                (fun s pf => (getSt a pf).1))).
Next Obligation.
  admit.
Admitted.

Program Definition read_state:
  {(e: nat) (rs: RoleState)}, DHT [a, W]
  (fun i => loc i = st :-> (e, rs), 
   fun r m => loc m = st :-> (e, rs) /\
              exists (pf : coh (getS m)), r = (getSt a pf).2) :=
  Do (act (@skip_action_wrapper W a l paxos (prEq paxos) _
                                (fun s pf => (getSt a pf).2))).
Next Obligation.
  admit.
Admitted.

(* Step 1: Receive prepare req *)

(* TODO: Check ending condition *)
(* Ending condition *)
Definition r_prepare_req_cond (res : option proposal) := res == None.

(* ??  Do I need to check the higher proposal number according to the state? *)
(* Invariant relates the argument and the shape of the state *)
Definition r_prepare_req_inv (e : nat) (pinit: proposal): cont (option proposal) :=
  fun res i =>
    if res is Some psal
    then loc i = st :-> (e, APromised psal)
    else loc i = st :-> (e, AInit).

  (* (fun i => loc i = st :-> (e, AInit), *)
  (*  fun res m => exists psal, res = Some psal /\ loc m = st :-> (e, APromised psal)) *)
  (* := *)
  (* Do _ (@while a W _ _ r_prepare_req_cond (r_prepare_req_inv e) _ *)
  (*       (fun _ => Do _ ( *)
  (*          r <-- tryrecv_prepare_req; *)
  (*          match r with *)
  (*          | Some (from, tg, body) => ret _ _ (Some body) *)
  (*          | None => ret _ _ None *)
  (*          end               *)
  (*       )) None). *)

(* Loops until it receives a prepare req *)
Program Definition receive_prepare_req_loop (e : nat):
  DHT [a, W]
  (fun i => loc i = st :-> (e, AInit),
   fun res m => exists psal, res = Some psal /\
       loc m = st :-> (e, APromised psal))
  :=
  Do _ (@while a W _ _ r_prepare_req_cond (r_prepare_req_inv e) _
        (fun _ => Do _ (
           r <-- tryrecv_prepare_req;
           match r with
           | Some (from, tg, body) => ret _ _ (Some body)
           | None => ret _ _ None
           end
        )) None).
Next Obligation. by apply: with_spec x. Defined.
Next Obligation. by move:H; rewrite /r_prepare_req_inv (rely_loc' _ H0). Qed.
Next Obligation.
  apply:ghC=>i1 psal[/eqP->{H}/=E1]C1; apply: step.
  apply: act_rule=>i2/=R1; split; first by case: (rely_coh R1).
  case=>[[[from e']d i3 i4]|i3 i4]; last first.
  - case=>S/=[]?; case; last by case=>?[?][?][?][?][?][].
    case=>_ _ Z; subst i3=>R2; apply: ret_rule=>i5 R4/=.
    by rewrite (rely_loc' _ R4) (rely_loc' _ R2)(rely_loc' _ R1).
  case=>Sf[]C2[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E2 Hw/=]; first by case.
  case/andP=>/eqP Z G->[]Z1 Z2 Z3 R2; subst l' from' e' d.
  move: rt pf (coh_s (w:=W) l (s:=i2) C2) Hin R2 E2 Hw G E; rewrite prEq/=.
  move=>rt pf Cj' Hin R E2 Hw G E.
  have D: rt = receive_prepare_req_trans _ _.
  - move: Hin G; by do! [case=>/=; first by move=>->].
  subst rt=>{G}.
  have P1: valid (dstate (getS i2))
    by apply: (@cohVl _ coh); case: (Cj')=>P1 P2 P3 P4; split=>//=; done.
  have P2: valid i2 by apply: (cohS (proj2 (rely_coh R1))).
  have P3: l \in dom i2 by rewrite -(cohD (proj2 (rely_coh R1)))/ddom gen_domPt inE/=.

  apply: ret_rule=>//i5 R4.
  - rewrite /r_prepare_req_inv; rewrite (rely_loc' _ R4) (rely_loc' _ R) locE//=.
    rewrite /PaxosProtocol.r_step /=.
    rewrite -(rely_loc' _ R1) in E1.
    (* Write getter lemmas to finish this *)
  admit.
Admitted.
Next Obligation.
  (* Can't apply ghC as no Hoare Type *)
  admit.
Admitted.

(* Finds the promised number from current state *)
Definition read_promised_number (rs: RoleState) :=
  match rs with
  | APromised psal => head 0 psal
  | _ => 0
  end.

Definition read_promised_value (rs: RoleState) :=
  match rs with
  | APromised psal => last 0 psal
  | _ => 0
  end.

(* Step 2: Respond promise or nack to the proposer *)
Program Definition resp_to_prepare_req (e: nat) (prepare_no: nat):
  {(pinit pfinal: proposal)}, DHT [a, W]
   (fun i => loc i = st :-> (e, APromised pinit) \/ loc i = st :-> (e, AInit),
    fun (_ : seq nat) m => loc m = st :-> (e, APromised pinit) \/
        loc m = st :-> (e, APromised pfinal))
  := Do (rs <-- read_state;
         let: promised := read_promised_number rs in
         let: value := read_promised_value rs in  
         if prepare_no > promised
         then send_promise_resp [:: promised; value] prepare_no
         else send_nack_resp [:: 0; 0] prepare_no).
Next Obligation.
  admit.
Admitted.

(* TODO: Check ending condition *)
(* Ending condition *)
Definition r_acc_req_cond (res : option proposal) := res == None.

(* ??  Do I need to check the higher proposal number according to the state? *)
(* Invariant relates the argument and the shape of the state *)
Definition r_acc_req_inv (e : nat) (psal: proposal) : cont (option proposal) :=
  fun res i =>
    if res is Some psal
    then loc i = st :-> (e, AAccepted psal)
    else loc i = st :-> (e, AInit).

(* Loops until it receives a accept req *)
Program Definition receive_acc_req_loop (e : nat):
  {(pinit: proposal)}, DHT [a, W]
  (fun i => loc i = st :-> (e, AInit) \/ loc i = st :-> (e, APromised),
  fun res m => exists psal, res = Some psal /\ (
    loc m = st :-> (e, APromised psal) \/
    loc m = st :-> (e, AAccepted psal)
  )) :=
  Do _ (@while a W _ _ r_acc_req_cond (r_acc_req_inv e) _
        (fun _ => Do _ (
           r <-- tryrecv_accept_req;
           match r with
           | Some (from, tg, body) => ret _ _ (Some body)
           | None => ret _ _ None
           end              
        )) None).
Next Obligation. by apply: (with_spec x). Defined.
Next Obligation. by move:H; rewrite /r_acc_req_inv (rely_loc' _ H0). Qed.
Next Obligation.
  apply:ghC=>i1 psal [/eqP->{H}/=E1]C1. apply: step.
  apply: act_rule=>i2/=R1; split; first by case: (rely_coh R1).
  case=>[[[from e']v i3 i4]|i3 i4]; last first.
  - case=>S/=[]?; case; last by case=>?[?][?][?][?][?][].
    case=>_ _ Z; subst i3=>R2; apply: ret_rule=>i5 R4/=.
    rewrite /r_acc_req_inv/= in E1 *.
    by rewrite (rely_loc' _ R4) (rely_loc' _ R2) (rely_loc' _ R1).
  case=>Sf[]C2[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E2 Hw/=]; first by case.
  case/andP=>/eqP Z G->[]Z1 Z2 Z3 R2; subst l' from' e' v.
  move: rt pf (coh_s (w:=W) l (s:=i2) C2) Hin R2 E2 Hw G E; rewrite prEq/=.
  move=>rt pf Cj' Hin R E2 Hw G E.
  have P1: valid (dstate (getS i2))
    by apply: (@cohVl _ coh); case: (Cj')=>P1 P2 P3 P4; split=>//=; done.
  have P2: valid i2 by apply: (cohS (proj2 (rely_coh R1))).
  have P3: l \in dom i2 by rewrite-(cohD (proj2 (rely_coh R1)))/ddom gen_domPt inE/=.
  have D: rt = receive_accept_req_trans _ _.
  -  move: Hin G. clear E1.
     case => //. move => ->.
  admit.
Admitted.
Next Obligation.
  apply: ghC=>i1 psal E1 C1/=.
  apply: (gh_ex (g := psal)). apply: call_rule => //[r|r i2 [H1]H2 C2].
  admit.
  rewrite /r_acc_req_cond/r_acc_req_inv in H1 H2; case: r H1 H2=>//b _ i2_AA.
  exists b.
  by split => //; right.
Admitted.

(* Using resp_to_prepare_req 0 as a 'do nothing' transition for now.
As 0 will never be > 0 so the acceptor won't send a promise *)
Program Definition acceptor_round:
  {(e: nat) (psal: proposal)}, DHT [a, W] 
  (fun i => loc i = st :-> (e, AInit) \/ loc i = st :-> (e, APromised psal),
   fun (_: unit) m => (
     loc m = st :-> (e, AInit) \/
     loc m = st :-> (e, APromised psal) \/
     loc m = st :-> (e, AAccepted psal)
  )) :=
    Do _ (e <-- read_round;
          msg <-- receive_prepare_req_loop e;
          (match msg with
          | Some (cons p_no p_val) => resp_to_prepare_req e p_no
          | _  => resp_to_prepare_req e 0
          end);;
         receive_acc_req_loop e;;
         ret _ _ tt).
         (** ?? I think don't need to respond to accept request as the step_recv
          function in the protocol file handles updating state? *)
Next Obligation.
  admit.
Admitted.


End AcceptorImplementation.
End PaxosAcceptor.

Module Exports.
Section Exports.

Definition acceptor_round := acceptor_round.

End Exports.
End Exports.

End PaxosAcceptor.


Export PaxosAcceptor.Exports.
