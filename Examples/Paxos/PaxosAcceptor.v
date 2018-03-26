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
  {(s: StateT)}, DHT [a, W]
  (fun i => loc i = st :-> s,
   fun r m => loc m = st :-> s /\
              exists (pf : coh (getS m)), r = (getSt a pf).1) :=
  Do (act (@skip_action_wrapper W a l paxos (prEq paxos) _
                                (fun s pf => (getSt a pf).1))).
Next Obligation.
  apply: ghC.
  move => s st s_is_st s_in_coh_w.
  apply: act_rule => j R.
  split => [|r k m].
    by case: (rely_coh R).
  case=>/=H1[Cj]Z.
  subst j=>->R'.
  split; first by rewrite (rely_loc' l R') (rely_loc' _ R).
  case: (rely_coh R')=>_; case=>_ _ _ _/(_ l)=>/= pf; rewrite prEq in pf.
  exists pf; move: (rely_loc' l R') =>/sym E'.
  suff X: getSt a (Actions.safe_local (prEq paxos) H1) = getSt a pf by rewrite X.
Admitted.

Program Definition read_state:
  {(s: StateT)}, DHT [a, W]
  (fun i => loc i = st :-> s, 
   fun r m => loc m = st :-> s /\
              exists (pf : coh (getS m)), r = (getSt a pf).2) :=
  Do (act (@skip_action_wrapper W a l paxos (prEq paxos) _
                                (fun s pf => (getSt a pf).2))).
Next Obligation.
  apply: ghC.
  move => s st s_is_st s_in_coh_w.
  apply: act_rule => j R.
  split => [|r k m].
    by case: (rely_coh R).
  case=>/=H1[Cj]Z.
  subst j=>->R'.
  split; first by rewrite (rely_loc' l R') (rely_loc' _ R).
  case: (rely_coh R')=>_; case=>_ _ _ _/(_ l)=>/= pf; rewrite prEq in pf.
  exists pf; move: (rely_loc' l R') =>/sym E'.
  suff X: getSt a (Actions.safe_local (prEq paxos) H1) = getSt a pf by rewrite X.
(*   by apply: (getStE pf _ E').  *)
(* Qed. *)
Admitted.

(* Step 1: Receive prepare req *)

(* Ending condition *)
Definition r_prepare_req_cond (res : option proposal) := res == None.

(* Invariant relates the argument and the shape of the state *)
Definition r_prepare_req_inv (e : nat) (pinit: proposal): cont (option proposal) :=
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
    rewrite /step_recv.
    (* execute getSt i2 on E1 to get only AInit after which easy *)
    (* rewrite /(getS i2). *)
    case getSt.
    move => n r.
    case r.
    move => p.
    rewrite /mkLocal.
    (* How do I finish this? I need to execute getSt *)
  admit.
Admitted.
Next Obligation.
  (* Can't apply ghC as no Hoare Type *)
  admit.
Admitted.

(* Finds the promised number from current state *)
Definition read_promised_number (rs: RoleState): nat :=
  match rs with
  | APromised psal => head 0 psal
  | _ => 0
  end.

Definition read_promised_value (rs: RoleState): nat :=
  match rs with
  | APromised psal => last 0 psal
  | _ => 0
  end.

(* Step 2: Respond promise or nack to the proposer *)
Program Definition resp_to_prepare_req (e: nat) (prepare_no: nat)
  (promised_no: nat) (promised_val: nat):
  {(pif: (proposal * proposal))}, DHT [a, W]
   (fun i => loc i = st :-> (e, APromised pif.1) \/ loc i = st :-> (e, AInit),
    fun (_ : seq nat) m =>
      if head 0 pif.2 > head 0 pif.1
      then loc m = st :-> (e, APromised pif.2)
      else loc m = st :-> (e, APromised pif.1))
  := Do (rs <-- read_state;
         if prepare_no > promised_no
         then send_promise_resp [:: promised_no; promised_val] prepare_no
         else send_nack_resp [:: 0; 0] prepare_no).
Next Obligation.
  apply:ghC=>i [pinit pfinal]E1 C1.
  have Pre: forall i2 proposer_id, network_rely W a i i2 ->
          Actions.send_act_safe W (p:=paxos) a l
          (if prepare_no > promised_no
           then (
               send_promise_resp_trans proposers acceptors
           )
           else (
               send_nack_resp_trans proposers acceptors
          )) [:: e] proposer_id i2.
  - move=>i2 pid R1.
    split; first by case: (rely_coh R1).
    case: (proj2 (rely_coh R1))=>_ _ _ _/(_ l); rewrite (prEq paxos)=>C.

    case: prepare_no promised_no. split=>//.
    admit. (* write Hin *)
    admit.
    admit. (* write Hin *)
    admit.
    (* Need inE to work *)
    (* + rewrite /Actions.can_send /nodes inE/= mem_cat Hpin orbC. *)
    (* by rewrite -(cohD (proj2 (rely_coh R1)))/ddom gen_domPt inE/= eqxx. *)
    by rewrite /Actions.filter_hooks um_filt0=>???/sym/find_some; rewrite dom0 inE.
    admit.
Admitted.


(* Ending condition *)
Definition r_acc_req_cond (res : option proposal) := res == None.

(* Invariant relates the argument and the shape of the state *)
Definition r_acc_req_inv (e : nat) (promised: bool) (psal: proposal): cont (option proposal) :=
  fun res i =>
    if res is Some psal
    then loc i = st :-> (e, AAccepted psal)
    else if promised
         then loc i = st :-> (e, APromised psal)
         else loc i = st :-> (e, AInit).

(* Loops until it receives a accept req *)
Program Definition receive_acc_req_loop (e : nat) (promised: bool):
  {(pinit: proposal)}, DHT [a, W]
   (fun i => if promised
             then loc i = st :-> (e, APromised pinit)
             else loc i = st :-> (e, AInit),
  fun res m => exists psal, res = Some psal /\ (
    loc m = st :-> (e, APromised psal) \/
    loc m = st :-> (e, AAccepted psal)
  )) :=
  Do _ (@while a W _ _ r_acc_req_cond (r_acc_req_inv e promised) _
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
  admit.
  apply: ret_rule=>//i5 R4.
  - rewrite /r_acc_req_inv (rely_loc' _ R4) (rely_loc' _ R) locE//=.
    rewrite -(rely_loc' _ R1) in E1.
    rewrite D.
    rewrite/step_recv/=.
    rewrite /r_step.
    rewrite /step_recv/=.
Admitted.
Next Obligation.
  apply: ghC=>i1 psal E1 C1/=.
  apply: (gh_ex (g := psal)); apply: call_rule => //r i2 [H1]H2 C2.
  rewrite /r_acc_req_cond/r_acc_req_inv in H1 H2; case: r H1 H2=>//b _ i2_AA.
  exists b.
  by split => //; right.
Qed.

(* Using resp_to_prepare_req 0 as a 'do nothing' transition for now.
As 0 will never be > 0 so the acceptor won't send a promise *)
Program Definition acceptor_round:
  {(ep: nat * proposal)}, DHT [a, W] 
  (fun i => loc i = st :-> (ep.1, AInit),
   fun (_: unit) m => (
     loc m = st :-> (ep.1, AInit) \/
     loc m = st :-> (ep.1, APromised ep.2) \/
     loc m = st :-> (ep.1, AAccepted ep.2)
  )) :=
     Do _ (e <-- read_round;
          (* need to read state here as once it receives the message, 
             it already changes state *)
          rs <-- read_state;
          msg <-- receive_prepare_req_loop e;
          (match msg with
           | Some body =>
             let: prepare_no := head 0 body in
             let: promised_no := read_promised_number rs in
             let: promised_val := read_promised_value rs in
             resp_to_prepare_req e prepare_no promised_no promised_val
           | _  => resp_to_prepare_req e 0 0 0 (* results in sending nack *)
          end);;
         rs <-- read_state;
         (match rs with
         | APromised _ => receive_acc_req_loop e true
         | _  => receive_acc_req_loop e false
         end);;
         ret _ _ tt).
Next Obligation.
  apply: ghC => i1[e psal]/=E1 C1; apply: step.
  apply: (gh_ex (g:=(e, AInit))); apply: call_rule=>//e' i2 [E2][pf]->C2.
  apply: step.
  apply: (gh_ex (g:=(e, AInit))). apply: call_rule=>//??[?]??.
  apply: step.
  apply: call_rule; last first.
  move=>x? _ _. case: x=>a'. apply: step.
  apply: (gh_ex (g:=([::], [::]))). apply: call_rule; last first.
  move=>?? _ _. apply: step.
  apply: (gh_ex (g:=(e, AInit))). apply: call_rule; last first.
  move=>y ? _ _.
  case: y=>//.
  
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
