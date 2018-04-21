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
Variables (proposers: seq nid) (acceptors: seq nid).
Variable p: nid.

Hypothesis AcceptorsNonEmpty : acceptors != [::].

Check PaxosProtocol.

Definition paxos := PaxosProtocol proposers acceptors l.
Notation W := (mkWorld paxos).

Section ProposerImplementation.

(************** Atomic actions **************)

(* Two send-actions, e -- id of the current era *)
Program Definition send_prepare_req psal to :=
  act (@send_action_wrapper W paxos p l (prEq paxos)
       (send_prepare_req_trans proposers acceptors) _ psal to).
Next Obligation.
  by rewrite InE; do![left|right].
Qed.

Program Definition send_accept_req psal to :=
  act (@send_action_wrapper W paxos p l (prEq paxos)
       (send_accept_req_trans proposers acceptors) _ psal to).
Next Obligation.
  by rewrite !InE; right; left.
Qed.


(* Two receive-actions *)
Program Definition tryrecv_prepare_resp := act (@tryrecv_action_wrapper W p
      (* filter *)
      (fun k _ t b => (k == l) && ((t == promise_resp) || (t == nack_resp))) _).
Next Obligation.
  by case/andP: H=>/eqP->_; rewrite /ddom gen_domPt inE/=.
Qed.


(************** Proposer code **************)

(*** Reading internal state ***)
Implicit Arguments PaxosProtocol.PaxosCoh [proposers acceptors].
Notation coh := (@PaxosProtocol.PaxosCoh proposers acceptors).
Notation getS s := (getStatelet s l).
Notation loc i := (getLocal p (getStatelet i l)).

Export PaxosProtocol.

Program Definition read_round:
  {(s: StateT)}, DHT [p, W]
  (fun i => loc i = st :-> s,
   fun r m => loc m = st :-> s /\
              exists (pf : coh (getS m)), r = (getSt p pf).1) :=
  Do (act (@skip_action_wrapper W p l paxos (prEq paxos) _
                                (fun s pf => (getSt p pf).1))).
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
  suff X: getSt p (Actions.safe_local (prEq paxos) H1) = getSt p pf by rewrite X. 
  by apply: (getStE' pf _ E').
Qed.

(*******************************************)
(***   Sending out proposals in a loop   ***)
(*******************************************)

Definition send_prepare_req_loop_spec (e : nat) := forall to_send,
  {(pinit: proposal)}, DHT [p, W]
  (fun i =>
     loc i = st :-> (e, PInit pinit) /\
     (perm_eq acceptors to_send \/
     if to_send == [::]
     then loc i = st :-> (e, PWaitPrepResp [::] pinit)
     else exists (acptrs : seq nid),
         loc i = st :-> (e, PSentPrep acptrs pinit) /\
         perm_eq acceptors (acptrs ++ to_send)),
     fun r m => r = tt /\ loc m = st :-> (e, PWaitPrepResp [::] pinit)).

Program Definition send_prepare_req_loop e (psal: proposal):
  {(pinit: proposal)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PInit pinit),
   fun r m => r = tt /\
              loc m = st :-> (e, PWaitPrepResp [::] pinit)) :=
  Do (ffix (fun (rec : send_prepare_req_loop_spec e) to_send =>
              Do (match to_send with
                  | to :: tos => send_prepare_req psal to ;; rec tos
                  | [::] => ret _ _ tt
                  end)) acceptors).
Next Obligation.
  apply: ghC => i1 p'.
  case=>[[E1 P1 C1]].
  case: (to_send)=>[|x xs]; last first.
  apply: step; apply: act_rule => j1 R1/=; split=>[|r k m[Sf]St R2].
  split=>//=; first by case: (rely_coh R1).
  rewrite /node_safe.
  split.
  split.
  admit. (* what does p \in nodes proposers acceptors mean? *)
  admit.
  split.
  admit. (* again Hin *)
  rewrite /send_prepare_req_prec.
  admit. (* Where do I get coherence from *)
  (* because of inE *)
  (* + rewrite /Actions.can_send /nodes inE eqxx andbC/=. *)
  (*   by rewrite -(cohD (proj2 (rely_coh R1)))/ddom gen_domPt inE/=. *)
  admit.
  by rewrite /Actions.filter_hooks um_filt0=>???/sym/find_some; rewrite dom0 inE.
Admitted.
Next Obligation.
  apply:ghC=>i lg E1 _; apply: (gh_ex (g:=lg)).
  apply: call_rule=>C1. split => //. by left. done.
Qed.

(*******************************************)
(*** Receiving responses to the proposal ***)
(*******************************************)

(* Ending condition *)
Definition rc_prepare_resp_cond (recv_promises : promises) :=
  ~~ perm_eq (map fst' recv_promises) acceptors.

(* Invariant relates the argument and the shape of the state *)
Definition rc_prepare_resp_inv (e : nat) (psal: proposal): cont (promises) :=
  fun acc i => loc i = st :-> (e, PWaitPrepResp acc psal).

Program Definition receive_prepare_resp_loop (e : nat):
  {(pinit : proposal)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PWaitPrepResp [::] pinit),
   fun res m =>
       loc m = st :-> (e, PWaitPrepResp res pinit) /\
       (perm_eq (map fst' res) acceptors))
  :=
  Do _ (@while p W _ _ rc_prepare_resp_cond (rc_prepare_resp_inv e) _
        (fun recv_promises => Do _ (
           r <-- tryrecv_prepare_resp;
           match r with
           | Some (from, tg, body) =>
             if (from \in acceptors) && (from \notin (map fst' recv_promises))
             then ret _ _ ((from, tg == promise_resp, body) :: recv_promises)
             else ret _ _ recv_promises
           | None => ret _ _ recv_promises
           end
        )) [::]).
Next Obligation.
  by apply: with_spec x.
Defined.
Next Obligation.
  by move:H; rewrite /rc_prepare_resp_inv (rely_loc' _ H0).
Qed.
Next Obligation.
  move => i [psal] /= [H1 I1].
  apply: step.
  apply: act_rule=>j R1/=; split; first by case: (rely_coh R1).
  case=>[[[from tg] body] k m|k m]; last first.
  - case=>Sf []Cj[]H; last by case: H=>[?][?][?][?][?][?][].
    have E: k = j by case: H.
    move: H. subst k=>_ R2. apply: ret_rule.
    move => m' R3.
    move => x [] cond.
    rewrite /rc_prepare_resp_inv.
    by rewrite -(rely_loc' _ R1)-(rely_loc' _ R2)-(rely_loc' _ R3).
  case=>Sf []Cj[]=>[|[l'][mid][tms][from'][rt][pf][][E]Hin E1 Hw/=]; first by case.
  case/andP=>/eqP Z G->{k}[]Z1 Z2 Z3 R2; subst l' from' tg body.
  move: rt pf (coh_s (w:=W) l (s:=j) Cj) Hin R2 E1 Hw G E; rewrite prEq/=.
  move=>rt pf Cj' Hin R E1 Hw G E.
  have D: rt = receive_prepare_req_trans _ _.
  - case: Hin G=>/=; first by intuition.
Admitted.
Next Obligation.
  apply: ghC=>i pinit E1 C1.
  have Pre: rc_prepare_resp_inv e pinit [::] i by rewrite /rc_prepare_resp_inv/= E1.
  apply: call_rule'=>[|acc m]; first by exists pinit.
  case/(_ pinit Pre)=>/=H1 H2 Cm; split=>//;  by move/negbNE: H1.
Qed.

Definition read_res (st : StateT) :=
  let: (_, rs) := st in
  match rs with
  | PWaitPrepResp res _ => res
  | _ => [::]
  end.

(*******************************************)
(***    Sending accept requests          ***)
(*******************************************)

Definition send_accept_req_loop_spec (e : nat) psal := forall to_send,
  {(pinit: proposal)}, DHT [p, W]
  (fun i =>
     (exists res,
         [/\ loc i = st :-> (e, PWaitPrepResp res pinit),
         to_send = acceptors &
         perm_eq (map fst' res) acceptors]) \/
      if to_send == [::]
      then loc i = st :-> (e, PAbort)
      else exists (acptrs : seq nid),
        loc i = st :-> (e, PSentAccReq acptrs psal) /\
        perm_eq acceptors (acptrs ++ to_send),
   fun (r : unit) m => loc m = st :-> (e, PAbort)).
   (* Aborts after sending all accept requests *)

Program Definition send_accept_req_loop e psal: send_accept_req_loop_spec e psal :=
  fun to_send  =>
    Do (fix rec to_send :=
          (match to_send with
           | to :: tos => send_accept_req psal to ;; rec tos
           | [::] => ret _ _ tt
           end)) to_send.
Next Obligation.
  apply: ghC=>s1 psal' E1 C1; elim: to_send s1 E1 C1=>//=.
  - move=>s1; case; first by case=>?[]_ Z; rewrite -Z in (AcceptorsNonEmpty).
    move => E1 _. apply: ret_rule=>i2 R. by rewrite (rely_loc' _ R).
  move=>to tos Hi s1 H C1.
  apply: step; apply: act_rule=>s2 R2/=.
  have Pre: Actions.send_act_safe W (p:=paxos) p l
          (send_accept_req_trans proposers acceptors) [:: e] to s2.
  - split; [by case: (rely_coh R2) | | |]; last first.
    + by rewrite /Actions.filter_hooks um_filt0=>???/sym/find_some; rewrite dom0 inE.
    (* Because of inE *)
    (* + rewrite /Actions.can_send /nodes inE eqxx andbC/=. *)
    (*     by rewrite -(cohD (proj2 (rely_coh R2)))/ddom gen_domPt inE/=. *)
      admit.
    case: (proj2 (rely_coh R2))=>_ _ _ _/(_ l); rewrite prEq=>C; split.
    (* Because of inE *)  
    (* + split=>//; case: H; first by case=>?[_]<-; rewrite inE eqxx. *)
    (*     by case=>ps[_]/perm_eq_mem->; rewrite mem_cat orbC inE eqxx.   *)
    admit.
  split.
  admit. (* Because of Hin *)
  admit. (* Don't know why this doesn't work *)


  (* Postcondition *)
  split => //.
  admit. (* Actions.send_act_safe *)
  move => body i3 i4[Sf]/=St R3.
  apply: Hi; last by case: (rely_coh R3).
  right; rewrite (rely_loc' _ R3).
  admit.
Admitted.

Program Definition send_accept_reqs e psal:
  {(pinit: proposal)}, DHT [p, W]
  (fun i => exists recv_promises,
         [/\ loc i = st :-> (e, PWaitPrepResp recv_promises pinit) &
          perm_eq (map fst' recv_promises) acceptors],
   fun (r : unit) m => loc m = st :-> (e, PAbort))
  := Do (send_accept_req_loop e psal acceptors).
Next Obligation.
  apply: ghC=>i lg[res][H1]H2 H3 C; apply: (gh_ex (g:=lg)).
  apply: call_rule=>//; first by move=>_; left; exists res.
  done.
Qed.

(*****************************************************)
(*      Full Proposer Implementation                 *)
(*****************************************************)
Search _ (?X :-> _ = ?X :-> _).
(* This is only ment to be run once for each proposer *)
Program Definition proposer_round (p_init: proposal):
  {(psal: proposal) (e : nat)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PInit psal),
   fun (_: unit) m => loc m = st :-> (e, PAbort))
  :=
  Do (e <-- read_round;
      send_prepare_req_loop e p_init;;
      recv_promises <-- receive_prepare_resp_loop e;
      send_accept_reqs e (create_proposal_for_acc_req recv_promises p_init);;
      ret _ _ tt).
Next Obligation.
  move=>s0/=[psal [e]] E0. apply: step.
  apply: (gh_ex (g := (e, PInit psal))).
  apply: call_rule=>//e' s1 [E1][pf]->C1.
Admitted.

End ProposerImplementation.
End PaxosProposer.

Module Exports.
Section Exports.

Definition proposer_round := proposer_round.

End Exports.
End Exports.

End PaxosProposer.

Export PaxosProposer.Exports.
