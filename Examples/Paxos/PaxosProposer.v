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

(* Hypothesis AcptrsNonEmpty : acceptors != [::]. *)
(* Hypothesis HPin: p \in proposers. *)

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
(* ?? not sure if to use p or proposers *)
Notation loc i := (getLocal p (getStatelet i l)).

Export PaxosProtocol.
Check act_rule.
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
  apply: act_rule.
  admit.
Admitted.

(*******************************************)
(***   Sending out proposals in a loop   ***)
(*******************************************)

(* ?? What's the difference between using forall here instead of just using the
Hoare spec to universally quantify over to_send? *)
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
  apply: step.
  apply: act_rule.
  (* - case: to_send P1=>[|to tos Hp]. *)
  (* case => s_init. *)
  
  (* case => tosend_eq_acc s_in_coh_w. *)
  
  (* - case: to_send tosend_eq_acc. *)
  (*   (* + by move/perm_eq_size=>/=/size0nil=>Z; rewrite Z in (AcptrsNonEmpty). *) *)
  (* - move => to tos perm_eq_acptrs. *)
  (*   apply: step. *)
  (*   apply: act_rule => j1 R1 /=. split=>[|r k m[Sf]St R2]. *)
  (*   split=>//=; first by case: (rely_coh R1). *)
  (*   split. *)
  (*   split. *)
  (*   (* + split; first by split=>//; move/perm_eq_mem: perm_eq_acptrs->; rewrite inE eqxx. *) *)
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.

(*******************************************)
(*** Receiving responses to the proposal ***)
(*******************************************)

(* TODO: Need to ensure ending condition and invariant are such that the loop ends only when ALL the responses have been received *)
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
             (* TODO: need to check if received msg is for this round
               might need to change proposal to be like [e, p_no, p_val] *)
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
  (* - case: Hin G=>/=; first by intuition. *)
  (*   case.  *)
  (*     by intuition. *)
  admit.
  admit.
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

(* Reading the accumulated responses from the state *)
Program Definition check_promises recv_promises :
  {(e : nat) (pinit : proposal) res}, DHT [p, W]
  (fun i => loc i = st :-> (e, PWaitPrepResp res pinit),
   fun _ m => loc m = st :-> (e, PWaitPrepResp res pinit)):=
  Do (ret _ _ (
            (perm_eq (map fst' recv_promises) acceptors) &&
            (all (fun i => i) (map snd' recv_promises))
     )).
Next Obligation.
  admit.
Admitted.

(*******************************************)
(***    Sending accept requests          ***)
(*******************************************)

Definition send_accept_req_loop_spec (e : nat) psal := forall to_send,
  {(pinit: proposal)}, DHT [p, W]
  (fun i =>
     (exists res,
         [/\ loc i = st :-> (e, PWaitPrepResp res pinit),
          to_send = acceptors, perm_eq (map fst' res) acceptors &
          all id (map snd' res)]) \/
      if to_send == [::]
      then loc i = st :-> (e, PSentAccReq [::] psal)
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
  admit.
Admitted.

(** ?? Should this pinit be universally quantified or should it be in the exists
cluase? *)
Program Definition send_accept_reqs e psal:
  {(pinit: proposal)}, DHT [p, W]
  (fun i => exists recv_promises,
         [/\ loc i = st :-> (e, PWaitPrepResp recv_promises pinit),
          perm_eq (map fst' recv_promises) acceptors &
          all id (map snd' recv_promises)],
   fun (r : unit) m => loc m = st :-> (e, PSentAccReq [::] pinit))
  := Do (send_accept_req_loop e psal acceptors).
Next Obligation.
  admit.
Admitted.

(*****************************************************)
(*      Full Proposer Implementation                 *)
(*****************************************************)


(* This is only ment to be run once for each proposer
   TODO: change receive_prepare_resp_loop to get all responses and only then
         return otherwise, it'll return after getting one resp.
         Just need to change its invariant.
*)
Program Definition proposer_round (psal: proposal):
  {(e : nat)}, DHT [p, W]
  (fun i => loc i = st :-> (e, PInit psal),
   fun res m => loc m = st :-> (e.+1, PAbort))
  :=
  Do (e <-- read_round;
      send_prepare_req_loop e psal;;
      recv_promises <-- receive_prepare_resp_loop e;
      check <-- check_promises recv_promises;
      if check
      then send_accept_reqs e (choose_highest_numbered_proposal psal recv_promises)
      else send_accept_reqs e [:: 0; 0]).
     (* If check fails then send an acc_req for (0, 0) which will never be
        accepted by any acceptor *)
Next Obligation.
  move=>s0/=[e]E0; apply: step.
  apply: (gh_ex (g := (e, PInit psal))).
  apply: call_rule=>//e' s1 [E1][pf]->C1.
  admit.
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
