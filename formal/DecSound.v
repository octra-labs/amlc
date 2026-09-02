(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Dec.
Require Import DecRel.

Import ListNotations.

Opaque takeb openb closeb.

Theorem checkb_sound : forall gamma term typ row cost next,
  checkb gamma term = Some (typ, row, cost, next) ->
  check gamma term typ row cost next.
Proof.
  intros gamma term.
  revert gamma.
  induction term; intros gamma typ row cost next accepted; cbn in accepted.
  - destruct (ktype v t) eqn:typed.
    + destruct (ktype_sound v t typed) as [scalar value_ty].
      inversion accepted; subst.
      constructor; assumption.
    + discriminate.
  - destruct (bytes_b l) eqn:valid.
    + apply bytes_b_spec in valid.
      inversion accepted; subst.
      apply CBytes.
      exact valid.
    + discriminate.
  - inversion accepted; subst.
    constructor.
  - destruct (takeb n gamma) as [[found_ty found_next] |] eqn:found;
      try discriminate.
    inversion accepted; subst.
    apply CVar.
    eapply takeb_sound.
    exact found.
  - destruct (checkb gamma term1) as [value_out |] eqn:value_run;
      try discriminate.
    destruct value_out as [[[value_ty value_row] value_cost] value_next].
    destruct (ty_eqb value_ty (bty b)) eqn:same_ty; try discriminate.
    apply ty_eqb_eq in same_ty.
    subst value_ty.
    destruct (bmul b) eqn:mode.
    + destruct value_row; try discriminate.
      destruct (ctx_eqb value_next gamma) eqn:same_next; try discriminate.
      apply ctx_eqb_eq in same_next.
      subst value_next.
      destruct (openb b gamma) as [opened |] eqn:open_run; try discriminate.
      destruct (checkb opened term2) as [body_out |] eqn:body_run;
        try discriminate.
      destruct body_out as [[[body_ty body_row] body_cost] prior].
      destruct (closeb b prior) as [final |] eqn:close_run; try discriminate.
      inversion accepted; subst.
      destruct b as [id binder_mode binder_ty].
      cbn in mode.
      subst binder_mode.
      apply CLet0 with (value_cost := value_cost) (opened := opened)
        (prior := prior).
      * apply IHterm1.
        exact value_run.
      * apply openb_sound.
        exact open_run.
      * apply IHterm2.
        exact body_run.
      * apply closeb_sound.
        exact close_run.
    + destruct (openb b value_next) as [opened |] eqn:open_run; try discriminate.
      destruct (checkb opened term2) as [body_out |] eqn:body_run;
        try discriminate.
      destruct body_out as [[[body_ty body_row] body_cost] prior].
      destruct (closeb b prior) as [final |] eqn:close_run; try discriminate.
      inversion accepted; subst.
      destruct b as [id binder_mode binder_ty].
      cbn in mode.
      subst binder_mode.
      apply CLet1 with (mid := value_next) (opened := opened) (prior := prior).
      * apply IHterm1.
        exact value_run.
      * apply openb_sound.
        exact open_run.
      * apply IHterm2.
        exact body_run.
      * apply closeb_sound.
        exact close_run.
    + destruct (openb b value_next) as [opened |] eqn:open_run; try discriminate.
      destruct (checkb opened term2) as [body_out |] eqn:body_run;
        try discriminate.
      destruct body_out as [[[body_ty body_row] body_cost] prior].
      destruct (closeb b prior) as [final |] eqn:close_run; try discriminate.
      inversion accepted; subst.
      destruct b as [id binder_mode binder_ty].
      cbn in mode.
      subst binder_mode.
      apply CLetM with (mid := value_next) (opened := opened) (prior := prior).
      * apply IHterm1.
        exact value_run.
      * apply openb_sound.
        exact open_run.
      * apply IHterm2.
        exact body_run.
      * apply closeb_sound.
        exact close_run.
  - destruct (checkb gamma term1) as [guard_out |] eqn:guard_run.
    + destruct guard_out as [[[guard_ty guard_row] guard_cost] mid].
      destruct (ty_eqb guard_ty TBool) eqn:guard_bool.
      * apply ty_eqb_eq in guard_bool.
        subst guard_ty.
        destruct (checkb mid term2) as [yes_out |] eqn:yes_run.
        -- destruct yes_out as [[[yes_ty yes_row] yes_cost] yes_next].
           destruct (checkb mid term3) as [no_out |] eqn:no_run.
           ++ destruct no_out as [[[no_ty no_row] no_cost] no_next].
              destruct (ty_eqb yes_ty no_ty && ctx_eqb yes_next no_next)
                eqn:branches.
              ** apply andb_true_iff in branches.
                 destruct branches as [same_ty same_next].
                 apply ty_eqb_eq in same_ty.
                 apply ctx_eqb_eq in same_next.
                 subst no_ty no_next.
                 inversion accepted; subst.
                 apply CIf with (mid := mid).
                 --- apply IHterm1.
                     exact guard_run.
                 --- apply IHterm2.
                     exact yes_run.
                 --- apply IHterm3.
                     exact no_run.
              ** discriminate.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (checkb mid term2) as [right_out |] eqn:right_run.
      * destruct right_out as [[[right_ty right_row] right_cost] final].
        inversion accepted; subst.
        apply CPair with (mid := mid).
        -- apply IHterm1.
           exact left_run.
        -- apply IHterm2.
           exact right_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [pair_out |] eqn:pair_run.
    + destruct pair_out as [[[pair_ty pair_row] pair_cost] mid].
      destruct pair_ty; try discriminate.
      destruct (ty_eqb (bty b) pair_ty1 && ty_eqb (bty b0) pair_ty2)
        eqn:binders.
      * apply andb_true_iff in binders.
        destruct binders as [left_ty right_ty].
        apply ty_eqb_eq in left_ty.
        apply ty_eqb_eq in right_ty.
        destruct (openb b mid) as [first |] eqn:left_open.
        -- destruct (openb b0 first) as [second |] eqn:right_open.
           ++ destruct (checkb second term2) as [body_out |] eqn:body_run.
              ** destruct body_out as [[[body_ty body_row] body_cost] prior].
                 destruct (closeb b0 prior) as [last |] eqn:right_close.
                 --- destruct (closeb b last) as [final |] eqn:left_close.
                     +++ inversion accepted; subst.
                         apply CUnpair with (lty := bty b)
                           (rty := bty b0) (mid := mid) (first := first)
                           (second := second) (prior := prior) (last := last).
                         *** apply IHterm1.
                             exact pair_run.
                         *** reflexivity.
                         *** reflexivity.
                         *** apply openb_sound.
                             exact left_open.
                         *** apply openb_sound.
                             exact right_open.
                         *** apply IHterm2.
                             exact body_run.
                         *** apply closeb_sound.
                             exact right_close.
                         *** apply closeb_sound.
                             exact left_close.
                     +++ discriminate.
                 --- discriminate.
              ** discriminate.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [pair_out |] eqn:pair_run.
    + destruct pair_out as [[[pair_ty pair_row] pair_cost] final].
      destruct pair_ty; try discriminate.
      destruct (data_b pair_ty2) eqn:right_data.
      * apply data_b_spec in right_data.
        inversion accepted; subst.
        apply CFst with (right := pair_ty2).
        -- exact right_data.
        -- apply IHterm.
           exact pair_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [pair_out |] eqn:pair_run.
    + destruct pair_out as [[[pair_ty pair_row] pair_cost] final].
      destruct pair_ty; try discriminate.
      destruct (data_b pair_ty1) eqn:left_data.
      * apply data_b_spec in left_data.
        inversion accepted; subst.
        apply CSnd with (left := pair_ty1).
        -- exact left_data.
        -- apply IHterm.
           exact pair_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[left_ty value_row] value_cost] final].
      inversion accepted; subst.
      apply CInl.
      apply IHterm.
      exact value_run.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[right_ty value_row] value_cost] final].
      inversion accepted; subst.
      apply CInr.
      apply IHterm.
      exact value_run.
    + discriminate.
  - destruct (checkb gamma term1) as [value_out |] eqn:value_run.
    + destruct value_out as [[[value_ty value_row] value_cost] mid].
      destruct value_ty; try discriminate.
      destruct (ty_eqb (bty b) value_ty1 && ty_eqb (bty b0) value_ty2)
        eqn:binders.
      * apply andb_true_iff in binders.
        destruct binders as [left_ty right_ty].
        apply ty_eqb_eq in left_ty.
        apply ty_eqb_eq in right_ty.
        destruct (openb b mid) as [left_ctx |] eqn:left_open.
        -- destruct (openb b0 mid) as [right_ctx |] eqn:right_open.
           ++ destruct (checkb left_ctx term2) as [yes_out |] eqn:yes_run.
              ** destruct yes_out as [[[yes_ty yes_row] yes_cost] yes_prior].
                 destruct (checkb right_ctx term3) as [no_out |] eqn:no_run.
                 --- destruct no_out as [[[no_ty no_row] no_cost] no_prior].
                     destruct (closeb b yes_prior) as [yes_next |]
                       eqn:left_close.
                     +++ destruct (closeb b0 no_prior) as [no_next |]
                           eqn:right_close.
                         *** destruct
                               (ty_eqb yes_ty no_ty && ctx_eqb yes_next no_next)
                               eqn:branches.
                             ---- apply andb_true_iff in branches.
                                  destruct branches as [same_ty same_next].
                                  apply ty_eqb_eq in same_ty.
                                  apply ctx_eqb_eq in same_next.
                                  subst no_ty no_next.
                                  inversion accepted; subst.
                                  apply CCase with (lty := bty b)
                                    (rty := bty b0) (mid := mid)
                                    (ly := left_ctx) (ln := right_ctx)
                                    (py := yes_prior) (pn := no_prior).
                                  ++++ apply IHterm1.
                                       exact value_run.
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ apply openb_sound.
                                       exact left_open.
                                  ++++ apply IHterm2.
                                       exact yes_run.
                                  ++++ apply closeb_sound.
                                       exact left_close.
                                  ++++ apply openb_sound.
                                       exact right_open.
                                  ++++ apply IHterm3.
                                       exact no_run.
                                  ++++ apply closeb_sound.
                                       exact right_close.
                             ---- discriminate.
                         *** discriminate.
                     +++ discriminate.
                 --- discriminate.
              ** discriminate.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [body_out |] eqn:body_run.
    + destruct body_out as [[[body_ty body_row] body_cost] final].
      inversion accepted; subst.
      apply CAct.
      apply IHterm.
      exact body_run.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (ty_eqb left_ty TInt) eqn:left_int.
      * apply ty_eqb_eq in left_int.
        subst left_ty.
        destruct (checkb mid term2) as [right_out |] eqn:right_run.
        -- destruct right_out as [[[right_ty right_row] right_cost] final].
           destruct (ty_eqb right_ty TInt) eqn:right_int.
           ++ apply ty_eqb_eq in right_int.
              subst right_ty.
              inversion accepted; subst.
              apply CAdd with (mid := mid).
              ** apply IHterm1.
                 exact left_run.
              ** apply IHterm2.
                 exact right_run.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (ty_eqb left_ty TInt) eqn:left_int.
      * apply ty_eqb_eq in left_int.
        subst left_ty.
        destruct (checkb mid term2) as [right_out |] eqn:right_run.
        -- destruct right_out as [[[right_ty right_row] right_cost] final].
           destruct (ty_eqb right_ty TInt) eqn:right_int.
           ++ apply ty_eqb_eq in right_int.
              subst right_ty.
              inversion accepted; subst.
              apply CSub with (mid := mid).
              ** apply IHterm1.
                 exact left_run.
              ** apply IHterm2.
                 exact right_run.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (ty_eqb left_ty TInt) eqn:left_int.
      * apply ty_eqb_eq in left_int.
        subst left_ty.
        destruct (checkb mid term2) as [right_out |] eqn:right_run.
        -- destruct right_out as [[[right_ty right_row] right_cost] final].
           destruct (ty_eqb right_ty TInt) eqn:right_int.
           ++ apply ty_eqb_eq in right_int.
              subst right_ty.
              inversion accepted; subst.
              apply CMul with (mid := mid).
              ** apply IHterm1.
                 exact left_run.
              ** apply IHterm2.
                 exact right_run.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (ty_eqb left_ty TInt) eqn:left_int.
      * apply ty_eqb_eq in left_int.
        subst left_ty.
        destruct (checkb mid term2) as [right_out |] eqn:right_run.
        -- destruct right_out as [[[right_ty right_row] right_cost] final].
           destruct (ty_eqb right_ty TInt) eqn:right_int.
           ++ apply ty_eqb_eq in right_int.
              subst right_ty.
              inversion accepted; subst.
              apply CDiv with (mid := mid).
              ** apply IHterm1.
                 exact left_run.
              ** apply IHterm2.
                 exact right_run.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (ty_eqb left_ty TInt) eqn:left_int.
      * apply ty_eqb_eq in left_int.
        subst left_ty.
        destruct (checkb mid term2) as [right_out |] eqn:right_run.
        -- destruct right_out as [[[right_ty right_row] right_cost] final].
           destruct (ty_eqb right_ty TInt) eqn:right_int.
           ++ apply ty_eqb_eq in right_int.
              subst right_ty.
              inversion accepted; subst.
              apply CMod with (mid := mid).
              ** apply IHterm1.
                 exact left_run.
              ** apply IHterm2.
                 exact right_run.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[value_ty value_row] value_cost] final].
      destruct (ty_eqb value_ty TInt) eqn:value_int.
      * apply ty_eqb_eq in value_int.
        subst value_ty.
        inversion accepted; subst.
        apply CNeg.
        apply IHterm.
        exact value_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[value_ty value_row] value_cost] final].
      destruct (ty_eqb value_ty TInt) eqn:value_int.
      * apply ty_eqb_eq in value_int.
        subst value_ty.
        inversion accepted; subst.
        apply CAbs.
        apply IHterm.
        exact value_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (ty_eqb t left_ty) eqn:declared_ty.
      * apply ty_eqb_eq in declared_ty.
        subst t.
        destruct (eq_b left_ty) eqn:left_data.
        -- apply eq_b_spec in left_data.
           destruct (checkb mid term2) as [right_out |] eqn:right_run.
           ++ destruct right_out as [[[right_ty right_row] right_cost] final].
              destruct (ty_eqb left_ty right_ty) eqn:same_ty.
              ** apply ty_eqb_eq in same_ty.
                 subst right_ty.
                 inversion accepted; subst.
                 apply CEq with (typ := left_ty) (mid := mid).
                 --- exact left_data.
                 --- apply IHterm1.
                     exact left_run.
                 --- apply IHterm2.
                     exact right_run.
              ** discriminate.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct (ty_eqb left_ty TInt) eqn:left_int.
      * apply ty_eqb_eq in left_int.
        subst left_ty.
        destruct (checkb mid term2) as [right_out |] eqn:right_run.
        -- destruct right_out as [[[right_ty right_row] right_cost] final].
           destruct (ty_eqb right_ty TInt) eqn:right_int.
           ++ apply ty_eqb_eq in right_int.
              subst right_ty.
              inversion accepted; subst.
              eapply CCmp with (mid := mid).
              ** apply IHterm1.
                 exact left_run.
              ** apply IHterm2.
                 exact right_run.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct left_ty; try discriminate.
      destruct (checkb mid term2) as [right_out |] eqn:right_run.
      * destruct right_out as [[[right_ty right_row] right_cost] final].
        destruct right_ty; try discriminate.
        inversion accepted; subst.
        eapply CCat with (mid := mid).
        -- apply IHterm1.
           exact left_run.
        -- apply IHterm2.
           exact right_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[value_ty value_row] value_cost] final].
      destruct value_ty; try discriminate.
      destruct (Nat.leb n n0) eqn:within_len.
      * apply Nat.leb_le in within_len.
        inversion accepted; subst.
        eapply CTake.
        -- exact within_len.
        -- apply IHterm.
           exact value_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[value_ty value_row] value_cost] final].
      destruct value_ty; try discriminate.
      destruct (Nat.leb n n0) eqn:within_len.
      * apply Nat.leb_le in within_len.
        inversion accepted; subst.
        eapply CDrop.
        -- exact within_len.
        -- apply IHterm.
           exact value_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [first_out |] eqn:first_run.
    + destruct first_out as [[[elem first_row] first_cost] mid].
      destruct (checkb mid term2) as [rest_out |] eqn:rest_run.
      * destruct rest_out as [[[rest_ty rest_row] rest_cost] final].
        destruct rest_ty; try discriminate.
        destruct (ty_eqb elem rest_ty) eqn:same_elem.
        -- apply ty_eqb_eq in same_elem.
           subst rest_ty.
           inversion accepted; subst.
           eapply CVcons with (mid := mid).
           ++ apply IHterm1.
              exact first_run.
           ++ apply IHterm2.
              exact rest_run.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [left_out |] eqn:left_run.
    + destruct left_out as [[[left_ty left_row] left_cost] mid].
      destruct left_ty; try discriminate.
      destruct (checkb mid term2) as [right_out |] eqn:right_run.
      * destruct right_out as [[[right_ty right_row] right_cost] final].
        destruct right_ty; try discriminate.
        destruct (ty_eqb left_ty right_ty) eqn:same_elem.
        -- apply ty_eqb_eq in same_elem.
           subst right_ty.
           inversion accepted; subst.
           eapply CVcat with (mid := mid).
           ++ apply IHterm1.
              exact left_run.
           ++ apply IHterm2.
              exact right_run.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[value_ty value_row] value_cost] final].
      destruct value_ty; try discriminate.
      change
        ((if (Nat.ltb n n0 && data_b value_ty) then
            Some (value_ty, value_row, rsucc value_cost, final)
          else None) = Some (typ, row, cost, next)) in accepted.
      destruct (Nat.ltb n n0 && data_b value_ty) eqn:allowed.
      * apply andb_true_iff in allowed.
        destruct allowed as [in_range elem_data].
        apply Nat.ltb_lt in in_range.
        apply data_b_spec in elem_data.
        inversion accepted; subst.
        eapply CAt.
        -- exact in_range.
        -- exact elem_data.
        -- apply IHterm.
           exact value_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [value_out |] eqn:value_run.
    + destruct value_out as [[[value_ty value_row] value_cost] final].
      destruct value_ty; try discriminate.
      destruct n; try discriminate.
      inversion accepted; subst.
      eapply CUncons.
      apply IHterm.
      exact value_run.
    + discriminate.
  - destruct (checkb gamma term1) as [vector_out |] eqn:vector_run.
    + destruct vector_out as [[[vector_ty vector_row] vector_cost] mid].
      destruct vector_ty; try discriminate.
      fold Nat.eqb in accepted.
      destruct (Nat.eqb n n0 && ty_eqb (bty b) vector_ty) eqn:vector_ok.
      * apply andb_true_iff in vector_ok.
        destruct vector_ok as [same_len same_elem].
        apply Nat.eqb_eq in same_len.
        apply ty_eqb_eq in same_elem.
        subst n0 vector_ty.
        destruct (checkb mid term2) as [seed_out |] eqn:seed_run.
        -- destruct seed_out as [[[seed_ty seed_row] seed_cost] outer].
           destruct (ty_eqb (bty b0) seed_ty) eqn:same_seed.
           ++ apply ty_eqb_eq in same_seed.
              subst seed_ty.
              destruct (openb b outer) as [opened_item |] eqn:item_open.
              ** destruct (openb b0 opened_item) as [opened_state |]
                   eqn:state_open.
                 --- destruct (checkb opened_state term3) as [body_out |]
                       eqn:body_run.
                     +++ destruct body_out as
                           [[[body_ty body_row] body_cost] prior].
                         destruct (ty_eqb body_ty (bty b0)) eqn:same_body.
                         *** apply ty_eqb_eq in same_body.
                             subst body_ty.
                             destruct (closeb b0 prior) as [after_state |]
                               eqn:state_close.
                             ---- destruct (closeb b after_state) as [final |]
                                    eqn:item_close.
                                  ++++ destruct (ctx_eqb final outer)
                                         eqn:same_outer.
                                       ***** apply ctx_eqb_eq in same_outer.
                                             subst final.
                                             inversion accepted; subst.
                                             eapply CFold with (mid := mid)
                                               (opened_item := opened_item)
                                               (opened_state := opened_state)
                                               (prior := prior)
                                               (after_state := after_state).
                                             ------ apply IHterm1.
                                                    exact vector_run.
                                             ------ apply IHterm2.
                                                    exact seed_run.
                                             ------ reflexivity.
                                             ------ reflexivity.
                                             ------ apply openb_sound.
                                                    exact item_open.
                                             ------ apply openb_sound.
                                                    exact state_open.
                                             ------ apply IHterm3.
                                                    exact body_run.
                                             ------ apply closeb_sound.
                                                    exact state_close.
                                             ------ apply closeb_sound.
                                                    exact item_close.
                                       ***** discriminate.
                                  ++++ discriminate.
                             ---- discriminate.
                         *** discriminate.
                     +++ discriminate.
                 --- discriminate.
              ** discriminate.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term1) as [cap_out |] eqn:cap_run.
    + destruct cap_out as [[[cap_ty cap_row] cap_cost] mid].
      destruct cap_ty; try discriminate.
      destruct (checkb mid term2) as [value_out |] eqn:value_run.
      * destruct value_out as [[[value_ty value_row] value_cost] final].
        inversion accepted; subst.
        eapply CStep with (mid := mid).
        -- apply IHterm1.
           exact cap_run.
        -- apply IHterm2.
           exact value_run.
      * discriminate.
    + discriminate.
  - destruct (checkb gamma term) as [cap_out |] eqn:cap_run.
    + destruct cap_out as [[[cap_ty cap_row] cap_cost] final].
      destruct cap_ty; try discriminate.
      inversion accepted; subst.
      eapply CClose.
      apply IHterm.
      exact cap_run.
    + discriminate.
Qed.