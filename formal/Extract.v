(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatBigInt.
From Stdlib Require Import ExtrOcamlZBigInt.
From Stdlib Require Import NArith.Nnat.
From Stdlib Require Import ZArith.ZArith.

Require Import Uni.
Require Import Dec.
Require Import Lim.
Require Import Bin.
Require Import Ser.
Require Import Low.
Require Import Fin.
Require Import Fun.
Require Import Law.
Require Import Spec.
Require Import Poly.
Require Import Data.
Require Import Rec.
Require Import Quant.
Require Import Weave.
Require Import Braid.
Require Import Loom.
Require Import Orbit.
Require Import Wake.
Require Import Rift.
Require Import Idx.
Require Import Raw.
Require Import Perm.
Require Import Fhe.
Require Import Hop.
Require Import Param.
Require Import Fp.
Require Import Crypt.
Require Import Hfhe.
Require Import Graph.
Require Import Ent.
Require Import Hpar.
Require Import Sess.
Require Import Sbin.
Require Import Pbin.
Require Import Rule.
Require Import Prof.
Require Import Text.
Require Import Lex.
Require Import Sha.
Require Import Root.
Require Import Host.
Require Import Effect.
Require Import Turn.
Require Import Proj.
Require Import Pimg.
Require Import Pack.
Require Import Cert.
Require Import Scert.
Require Import Read.
Require Import Comp.
Require Import Src.
Require Import Seal.
Require Import Emit.
Require Import Feed.
Require Import Rval.
Require Import Trace.
Require Import Mach.
Require Import Smap.
Require Import Live.
Require Import Path.
Require Import Folio.
Require Import Dbg.
Require Import Dbin.

Extraction Language OCaml.
Set Extraction Output Directory ".".
Extract Inductive comparison => "[ `CEq | `CLt | `CGt ]"
  ["`CEq" "`CLt" "`CGt"].
Extract Constant Nat.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant N.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Pos.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Pos.compare_cont =>
  "(fun c x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then c else if s < 0 then `CLt else `CGt)".
Extract Constant Z.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Init.Nat.eqb => "Big_int_Z.eq_big_int".
Extract Constant Nat.eqb => "Big_int_Z.eq_big_int".
Extract Constant BinNat.N.of_nat => "(fun value -> value)".
Extract Constant BinNat.N.to_nat => "(fun value -> value)".
Extraction "uni_model.ml"
  Lim.lim Lim.acceptb Lim.runb
  Ser.enc_ty Ser.dec_ty
  Ser.enc_value Ser.dec_value
  Ser.enc_row Ser.dec_row
  Ser.enc_res Ser.dec_res
  Ser.enc_snap Ser.dec_snap
  Fin.fin_nodes Fin.fin_depth Fin.fin_fit Fin.fin_valid
  Low.low Low.scheck Low.prog Low.pcheck
  Fun.capm Fun.fcheckb Fun.fprog Fun.fpcheck
  Law.law_b Law.laws_b Law.lhold Law.lholds
  Spec.ifn_b Spec.fspec Spec.fspec_check
  Poly.pfn_b Poly.pvals Poly.ysub Poly.ifsub Poly.pspec
  Data.tagt Data.dtype_t Data.decl_b Data.arms_b Data.make Data.dcase Data.dprog
  Data.dpcheck
  Rec.prodt Rec.rtype_t Rec.rdecl_b Rec.items_b Rec.picks_b Rec.rmake Rec.rsplit
  Rec.rprog Rec.rpcheck
  Quant.qterm Quant.qcheck
  Weave.wvals Weave.wvec Weave.wbody Weave.wterm Weave.wcheck
  Braid.bvals Braid.bvec Braid.bbody Braid.bclear Braid.bterm Braid.bcheck
  Loom.lvals Loom.lvec Loom.lbody Loom.lterm Loom.lcheck
  Orbit.oval Orbit.obody Orbit.oterm Orbit.ocheck
  Wake.kval Wake.kout Wake.kdepth Wake.kbody Wake.kterm Wake.kcheck
  Rift.rift_make Rift.rift_check
  Idx.ienv_b Idx.ix_b Idx.ieval Idx.iput Idx.ity_b Idx.yelab Idx.isame Idx.ile
  Idx.ihold
  Raw.rb_elab Raw.relab
  Perm.phas Perm.ple Perm.pmeet Perm.pcut Perm.pset_b Perm.prow Perm.ppcheck.

Extraction "pbin_model.ml"
  Pbin.prog_b Pbin.enc_prog Pbin.dec_prog.

Extraction "fhe_model.ml"
  Fhe.profile_b Fhe.env_b Fhe.ftm_b Fhe.ftrim Fhe.fadd Fhe.fmul Fhe.fre
  Fhe.frun Fhe.fcheck
  Param.catalog_b Param.psel Param.params.

Extraction "hop_model.ml"
  Hop.hty Hop.herase Hop.hval Hop.hem Hop.lower.

Extraction "crypt_model.ml"
  Fp.p Fp.norm Fp.valid Fp.add Fp.mul
  Crypt.cenv_b Crypt.plain Crypt.ctrim Crypt.cadd Crypt.cmul Crypt.cre
  Crypt.crun Crypt.exec.

Extraction "hfhe_model.ml"
  Hfhe.prod Hfhe.prod_cert Hfhe.hadm_b Hfhe.hcert_b Hfhe.hshape_b
  Hfhe.henv_b Hfhe.hadd Hfhe.hmul Hfhe.hre Hfhe.hrun Hfhe.hcheck.

Extraction "graph_model.ml"
  Graph.fprime Graph.cfg_b Graph.graph_b Graph.merge Graph.compact Graph.norm.

Extract Constant Z.of_nat => "(fun value -> value)".
Extraction "ent_model.ml"
  Ent.prod Ent.prof_b Ent.den Ent.scale Ent.build Ent.plan Ent.mode Ent.bind
  Ent.bind_at.

Extraction "hpar_model.ml"
  Hpar.prod_set Hpar.prod_cat Hpar.hset_b Hpar.seal Hpar.hcatalog_b Hpar.hsel
  Hpar.caps Hpar.bind_b Hpar.bind Hpar.check Hpar.check_cat.

Extraction "sess_model.ml"
  Sess.scope_eqb Sess.scope_b Sess.entry_lt Sess.entries_b Sess.view_b
  Sess.entry_get Sess.realize Sess.start Sess.current Sess.put Sess.bump
  Sess.issue Sess.take Sbin.tok_b Sbin.enc_scope Sbin.dec_scope Sbin.enc_tok
  Sbin.dec_tok Sbin.enc_view Sbin.dec_view.

Extraction "rule_model.ml"
  Rule.local Rule.limits_b Rule.limits_eqb Rule.rid_vals Rule.rid_eqb
  Rule.rule_b Rule.schedule_b Rule.active Rule.newer Rule.rsel
  Rule.supported Rule.rcheck Rule.rrun.

Extraction "cert_model.ml"
  Cert.row_norm Cert.enc_cert Cert.dec_cert Cert.issue Cert.verifyb.

Extraction "scert_model.ml"
  Low.low Low.prog Low.pcheck Scert.sissue Scert.sverifyb.

From Stdlib Require Import ExtrOcamlString.
Extract Constant Nat.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant N.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Pos.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Pos.compare_cont =>
  "(fun c x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then c else if s < 0 then `CLt else `CGt)".
Extract Constant Z.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Init.Nat.eqb => "Big_int_Z.eq_big_int".
Extract Constant Nat.eqb => "Big_int_Z.eq_big_int".
Extraction "read_model.ml"
  Read.pix_add Read.pty Read.pbind Read.pread Read.bopen Read.read
  Comp.run Comp.load Src.source Src.compile.

Extraction "seal_model.ml"
  Seal.dec_artifact Seal.source_seal Seal.source_acceptb.

Extraction "text_model.ml"
  Text.tok_beq Text.take Text.parse Text.accept.

Extraction "lex_model.ml" Lex.scan.

Extraction "sha_model.ml" Sha.hash.

Extraction "root_model.ml" Root.image Root.root.

Extraction "turn_model.ml"
  Host.typed Host.shape Host.load Host.caps Host.cap
  Turn.verify Turn.turn.

Extraction "proj_model.ml"
  Proj.path_b Proj.name_b Proj.body_b Proj.deps_b Proj.src_b Proj.srcs_b
  Proj.src_names Proj.root_b Proj.roots_b Proj.src_size Proj.srcs_size
  Proj.root_size Proj.roots_size Proj.rid_b Proj.target_b Proj.proj_b
  Proj.ext Proj.out Proj.outputs.

Extraction "pimg_model.ml"
  Pimg.image_b Pimg.enc_proj Pimg.dec_proj.

Extraction "pack_model.ml"
  Pack.src_at Pack.source_b Pack.root_b Pack.item_at Pack.plan_at Pack.plan.

Extraction "emit_model.ml"
  Emit.octet_b Emit.lty Emit.lit_of Emit.emit Emit.source_emit.

Extraction "effect_model.ml" Effect.traceb Effect.sealed_plan.

Extraction "feed_model.ml"
  Feed.feed_b Feed.feed_fit Feed.enc_feed Feed.dec_feed
  Feed.load Feed.term_of Feed.sub_of Feed.close.

Extraction "rval_model.ml"
  Rval.plain_b Rval.root_b Rval.rval_b Rval.rval_fit
  Rval.enc_rval Rval.dec_rval.

Extraction "trace_model.ml"
  Trace.nats_eqb Trace.lit_eqb Trace.advance Trace.replay Trace.trace
  Trace.source_trace.

Extraction "mach_model.ml"
  Mach.into Mach.lower Mach.take Mach.openm Mach.closem Mach.size Mach.exec
  Mach.open_inputs Mach.terminal Mach.replay_plan Mach.replay
  Mach.replay_plan_in Mach.replay_in Mach.image_code Mach.image_feed_code
  Mach.source_open_code
  Mach.image_plan_code Mach.source_code Mach.source_feed_code
  Mach.source_plan_code Live.scan Live.analyze.

Extraction "smap_model.ml"
  Smap.map_b Smap.map_fit Smap.enc_map Smap.dec_map.

Extraction "live_model.ml"
  Live.slot_b Live.row_b Live.live_b Live.live_fit Live.enc_live Live.dec_live.

Extraction "path_model.ml"
  Path.kinds Path.plan Path.join Path.make Path.make_feed Path.replay.

Extraction "folio_model.ml"
  Folio.src_at Folio.octets Folio.feed_at Folio.origin_one Folio.origins_at
  Folio.origins Folio.origin_b Folio.part_b Folio.parts_b Folio.shape_b
  Folio.folio_fit Folio.enc_folio Folio.dec_folio.

Extraction "dbg_model.ml"
  Dbg.hit_b Dbg.hits_b Dbg.decide Dbg.check.

Extraction "dbin_model.ml"
  Dbin.hex_b Dbin.digest_b Dbin.stop_b Dbin.stop_lt Dbin.stops_lt
  Dbin.stops_b Dbin.dlit_b Dbin.expect_b Dbin.cfg_b Dbin.dstate_b
  Dbin.dstate_fit Dbin.enc_dstate Dbin.dec_dstate.