(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import NArith.

Import ListNotations.

Definition word := N.
Definition modulus : N := 4294967296.
Definition mask : N := 4294967295.

Definition norm (value : word) : word := N.modulo value modulus.

Definition add2 (left right : word) : word := norm ((left + right)%N).
Definition add4 (a b c d : word) : word := add2 (add2 a b) (add2 c d).
Definition add5 (a b c d e : word) : word := add2 (add4 a b c d) e.

Definition rotr (value : word) (count : nat) : word :=
  norm (N.lor
    (N.shiftr value (N.of_nat count))
    (N.shiftl value (N.of_nat (32 - count)))).

Definition shr (value : word) (count : nat) : word :=
  N.shiftr value (N.of_nat count).

Definition bxor3 (a b c : word) : word := N.lxor a (N.lxor b c).

Definition choose (x y z : word) : word :=
  N.lxor (N.land x y) (N.land (N.lxor x mask) z).

Definition major (x y z : word) : word :=
  bxor3 (N.land x y) (N.land x z) (N.land y z).

Definition sum0 (value : word) : word :=
  bxor3 (rotr value 2) (rotr value 13) (rotr value 22).

Definition sum1 (value : word) : word :=
  bxor3 (rotr value 6) (rotr value 11) (rotr value 25).

Definition sig0 (value : word) : word :=
  bxor3 (rotr value 7) (rotr value 18) (shr value 3).

Definition sig1 (value : word) : word :=
  bxor3 (rotr value 17) (rotr value 19) (shr value 10).

Definition byte_at (value : N) (shift : nat) : nat :=
  N.to_nat (N.modulo (N.shiftr value (N.of_nat shift)) 256).

Definition be64 (value : N) : list nat :=
  [byte_at value 56; byte_at value 48; byte_at value 40; byte_at value 32;
   byte_at value 24; byte_at value 16; byte_at value 8; byte_at value 0].

Definition word_bytes (value : word) : list nat :=
  [byte_at value 24; byte_at value 16; byte_at value 8; byte_at value 0].

Definition read4 (bytes : list nat) : word :=
  match bytes with
  | a :: b :: c :: d :: _ =>
      norm
        ((N.shiftl (N.of_nat a) 24 + N.shiftl (N.of_nat b) 16 +
          N.shiftl (N.of_nat c) 8 + N.of_nat d)%N)
  | _ => N0
  end.

Fixpoint words (count : nat) (bytes : list nat) : list word :=
  match count with
  | 0 => []
  | S rest => read4 bytes :: words rest (skipn 4 bytes)
  end.

Definition nthw (index : nat) (values : list word) : word :=
  nth index values N0.

Fixpoint extend (index count : nat) (values : list word) : list word :=
  match count with
  | 0 => values
  | S rest =>
      let value :=
        add4
          (sig1 (nthw (index - 2) values))
          (nthw (index - 7) values)
          (sig0 (nthw (index - 15) values))
          (nthw (index - 16) values) in
      extend (S index) rest (values ++ [value])
  end.

Definition schedule (block : list nat) : list word :=
  extend 16 48 (words 16 block).

Record regs : Type := Regs {
  ra : word;
  rb : word;
  rc : word;
  rd : word;
  re : word;
  rf : word;
  rg : word;
  rh : word
}.

Open Scope N_scope.

Definition init : regs :=
  Regs 1779033703 3144134277 1013904242 2773480762
    1359893119 2600822924 528734635 1541459225.

Definition keys : list word :=
  [1116352408; 1899447441; 3049323471; 3921009573;
   961987163; 1508970993; 2453635748; 2870763221;
   3624381080; 310598401; 607225278; 1426881987;
   1925078388; 2162078206; 2614888103; 3248222580;
   3835390401; 4022224774; 264347078; 604807628;
   770255983; 1249150122; 1555081692; 1996064986;
   2554220882; 2821834349; 2952996808; 3210313671;
   3336571891; 3584528711; 113926993; 338241895;
   666307205; 773529912; 1294757372; 1396182291;
   1695183700; 1986661051; 2177026350; 2456956037;
   2730485921; 2820302411; 3259730800; 3345764771;
   3516065817; 3600352804; 4094571909; 275423344;
   430227734; 506948616; 659060556; 883997877;
   958139571; 1322822218; 1537002063; 1747873779;
   1955562222; 2024104815; 2227730452; 2361852424;
   2428436474; 2756734187; 3204031479; 3329325298].

Close Scope N_scope.

Definition round (state : regs) (key value : word) : regs :=
  let first := add5 (rh state) (sum1 (re state))
    (choose (re state) (rf state) (rg state)) key value in
  let second := add2 (sum0 (ra state)) (major (ra state) (rb state) (rc state)) in
  Regs (add2 first second) (ra state) (rb state) (rc state)
    (add2 (rd state) first) (re state) (rf state) (rg state).

Fixpoint rounds (state : regs) (ks values : list word) : regs :=
  match ks, values with
  | key :: keys', value :: values' =>
      rounds (round state key value) keys' values'
  | _, _ => state
  end.

Definition join (left right : regs) : regs :=
  Regs
    (add2 (ra left) (ra right))
    (add2 (rb left) (rb right))
    (add2 (rc left) (rc right))
    (add2 (rd left) (rd right))
    (add2 (re left) (re right))
    (add2 (rf left) (rf right))
    (add2 (rg left) (rg right))
    (add2 (rh left) (rh right)).

Definition compress (state : regs) (block : list nat) : regs :=
  join state (rounds state keys (schedule block)).

Fixpoint chunks (count : nat) (bytes : list nat) : list (list nat) :=
  match count with
  | 0 => []
  | S rest => firstn 64 bytes :: chunks rest (skipn 64 bytes)
  end.

Fixpoint fold_blocks (state : regs) (blocks : list (list nat)) : regs :=
  match blocks with
  | [] => state
  | block :: rest => fold_blocks (compress state block) rest
  end.

Definition padding (size : nat) : nat :=
  (119 - (size mod 64)) mod 64.

Example padding_55 : padding 55 = 0.
Proof. reflexivity. Qed.

Example padding_56 : padding 56 = 63.
Proof. reflexivity. Qed.

Example padding_63 : padding 63 = 56.
Proof. reflexivity. Qed.

Definition pad (bytes : list nat) : list nat :=
  bytes ++ [128] ++ repeat 0 (padding (length bytes)) ++
    be64 (N.of_nat (length bytes * 8)).

Definition digest_bytes (state : regs) : list nat :=
  word_bytes (ra state) ++ word_bytes (rb state) ++
  word_bytes (rc state) ++ word_bytes (rd state) ++
  word_bytes (re state) ++ word_bytes (rf state) ++
  word_bytes (rg state) ++ word_bytes (rh state).

Definition hash (bytes : list nat) : list nat :=
  let padded := pad bytes in
  digest_bytes (fold_blocks init (chunks (length padded / 64) padded)).

Theorem hash_length : forall bytes, length (hash bytes) = 32.
Proof.
  intros bytes.
  unfold hash, digest_bytes, word_bytes.
  destruct (fold_blocks init
    (chunks (length (pad bytes) / 64) (pad bytes))).
  reflexivity.
Qed.

Example hash_empty :
  hash [] =
    [227; 176; 196; 66; 152; 252; 28; 20;
     154; 251; 244; 200; 153; 111; 185; 36;
     39; 174; 65; 228; 100; 155; 147; 76;
     164; 149; 153; 27; 120; 82; 184; 85].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example hash_abc :
  hash [97; 98; 99] =
    [186; 120; 22; 191; 143; 1; 207; 234;
     65; 65; 64; 222; 93; 174; 34; 35;
     176; 3; 97; 163; 150; 23; 122; 156;
     180; 16; 255; 97; 242; 0; 21; 173].
Proof.
  vm_compute.
  reflexivity.
Qed.