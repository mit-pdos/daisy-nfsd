From Coq Require Import ZArith Lia.
From Coq Require Import ssreflect.

Open Scope Z.
Open Scope general_if_scope.

Definition divup x k := (x + (k - 1)) / k.

Definition roundup x k := divup x k * k.

Lemma Zmod_split x k :
  0 < k ->
  0 <= x ->
  x = x / k * k + x mod k.
Proof.
  intros.
  rewrite -> Zmod_eq by lia.
  lia.
Qed.

Lemma Zdiv_mul_divisible x k :
  0 < k ->
  0 <= x ->
  x mod k = 0 ->
  x = x / k * k.
Proof.
  intros.
  rewrite {1}(Zmod_split x k) //.
  lia.
Qed.

Lemma divup_alt x k :
  0 < k ->
  0 <= x ->
  divup x k = if Z.eq_dec (x mod k) 0 then x/k else x/k + 1.
Proof.
  intros.
  rewrite /divup.
  destruct (Z.eq_dec _ _).
  - rewrite {1}(Zdiv_mul_divisible x k) //.
    rewrite -> Z.div_add_l by lia.
    rewrite -> (Z.div_small (k-1)) by lia.
    lia.
  - rewrite {1}(Zmod_split x k) //.
    rewrite -Z.add_assoc.
    replace (x mod k + (k - 1)) with (k + (x mod k - 1)) by lia.
    rewrite Z.add_assoc.
    replace (x / k * k + k) with ((x / k + 1) * k) by lia.
    rewrite -> Z.div_add_l by lia.
    rewrite -> (Z.div_small (x mod k - 1)); [ lia | ].
    pose proof (Z.mod_bound_pos x k).
    lia.
Qed.
