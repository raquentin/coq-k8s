From Coq Require Import List String Arith Bool Lia.
From Kube Require Import Model Scheduler.

(*
  Reflection lemma:
  [leq_resources a b = true] iff [a.cpu <= b.cpu && a.memory <= b.memory].
*)
Lemma leq_resources_iff (a b : Resources) :
  leq_resources a b = true <->
    a.(cpu) <= b.(cpu) /\ a.(memory) <= b.(memory).
Proof.
  unfold leq_resources; rewrite andb_true_iff.
  split.
  - intros [Hc Hm]; apply Nat.leb_le in Hc; apply Nat.leb_le in Hm; split; assumption.
  - intros [Hc Hm]; apply Nat.leb_le in Hc; apply Nat.leb_le in Hm; now rewrite Hc, Hm.
Qed.