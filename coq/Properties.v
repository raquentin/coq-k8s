From Coq Require Import List String Bool Arith.
Import ListNotations.

From Kube Require Import Model.

Lemma leq_resources_iff (a b : Resources) :
  leq_resources a b = true <->
    a.(cpu) <= b.(cpu) /\ a.(memory) <= b.(memory).
Proof.
  unfold leq_resources; rewrite andb_true_iff.
  split.
  - intros [Hc Hm]; apply Nat.leb_le in Hc; apply Nat.leb_le in Hm; split; assumption.
  - intros [Hc Hm]; apply Nat.leb_le in Hc; apply Nat.leb_le in Hm; now rewrite Hc, Hm.
Qed.

(* from the boolean result, recover the ≤ pair directly. *)
Corollary leq_resources_true_inv a b :
  leq_resources a b = true ->
  a.(cpu) <= b.(cpu) /\ a.(memory) <= b.(memory).
Proof. intro H; apply leq_resources_iff in H; exact H. Qed.

(* to prove the boolean, it suffices to prove the two ≤ subgoals. *)
Corollary leq_resources_intro a b :
  a.(cpu) <= b.(cpu) ->
  a.(memory) <= b.(memory) ->
  leq_resources a b = true.
Proof. intros Hc Hm; apply leq_resources_iff; split; assumption. Qed.

(* splits a forallb over a cons; peel off the head element cleanly. *)
Lemma forallb_cons_true_iff {A} (P : A -> bool) x xs :
  forallb P (x :: xs) = true <-> P x = true /\ forallb P xs = true.
Proof. simpl; rewrite andb_true_iff; tauto. Qed.

(* forallb over append = and of the two parts; reason about left/right segments. *)
Lemma forallb_app {A} (P : A -> bool) xs ys :
  forallb P (xs ++ ys) = andb (forallb P xs) (forallb P ys).
Proof.
  induction xs as [|h t IH]; simpl; auto.
  now rewrite IH, andb_assoc.
Qed.

(* from forallb true to “every element satisfies P”. *)
Lemma forallb_forall {A} (P : A -> bool) (l : list A) :
  forallb P l = true -> forall x, In x l -> P x = true.
Proof.
  induction l as [|h t IH]; intros H x Hin; simpl in *; try contradiction.
  apply andb_true_iff in H as [Hh Ht]. destruct Hin as [->|Hin]; auto.
Qed.

(* each sub-check true; lets proofs grab the needed piece. *)
Lemma eligible_implies_subchecks p n :
  pod_node_eligible p n = true ->
  pod_fits_resources p n = true /\
  pod_matches_node_selector p n = true /\
  pod_tolerates_node_taints p n = true.
Proof.
  unfold pod_node_eligible; rewrite !andb_true_iff; tauto.
Qed.
