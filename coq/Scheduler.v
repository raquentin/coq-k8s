From Coq Require Import List String Arith Bool.
Import ListNotations.
Local Open Scope string_scope.

From Kube Require Import Model.

Definition pod_better_or_equal (p q : Pod) : bool :=
  Nat.leb q.(pod_priority) p.(pod_priority).

Fixpoint pick_highest_priority (best : Pod) (ps : list Pod) : Pod :=
  match ps with
  | [] => best
  | p :: tl =>
      pick_highest_priority (if pod_better_or_equal p best then p else best) tl
  end.

Definition select_next_pod (ps : list Pod) : option (Pod * list Pod) :=
  match ps with
  | [] => None
  | p :: tl =>
      let chosen := pick_highest_priority p tl in
      let rest := filter (fun q => negb (String.eqb q.(pod_name) chosen.(pod_name))) ps in
      Some (chosen, rest)
  end.

Fixpoint first_eligible_node (p : Pod) (ns : list Node) : option Node :=
  match ns with
  | [] => None
  | n :: tl =>
      if pod_node_eligible p n then Some n else first_eligible_node p tl
  end.

Definition schedule_one (c : Cluster) : option Cluster :=
  match select_next_pod c.(pending) with
  | None => None
  | Some (p, rest) =>
      match first_eligible_node p c.(nodes) with
      | None => None
      | Some n =>
          let n'  := node_consume_pod p n in
          let ns' := update_node_by_name c.(nodes) n.(node_name) (fun _ => n') in
          Some {| nodes := ns';
                  pending := rest;
                  bindings := {| binding_pod := p.(pod_name);
                                  binding_node := n.(node_name) |}
                              :: c.(bindings) |}
      end
  end.

Fixpoint schedule_all (fuel : nat) (c : Cluster) : Cluster :=
  match fuel with
  | 0 => c
  | S f' =>
      match schedule_one c with
      | None => c
      | Some c' => schedule_all f' c'
      end
  end.
  
(* Find the first eligible node; return (prefix, chosen, suffix). *)
Fixpoint find_eligible_split (p : Pod) (ns : list Node)
  : option (list Node * Node * list Node) :=
  match ns with
  | [] => None
  | n :: tl =>
      if pod_node_eligible p n
      then Some ([], n, tl)
      else match find_eligible_split p tl with
           | None => None
           | Some (l, c, r) => Some (n :: l, c, r)
           end
  end.

(* One step using the split (avoids “update-by-name” aliasing in proofs). *)
Definition schedule_one' (c : Cluster) : option Cluster :=
  match select_next_pod c.(pending) with
  | None => None
  | Some (p, rest) =>
      match find_eligible_split p c.(nodes) with
      | None => None
      | Some (l, n, r) =>
          let n' := node_consume_pod p n in
          Some {| nodes := l ++ n' :: r;
                  pending := rest;
                  bindings := {| binding_pod := p.(pod_name);
                                 binding_node := n.(node_name) |}
                              :: c.(bindings) |}
      end
  end.

Fixpoint schedule_all' (fuel : nat) (c : Cluster) : Cluster :=
  match fuel with
  | 0 => c
  | S f' =>
      match schedule_one' c with
      | None => c
      | Some c' => schedule_all' f' c'
      end
  end.
