From Coq Require Import List String Arith Bool.
Import ListNotations.
Local Open Scope string_scope.

Record Resources := { cpu : nat; memory : nat }.

Definition leq_resources (a b : Resources) : bool :=
  Nat.leb a.(cpu) b.(cpu) && Nat.leb a.(memory) b.(memory).

Definition add_resources (a b : Resources) : Resources :=
  {| cpu := a.(cpu) + b.(cpu); memory := a.(memory) + b.(memory) |}.

Definition Label := (string * string)%type.

Record Taint := { taint_key : string }.
Record Toleration := { toleration_key : string }.

Record Pod := {
  pod_name             : string;
  pod_resource_request : Resources;
  pod_node_selector    : list Label;
  pod_tolerations      : list Toleration;
  pod_priority         : nat
}.

Record Node := {
  node_name      : string;
  node_capacity  : Resources;
  node_allocated : Resources;
  node_labels    : list Label;
  node_taints    : list Taint
}.

Definition node_remaining_capacity (n : Node) : Resources :=
  {| cpu := n.(node_capacity).(cpu) - n.(node_allocated).(cpu);
    memory := n.(node_capacity).(memory) - n.(node_allocated).(memory) |}.

Definition pod_fits_resources (p : Pod) (n : Node) : bool :=
  leq_resources p.(pod_resource_request) (node_remaining_capacity n).

Definition label_member (k v : string) (ls : list Label) : bool :=
  existsb (fun '(k',v') => String.eqb k k' && String.eqb v v') ls.

Fixpoint labels_subset (need : list Label) (have : list Label) : bool :=
  match need with
  | [] => true
  | (k,v) :: tl =>
      if label_member k v have then labels_subset tl have else false
  end.

Definition pod_matches_node_selector (p : Pod) (n : Node) : bool :=
  labels_subset p.(pod_node_selector) n.(node_labels).

Definition taint_tolerated (t : Taint) (tls : list Toleration) : bool :=
  existsb (fun tol => String.eqb t.(taint_key) tol.(toleration_key)) tls.

Fixpoint all_taints_tolerated (ts : list Taint) (tls : list Toleration) : bool :=
  match ts with
  | [] => true
  | t :: tl =>
      if taint_tolerated t tls then all_taints_tolerated tl tls else false
  end.

Definition pod_tolerates_node_taints (p : Pod) (n : Node) : bool :=
  all_taints_tolerated n.(node_taints) p.(pod_tolerations).

Definition pod_node_eligible (p : Pod) (n : Node) : bool :=
  pod_fits_resources p n
  && pod_matches_node_selector p n
  && pod_tolerates_node_taints p n.

Record Binding := { binding_pod : string; binding_node : string }.

Record Cluster := {
  nodes    : list Node;
  pending  : list Pod;
  bindings : list Binding
}.

Definition resources_within_capacity (n : Node) : bool :=
  leq_resources n.(node_allocated) n.(node_capacity).

Definition capacities_ok (c : Cluster) : bool :=
  forallb resources_within_capacity c.(nodes).

Definition node_consume_pod (p : Pod) (n : Node) : Node :=
  {| node_name      := n.(node_name);
    node_capacity  := n.(node_capacity);
    node_allocated := add_resources n.(node_allocated) p.(pod_resource_request);
    node_labels    := n.(node_labels);
    node_taints    := n.(node_taints) |}.

Fixpoint update_node_by_name (ns : list Node) (name : string) (f : Node -> Node)
  : list Node :=
  match ns with
  | [] => []
  | n :: tl =>
      if String.eqb n.(node_name) name
      then f n :: tl
      else n :: update_node_by_name tl name f
  end.