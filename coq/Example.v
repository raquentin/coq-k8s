From Coq Require Import List String.
Import ListNotations.
Local Open Scope string_scope.

From Kube Require Import Model Scheduler.

Definition n1 : Node :=
  {| node_name := "node-a";
     node_capacity := {| cpu := 4; memory := 8 |};
     node_allocated := {| cpu := 0; memory := 0 |};
     node_labels := [("zone","east")];
     node_taints := [] |}.

Definition n2 : Node :=
  {| node_name := "node-b";
     node_capacity := {| cpu := 2; memory := 4 |};
     node_allocated := {| cpu := 1; memory := 1 |};
     node_labels := [("zone","west")];
     node_taints := [{| taint_key := "gpu" |}] |}.

Definition p_ok : Pod :=
  {| pod_name := "frontend";
     pod_resource_request := {| cpu := 1; memory := 2 |};
     pod_node_selector := [("zone","east")];
     pod_tolerations := [];
     pod_priority := 10 |}.

Definition p_needs_toleration : Pod :=
  {| pod_name := "trainer";
     pod_resource_request := {| cpu := 1; memory := 1 |};
     pod_node_selector := [("zone","west")];
     pod_tolerations := [{| toleration_key := "gpu" |}];
     pod_priority := 5 |}.

Definition p_too_big : Pod :=
  {| pod_name := "db";
     pod_resource_request := {| cpu := 8; memory := 8 |};
     pod_node_selector := [];
     pod_tolerations := [];
     pod_priority := 1 |}.

Definition st0 : Cluster :=
  {| nodes := [n1; n2];
     pending := [p_ok; p_needs_toleration; p_too_big];
     bindings := [] |}.