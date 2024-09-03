import MyProject

import MyProject.cut_dense_delete_vertices
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable  [FinV: Fintype V]
variable  [DecG: DecidableRel G.Adj]
variable  [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
 



/-lemma cut_dense_delete_vertices
(H: Subgraph G)
(cutdense:  cut_dense G H p)
(S: Set V)
(S_small: 4*p*S.toFinset.card ≤ H.verts.toFinset.card)
:
cut_dense G (H.deleteVerts S) (4*p)
:= by


lemma Cut_Dense_path_connected
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
:
∃ (P: SubgraphPath H u v), P.Wa.length≤ 10*p
:=by


structure SubgraphWalk
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_In_H: Wa.toSubgraph≤ H

structure SubgraphPath
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_Is_Path: Wa.IsPath
  Wa_In_H: Wa.toSubgraph≤ H

-/


lemma Cut_Dense_path_avoiding0
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
(Fb: Set V)
(FbSmall: 4*p*Fb.toFinset.card ≤ H.verts.toFinset.card)
(hu: u ∉ Fb)
(hv: v ∉ Fb)
:
∃ (P: SubgraphPath H u v), P.Wa.length≤ 40*p∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb)
:= by
let Hd: Subgraph G:= H.deleteVerts Fb
have Hd_cutdense: cut_dense G Hd (4*p) :=by
  apply cut_dense_delete_vertices H H_cut_dense Fb
  repeat assumption

have hud: u ∈ Hd.verts := by
  dsimp[Hd]
  simp
  exact ⟨u_in_H, hu⟩

have hvd: v ∈ Hd.verts := by
  dsimp[Hd]
  simp
  exact ⟨v_in_H, hv⟩


have ex: ∃ (P: SubgraphPath Hd u v), P.Wa.length≤ 10*(4*p):= by
  apply Cut_Dense_path_connected Hd Hd_cutdense u v hvd hud
  exact Nat.succ_mul_pos 3 pPositive

rcases ex with ⟨P, hP⟩

have hPHd:  (P.Wa.support.toFinset.toSet) ⊆ Hd.verts:= by
  calc
    (P.Wa.support.toFinset.toSet)⊆ P.Wa.toSubgraph.verts:= by simp
    _⊆ Hd.verts:= by
      apply  subgraphs_vertex_sets_subsets G
      exact P.Wa_In_H

have hdisj1: Disjoint (Hd.verts)  Fb:= by
  dsimp[Hd]
  exact Set.disjoint_sdiff_left

have hdisj2: Disjoint (P.Wa.support.toFinset.toSet)  Fb:= by
  exact Set.disjoint_of_subset hPHd (fun ⦃a⦄ a ↦ a) hdisj1

have PinH: P.Wa.toSubgraph≤ H:= by
  calc
    P.Wa.toSubgraph≤ Hd:= by exact P.Wa_In_H
    _≤ H:= by exact Subgraph.deleteVerts_le

let P': SubgraphPath H u v:=
  {Wa:= P.Wa
  ,Wa_Is_Path:= P.Wa_Is_Path
  ,Wa_In_H:= PinH
  }
use P'

constructor
dsimp [P']
calc
  P.Wa.length ≤ 10*(4*p):= by exact hP
  _=40*p:= by ring_nf
exact hdisj2



lemma Cut_Dense_path_avoiding
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
(Fb: Set V)
(FbSmall: 4*p*(Fb∩ H.verts).toFinset.card ≤ H.verts.toFinset.card)
(hu: u ∉ Fb)
(hv: v ∉ Fb)
:
∃ (P: SubgraphPath H u v), P.Wa.length≤ 40*p∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb)
:= by
let Hd: Subgraph G:= H.deleteVerts Fb
have Hd_cutdense: cut_dense G Hd (4*p) :=by
  let Fb':Set V:=Fb∩ H.verts
  have h1: H.deleteVerts Fb=H.deleteVerts Fb':= by
    exact Subgraph.deleteVerts_inter_verts_set_right_eq.symm
  dsimp[Hd]
  rw[h1]
  apply cut_dense_delete_vertices H H_cut_dense Fb'
  repeat assumption
  dsimp [Fb']
  simp
  simp at FbSmall
  exact FbSmall
  repeat assumption


have hud: u ∈ Hd.verts := by
  dsimp[Hd]
  simp
  exact ⟨u_in_H, hu⟩

have hvd: v ∈ Hd.verts := by
  dsimp[Hd]
  simp
  exact ⟨v_in_H, hv⟩


have ex: ∃ (P: SubgraphPath Hd u v), P.Wa.length≤ 10*(4*p):= by
  apply Cut_Dense_path_connected Hd Hd_cutdense u v hvd hud
  exact Nat.succ_mul_pos 3 pPositive

rcases ex with ⟨P, hP⟩

have hPHd:  (P.Wa.support.toFinset.toSet) ⊆ Hd.verts:= by
  calc
    (P.Wa.support.toFinset.toSet)⊆ P.Wa.toSubgraph.verts:= by simp
    _⊆ Hd.verts:= by
      apply  subgraphs_vertex_sets_subsets G
      exact P.Wa_In_H

have hdisj1: Disjoint (Hd.verts)  Fb:= by
  dsimp[Hd]
  exact Set.disjoint_sdiff_left

have hdisj2: Disjoint (P.Wa.support.toFinset.toSet)  Fb:= by
  exact Set.disjoint_of_subset hPHd (fun ⦃a⦄ a ↦ a) hdisj1

have PinH: P.Wa.toSubgraph≤ H:= by
  calc
    P.Wa.toSubgraph≤ Hd:= by exact P.Wa_In_H
    _≤ H:= by exact Subgraph.deleteVerts_le

let P': SubgraphPath H u v:=
  {Wa:= P.Wa
  ,Wa_Is_Path:= P.Wa_Is_Path
  ,Wa_In_H:= PinH
  }
use P'

constructor
dsimp [P']
calc
  P.Wa.length ≤ 10*(4*p):= by exact hP
  _=40*p:= by ring_nf
exact hdisj2






/-let Fb':Set V:= Fb∩ H.verts

have ex: ∃ (P: SubgraphPath H u v), P.Wa.length≤ 40*p∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb'):= by
  dsimp[Fb']
  apply Cut_Dense_path_avoiding0
  repeat assumption
  simp
  simp at FbSmall
  exact FbSmall
  simp
  exact fun a a_1 ↦ hu a
  simp
  exact fun a a_1 ↦ hv a

rcases ex with ⟨P, ⟨hP1, hP2 ⟩  ⟩

use P

dsimp [Fb'] at hP2
simp
-/
