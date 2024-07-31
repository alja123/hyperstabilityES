import MyProject

import MyProject.path_avoiding
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
variable (iSub:Inhabited (Subgraph G))

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}




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




lemma Cut_Dense_path_avoiding
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
-/



structure SubgraphPath_implicit
(G: SimpleGraph V) where
  H: Subgraph G
  s: V
  e: V
  Pa: SubgraphPath H s e



variable (iSP:Inhabited (SubgraphPath_implicit   G) )



def starts_equal
(S : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s)


def ends_equal
(E : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((E.get! i)=(P.get! i).e)

def graphs_equal
(H : Subgraph G)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((P.get! i).H=H)


structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))


def cut_dense_list
(HL: List (Subgraph G))
(p: ℕ )
:=∀(i: Fin (HL.length)),  (cut_dense G  (HL.get i) p)

def small_intersection_list
(HL: List (Subgraph G))
(Fb: Set V)
(p: ℕ )
--(k: ℕ )
:=∀(i: Fin (HL.length)),
(8*p*
((HL.get i).verts∩ Fb).toFinset.card≤ (HL.get i).verts.toFinset.card
)



lemma path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k: ℕ )
(Slength: S.length≥ k)
(Elength: E.length≥ k)
(HLlength: HL.length≥ k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)
(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p )--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
:= by

induction' k with k hd1
let S0: List V:=[]
let E0: List V:=[]
let P0: List (SubgraphPath_implicit G):=[]
--have Seq: S=[]:= by
--  exact List.length_eq_zero.mp Slength
--have Eeq: E=[]:= by
--  exact List.length_eq_zero.mp Elength

have Starts_equal: starts_equal iV iSP S P0 0:= by
  unfold starts_equal
  intro i hi1
  by_contra
  exact Nat.not_succ_le_zero i hi1

have Ends_equal: ends_equal iV iSP E P0 0:= by
  unfold ends_equal
  intro i hi1
  by_contra
  exact Nat.not_succ_le_zero i hi1

have Graphs_equal: graphs_equal  iSP H P0 0:= by
  unfold graphs_equal
  intro i hi1
  by_contra
  exact Nat.not_succ_le_zero i hi1

let F0:PathForest iV iSP H:= ⟨S, E, P0, 0, Starts_equal, Ends_equal, Graphs_equal ⟩
use F0



have hex: ∃ (Fo: PathForest iV iSP H),Fo.S=S∧ Fo.E=E∧ Fo.k=k:= by
  apply hd1
  exact Nat.le_of_succ_le Slength
  exact Nat.le_of_succ_le Elength
  exact Nat.le_of_succ_le HLlength

rcases hex with ⟨Fo, ⟨FS, ⟨FE, ⟨Fk⟩⟩⟩⟩

