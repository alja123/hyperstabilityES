import MyProject

import MyProject.path_forests_joining
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 50000

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
variable (iSP:Inhabited (SubgraphPath_implicit   G) )

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}

lemma long_path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (172*p*p*kmax))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
:= by

sorry




/-lemma path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (172*p*p*kmax))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
:= by-/

/-

lemma join_three_forests
(H: Subgraph G)
(F1 F2 F3: PathForest iV iSP H)
(hF1_F2: F1.E=F2.S)
(hF2_F3: F2.E=F3.S)
(hF3_F1: F3.E=F1.S.tail)

(t tmax: ℕ )

( hdisj11: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
( hdisj22: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)))
( hdisj33: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)))
( hdisj12: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)))
( hdisj21: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)))
( hdisj13: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)))
( hdisj31: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F1.P.get! j)))
( hdisj23: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)))
( hdisj32: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)))

(Slength: tmax < F1.S.length)

(ht: t<tmax)
(pos1: tmax<F1.k)
(pos2: tmax<F2.k)
(pos3: tmax<F3.k)


:
∃ (P: SubgraphPath H (F1.S.get! 0) (F3.E.get! (t))),
{v:V|v∈ P.Wa.support}=Path_forest_support_until_t iV iSP  F1 (t+1)∪ Path_forest_support_until_t iV iSP  F2 (t+1)∪ Path_forest_support_until_t iV iSP  F3 (t+1)
-/


/-simp only [Walk.mem_support_append_iff]
have h5:  {v | v ∈ P.Wa.support ∨ v ∈ Q.Wa.support}= {v | v ∈ P.Wa.support} ∪ {v | v ∈ Q.Wa.support}:= by

rw[h5]
rw[hP1, hQ2]

unfold Path_forest_support_until_t
ext v
constructor
intro h
simp
simp at h

aesop
-/

--#check SimpleGraph.append_paths



/-
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
:=∀ (i: ℕ ), i< k→ ((P.get! i).H≤ H)


def paths_disjoint
 (P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i j: ℕ ), i< j→ j< k→ (Disjoint {v:V|v∈ (P.get! i).Pa.Wa.support} {v:V|v∈ (P.get! j).Pa.Wa.support})


structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  (Paths_disjoint: paths_disjoint iSP  P k)  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))
  (P_length: P.length=k)

def Path_forest_support
{H: Subgraph G}
(Fo: PathForest iV iSP H)
: Set V
:={v: V| ∃ (Pi: SubgraphPath_implicit G), Pi∈ Fo.P∧  (v∈ Pi.Pa.Wa.support)}


def Path_forest_avoids
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: Set V)
:=
∀ (i: ℕ ), i< Fo.k→ (Disjoint {v:V|v∈ (Fo.P.get! i).Pa.Wa.support} Fb)

def Path_forest_avoids_list
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: List V)
:=
∀ (i: ℕ ), i< Fo.k→ (List.Disjoint ((Fo.P.get! i).Pa.Wa.support) Fb)


def cut_dense_list
(HL: List (Subgraph G))
(p: ℕ )
:=∀(i: Fin (HL.length)),  (cut_dense G  (HL.get i) p)

def small_intersection_list
(HL: List (Subgraph G))
(Fb: Set V)
(p e: ℕ )
--(k: ℕ )
:=∀(i: Fin (HL.length)),
(8*p*
(Fb∩ (HL.get i).verts).toFinset.card+e≤ (HL.get i).verts.toFinset.card
)

def vertex_list_in_graph_list
(S: List V)
(HL: List (Subgraph G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∈ (HL.get! i).verts


def vertex_list_outside_set
(S: List V)
(Fb: Set V)
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∉ Fb

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
