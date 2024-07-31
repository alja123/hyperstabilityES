import MyProject

import MyProject.path_avoiding
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 400000

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
:=∀ (i: ℕ ), i< k→ ((P.get! i).H≤ H)


structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))


def Path_forest_avoids
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: Set V)
:=
∀ (i: ℕ ), i< Fo.k→ (Disjoint {v:V|v∈ (Fo.P.get! i).Pa.Wa.support} Fb)

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
(Fb∩ (HL.get i).verts).toFinset.card≤ (HL.get i).verts.toFinset.card
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


lemma path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k: ℕ )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))



(Slength: S.length> k)
(Elength: E.length> k)
(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))


(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p )--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
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

have h3: P0.length = 0:= by exact rfl

let F0:PathForest iV iSP H:= ⟨S, E, P0, 0, Starts_equal, Ends_equal, Graphs_equal ⟩
use F0
repeat constructor;exact rfl
intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi


have hex: ∃ (Fo: PathForest iV iSP H),Fo.S=S∧ Fo.E=E∧ Fo.k=k∧ (Fo.P.length=k)∧ (Path_forest_avoids iV iSP Fo Fb):= by
  apply hd1

  exact Nat.lt_of_succ_lt Slength
  exact Nat.lt_of_succ_lt Elength
  exact Nat.lt_of_succ_lt HLlength


  --intro i hi
  --apply SinH
  --exact Nat.lt_add_right 1 hi
  --intro i hi
  --apply EinH
  --exact Nat.lt_add_right 1 hi


--rcases hex with ⟨Fo, ⟨FS, ⟨FE, ⟨Fk⟩⟩⟩⟩
rcases hex with ⟨Fo, ⟨FS, ⟨FE, ⟨Fk, ⟨ FFoL, FAvoid  ⟩ ⟩⟩⟩⟩

--let k:ℕ := Fo.k

have kUB_KL: k+1< HL.length:= by
  exact Nat.succ_le_of_lt HLlength
have hKLget: (HL.get! (k + 1))=HL.get ⟨k+1, kUB_KL⟩:= by
  simp
  exact List.getD_eq_get HL default kUB_KL

have kUB_S: k+1< S.length:= by
  exact Nat.succ_le_of_lt Slength
have hSget: (S.get! (k + 1))=S.get ⟨k+1, kUB_S⟩:= by
  simp
  exact List.getD_eq_get S default kUB_S

have kUB_E: k+1< E.length:= by
  exact Nat.succ_le_of_lt Elength
have hEget: (E.get! (k + 1))=E.get ⟨k+1, kUB_E⟩:= by
  simp
  exact List.getD_eq_get E default kUB_E


have exN:∃ (PN: SubgraphPath (HL.get! (k+1)) (S.get! (k+1)) (E.get! (k+1))), PN.Wa.length≤ 40*p∧ (Disjoint (PN.Wa.support.toFinset.toSet)  Fb):=by
  apply Cut_Dense_path_avoiding
  repeat assumption

  unfold cut_dense_list at cutdense
  rw[hKLget]
  apply cutdense

  apply EinH
  exact HLlength

  apply SinH
  exact HLlength

  unfold small_intersection_list at Fbcard
  calc
    4*p*((Fb∩ (HL.get! (k+1)).verts).toFinset.card)
    ≤ 8*p*((Fb∩ (HL.get! (k+1)).verts).toFinset.card):=by
      gcongr; exact Nat.le_of_ble_eq_true rfl
    _=8*p*((Fb∩ (HL.get ⟨ k+1, kUB_KL ⟩ ).verts).toFinset.card):= by
      rw[hKLget]
    _≤ ((HL.get  ⟨ k+1, kUB_KL ⟩ ).verts.toFinset.card):= by
      apply Fbcard ⟨k+1, kUB_KL ⟩

    _= ((HL.get! (k+1)).verts.toFinset.card):= by
      rw[hKLget.symm]

  apply SoutsideFb
  exact HLlength

  apply EoutsideFb
  exact HLlength


have exN:∃ (PN: SubgraphPath (HL.get! (k)) (S.get! (k)) (E.get! (k))), PN.Wa.length≤ 40*p∧ (Disjoint (PN.Wa.support.toFinset.toSet)  Fb):=by
  sorry


rcases exN with ⟨PN, ⟨ hPN1, hPN2⟩ ⟩


let PN_imp: SubgraphPath_implicit G:=⟨HL.get! (k), S.get! (k), E.get! (k), PN⟩

let  Fo': List (SubgraphPath_implicit G):= Fo.P++[PN_imp]

have Starts_equal: starts_equal iV iSP S Fo' (k+1):= by
  unfold starts_equal
  intros i hi
  by_cases case:(i< k)
  rw[FS.symm]
  rw[Fo.Starts_equal i]
  dsimp[Fo']
  simp
  congr 1
  refine (List.getD_append Fo.P [PN_imp] default i ?_).symm
  rw[FFoL]
  exact case
  rw[Fk]
  exact case

  simp at case
  have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
  rw[hieq]
  dsimp[Fo']
  have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
  simp at h1
  rw[FFoL] at h1
  simp
  rw[h1]

  dsimp[PN_imp]
  simp

have Ends_equal: ends_equal iV iSP E Fo' (k+1):= by
  unfold ends_equal
  intros i hi
  by_cases case:(i< k)
  rw[FE.symm]
  rw[Fo.Ends_equal i]
  dsimp[Fo']
  simp
  congr 1
  refine (List.getD_append Fo.P [PN_imp] default i ?_).symm
  rw[FFoL]
  exact case
  rw[Fk]
  exact case

  simp at case
  have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
  rw[hieq]
  dsimp[Fo']
  have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
  simp at h1
  rw[FFoL] at h1
  simp
  rw[h1]

  dsimp[PN_imp]
  simp


have kUb2: k< HL.length:= by
  exact Nat.lt_of_succ_lt HLlength

have Graphs_equal: graphs_equal iSP H Fo' (k+1):= by
  unfold graphs_equal
  intros i hi
  by_cases case:(i< k)
  dsimp[Fo']
  --simp
  have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
  rw[h1]
  apply Fo.Graphs_equal
  exact Nat.lt_of_lt_of_eq case (id Fk.symm)

  simp at case
  have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
  rw[hieq]
  dsimp[Fo']
  have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
  simp at h1
  rw[FFoL] at h1
  simp
  rw[h1]

  dsimp[PN_imp]
  simp
  calc
    HL.getD k default
    =HL.get ⟨ k, kUb2⟩:= by
      exact List.getD_eq_get HL default kUb2
    _≤ H:=by
      apply HL_in_H




let F1:PathForest iV iSP H:= ⟨S, E, Fo', k+1, Starts_equal, Ends_equal, Graphs_equal ⟩

use F1

constructor
exact rfl
constructor
exact rfl
constructor
exact rfl
constructor
dsimp[F1]
dsimp[Fo']
simp
exact FFoL

intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
apply FAvoid
exact Nat.lt_of_lt_of_eq case (id Fk.symm)

simp at case
have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
rw[hieq]
dsimp[Fo']
have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
simp at h1
rw[FFoL] at h1
have h6: (Fo.P ++ [PN_imp]).get! k=PN_imp:= by
  simp
  rw[h1]
rw[h6]


dsimp[PN_imp]
simp at hPN2
exact hPN2




--∃ (P: SubgraphPath H u v), P.Wa.length≤ 40*p∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb)
