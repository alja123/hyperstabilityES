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



lemma head_nin_tail
(S: List V)
(nodup: S.Nodup)
(ne: S≠ [])
:
S.head ne ∉ S.tail :=by
refine List.Nodup.not_mem ?h
have h2: S.head ne :: S.tail=S:=by
  exact List.head_cons_tail S ne
rw[h2]
exact nodup


lemma getk_nin_dropk
(S: List V)
(nodup: S.Nodup)
(k: ℕ )
(hk: k< S.length)
:
S.get! k ∉ List.drop (k + 1) S
:= by


have Snonemp: (List.drop k S)≠ []:= by
  refine List.ne_nil_of_length_pos ?_
  exact List.lt_length_drop S hk
have h1: S.get! k=S.get ⟨k, hk⟩:= by
  simp
  exact List.getD_eq_get S default hk
--rw[h1]

have hk':  k+0< S.length:= by simp; exact hk
have h1: S.get! k=S.get ⟨k+0, hk'⟩:= by
  simp
  exact List.getD_eq_get S default hk
rw[h1]

rw[List.get_drop S hk']

have hdropeq:  List.drop (k + 1) S=List.drop 1 (List.drop k S):= by
  simp
  rw[add_comm]

have hdropeq2:  List.drop 1 (List.drop k S)=List.tail (List.drop k S):= by
  exact List.drop_one (List.drop k S)

rw[hdropeq, hdropeq2]

have hin:  0 < (List.drop k S).length:=by
  exact List.length_pos.mpr Snonemp

have hgethead: (List.drop k S).get ⟨0, hin⟩=(List.drop k S).head Snonemp:= by
  exact List.get_mk_zero hin

rw[hgethead]
apply head_nin_tail
have sublist: List.Sublist (List.drop k S) S:= by
  exact List.drop_sublist k S
exact List.Nodup.sublist sublist nodup
--have h2: S.get ⟨k, hk⟩=(List.drop k S).head Snonemp:= by
--  simp



lemma path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k: ℕ )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)
(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p )--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
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

have Paths_disjoint: paths_disjoint  iSP  P0 0:= by
  unfold paths_disjoint
  intro i j hi1 hji
  by_contra
  exact Nat.not_succ_le_zero j hji

have h3: P0.length = 0:= by exact rfl

let F0:PathForest iV iSP H:= ⟨S, E, P0, 0, Starts_equal, Ends_equal, Graphs_equal, Paths_disjoint ⟩
use F0
repeat constructor;exact rfl
constructor

intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi

constructor
unfold Path_forest_support
simp
exact filter_False univ

constructor
intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi
intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi


have hex: ∃ (Fo: PathForest iV iSP H),Fo.S=S
  ∧ Fo.E=E∧ Fo.k=k
  ∧ (Fo.P.length=k)
  ∧ (Path_forest_avoids iV iSP Fo Fb)
  ∧ ((Path_forest_support iV iSP Fo ).toFinset.card≤ p*k)
  ∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
  ∧ Path_forest_avoids iV iSP Fo {v: V|v∈ (List.drop k E)}:= by
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
rcases hex with ⟨Fo, ⟨FS, ⟨FE, ⟨Fk, ⟨ FFoL, ⟨ FAvoid, ⟨ FSupport, ⟨ FAvoidS, FAvoidE⟩   ⟩ ⟩ ⟩ ⟩⟩⟩⟩

--let k:ℕ := Fo.k

have kUB_KL: k+1< HL.length:= by
  exact Nat.succ_le_of_lt HLlength
have hKLget: (HL.get! (k + 1))=HL.get ⟨k+1, kUB_KL⟩:= by
  simp
  exact List.getD_eq_get HL default kUB_KL

have kUb2: k< HL.length:= by
  exact Nat.lt_of_succ_lt HLlength
have hKLget2: (HL.get! (k ))=HL.get ⟨k, kUb2⟩:= by
  simp
  exact List.getD_eq_get HL default kUb2

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


let Fb2: Set V:= Fb∪ {v: V| ∃ (i: ℕ ), i< k∧ v∈ (Fo.P.get! i).Pa.Wa.support}∪ {v | v ∈ List.drop (k + 1) S}∪ {v | v ∈ List.drop (k + 1) E}

have exN:∃ (PN: SubgraphPath (HL.get! (k)) (S.get! (k)) (E.get! (k))), PN.Wa.length≤ 40*p∧ (Disjoint (PN.Wa.support.toFinset.toSet)  Fb2):=by
  apply Cut_Dense_path_avoiding
  repeat assumption

  unfold cut_dense_list at cutdense
  rw[hKLget2]
  apply cutdense

  apply EinH
  exact kUb2

  apply SinH
  exact kUb2

  unfold small_intersection_list at Fbcard
  calc
    _
    ≤
    4*p*((Fb∩ (HL.get! (k)).verts).toFinset.card):=by
      sorry
    _≤ 8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card):=by
      gcongr; exact Nat.le_of_ble_eq_true rfl
    _=8*p*((Fb∩ (HL.get ⟨ k, kUb2 ⟩ ).verts).toFinset.card):= by
      rw[hKLget2]
    _≤ ((HL.get  ⟨ k, kUb2 ⟩ ).verts.toFinset.card):= by
      apply Fbcard ⟨k , kUb2 ⟩

    _= ((HL.get! (k)).verts.toFinset.card):= by
      rw[hKLget2.symm]

  dsimp [Fb2]
  simp only [ Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and]
  constructor
  constructor
  constructor
  apply SoutsideFb
  exact kUb2

  intro x hx
  have h7: S.get! k∈(List.drop k S):= by
    have h9: k+0< S.length:= by
      exact Nat.lt_of_succ_lt Slength
    have h10: (S.get! k)=S.get ⟨k+0, h9⟩:= by
      simp
      exact List.getD_eq_get S default h9
    rw[h10]
    rw[List.get_drop S h9]
    exact List.get_mem (List.drop k S) 0 (List.lt_length_drop S h9)
  have h8: Disjoint {v:V|v∈ (Fo.P.get! x).Pa.Wa.support} {v:V|v∈ (List.drop k S)}:= by
    unfold Path_forest_avoids at FAvoidS
    apply FAvoidS
    exact Nat.lt_of_lt_of_eq hx (id Fk.symm)
  have h72: S.get! k∈{v:V|v∈ (List.drop k S)}:= by
    simp only [Set.mem_setOf_eq]
    exact h7
  have h11: S.get! k ∉ {v: V|v∈ (Fo.P.get! x).Pa.Wa.support}:= by
    by_contra cont
    simp only [ Set.mem_setOf_eq] at cont
    have hneg: ¬(Disjoint {v | v ∈ (Fo.P.get! x).Pa.Wa.support} {v | v ∈ List.drop k S}):= by
      unfold Disjoint
      simp only [Set.le_eq_subset, Set.bot_eq_empty, not_forall, Classical.not_imp]
      use {S.get! k}
      simp only [Set.singleton_subset_iff, Set.mem_empty_iff_false,
        not_false_eq_true, Set.mem_setOf_eq, exists_prop, and_true]
      exact ⟨cont, h72⟩
    simp at hneg
    exact  hneg h8
  simp only [Set.mem_setOf_eq] at h11
  exact h11


  apply getk_nin_dropk
  exact Snodup
  exact Nat.lt_of_succ_lt Slength

  have h5: S.get! k∈ S:= by
    have h9: k< S.length:= by
      exact Nat.lt_of_succ_lt Slength
    have h10: (S.get! k)=S.get ⟨k, h9⟩:= by
      simp
      exact List.getD_eq_get S default h9
    rw[h10]
    exact List.get_mem S k h9
  have h5: S.get! k∉ E:= by
    exact SE_Disjoint h5
  --have h13: List.Sublist (List.drop (k + 1) E) E:= by
  --  exact List.drop_sublist (k + 1) E
  by_contra cont
  --simp only [List.get!_eq_getD] at cont
  have h5': S.get! k∈  E:= by
    exact List.mem_of_mem_drop cont
  exact h5 h5'

  sorry


  unfold Path_forest_avoids at FAvoidS
  intro x hx
  have h7: S.get! k∈(List.drop k S):= by
    have h9: k+0< S.length:= by
      exact Nat.lt_of_succ_lt Slength
    have h10: (S.get! k)=S.get ⟨k+0, h9⟩:= by
      simp
      exact List.getD_eq_get S default h9
    rw[h10]
    rw[List.get_drop S h9]
    exact List.get_mem (List.drop k S) 0 (List.lt_length_drop S h9)

  have h8: (Fo.P.get! x).Pa.Wa.support.Disjoint (List.drop k S):= by
    apply FAvoidS
    exact Nat.lt_of_lt_of_eq hx (id Fk.symm)
  exact id (List.Disjoint.symm h8) h7


  dsimp [Fb2]
  simp only [ Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and]
  constructor
  apply EoutsideFb
  exact kUb2



  /-unfold Path_forest_avoids_list at FAvoidS
  intro x hx
  have h7: E.get! k∈(List.drop k E):= by
    have h9: k+0< E.length:= by
      exact Nat.lt_of_succ_lt Elength
    have h10: (E.get! k)=E.get ⟨k+0, h9⟩:= by
      simp
      exact List.getD_eq_get E default h9
    rw[h10]
    rw[List.get_drop E h9]
    exact List.get_mem (List.drop k E) 0 (List.lt_length_drop E h9)

  have h8: (Fo.P.get! x).Pa.Wa.support.Disjoint (List.drop k E):= by
    apply FAvoidE
    exact Nat.lt_of_lt_of_eq hx (id Fk.symm)
  exact id (List.Disjoint.symm h8) h7-/

--have exN:∃ (PN: SubgraphPath (HL.get! (k)) (S.get! (k)) (E.get! (k))), PN.Wa.length≤ 40*p∧ (Disjoint (PN.Wa.support.toFinset.toSet)  Fb):=by
--  sorry


rcases exN with ⟨PN, ⟨ hPN1, hPN2⟩ ⟩

dsimp [Fb2] at hPN2
simp at hPN2
let ⟨⟨⟨  hPN2a, hPN2b⟩ , hPN2c⟩ , hPN2d⟩:= hPN2

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



have Paths_disjoint: paths_disjoint iSP  Fo' (k+1):= by
  intro i j hi hj
  by_cases case:(j< k)
  dsimp[Fo']
  --simp
  have h1: (Fo.P ++ [PN_imp]).get! j=(Fo.P).get! j:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
  have h2: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    have h3: i<k:= by exact Nat.lt_trans hi case
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq h3 (id FFoL.symm)
  rw[h1, h2]
  apply Fo.Paths_disjoint
  exact hi
  exact Nat.lt_of_lt_of_eq case (id Fk.symm)

  simp at case
  have hieq: j=k:= by
      exact Nat.eq_of_le_of_lt_succ case hj
  rw[hieq]
  dsimp[Fo']
  have h2: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    have h3: i<k:= by exact Nat.lt_of_lt_of_eq hi hieq
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq h3 (id FFoL.symm)
  rw[h2]


  have h4: ((Fo.P ++ [PN_imp]).get! k)=PN_imp:= by
    have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
      apply List.getD_append_right
      exact Nat.le_refl Fo.P.length
    simp at h1
    rw[FFoL] at h1
    simp
    rw[h1]
  rw[h4]
  dsimp[PN_imp]
  have h5: {v | v ∈ (Fo.P.get! i).Pa.Wa.support}⊆ {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}:= by
    simp
    intro a ha
    use i
    constructor
    exact Nat.lt_of_lt_of_eq hi hieq
    exact ha
  have h5: {v | v ∈ (Fo.P.get! i).Pa.Wa.support}≤  {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}:= by
    exact h5
  apply Disjoint.mono_left h5 --hPN2.2
  apply Disjoint.symm
  exact hPN2b






let F1:PathForest iV iSP H:= ⟨S, E, Fo', k+1, Starts_equal, Ends_equal, Graphs_equal, Paths_disjoint ⟩

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

constructor

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

exact hPN2a




dsimp[F1]
unfold Path_forest_support
dsimp[Fo']
simp only [List.mem_append, List.mem_singleton]

have h20: {v | ∃ Pi, (Pi ∈ Fo.P ∨ Pi = PN_imp) ∧ v ∈ Pi.Pa.Wa.support}={v | ∃ Pi, Pi ∈ Fo.P  ∧ v ∈ Pi.Pa.Wa.support}∪ {v |  v ∈ PN_imp.Pa.Wa.support}:= by
  ext v
  constructor
  intro h
  simp
  simp at h
  rename_i
    h_1
  aesop_subst
    [Fk,
    FS,
    FE]
  simp_all only [gt_iff_lt,
    Set.toFinset_card,
    Fintype.card_ofFinset,
    List.get!_eq_getD,
    true_implies,
    and_self,
    PN_imp]
  unhygienic
    with_reducible
      aesop_destruct_products
  unhygienic
    aesop_cases
      left
  · apply
      Or.inl
    apply
      Exists.intro
    apply
      And.intro
    on_goal
      2 =>
      exact
        right
    simp_all only
  · aesop_subst
      h
    simp_all only [or_true]

  intro
    a
  aesop_subst
    [Fk,
    FS,
    FE]
  simp_all only [gt_iff_lt,
    Set.toFinset_card,
    Fintype.card_ofFinset,
    List.get!_eq_getD,
    true_implies,
    and_self,
    Set.mem_union,
    Set.mem_setOf_eq,
    PN_imp]
  unhygienic
    aesop_cases
      a
  · unhygienic
      with_reducible
        aesop_destruct_products
    apply
      Exists.intro
    apply
      And.intro
    on_goal
      2 =>
      exact
        right
    simp_all only [true_or]
  · apply
      Exists.intro
    apply
      And.intro
    apply
      Or.inr
    apply
      Eq.refl
    simp_all only
simp_rw[h20]


constructor
calc
  ({v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support} ∪ {v | v ∈ PN.Wa.support}).toFinset.card
  =
  ({v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}.toFinset ∪ {v | v ∈ PN.Wa.support}.toFinset).card:= by
    simp
  _≤ {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}.toFinset.card + {v | v ∈ PN.Wa.support}.toFinset.card:= by
    exact
      card_union_le {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}.toFinset
        {v | v ∈ PN.Wa.support}.toFinset

  _≤p*k+p:= by
    gcongr
    unfold Path_forest_support at FSupport
    simp at FSupport
    simp
    exact FSupport

    simp only [Set.mem_setOf_eq]
    calc
      {v | v ∈ PN.Wa.support}.toFinset.card
      = PN.Wa.support.toFinset.card:= by
        congr
        simp
        ext v
        constructor

        intro h
        simp
        simp at h
        exact h
        intro h
        simp
        simp at h
        exact h
      _≤ PN.Wa.support.length:=by
        exact List.toFinset_card_le PN.Wa.support

      _=PN.Wa.length+1:= by
        simp
      _≤ p:= by sorry
  _=p*(k+1):= by
    ring_nf

--∃ (P: SubgraphPath H u v), P.Wa.length≤ 40*p∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb)


constructor

--------------- Avoid S
intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
have h13: {v | v ∈ List.drop (k + 1) S}⊆ {v | v ∈ List.drop (k ) S}:= by
  simp
  intro b hb
  have h12: List.drop (1+k) S= List.drop (1) (List.drop (k) S):= by
    exact List.drop_add 1 k S
  rw[add_comm] at h12
  apply List.mem_of_mem_drop
  rw[h12] at hb
  exact hb
apply Disjoint.mono_right h13
apply FAvoidS
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
exact hPN2c







--------------- Avoid E
intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
have h13: {v | v ∈ List.drop (k + 1) E}⊆ {v | v ∈ List.drop (k ) E}:= by
  simp
  intro b hb
  have h12: List.drop (1+k) E= List.drop (1) (List.drop (k) E):= by
    exact List.drop_add 1 k E
  rw[add_comm] at h12
  apply List.mem_of_mem_drop
  rw[h12] at hb
  exact hb
apply Disjoint.mono_right h13
apply FAvoidE
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
exact hPN2d
