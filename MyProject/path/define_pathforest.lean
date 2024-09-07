import MyProject

import MyProject.path_avoiding
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 200000

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
  (Graphs_equal: graphs_equal  iSP H P (k-1)) --∀ (i: ℕ ), i< k→ (P.get! i).H=H)
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




lemma finsets4card
(A B C D T: Finset V)
:
((A∪ B∪ C∪ D)∩ T).card≤ (A∩ T).card+B.card+C.card+D.card:=by
calc
((A∪ B∪ C∪ D)∩ T).card
≤ (A ∩ T ∪ B ∪ C ∪ D).card:= by
  gcongr
  intro x hx
  simp
  simp at hx
  simp_all only [gt_iff_lt,
    and_true]
_≤ (A∩ T).card+B.card+C.card+D.card:= by
  exact card_union_4 (A ∩ T) B C D

lemma sets4card
(A B C D T: Set V)
:
((A∪ B∪ C∪ D)∩ T).toFinset.card≤ (A∩ T).toFinset.card+B.toFinset.card+C.toFinset.card+D.toFinset.card:=by
calc
((A∪ B∪ C∪ D)∩ T).toFinset.card
_= ((A.toFinset ∪ B.toFinset∪ C.toFinset∪ D.toFinset)∩ T.toFinset).card:= by
  simp
_≤ (A.toFinset ∩ T.toFinset).card+B.toFinset.card
+C.toFinset.card
+D.toFinset.card:= by
  apply finsets4card
_=(A∩ T).toFinset.card+B.toFinset.card+C.toFinset.card+D.toFinset.card:=by
  congr; simp



lemma sets4cardinequality
(A B C D T: Set V)
(a b c d: ℕ)
(ha: (A∩ T).toFinset.card≤ a)
(hb: B.toFinset.card≤ b)
(hc: C.toFinset.card≤ c)
(hd: D.toFinset.card≤ d)
:
((A∪ B∪ C∪ D)∩ T).toFinset.card≤ a+b+c+d:=by
calc
((A∪ B∪ C∪ D)∩ T).toFinset.card
≤ (A∩ T).toFinset.card+B.toFinset.card+C.toFinset.card+D.toFinset.card:= by
  apply sets4card
_≤ a+b+c+d:= by
  gcongr




lemma finsets4cardinequality
(A B C D T: Finset V)
(a b c d: ℕ)
(ha: (A∩ T).card≤ a)
(hb: B.card≤ b)
(hc: C.card≤ c)
(hd: D.card≤ d)
:
((A∪ B∪ C∪ D)∩ T).card≤ a+b+c+d:=by
calc
((A∪ B∪ C∪ D)∩ T).card
≤ (A∩ T).card+B.card+C.card+D.card:= by
  apply finsets4card
_≤ a+b+c+d:= by
  gcongr




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


lemma list_rotate_get_V
(L: List V)
(t: ℕ )
(ht: t+1<L.length)
:
(L.rotate 1).get! t=L.get! (t+1)
:= by
have ht2:t< (L.rotate 1).length:=by
  simp
  exact Nat.lt_of_succ_lt ht
have get1: L.get! (t+1)=L.get ⟨t+1, ht⟩:= by
  simp
  exact List.getD_eq_get L default ht
have get2: (L.rotate 1).get! t=(L.rotate 1).get ⟨t, ht2⟩:= by
  simp
  exact List.getD_eq_get (L.rotate 1) default ht2
rw[get1, get2]
rw[List.get_rotate L]
simp
have h3: (t + 1) % L.length=t+1:= by
  exact Nat.mod_eq_of_lt ht
simp_rw[h3]


lemma list_rotate_get_V_last
(L: List V)
(ht:  (L.length)>0 )
:
(L.rotate 1).get! (L.length-1)=L.get! (0)
:= by
have ht2: (L.length-1)< (L.rotate 1).length:=by
  simp
  refine Nat.sub_lt ?_ ?_
  exact ht
  simp
have get1: L.get!  0=L.get ⟨ 0, ht⟩:= by
  simp
  exact List.getD_eq_get L default ht
have get2: (L.rotate 1).get!  (L.length-1)=(L.rotate 1).get ⟨ (L.length-1), ht2⟩:= by
  simp
  exact List.getD_eq_get (L.rotate 1) default ht2
rw[get1, get2]
rw[List.get_rotate L]
simp
have h3: (L.length - 1 + 1) % L.length=0:= by
  rw [Nat.sub_one_add_one_eq_of_pos ht]
  simp
simp_rw[h3]


