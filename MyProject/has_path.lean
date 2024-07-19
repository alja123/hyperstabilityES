
import MyProject

import MyProject.J_bound
import MyProject.clumpfamily_maximal
 --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}




structure SubgraphPath
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_Is_Path: Wa.IsPath
  Wa_In_H: Wa.toSubgraph≤ H

def No_Length_d_Paths (H: Subgraph G) (d: ℕ): Prop:=
  ∀ (u v: V), ∀ (P: SubgraphPath H u v), P.Wa.length < d


def Has_length_d_path (H: Subgraph G) (d: ℕ): Prop:=
  ∃  (u v: V), ∃  (P: SubgraphPath H u v), P.Wa.length ≥  d



def Vertex_list_in_clump_list
  (Ord: List (Clump G p m κ pr h))
  (Ver: List V): Prop:=
  ∀ (i: ℕ), (i< Ord.length)→ ((Ver.get! i)∈  (((Ord.get! i).Gr.verts)∩((Ord.get! (i+1)).Gr.verts)))


def Clump_Family_Union
(KFam: Finset (Clump G p m κ pr h))
:Subgraph G
:= sSup (Finset.image (fun C: Clump G p m κ pr h => C.Gr) KFam)


structure ClumpPathSequence
(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver)
  (hlength: Ord.length ≥  h*pr)


lemma clump_sequence_gives_path
(KFam: Finset (Clump G p m κ pr h))
(Ord: List (Clump G p m κ pr h))
(Ord_eq_KFam: Ord.toFinset= KFam)
(Ver: List V)
(VerNoDup: Ver.Nodup)
(VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver)
(hlength: Ord.length ≥  h*pr)
:
Has_length_d_path (Clump_Family_Union KFam) (h*m)
:=by

sorry


lemma clump_path_sequence_gives_path
(KFam: Finset (Clump G p m κ pr h))
(ClumpPathSeq: ClumpPathSequence iI iV KFam)
:
Has_length_d_path (Clump_Family_Union KFam) (h*m)
:=by

sorry





lemma Wide_clump_implies_path_sequence
(K: Clump G p m κ pr h)
(hWide1: K.k≥ pr*pr*h)
(hWide2: K.k≤  4*pr*pr*h)
: Nonempty (ClumpPathSequence iI iV {K})
:=by

sorry




lemma dense_list_implies_path_sequence
(KFam: Finset (Clump G p m κ pr h))
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
Nonempty (ClumpPathSequence iI iV KFam)
:=by

sorry



--#check Clump_family_contained_in_L L.Gr KFam



lemma Wide_clump_implies_path
(L: Locally_Dense G p m h)
(K: Clump G p m κ pr h)
(K_In_L: K.Gr≤ L.Gr)
(hWide1: K.k≥ pr*pr*h)
(hWide2: K.k≤  4*pr*pr*h)
:
Has_length_d_path (L.Gr) (h*m):=by
sorry

lemma dense_list_implies_path
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
(KFam_In_L:Clump_family_contained_in_L L.Gr KFam)
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
Has_length_d_path (L.Gr) (h*m):=by
sorry

