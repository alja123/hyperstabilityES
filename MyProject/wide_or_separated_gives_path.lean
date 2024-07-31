
import MyProject

import MyProject.build_path
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 300000

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
variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}


/-structure ClumpPathSequence
 (β : ℕ )(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (LM_Sparse: family_sparse β m (LM.toFinset) )
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
  (hlength: Ord.length ≥  h*pr)
  (hlengthM: LM.length=Ord.length)
  (hlengthVer: Ver.length=Ord.length-1)-/


lemma Wide_clump_implies_path
(L: Locally_Dense G p m h)
(K: Clump G p m κ pr h)
(K_In_L: K.Gr≤ L.Gr)
(hWide1: K.k≥ pr*pr*h)
(hWide2: K.k≤  4*pr*pr*h)
:
Has_length_d_path (L.Gr) (h*m):=by
have hNonemp: Nonempty (ClumpPathSequence iI iV α {K}):=by
  exact Wide_clump_implies_path_sequence iI iV α K hWide1 hWide2
let KSeq:= hNonemp.some
have h1: Has_length_d_path (Clump_Family_Union {K}) (h*m):=by
  apply clump_path_sequence_gives_path iI iV {K} KSeq

apply has_path_monotone   (Clump_Family_Union {K})  L.Gr (h*m) _ (h1)
calc
  Clump_Family_Union {K} = K.Gr:= by exact Clump_Family_Union_singleton K
  _ ≤ L.Gr:= by exact K_In_L


lemma family_union_from_familycontainedinL
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
(KFam_In_L:Clump_family_contained_in_L L.Gr KFam)
:
Clump_Family_Union KFam ≤ L.Gr:=by
unfold  Clump_Family_Union
simp
exact KFam_In_L

lemma dense_list_implies_path
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
(KFam_Nonempty:  KFam.Nonempty)
(KFam_In_L:Clump_family_contained_in_L L.Gr KFam)
--(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
Has_length_d_path (L.Gr) (h*m):=by
have hNonemp: Nonempty (ClumpPathSequence iI iV κ KFam):=by
  apply Dense_list_implies_path_sequence_with_M iI iV KFam KFam_Nonempty
  repeat assumption

  --exact Dense_list_implies_path_sequence_with_M iI iV KFam KFam_Nonempty separated has_dense_sets
let KSeq:= hNonemp.some
have h1: Has_length_d_path (Clump_Family_Union KFam) (h*m):=by
  apply clump_path_sequence_gives_path iI iV KFam KSeq

apply has_path_monotone   (Clump_Family_Union KFam)  L.Gr (h*m) _ (h1)
exact family_union_from_familycontainedinL L KFam KFam_In_L
