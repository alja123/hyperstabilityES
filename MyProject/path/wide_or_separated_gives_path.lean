
import MyProject

import MyProject.path.numbersfind

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
variable (iSub: Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )
variable (pLarge: p≥ 20)
variable (prggp: pr ≥ gg2 p)
variable (hggp: h ≥ gg1 pr)
variable (κggh: κ ≥ gg1 h)
variable (mggκ :m≥ gg2 κ )
variable (GComplete: G=completeGraph V)
variable (Vcard: Fintype.card V ≥ 4 * m)




/-
lemma clump_path_sequence_gives_path4
(H: Subgraph G)
(KFam: Finset (Clump G p m κ pr h))
(Seq: ClumpPathSequence iI iV κ  KFam)
(Seqlen: Seq.Ord.length=h* pr*pr*pr+1)
(Fam_in_H':∀ (i : (Clump G p m κ pr h) ), i∈ KFam →  i.Gr≤ H)
(narrow': Clump_family_narrow' KFam)
:
∃  (u v: V), ∃  (P: SubgraphPath H u v), P.Wa.length ≥  h*m


structure ClumpPathSequence
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
--(H: Subgraph G)
(L: Locally_Dense G p m h)
(K: Clump G p m κ pr h)
(K_In_L: K.Gr≤ L.Gr)
(hWide1: K.k≥ pr*pr*pr*pr*h)
(hWide2: K.k≤  4*pr*pr*pr*pr*h)
:
Has_length_d_path (L.Gr) (h*m):=by
have hNonemp: Nonempty (ClumpPathSequence iI iV κ  {K}):=by
  apply Wide_clump_implies_path_sequence --iI iV _ _ _ _  α K hWide1 hWide2
  repeat assumption
  --

let KSeq:= hNonemp.some
have h1: ∃  (u v: V), ∃  (P: SubgraphPath (L.Gr) u v), P.Wa.length ≥  (h*m):= by
  apply clump_path_sequence_gives_path4
  exact κPositive
  exact pPositive
  exact mPositive
  exact hPositive
  exact prPositive
  repeat assumption
  simp
  exact K_In_L
  unfold Clump_family_narrow'
  simp
  calc
   K.k≤ 4*pr*pr*pr*pr*h:= by exact hWide2
   _≤ 5*pr*pr*pr*pr*h:= by gcongr;simp




rcases h1 with ⟨u,v, SP, hSP ⟩

  --
--have h1: Has_length_d_path (Clump_Family_Union {K}) (h*m):=by

unfold Has_length_d_path

use u
use v
use SP
--  apply clump_path_sequence_gives_path iI iV {K} KSeq

--apply has_path_monotone   (Clump_Family_Union {K})  L.Gr (h*m) _ (h1)
--calc
--  Clump_Family_Union {K} = K.Gr:= by exact Clump_Family_Union_singleton K
--  _ ≤ L.Gr:= by exact K_In_L


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
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
(κggα: κ ≥ gg1 α )
(αggh: α ≥ h)
:
Has_length_d_path (L.Gr) (h*m):=by
have hNonemp: Nonempty (ClumpPathSequence iI iV κ KFam):=by
  apply Dense_list_implies_path_sequence_with_M iI iV
  repeat assumption


  --exact Dense_list_implies_path_sequence_with_M iI iV KFam KFam_Nonempty separated has_dense_sets
let KSeq:= hNonemp.some
have h1: ∃  (u v: V), ∃  (P: SubgraphPath (L.Gr) u v), P.Wa.length ≥  (h*m):= by
  apply clump_path_sequence_gives_path4
  exact κPositive
  exact pPositive
  exact mPositive
  exact hPositive
  exact prPositive
  repeat assumption
  intro Ki hKi
  calc
    Ki.k≤ pr * pr * pr * pr * h:= by exact narrow Ki hKi
    _=1*pr * pr * pr * pr * h:= by ring_nf
    _≤ _:= by gcongr;simp
  --
rcases h1 with ⟨u,v, SP, hSP ⟩

unfold Has_length_d_path

use u
use v
use SP
