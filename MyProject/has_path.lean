
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

lemma has_path_monotone
(H K: Subgraph G)
(d: ℕ)
(hHK: H≤ K)
(hHasPath: Has_length_d_path H d)
:
Has_length_d_path K d:=by
rcases hHasPath with ⟨u, v, P, hP⟩
use u
use v
have P_in_K: P.Wa.toSubgraph≤ K:=by
  calc
    P.Wa.toSubgraph ≤ H:= by exact P.Wa_In_H
    _≤ K:= by exact hHK
let P':SubgraphPath K u v:=⟨P.Wa, P.Wa_Is_Path, P_in_K⟩
use P'



def Vertex_list_in_clump_list
  (Ord: List (Clump G p m κ pr h))
  (Ver: List V): Prop:=
  ∀ (i: ℕ), (i< Ord.length-1)→ ((Ver.get! i)∈  (((Ord.get! i).Gr.verts)∩((Ord.get! (i+1)).Gr.verts)))


def M_list_in_clump_list
  (ML: List (Subgraph G))
  (Ord: List (Clump G p m κ pr h))
  : Prop:=
  ∀ (i: Fin (Ord.length)), ((ML.get! i)∈  ((Ord.get! i).M))


def Clump_Family_Union
(KFam: Finset (Clump G p m κ pr h))
:Subgraph G
:= sSup (Finset.image (fun C: Clump G p m κ pr h => C.Gr) KFam)


structure ClumpPathSequence
(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (MSparse: ???)
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver)
  (hlength: Ord.length ≥  h*pr)

structure ClumpPathSequence_nolength
(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver)
 -- (hlength: Ord.length ≥  h*pr)


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

lemma define_constant_list
(K: Clump G p m κ pr h)
(n:ℕ )
(hn: n>0)
:
∃ (L: List (Clump G p m κ pr h)), L.length=n∧(∀ (i: Fin (L.length)), (L.get i=K))∧ (L.toFinset= {K}):=by

refine List.exists_iff_exists_tuple.mpr ?_
let f: Fin (n)→  Clump G p m κ pr h:=fun x=> K
use n
use f
constructor
exact List.length_ofFn f
constructor
intro i
exact List.get_ofFn f i
dsimp [f]
--simp only [List.ofFn_const, List.toFinset_eq_empty_iff]
--refine subset_singleton_iff'.mpr ?h.right.right.a
simp
refine List.toFinset_replicate_of_ne_zero ?h.right.right.hn
exact Nat.not_eq_zero_of_lt hn

lemma get_eq_get!
{α: Type u}
(hI: Inhabited α)
(L: List α)
(i: Fin L.length)
:
L.get i = L.get! i:=by
refine (List.get!_of_get? ?_).symm
apply List.get_eq_iff.1
exact rfl

lemma get_eq_get2!
{α: Type u}
(hI: Inhabited α)
(L: List α)
(i: ℕ )
(hi: i<L.length)
:
L.get ⟨ i,hi ⟩ = L.get! i:=by
have h1: L.get ⟨ i,hi ⟩ = L.get! (⟨ i,hi ⟩: Fin L.length):=by
  apply get_eq_get!
rw[h1]

lemma define_constant_list_get!
(K: Clump G p m κ pr h)
(n:ℕ )
(hn: n>0)
:
∃ (L: List (Clump G p m κ pr h)), L.length=n∧(∀ (i:ℕ ), (i< L.length→ (L.get! i=K)))∧ (L.toFinset={K}):=by
have h1:_:=by exact define_constant_list K n hn
rcases h1 with ⟨ L, ⟨ hL1, ⟨ hL2, hL3⟩ ⟩  ⟩
use L
constructor
exact hL1
constructor
intro i hi
let j: Fin (L.length):= ⟨ i,hi⟩
have h2: L.get j=K:=by
  exact hL2 j
rw[h2.symm]
dsimp [j]
exact (get_eq_get2! iI L i hi).symm
exact hL3

lemma Wide_clump_implies_path_sequence
(K: Clump G p m κ pr h)
(hWide1: K.k≥ pr*pr*h)
(hWide2: K.k≤  4*pr*pr*h)
: Nonempty (ClumpPathSequence iI iV {K})
:=by
have hcard: K.Gr.verts.toFinset.card ≥  (h*pr):=by
  sorry
have hVex: ∃(VS:Finset V), (VS⊆ K.Gr.verts.toFinset)∧ (VS.card = (h*pr)):=by
  exact exists_smaller_set K.Gr.verts.toFinset (h*pr) hcard

rcases hVex with ⟨ VS, ⟨VS1, VS2 ⟩   ⟩
let VL:= VS.toList


have LEx: ∃ (L: List (Clump G p m κ pr h)), L.length=(h*pr)+1∧(∀ (i:ℕ ), (i< L.length→ (L.get! i=K)))∧ L.toFinset={K}:=by
  apply define_constant_list_get!
  exact Nat.zero_lt_succ (h * pr)
rcases LEx with ⟨ LK, ⟨ hLK1, hLK2, hLK3⟩  ⟩


refine Nonempty.intro ?val
refine
  { Ord := ?val.Ord, Ord_eq_KFam := ?KFam, Ver := ?val.Ver, VerNoDup := ?val.VerNoDup,
    VerInOrd := ?val.VerInOrd, hlength := ?val.hlength }
exact LK

refine subset_singleton_iff.mpr ?KFam.a
right
exact hLK3

exact VL
exact nodup_toList VS
unfold Vertex_list_in_clump_list
intro i hi
have hi':i<LK.length:=by
  exact Nat.lt_of_lt_pred hi
have hleneq: VL.length = VS.card:=by
  exact length_toList VS
have hlen: VL.length = (h*pr):=by
  rw[hleneq]
  exact VS2
have hi2: i<VL.length:=by
  rw[hlen]
  rw[hLK1] at hi
  exact hi
have h1: VL.get! i∈ K.Gr.verts:=by
  dsimp [VL]
  have h2: (VS.toList).get! i =(VS.toList).get ⟨ i, hi2⟩ :=by
    exact (get_eq_get2! iV VS.toList i (sorryAx (i < VS.toList.length) true)).symm
  rw[h2]
  have h3: (VS.toList).get ⟨ i, hi2⟩ ∈ VS.toList.toFinset:=by
    refine List.mem_toFinset.mpr ?_
    exact List.get_mem VS.toList i hi2
  simp at h3
  exact Set.mem_toFinset.mp (VS1 h3)
have h2: LK.get! i=K:=by
  exact hLK2 i hi'
have h3: (LK.get! (i + 1))=K:=by
  apply hLK2
  exact Nat.add_lt_of_lt_sub hi
have h4: (LK.get! i).Gr.verts ∩ (LK.get! (i + 1)).Gr.verts=K.Gr.verts:=by
  rw[h2]
  rw[h3]
  simp
rw[h4]
exact h1

exact Nat.le.intro (id hLK1.symm)




lemma dense_list_implies_path_sequence2
(KFam: Finset (Clump G p m κ pr h))
(t: ℕ)
(ht: t≤ h*pr)
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
∃ (S:ClumpPathSequence_nolength iI iV KFam), S.Ord.length=t
:=by
unfold family_contains_dense_list at has_dense_sets
rcases has_dense_sets with ⟨ LA, ⟨ hLA1, ⟨ hLA2, hLA3⟩ ⟩ ⟩
unfold clump_list_dense at hLA3

sorry


lemma dense_list_implies_path_sequence
(KFam: Finset (Clump G p m κ pr h))
(t: ℕ)
(ht: t≤ h*pr)
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
∃ (S:ClumpPathSequence_nolength iI iV KFam), S.Ord.length=t
:=by
induction' t with t' ht'
--Ord: List (Clump G p m κ pr h))
simp
let Ord:List (Clump G p m κ pr h):= []
have Ord_eq_KFam: Ord.toFinset⊆  KFam:=by exact inter_eq_left.mp rfl
let Ver: List V:=[]
have VerNoDup: Ver.Nodup:=by exact List.nodup_nil
have VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver:=by
  unfold Vertex_list_in_clump_list
  intro i hi
  exfalso
  exact Nat.not_succ_le_zero i hi
let S:ClumpPathSequence_nolength iI iV KFam:=⟨Ord, Ord_eq_KFam, Ver, VerNoDup, VerInOrd⟩
use S


have hineq: t' ≤ h*pr:=by exact Nat.le_of_succ_le ht
rcases ht' hineq with ⟨ S', hS'⟩

sorry



--#check Clump_family_contained_in_L L.Gr KFam

lemma Clump_Family_Union_singleton
(K: Clump G p m κ pr h)
: Clump_Family_Union {K} = K.Gr:=by
unfold  Clump_Family_Union
simp

lemma Wide_clump_implies_path
(L: Locally_Dense G p m h)
(K: Clump G p m κ pr h)
(K_In_L: K.Gr≤ L.Gr)
(hWide1: K.k≥ pr*pr*h)
(hWide2: K.k≤  4*pr*pr*h)
:
Has_length_d_path (L.Gr) (h*m):=by
have hNonemp: Nonempty (ClumpPathSequence iI iV {K}):=by
  exact Wide_clump_implies_path_sequence iI iV K hWide1 hWide2
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
(KFam_In_L:Clump_family_contained_in_L L.Gr KFam)
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
Has_length_d_path (L.Gr) (h*m):=by
have hNonemp: Nonempty (ClumpPathSequence iI iV KFam):=by
  exact dense_list_implies_path_sequence iI iV KFam narrow separated has_dense_sets
let KSeq:= hNonemp.some
have h1: Has_length_d_path (Clump_Family_Union KFam) (h*m):=by
  apply clump_path_sequence_gives_path iI iV KFam KSeq

apply has_path_monotone   (Clump_Family_Union KFam)  L.Gr (h*m) _ (h1)
exact family_union_from_familycontainedinL L KFam KFam_In_L
