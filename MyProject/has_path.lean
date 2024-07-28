
import MyProject

import MyProject.J_bound
import MyProject.clumpfamily_maximal
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

def M_list_union
(Li: List (Subgraph G))
: Subgraph G:= sSup (Li.toFinset)

def M_list_union_dropping_first --(p m κ pr h : ℕ )
(Li: List (Subgraph G))
: Subgraph G
:=M_list_union  (Li.drop (1))



def M_list_sparse_at_1 --( p m κ pr h α: ℕ )
(m β: ℕ )
(Li: List (Subgraph G))
:=β*((Li.head!.verts)∩(( M_list_union_dropping_first Li).verts)).toFinset.card≤  m




def M_list_sparse -- ( p m κ pr h α: ℕ )
(m β : ℕ )
(Li: List (Subgraph G))
:=
--∀ (i: ℕ ),  @M_list_sparse_at_1 V G FinV   p m κ pr h α β  (Li.rotate i)
∀ (i: ℕ ),  M_list_sparse_at_1  m  β  (Li.rotate i)



structure ClumpPathSequence
 (β : ℕ )(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (LM_Sparse: M_list_sparse m β LM )
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver)
  (hlength: Ord.length ≥  h*pr)

structure ClumpPathSequence_nolength
 (β : ℕ )(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (LM_Sparse: M_list_sparse m β LM )
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver)
   -- (hlength: Ord.length ≥  h*pr)


structure ClumpPathSequence_nolength_noM
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
(ClumpPathSeq: ClumpPathSequence iI iV α KFam)
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
(β: ℕ )
(K: Clump G p m κ pr h)
(hWide1: K.k≥ pr*pr*h)
(hWide2: K.k≤  4*pr*pr*h)
: Nonempty (ClumpPathSequence iI iV β {K})
:=by
have hcard: K.Gr.verts.toFinset.card ≥  (h*pr):=by
  sorry
have hVex: ∃(VS:Finset V), (VS⊆ K.Gr.verts.toFinset)∧ (VS.card = (h*pr)):=by
  exact exists_smaller_set K.Gr.verts.toFinset (h*pr) hcard

have Mcard: K.M.card≥ h*pr :=by
  sorry

have hMex: ∃(MS:Finset (Subgraph G)), (MS⊆ K.M)∧ (MS.card = (h*pr)):=by
  exact exists_smaller_set K.M (h * pr) Mcard

rcases hVex with ⟨ VS, ⟨VS1, VS2 ⟩   ⟩
let VL:= VS.toList

rcases hMex with ⟨ MS, ⟨MS1, MS2 ⟩   ⟩
let ML:= MS.toList



have LEx: ∃ (L: List (Clump G p m κ pr h)), L.length=(h*pr)+1∧(∀ (i:ℕ ), (i< L.length→ (L.get! i=K)))∧ L.toFinset={K}:=by
  apply define_constant_list_get!
  exact Nat.zero_lt_succ (h * pr)
rcases LEx with ⟨ LK, ⟨ hLK1, hLK2, hLK3⟩  ⟩


refine Nonempty.intro ?val
refine
  { Ord := ?val.Ord, Ord_eq_KFam := ?KFam, LM := ?val.LM, LM_in_M := ?val.LM_in_M,
    LM_Sparse := ?val.LM_Sparse, Ver := ?val.Ver, VerNoDup := ?val.VerNoDup,
    VerInOrd := ?val.VerInOrd, hlength := ?val.hlength }

exact LK

refine subset_singleton_iff.mpr ?KFam.a
right
exact hLK3
exact ML
--M_list_in_clump_list iI ML LK
sorry
-- M_list_sparse m β ML
sorry
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



/-
lemma dense_list_implies_path_sequence2
(KFam: Finset (Clump G p m κ pr h))
(t β : ℕ)
(ht: t≤ h*pr)
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
∃ (S:ClumpPathSequence_nolength iI iV β KFam), S.Ord.length=t
:=by
unfold family_contains_dense_list at has_dense_sets
rcases has_dense_sets with ⟨ LA, ⟨ hLA1, ⟨ hLA2, hLA3⟩ ⟩ ⟩
unfold clump_list_dense at hLA3

sorry

structure ClumpPathSequence_nolength_noM
 (KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver)
-/

lemma get_last_eq
{T: Type}
{hI: Inhabited T}
(L: List T)
(LP2: L≠ [])
: L.get! (L.length -1)=L.getLast LP2
:=by
simp
have LengthPos: L.length>0:=by exact List.length_pos.mpr LP2
have h1: L.length-1<L.length:=by
  refine Nat.sub_one_lt_of_le LengthPos ?h₁
  exact Nat.le_refl L.length
calc
L.getD (L.length - 1) default=L.get ⟨ (L.length-1), h1⟩:=by
  exact List.getD_eq_get L default h1
_=L.getLast LP2 :=by exact List.get_length_sub_one h1

lemma get_last_eq_clump

(L: List (Clump G p m κ pr h))
(LP2: L≠ [])
: L.get! (L.length -1)=L.getLast LP2
:=by
simp
have LengthPos: L.length>0:=by exact List.length_pos.mpr LP2
have h1: L.length-1<L.length:=by
  refine Nat.sub_one_lt_of_le LengthPos ?h₁
  exact Nat.le_refl L.length
calc
L.getD (L.length - 1) default=L.get ⟨ (L.length-1), h1⟩:=by
  exact List.getD_eq_get L default h1
_=L.getLast LP2 :=by exact List.get_length_sub_one h1


/-lemma get_last_eq!
(T: Type)
(hI: Inhabited T)
(L: List T)
(LP2: L≠ [])
: L.getLast!=L.get! (L.length -1)
:=by
simp
calc
L.getLast!=L.getLast LP2:=by
  apply?

_=L.get! (L.length -1):=by exact (get_last_eq T hI L LP2).symm
-/

def dense_clump_family
(KFam: Finset (Clump G p m κ pr h))
:=
∀ (K: Clump G p m κ pr h),
K∈ KFam→
(α*(((BSet K)∩(Set.sUnion (Finset.image BSet (KFam\{K}) ).toSet)).toFinset.card)≥ m)



lemma finset_diff_int
(A B C: Finset V)
:
A∩ (B\ C)=(A∩ B)\ (A∩ C)
:=by
aesop



lemma bigunion_comparision_one_direction_BSet
(F: Finset (Clump G p m κ pr h))
(K: Clump G p m κ pr h)
(a:V)
:
a ∈ (⋃ H ∈ F, BSet K ∩ BSet H).toFinset
→
a∈ (Finset.biUnion F (fun H=>(BSet K∩ BSet H).toFinset))


:= by

intro h
refine mem_biUnion.mpr ?_

have h0: a ∈ (⋃ H ∈ F, BSet K ∩ BSet H):= by
  exact Set.mem_toFinset.mp h
have h1: ∃ H ∈ F, a ∈ BSet K ∩ BSet H:=by

  have h3:_:= by apply Set.mem_iUnion.1 h0
  rcases h3 with ⟨ x, y⟩
  have h4:_:= by apply Set.mem_iUnion.1 y
  rcases h4 with ⟨ z, h6⟩
  use x



rcases h1 with ⟨ a1, ha1⟩
have h12: a ∈ BSet K ∩ BSet a1:= by
  exact ha1.2
have h2:a ∈ (BSet K ∩ BSet a1).toFinset:= by
  exact Set.mem_toFinset.mpr h12

use a1
exact ⟨ha1.1, h2⟩


lemma bigunion_equality_Bset
(F: Finset (Clump G p m κ pr h))
(K: Clump G p m κ pr h)
:
(⋃ x ∈ F, BSet K ∩ BSet x).toFinset
=
(Finset.biUnion F (fun x=>(BSet K∩ BSet x).toFinset))
--(⋃ H ∈ F, H.verts).toFinset=(Finset.biUnion F (fun x=>x.verts.toFinset))
--(⋃ H ∈ F, H.verts).toFinset.card≤∑ H∈ F, H.verts.toFinset.card
:= by

ext a
constructor
exact fun a_1 ↦ bigunion_comparision_one_direction_BSet F K a a_1


intro b
refine Set.mem_toFinset.mpr ?_
refine Set.mem_iUnion₂.mpr ?_

have h1: ∃ H ∈ F, a ∈ (BSet K∩ BSet H).toFinset:=by
  exact mem_biUnion.mp b

rcases h1 with ⟨ a1, ha1⟩
have h11:_:= by
  exact ha1.1
have h12:_:= by
  exact ha1.2
use a1
simp
have h12: a ∈ (BSet K∩ BSet a1) := by exact Set.mem_toFinset.mp h12
constructor
exact Set.mem_of_mem_inter_left h12
constructor
exact h11
exact Set.mem_of_mem_inter_right h12

lemma separated_weakening
(KFam: Finset (Clump G p m κ pr h))
(K1 K2 : G.Clump p m κ pr h)
(hK1: K1 ∈ KFam)
(hK2: K2 ∈ KFam)
(hdiff: K1 ≠ K2)
(separated: Clump_family_separated KFam)
:  κ * (BSet K1 ∩ BSet K2).toFinset.card ≤  m
:=by
have h1: κ ^ (10 * (100 * K1.k.max K2.k).factorial) * (BSet K1 ∩ BSet K2).toFinset.card < m
  :=by
    apply separated
    repeat assumption
calc
κ * (BSet K1 ∩ BSet K2).toFinset.card
≤
κ ^ (10 * (100 * K1.k.max K2.k).factorial) * (BSet K1 ∩ BSet K2).toFinset.card
:=by
  gcongr
  --κ ≤ κ ^ (10 * (100 * K1.k.max K2.k).factorial)
  sorry
_≤ m:=by
  exact Nat.le_of_succ_le (separated K1 K2 hK1 hK2 hdiff)


lemma separated_Bset_int_union_bound
(KFam Av: Finset (Clump G p m κ pr h))
(K: Clump G p m κ pr h)
(hK: K ∈ KFam)
(hK2: K∉ Av)
(hAv:Av⊆  KFam)
(separated: Clump_family_separated KFam)
--(narrow: Clump_family_narrow KFam)
:
 κ *
(⋃ x ∈ Av, ↑(BSet K).toFinset ∩ BSet x).toFinset.card
≤ (Av.card*m)
:= by
--unfold Clump_family_separated at separated
--unfold Clumps_separated at separated

simp only [Set.coe_toFinset,  Fintype.card_ofFinset]
calc
κ * (⋃ x ∈ Av, BSet K ∩ BSet x).toFinset.card
= κ * (Finset.biUnion Av (fun x=>(BSet K∩ BSet x).toFinset)).card:=by
  congr
  exact bigunion_equality_Bset Av K
_≤  κ *(∑  (x ∈ Av), (BSet K ∩ BSet x).toFinset.card):=by
  gcongr
  simp
  exact card_biUnion_le
_= (κ *(∑  (x ∈ Av), (BSet K ∩ BSet x).toFinset.card)):=by
  ring_nf
_= (∑  (x ∈ Av), κ *(BSet K ∩ BSet x).toFinset.card):=by
  congr
  exact mul_sum Av (fun i ↦ (BSet K ∩ BSet i).toFinset.card) κ
_≤ (∑  (x ∈ Av), m):=by
  gcongr with Ki hKi
  apply separated_weakening KFam K Ki
  repeat assumption
  exact hAv hKi
  exact Ne.symm (ne_of_mem_of_not_mem hKi hK2)
  repeat assumption
_=(Av.card*m):=by
  congr
  exact sum_const_nat fun x ↦ congrFun rfl



lemma dense_family_subfamily
(KFam: Finset (Clump G p m κ pr h))
(KL:  Clump G p m κ pr h)
(KLInFam: KL∈ KFam)
--(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(dense_family: @dense_clump_family V G FinV FinV2 p m κ pr h α  KFam   )

(Av: Finset (Clump G p m κ pr h))
(AvoidContained: Av⊆ KFam)
(AvoidCard: Av.card≤ h*pr)
:
@dense_clump_family V G FinV FinV2 p m κ pr h (2*α)  (KFam\ Av)
:=by

unfold dense_clump_family
intro K hK
unfold Clump_family_separated at separated
--simp only [coe_image, coe_sdiff, coe_singleton, Set.sUnion_image,  mem_coe,
--  Set.mem_singleton_iff, Set.toFinset_inter, ge_iff_le]
--simp
unfold dense_clump_family at dense_family

simp at dense_family


have hAvSum: κ *( (⋃ x ∈ Av,(BSet K).toFinset ∩ BSet x).toFinset).card ≤ (Av.card*m):=by
  apply separated_Bset_int_union_bound KFam Av;
  repeat assumption
  simp at hK
  exact hK.1
  simp at hK
  exact hK.2
  repeat assumption


have hK_in_KFam: K ∈ KFam:=by
  simp at hK
  exact hK.1


calc
  2 * α * (BSet K ∩ ((image BSet ((KFam \ Av) \ {K})).toSet).sUnion).toFinset.card
  ≥ 2 * α * (BSet K ∩ (((image BSet (((KFam ) \ {K}))).toSet.sUnion)\ ((image BSet   Av).toSet.sUnion))).toFinset.card:=by
    gcongr
    simp
    gcongr
    simp
    refine Set.diff_subset_iff.mpr ?bc.a.h.a
    simp
    intro Ki hKi1 hKi2
    by_cases case: Ki∈ Av
    have h1:BSet Ki ⊆ (⋃ x ∈ Av, BSet x):=by
      exact Set.subset_biUnion_of_mem case
    exact
      Set.subset_union_of_subset_left h1 (⋃ x, ⋃ (_ : (x ∈ KFam ∧ x ∉ Av) ∧ ¬x = K), BSet x)

    have h2: (Ki ∈ KFam ∧ Ki ∉ Av) ∧ ¬Ki = K:=by
      aesop
    have h1: BSet Ki ⊆ ⋃ x, ⋃ (_ : (x ∈ KFam ∧ x ∉ Av) ∧ ¬x = K), BSet x:=by
      exact Set.subset_biUnion_of_mem h2
    exact Set.subset_union_of_subset_right h1 (⋃ x ∈ Av, BSet x)

  _= 2 * α * (
  (BSet K ∩ ((image BSet (((KFam ) \ {K}))).toSet.sUnion))
  \
  (BSet K ∩ ((image BSet   Av).toSet.sUnion))
  ).toFinset.card:=by
    simp
    congr
    left
    congr
    apply finset_diff_int

  _≥ 2 * α * (((
  (BSet K ∩ ((image BSet (((KFam ) \ {K}))).toSet.sUnion))
  ).toFinset.card)
  -
  ((BSet K ∩ ((image BSet   Av).toSet.sUnion)).toFinset.card)
  ):=by

    gcongr
    simp
    exact card_le_card_sdiff_add_card






  _≥ m:=by
    simp only [coe_image, coe_sdiff, coe_singleton, Set.sUnion_image,  mem_coe,
       Set.toFinset_inter]

    simp only [Set.mem_diff, mem_coe, Set.mem_singleton_iff, ge_iff_le]
    calc
      2 * α *
     (((BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card -
      ((BSet K).toFinset ∩ (⋃ x ∈ Av, BSet x).toFinset).card)
      =
      2 * α *
     (( (BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card -
      ( (⋃ x ∈ Av,(BSet K).toFinset ∩ BSet x).toFinset).card)
      :=by
        congr
        simp
        ext a
        constructor
        intro h
        simp
        simp at h
        aesop

        intro h
        simp
        simp at h
        aesop

      _=

      2*α *( (BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card -
      2 * α *( (⋃ x ∈ Av,(BSet K).toFinset ∩ BSet x).toFinset).card
      :=by
        simp
        exact
          Nat.mul_sub_left_distrib (2 * α)
            ((BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card
            (filter (fun x ↦ x ∈ BSet K ∧ ∃ x_1 ∈ Av, x ∈ BSet x_1) univ).card
      _=

      α *( (BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card*2 -
      2 * α *( (⋃ x ∈ Av,(BSet K).toFinset ∩ BSet x).toFinset).card
      :=by
        ring_nf

      _≥
      α *( (BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card*2 -
      κ *( (⋃ x ∈ Av,(BSet K).toFinset ∩ BSet x).toFinset).card / (h*pr)
      :=by
        sorry

      _≥
      α *( (BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card*2 -
      (Av.card*m)/ (h*pr)
      :=by

        gcongr

      _≥
      α *( (BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card*2 -
      (h*pr*m)/ (h*pr)
      :=by
        gcongr

      _=
      α *( (BSet K).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = K), BSet x).toFinset).card*2 -
      m
      :=by
        congr
        refine Nat.mul_div_cancel_left m ?_
        exact Nat.mul_pos hPositive prPositive
        --apply separated_Bset_int_union_bound

      _≥
      m*2 -
      m
      :=by
        gcongr
        apply dense_family
        exact hK_in_KFam




      _= m*2-m*1:=by ring_nf
      _= m*(2-1):=by exact (Nat.mul_sub_left_distrib m 2 1).symm
      _= m:=by simp
-- 2 * α * ((BSet K).toFinset ∩ (⋃ x, ⋃ (_ : (x ∈ KFam ∧ x ∉ Av) ∧ ¬x = K), BSet x).toFinset).card
--  ≥  2 * α * ((BSet K).toFinset ∩ (⋃ x, ⋃ (_ : (x ∈ KFam ∧ x ∉ Av) ∧ ¬x = K), BSet x).toFinset).card:=by sorry
--  _≥ m:=by sorry


lemma dense_list_implies_larger_list_no_Av
(KFam: Finset (Clump G p m κ pr h))
(KL:  Clump G p m κ pr h)
(KLInFam: KL∈ KFam)
(VOld: Finset V)
(hVOld: VOld.card≤ h*pr)
--(narrow: Clump_family_narrow KFam)
--(separated: Clump_family_separated KFam)
(dense_family: @dense_clump_family V G FinV FinV2 p m κ pr h α  KFam   )
:
∃ (K': Clump G p m κ pr h),
∃ (v': V),
(K'∈  KFam
∧ (v'∈ (BSet K' ∩ BSet KL))
∧ (v' ∉ VOld)
∧ K'≠ KL)
:=by
unfold dense_clump_family at dense_family
have hKint: α * (BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset.card ≥ m:=by
  apply dense_family KL
  repeat assumption

have hsizebigger:  (BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset.card ≥  VOld.card+1:=by
  sorry

have hnonempty:  ((BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset\ VOld).card >0:=by
  calc
  ((BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset\ VOld).card
  ≥ (BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset.card- VOld.card:=by
    exact le_card_sdiff VOld (BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset
  _≥ VOld.card+1-VOld.card:=by
    gcongr ?_-VOld.card
  _>0:=by
    simp

have hnonempty: Finset.Nonempty ((BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset\ VOld):=by
  simp
  simp at hnonempty
  exact card_pos.mp hnonempty

simp at hnonempty
rcases hnonempty with ⟨ v', h1⟩
simp at h1
let ⟨⟨  ha, hc⟩, hb⟩:= h1
rcases hc with ⟨ Hi, ⟨⟨ hHi1, hHi2⟩ , hHi3⟩ ⟩
use Hi
use v'

aesop



lemma dense_list_implies_larger_list_and_v
(KFam: Finset (Clump G p m κ pr h))
(KL:  Clump G p m κ pr h)
(KLInFam: KL∈ KFam)
--(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(dense_family: @dense_clump_family V G FinV FinV2 p m κ pr h α  KFam   )

(Av: Finset (Clump G p m κ pr h))
(AvoidContained: Av⊆ KFam)
(AvoidCard: Av.card≤ h*pr)

(VOld: Finset V)
(hVOld: VOld.card≤ h*pr)
:
∃ (K': Clump G p m κ pr h),
∃ (v': V),
(K'∈  KFam
∧ (v'∈ (BSet K' ∩ BSet KL))
∧ (v' ∉ VOld)
∧  K'∉Av)
:=by
let KFam2:= KFam\ (Av\ {KL})
have KLInFam2: KL∈ KFam2:=by
  aesop
have hAvCont: Av \ {KL}⊆ Av:=by
  exact sdiff_subset Av {KL}
have Fam2Separated: Clump_family_separated KFam2:=by
  sorry
have Fam2_dense: @dense_clump_family V G FinV FinV2 p m κ pr h (2*α)  KFam2:=by
  apply dense_family_subfamily
  repeat assumption
  exact fun ⦃a⦄ a_1 ↦ AvoidContained (hAvCont a_1)
  calc
    (Av \ {KL}).card ≤ Av.card:=by exact card_le_of_subset hAvCont
    _≤ h * pr:= by exact AvoidCard

have hEx1:
  ∃ (K': Clump G p m κ pr h),
  ∃ (v': V),
  (K'∈  KFam2
  ∧ (v'∈ (BSet K' ∩ BSet KL))
  ∧ (v' ∉ VOld)
  ∧ K'≠ KL)
  :=by
    apply dense_list_implies_larger_list_no_Av
    repeat assumption

rcases hEx1 with ⟨ Knew, ⟨ v', ⟨ h1, ⟨ h2, ⟨ h3, h4⟩⟩⟩⟩⟩
use Knew
use v'
dsimp [KFam2] at h1
constructor
simp at h1
exact h1.1
constructor
exact h2
constructor
exact h3
aesop


lemma dense_list_implies_larger_list_no_Av2
(KFam: Finset (Clump G p m κ pr h))
(KL:  Clump G p m κ pr h)
(KLInFam: KL∈ KFam)
--(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(dense_family: @dense_clump_family V G FinV FinV2 p m κ pr h α  KFam   )
:
∃ (Knew: Clump G p m κ pr h),
Knew∈ KFam
∧ (BSet Knew ∩ BSet KL).toFinset.card> h*pr
:=by
unfold dense_clump_family at dense_family
have hKint: α * (BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset.card ≥ m:=by
  apply dense_family KL
  repeat assumption
by_contra contr
simp at contr
have hunion: (BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset.card≤ h*pr*KFam.card:=by
  simp only [coe_image, coe_sdiff, coe_singleton, Set.sUnion_image, mem_coe,
    Set.mem_singleton_iff, Set.toFinset_inter]
  simp

  calc
    ((BSet KL).toFinset ∩ (⋃ x, ⋃ (_ : x ∈ KFam ∧ ¬x = KL), BSet x).toFinset).card

    =
    ((⋃ x ∈ KFam\ {KL},(BSet KL).toFinset ∩ BSet x).toFinset).card:=by
        congr
        simp
        ext a
        constructor
        intro h
        simp
        simp at h
        aesop

        intro h
        simp
        simp at h
        constructor
        exact h.1
        aesop
    _=
    ((⋃ x ∈ KFam\ {KL},(BSet KL) ∩ BSet x).toFinset).card:=by
      simp

    _= (Finset.biUnion (KFam\ {KL}) (fun x=>(BSet KL∩ BSet x).toFinset)).card:=by
        congr
        exact bigunion_equality_Bset (KFam\ {KL}) KL


    _≤
    ∑ x ∈ KFam\ {KL},(((BSet KL) ∩ BSet x).toFinset.card):=by
      exact card_biUnion_le

    _≤
    ∑ x ∈ KFam\ {KL},(h*pr):=by
      gcongr with Ki hKi
      calc
        (BSet KL ∩ BSet Ki).toFinset.card
        =
        ((BSet Ki).toFinset ∩ (BSet KL).toFinset).card:=by
          simp
          rw [@inter_comm]


        _≤ h * pr
        :=by apply contr; simp at hKi; exact hKi.1;







    _= ((KFam\ {KL}).card)*(h * pr) :=by
      exact sum_const_nat fun x ↦ congrFun rfl
    _≤ ((KFam).card)*(h * pr):=by
      gcongr
      exact sdiff_subset KFam {KL}
    _=(h * pr)*((KFam).card):=by
      ring_nf


have hc1: α * h*pr*(KFam.card)≥ m:=by
  calc
    α * h*pr*(KFam.card)
    =
    α * (h*pr*(KFam.card)):= by
      ring_nf
    _≥
    α *((BSet KL ∩ ((image BSet (KFam \ {KL})).toSet).sUnion).toFinset.card):=by
      gcongr α * ?_
    _≥ m:=by
      exact dense_family KL KLInFam



sorry

lemma dense_list_implies_larger_list2
(KFam: Finset (Clump G p m κ pr h))
(KL:  Clump G p m κ pr h)
(KLInFam: KL∈ KFam)
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(dense_family: @dense_clump_family V G FinV FinV2 p m κ pr h α  KFam   )

(Av: Finset (Clump G p m κ pr h))
(AvoidContained: Av⊆ KFam)
(AvoidCard: Av.card≤ h*pr)
:
∃ (Knew: Clump G p m κ pr h),
Knew∈ KFam
∧ Knew∉Av
∧ (Knew.Gr.verts ∩ KL.Gr.verts).toFinset.card> h*pr
:=by
unfold dense_clump_family at dense_family
have hInt: _ :=by apply dense_family KL KLInFam

sorry








lemma dense_list_implies_path_sequence
(KFam: Finset (Clump G p m κ pr h))
(KFamNonempty: KFam.Nonempty)
(t: ℕ)
(ht: t≤ h*pr)
(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
∃ (S: ClumpPathSequence_nolength_noM iI iV KFam), S.Ord.length=t+1∧ S.Ver.length=t∧ S.Ord.Nodup
:=by
induction' t with t' ht'
--Ord: List (Clump G p m κ pr h))
simp
rcases KFamNonempty with ⟨K, hK ⟩
let Ord:List (Clump G p m κ pr h):= [K]
have Ord_eq_KFam: Ord.toFinset⊆  KFam:=by
  dsimp[Ord]
  simp
  exact hK
let Ver: List V:=[]
have VerNoDup: Ver.Nodup:=by exact List.nodup_nil
have VerInOrd:Vertex_list_in_clump_list iI iV Ord Ver:=by
  unfold Vertex_list_in_clump_list
  intro i hi
  exfalso
  exact Nat.not_succ_le_zero i hi
let S:ClumpPathSequence_nolength_noM iI iV KFam:=⟨Ord, Ord_eq_KFam, Ver, VerNoDup, VerInOrd⟩
use S
constructor
exact rfl
constructor
exact rfl
dsimp[Ord]
exact List.nodup_singleton K

have hineq: t' ≤ h*pr:=by exact Nat.le_of_succ_le ht
rcases ht' hineq with ⟨ S', ⟨ hS'1, ⟨ hS'2, hS'3⟩ ⟩ ⟩
have OrdNE:S'.Ord≠ []:=by exact List.ne_nil_of_length_eq_succ hS'1
let KLast: Clump G p m κ pr h:= S'.Ord.getLast OrdNE
have hnewKEx: ∃ (Knew: Clump G p m κ pr h), Knew∈ KFam∧ Knew∉S'.Ord ∧ (Knew.Gr.verts ∩ KLast.Gr.verts).toFinset.card> h*pr:=by
  sorry
rcases hnewKEx with ⟨ Knew, ⟨ hKnew1, ⟨ hKnew2, hKnew3⟩ ⟩ ⟩

have hv_ex: ∃ (v: V), v∈ (Knew.Gr.verts ∩ KLast.Gr.verts).toFinset\ S'.Ver.toFinset:= by
  sorry

rcases hv_ex with ⟨ vNew, hvNew⟩
let OrdNew: List (Clump G p m κ pr h):= S'.Ord ++ [Knew]
let VerNew: List V:= S'.Ver ++ [vNew]
have hVerNew: VerNew.Nodup:=by
  dsimp[VerNew]
  refine List.Nodup.append ?d₁ ?d₂ ?dj
  exact S'.VerNoDup
  exact List.nodup_singleton vNew
  simp
  simp at hvNew
  exact hvNew.2
have hVerInOrdNew: Vertex_list_in_clump_list iI iV OrdNew VerNew:=by
  unfold Vertex_list_in_clump_list
  intro i hi
  by_cases case: i < S'.Ord.length-1
  have hv: VerNew.get! i= S'.Ver.get! i:=by
    dsimp[VerNew]
    simp
    apply List.getD_append
    calc
      i < S'.Ord.length-1 := by exact case
        _=S'.Ver.length:=by
          rw[hS'1, hS'2]
          simp
  have hOr: OrdNew.get! i= S'.Ord.get! i:=by
    dsimp[OrdNew]
    simp
    apply List.getD_append
    calc
      i < S'.Ord.length - 1:= by exact case
      _≤  S'.Ord.length := by
        exact Nat.sub_le S'.Ord.length 1
  have hOr2: OrdNew.get! (i+1)= S'.Ord.get! (i+1):=by
    dsimp[OrdNew]
    simp
    apply List.getD_append
    exact Nat.add_lt_of_lt_sub case


  rw[hv, hOr, hOr2]
  apply S'.VerInOrd
  exact case

  simp at case
  dsimp [OrdNew] at hi
  simp at hi
  have i_eq: i+1=S'.Ord.length:=by
    exact (Nat.le_antisymm case hi).symm
  have i_eq2: i=S'.Ord.length-1:=by exact Nat.eq_sub_of_add_eq i_eq
  have hOrdlast: OrdNew.get! (i + 1)=Knew:=by
    dsimp [OrdNew]
    rw[i_eq]
    simp
    have hle: S'.Ord.length< (S'.Ord ++ [Knew]).length:=by
      simp
    calc
      (S'.Ord ++ [Knew]).getD S'.Ord.length default=(S'.Ord ++ [Knew]).get ⟨ S'.Ord.length, hle⟩ :=by
        exact
          List.getD_eq_get (S'.Ord ++ [Knew]) default
            (sorryAx (S'.Ord.length < (S'.Ord ++ [Knew]).length) true)

      _=Knew:=by
        apply List.get_last
        simp
  have hOrdlast2: OrdNew.get! i=KLast:=by
    dsimp[OrdNew]
    calc
    (S'.Ord ++ [Knew]).get! i=(S'.Ord).get! i:=by
      simp
      exact List.getD_append S'.Ord [Knew] default i hi
    _=(S'.Ord).get! (S'.Ord.length-1):=by
      rw[i_eq2]
    _=KLast:=by
      dsimp [KLast]
      apply get_last_eq_clump iI  (S'.Ord) OrdNE

  have hVertLast:VerNew.get! i=vNew:=by
    dsimp[VerNew]
    rw[i_eq2]
    rw[hS'1, hS'2.symm]
    simp
    have hne:S'.Ver.length< (S'.Ver ++ [vNew]).length:=by
      exact List.get_of_append_proof rfl rfl
    calc
      (S'.Ver ++ [vNew]).getD S'.Ver.length default
      =(S'.Ver ++ [vNew]).get ⟨ S'.Ver.length, hne⟩:=by
        exact List.getD_eq_get (S'.Ver ++ [vNew]) default hne
      _=vNew:= by exact List.get_of_append rfl rfl

  rw[hOrdlast, hOrdlast2, hVertLast]
  simp  at hvNew
  simp
  aesop

have hOrdNew: OrdNew.toFinset⊆ KFam:=by
  dsimp[OrdNew]
  simp
  refine union_subset_iff.mpr ?_
  constructor
  exact S'.Ord_eq_KFam
  simp
  exact hKnew1
let S: ClumpPathSequence_nolength_noM iI iV KFam:=⟨OrdNew, hOrdNew, VerNew, hVerNew, hVerInOrdNew⟩
use S
constructor
simp
dsimp[OrdNew]
rw[hS'1.symm]
calc
  (S'.Ord ++ [Knew]).length=(S'.Ord).length + ([Knew]).length:=by
    exact List.length_append S'.Ord [Knew]
  _= S'.Ord.length + 1:=by
    simp

simp
dsimp[OrdNew]
constructor
dsimp[VerNew]
simp
--refine (Nat.eq_add_of_sub_eq ?h.right.left.hle ?h.right.left.h).symm
-- 1 ≤ t'
exact hS'2

--exact id hS'2.symm

refine List.Nodup.append ?h.right.d₁ ?h.right.d₂ ?h.right.dj
exact hS'3
exact List.nodup_singleton Knew
simp
exact hKnew2




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
