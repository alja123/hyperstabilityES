import MyProject

import MyProject.cut_dense_add_vertices
import MyProject.degree_edge_basics
 --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


--set_option maxHeartbeats 400000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]

def near_regular (H:Subgraph G)(r: ℕ): Prop :=
  (H.edgeSet.toFinset.card≥ r*H.verts.toFinset.card)
  ∧ (∀ (v: V), v ∈ H.verts → H.degree v ≤  2*r)∧ (H.verts.toFinset.card>0)


def MVertex_Disjoint (M: Finset (Subgraph G)):Prop:=  ∀ (A B: Subgraph G),  A∈ M→ B∈ M→ A≠ B→ (Disjoint A.verts  B.verts)
def MNear_Regular (M: Finset (Subgraph G))(r:ℕ ):Prop:= ∀ (A: Subgraph G), A ∈ M → near_regular A r
def Mgraphs_in_H (M: Finset (Subgraph G)) (H: Finset (Subgraph G)):Prop:=  ∀ (A: Subgraph G), A ∈ M→ (∃ (B: Subgraph G), B ∈ H ∧ A ≤ B)

def Mgraphs_in_L (M: Finset (Subgraph G)) (L: Subgraph G):Prop:=  ∀ (A: Subgraph G), A ∈ M→ (A ≤ L)


def HCut_Dense_Family (H: Finset (Subgraph G))(p:ℕ ):Prop:=  ∀ (A: Subgraph G), A ∈ H → cut_dense G A p
def HOrder_ge_m_Family (H: Finset (Subgraph G))(m:ℕ ):Prop:= ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m

def HOrder_le_hm_Family (H: Finset (Subgraph G))(m h:ℕ ):Prop:= ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≤  h*m


def HEdge_Disjoint (H: Finset (Subgraph G)):Prop:=  ∀ (A B: Subgraph G),  (A∈ H)→ (B∈ H)→ (A≠ B)→ (A.edgeSet ∩ B.edgeSet = ∅)
def FamilyContained_in_Graph (H: Finset (Subgraph G))(Gr: Subgraph G):Prop:=  ∀ (A: Subgraph G), A ∈ H → A ≤ Gr
--def MContained_in_C (M: Finset (Subgraph G))(C: Subgraph G):Prop:=  ∀ (A: Subgraph G), A ∈ M → A ≤ C


@[ext] structure Clump  (G: SimpleGraph V) (p m κ pr h: ℕ ) where
  Gr: Subgraph G
  k: ℕ
  H: Finset (Subgraph G)
  M: Finset (Subgraph G)
  C: Subgraph G
  H_Edge_Disjoint:  HEdge_Disjoint H -- ∀ (A B: Subgraph G),  (A∈ H)→ (B∈ H)→ (A≠ B)→ (A.edgeSet ∩ B.edgeSet = ∅)
  M_Vertex_Disjoint: MVertex_Disjoint M -- ∀ (A B: Subgraph G),  A∈ M→ B∈ M→ A≠ B→ (Disjoint A.verts  B.verts)
  H_Cut_Dense: HCut_Dense_Family H p --∀ (A: Subgraph G), A ∈ H → cut_dense G A p
  H_Order: HOrder_ge_m_Family H m -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_Order_Upper_Bound: HOrder_le_hm_Family H m h -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_In_K: FamilyContained_in_Graph H Gr--∀ (A: Subgraph G), A ∈ H → A ≤ Gr
  H_Partition_K: sSup H= Gr
  M_Near_Regular: MNear_Regular M (m/pr) -- ∀ (A: Subgraph G), A ∈ M → near_regular A (m/pr)
  C_In_K: C≤ Gr
  M_In_C: FamilyContained_in_Graph M C--∀ (A: Subgraph G), A ∈ M → A ≤ C
  M_Size: M.card = k
  C_Cut_Dense: cut_dense G C (κ^(Nat.factorial (100*k)))
  C_Order: C.verts.toFinset.card ≤  m*h* 4^(k)
  M_graphs_in_H:  Mgraphs_in_H M H--∀ (A: Subgraph G), A ∈ M→ (∃ (B: Subgraph G), B ∈ H ∧ A ≤ B)
  k_Maximal: ¬ (∃ (M': Finset (Subgraph G)), M'.card > k ∧ (MVertex_Disjoint M')∧ (MNear_Regular M' (m/pr))∧ (Mgraphs_in_H M' H))
  Nonemptyness: k>0
def BSet  {p m κ pr: ℕ }(K: Clump G p m κ pr h): Set V
:= {v| v ∈ (K.Gr).verts∧ (((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m)}

def BSetPlusM  {p m κ pr: ℕ }(K: Clump G p m κ pr h): Set V
:= (BSet K)∪ (sSup K.M: Subgraph G).verts



lemma Singleton_HEdge_Disjoint {L: Subgraph G}{H: Finset (Subgraph G)}(hH: H={L}):
HEdge_Disjoint H := by --∀ (A B: Subgraph G),  (A∈ H)→ (B∈ H)→ (A≠ B)→ (A.edgeSet ∩ B.edgeSet = ∅):= by
  intros A B hA hB hAB
  rw[hH] at hA hB
  have h1: A=L:= by exact Finset.mem_singleton.1 hA
  have h2: B=L:= by exact Finset.mem_singleton.1 hB
  rw[h1.symm]  at h2
  symm at h2
  exact (hAB h2).elim
--def PreClump  (G: SimpleGraph V)(K: Subgraph G)(H: Finset (Subgraph G))(M: Finset (Subgraph G)) where

lemma lower_bound_vertices_by_edges
(H: Subgraph G):
(H.verts.toFinset.card).choose 2≥H.edgeSet.toFinset.card
:= by
let U:= { x // x ∈ H.verts }
let K:SimpleGraph U:=H.coe
have h1: (Fintype.card U).choose 2≥  K.edgeFinset.card:= by
  exact card_edgeFinset_le_card_choose_two
have h2: Fintype.card U= (H.verts.toFinset.card):= by
  exact (Set.toFinset_card H.verts).symm
have h3: K.edgeFinset.card= H.edgeSet.toFinset.card:= by
  sorry
--rw[h2, h3] at h1
rw[h3.symm]
rw[h2.symm]
exact h1


lemma square_ge_choose {n:ℕ }: n^2≥n.choose 2:= by
  have h1: n^2=n*n:= by ring_nf
  have h2: n.choose 2= n*(n-1)/2:= by
    exact Nat.choose_two_right n
  have h3: n*(n-1)/2 ≤ n*n:= by calc
    n*(n-1)/2 ≤ n*(n-1):= by exact Nat.div_le_self (n * (n - 1)) 2
    _≤  n*n:= by gcongr; exact Nat.sub_le n 1
  rw[h1, h2]
  exact h3

lemma lower_bound_vertices_by_edges_weaker
(H: Subgraph G):
(H.verts.toFinset.card)^2≥H.edgeSet.toFinset.card
:=by calc
  (H.verts.toFinset.card)^2≥ (H.verts.toFinset.card).choose 2:= by exact square_ge_choose
  _≥H.edgeSet.toFinset.card:= by exact lower_bound_vertices_by_edges H

lemma near_regular_vertices_lower_bound
{H: Subgraph G}
{r: ℕ}
(h: near_regular H r):
H.verts.toFinset.card ≥ r:= by
  have h1: H.edgeSet.toFinset.card≥ r*H.verts.toFinset.card:= by exact h.1
  have h2: H.verts.toFinset.card^2≥H.edgeSet.toFinset.card:= by exact lower_bound_vertices_by_edges_weaker H
  have h3: H.verts.toFinset.card*H.verts.toFinset.card≥r*H.verts.toFinset.card:= by calc
    H.verts.toFinset.card*H.verts.toFinset.card=H.verts.toFinset.card^2:= by ring_nf
    _≥r*H.verts.toFinset.card:= by exact Nat.le_trans h1 h2
  exact Nat.le_of_mul_le_mul_right h3 h.2.2


def GG (a b: ℕ ): Prop:= (1=1)--∀ (f: ℕ → ℕ ), (a≥ f b)

@[inherit_doc] infixl:50 " ≫  " => GG


theorem near_regular_subgraph {H: Subgraph G}{p pr m:ℕ }(mggp: m≫ pr)(prggp: pr≫ p)(HEdges: p*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)(HOrder: H.verts.toFinset.card≥ m): ∃ (H': Subgraph G), H' ≤ H ∧ near_regular H' (m/pr):= by
 sorry


lemma exists_M_family_in_dense_graph_in_one_subgraph
{L: Subgraph G}
{p m pr:ℕ }
(mggpr: m≫ pr)(prggp: pr≫ p)
(LEdges: p*L.edgeSet.toFinset.card≥ L.verts.toFinset.card^2)
(LOrder: L.verts.toFinset.card≥ m)
:
∃ (M: Finset (Subgraph G)), M.card = 1 ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_L M L):= by

have h1: ∃ (R: Subgraph G), R ≤ L ∧ near_regular R (m/pr):= by

  exact near_regular_subgraph mggpr prggp LEdges LOrder

rcases h1 with ⟨R, hR⟩
let M:Finset (Subgraph G):={R}
have MCard: M.card = 1:= by exact rfl
have MNearReg: MNear_Regular M (m/pr):= by
  intros A hA
  have hA': A∈ {R}:= by exact hA
  #check Finset.mem_singleton
  have hAR:  A=R:= by apply Finset.mem_singleton.1 hA'
  rw[hAR.symm] at hR
  exact hR.2

have MVertexDisj: MVertex_Disjoint M:= by
  intros A B hA hB hAB
  have hA': A∈ {R}:= by exact hA
  have hB': B∈ {R}:= by exact hB
  have hAR:  A=R:= by apply Finset.mem_singleton.1 hA'
  have hBR:  B=R:= by apply Finset.mem_singleton.1 hB'
  rw[hAR.symm] at hBR
  exact (hAB (id hBR.symm)).elim

have MCard: M.card = 1:= by exact rfl

have Mgraphs_in_L: Mgraphs_in_L M L:= by
  intros A hA
  have hA': A∈ {R}:= by exact hA
  have hAR:  A=R:= by apply Finset.mem_singleton.1 hA'
  rw[hAR]
  exact hR.1

exact ⟨M, MCard, MVertexDisj, MNearReg, Mgraphs_in_L⟩

lemma exists_M_family_in_cut_dense_family
{H: Finset (Subgraph G)}
{m p pr:ℕ }
(mggp: m≫ pr)(prggp: pr≫ p)
(HCutDense: HCut_Dense_Family H p)
(HOrderm: HOrder_ge_m_Family H m )
(HNonempty: H.Nonempty)
:∃ (M: Finset (Subgraph G)), M.card = 1 ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H):= by

have hNonempty:∃ (L: Subgraph G), L∈ H:= by exact HNonempty
rcases hNonempty with ⟨L, hL⟩
have LCutDense: cut_dense G L p:= by exact HCutDense L hL
have LOrderm: L.verts.toFinset.card ≥ m:= by exact HOrderm L hL
have LDense: (p*2)*L.edgeSet.toFinset.card ≥ L.verts.toFinset.card^2:= by exact cut_dense_edges_lower_bound LCutDense
have prggp': pr≫ p*2:= by sorry
have h1: ∃ (M: Finset (Subgraph G)), M.card = 1 ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_L M L):= by
  exact exists_M_family_in_dense_graph_in_one_subgraph mggp prggp' LDense LOrderm
rcases h1 with ⟨M, hM⟩
have hMinH: Mgraphs_in_H M H:= by
  intros A hA
  have hAL: A ≤ L:= by apply hM.2.2.2 A hA
  exact ⟨L, hL, hAL⟩
exact ⟨M, hM.1, hM.2.1, hM.2.2.1, hMinH⟩


lemma sSup_biUnion_vertices
{M: Finset (Subgraph G)}
: (sSup M: Subgraph G).verts.toFinset= M.biUnion (fun A=>A.verts.toFinset)
:=by
ext v
constructor
intro hv
simp
simp at hv
exact hv

intro hv
simp
simp at hv
exact hv



lemma MVertex_Disjoint_card
{M: Finset (Subgraph G)}
(MVertDisj: MVertex_Disjoint M):
(sSup M: Subgraph G).verts.toFinset.card = ∑ (A∈ M), A.verts.toFinset.card:= by
have h1: (sSup M: Subgraph G).verts.toFinset= M.biUnion (fun A=>A.verts.toFinset):= by
  exact sSup_biUnion_vertices
have h2: (M.biUnion (fun A=>A.verts.toFinset)).card = ∑ (A∈ M), A.verts.toFinset.card:= by
  refine card_biUnion ?h
  intros A hA B hB hAB
  have h3: Disjoint A.verts B.verts:= by
    exact MVertDisj A B hA hB hAB
  exact Set.disjoint_toFinset.mpr (MVertDisj A B hA hB hAB)
rw[h1, h2]


lemma M_family_in_L_upper_bound_size
{M: Finset (Subgraph G)}
{L: Subgraph G}
{pr:ℕ }
(hMinH: Mgraphs_in_L M L)
(MNearReg: MNear_Regular M (m/pr))
(MVertDisj: MVertex_Disjoint M):
L.verts.toFinset.card≥ M.card*(m/pr) := by
have h1: ∀ (A: Subgraph G), A ∈ M → A.verts.toFinset.card ≥ (m/pr):= by
  intros A hA
  have hA': near_regular A (m/pr):= by exact MNearReg A hA
  exact near_regular_vertices_lower_bound hA'

calc
L.verts.toFinset.card≥  (sSup M: Subgraph G).verts.toFinset.card:= by
  gcongr
  simp
  intro A hA
  have h1:  A≤ L  :=by exact hMinH A hA
  exact @subgraphs_vertex_sets_subsets V G A L h1
_= ∑ (A∈ M), A.verts.toFinset.card:= by  exact MVertex_Disjoint_card MVertDisj
_≥ ∑ (A∈ M), (m/pr):= by  exact sum_le_sum h1
_=_:= by simp

lemma Mgraphs_in_H_Mgraphs_in_L
{M H: Finset (Subgraph G)}
(hMinH: Mgraphs_in_H M H):
Mgraphs_in_L M (sSup H):= by
intros A hA
have h1: ∃ (B: Subgraph G), B ∈ H ∧ A ≤ B:= by exact hMinH A hA
rcases h1 with ⟨B, hB⟩
have h3: B∈ H:= by exact hB.1
have h2: B ≤ sSup H:= by exact CompleteLattice.le_sSup (↑H) B h3
calc
A ≤ B:= by exact hB.2
_≤ sSup H:= by exact h2


lemma M_family_in_H_upper_bound_size
{M H: Finset (Subgraph G)}
{pr:ℕ }
(hMinH: Mgraphs_in_H M H)
(MNearReg: MNear_Regular M (m/pr))
(MVertDisj: MVertex_Disjoint M):
M.card * (m/pr) ≤  ((sSup H: Subgraph G).verts).toFinset.card
:= by
have h1: Mgraphs_in_L M (sSup H):= by exact Mgraphs_in_H_Mgraphs_in_L hMinH
let L0:Subgraph G:= (sSup ↑H:Subgraph G)
have hL: L0=sSup H:= by rfl
have h1: Mgraphs_in_L M L0:= by exact h1
have h5: ∃ (L: Subgraph G), L.verts = (sSup H: Subgraph G).verts∧ (Mgraphs_in_L M L):= by
  use L0
rcases h5 with ⟨L, hL⟩
have h6: L.verts.toFinset.card= ((sSup H: Subgraph G).verts).toFinset.card:= by
  simp_rw[hL.symm]
rw[h6.symm]
exact M_family_in_L_upper_bound_size hL.2 MNearReg MVertDisj


lemma have_1_in_k_Set
{H: Finset (Subgraph G)}
{m p pr:ℕ }
(mggp: m≫ pr)(prggp: pr≫ p)
(HCutDense: HCut_Dense_Family H p)
(HOrderm: HOrder_ge_m_Family H m )
(HNonempty: H.Nonempty)
(Sk: Set ℕ )
(hSk: Sk={ k:ℕ | ∃ (M: Finset (Subgraph G)), (M.card = k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H)})
: 1∈ Sk:= by
have h1: ∃ (M: Finset (Subgraph G)), M.card = 1 ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H):= by
  exact exists_M_family_in_cut_dense_family  mggp prggp HCutDense HOrderm HNonempty
rcases h1 with ⟨M, hM⟩
rw[hSk]
simp
use M

lemma k_Set_finite
{H: Finset (Subgraph G)}
{pr m:ℕ }
(hpmPositive: (m/pr)>0)
(Sk: Set ℕ )
(hSk: Sk={ k:ℕ | ∃ (M: Finset (Subgraph G)), (M.card = k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H)})
:∀ x ∈ Sk, x ≤ ((sSup H: Subgraph G).verts).toFinset.card/(m/pr)+1:= by
  intros x hx
  rw[hSk] at hx
  simp at hx
  rcases hx with ⟨M, hM⟩
  have h1: M.card=x:= by exact hM.1
  rw[h1.symm]
  have h1: M.card*(m/pr) ≤ ((sSup H: Subgraph G).verts).toFinset.card*1:= by calc
   M.card*(m/pr) ≤ ((sSup H: Subgraph G).verts).toFinset.card:= by exact M_family_in_H_upper_bound_size hM.2.2.2 hM.2.2.1 hM.2.1
   _= ((sSup H: Subgraph G).verts).toFinset.card*1:= by ring_nf
  calc
  M.card≤ (((sSup H: Subgraph G).verts).toFinset.card/(m/pr)+1)*1:= by
    exact nat_div_ge (sSup H:Subgraph G).verts.toFinset.card (m/pr) 1 M.card h1 hpmPositive
  _= ((sSup H: Subgraph G).verts).toFinset.card/(m/pr)+1:= by ring_nf

lemma maximal_k_existence
{H: Finset (Subgraph G)}
{m p pr:ℕ }
(mggp: m≫ pr)(prggp: pr≫ p)
(HCutDense: HCut_Dense_Family H p)
(HOrderm: HOrder_ge_m_Family H m )
(HNonempty: H.Nonempty)
(hpm: m/pr>0)
:∃ (k: ℕ),
(∃ (M: Finset (Subgraph G)), (M.card = k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H))
∧ ¬(∃ (M: Finset (Subgraph G)), (M.card > k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H))
∧ k≥ 1
∧ k≤ ((sSup H: Subgraph G).verts).toFinset.card/(m/pr)+1
:= by
let Sk: Set ℕ := { k:ℕ | ∃ (M: Finset (Subgraph G)), (M.card = k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H)}
let upperbound:ℕ := ((sSup H: Subgraph G).verts).toFinset.card/(m/pr)+1
have hbounded: ∀ x ∈ Sk, x ≤  upperbound:= by
  exact fun x a ↦    k_Set_finite hpm      {k | ∃ M, M.card = k ∧ MVertex_Disjoint M ∧ MNear_Regular M (m/pr) ∧ Mgraphs_in_H M H} rfl x a
let k:=sSup Sk
have h1inSk: 1∈ Sk:= by
  exact have_1_in_k_Set mggp prggp HCutDense HOrderm HNonempty  Sk rfl
have SkNonempty: Sk.Nonempty:= by
  exact ⟨1, h1inSk⟩
have SkBoundedAbove: BddAbove Sk:= by
  exact ⟨upperbound, hbounded⟩
have h2:k∈ Sk:= by exact Nat.sSup_mem SkNonempty SkBoundedAbove
--have h3: k+1∉ Sk:= by
--  have h4: k+1>k:= by exact lt_add_one k
--  exact not_mem_of_csSup_lt h4 SkBoundedAbove
have h5: ∃ (M: Finset (Subgraph G)), (M.card = k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H):= by
  exact h2
have h6: ¬(∃ (M: Finset (Subgraph G)), (M.card > k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H)):= by
  by_contra hcont
  rcases hcont with ⟨M, hM⟩
  have h7: M.card ∈ Sk:=by
    use M
    constructor
    exact rfl
    exact hM.2
  have h8: M.card > sSup Sk:= by
    calc M.card>k:= by exact hM.1
    _= sSup Sk:= by exact rfl
  have h9:M.card≤ sSup Sk:= by
    exact  ConditionallyCompleteLattice.le_csSup Sk M.card SkBoundedAbove h7
  have h10: ¬ (M.card≤ sSup Sk):= by exact Nat.not_le_of_lt h8
  exact h10 h9
have hkpos: k≥ 1:= by exact ConditionallyCompleteLattice.le_csSup Sk 1 SkBoundedAbove h1inSk
have hkub: k≤ upperbound:= by exact hbounded k h2
exact ⟨k, h5, h6, hkpos, hkub⟩



lemma initial_clump_construction
{L: Subgraph G}
{p pr κ m h: ℕ}
(mggp: m≫ pr)(prggp: pr≫ p)
(hpm: m/pr>0)
(hLorderUpperBound: L.verts.toFinset.card ≤  m*h*4)
(hLorderm: L.verts.toFinset.card ≥ m)
(hLorderhm: L.verts.toFinset.card ≤  h*m)
(hL: cut_dense G L p):
∃ (X: Clump G p m κ pr h), X.Gr=L ∧ X.H={L}∧ X.C=L
∧ X.k≥ 1∧ X.k≤ L.verts.toFinset.card/(m/pr)+1
:= by

let H: Finset (Subgraph G):={L}
have hHL: H={L}:= by rfl
have HNonempty: H.Nonempty:= by
  exact ⟨L, Finset.mem_singleton.2 rfl⟩
have HCutDense: HCut_Dense_Family H p:= by
  intros A hA
  have h1: A=L:= by exact Finset.mem_singleton.1 hA
  rw[h1]
  exact hL
have HOrderm: HOrder_ge_m_Family H m:= by
  intros A hA
  have h1: A=L:= by exact Finset.mem_singleton.1 hA
  rw[h1]
  exact hLorderm

have HOrder_le_hm: HOrder_le_hm_Family H m h:= by
  intros A hA
  have h1: A=L:= by exact Finset.mem_singleton.1 hA
  rw[h1]
  exact hLorderhm


have h1:∃ (k: ℕ),
(∃ (M: Finset (Subgraph G)), (M.card = k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H))
∧ ¬(∃ (M: Finset (Subgraph G)), (M.card > k) ∧ (MVertex_Disjoint M)∧ (MNear_Regular M (m/pr))∧ (Mgraphs_in_H M H))
∧ k≥ 1
∧ k≤ ((sSup H: Subgraph G).verts).toFinset.card/(m/pr)+1
:= by exact maximal_k_existence mggp prggp  HCutDense HOrderm HNonempty hpm

rcases h1 with ⟨k, hk⟩
rcases hk.1 with ⟨M, hM⟩


let C:Subgraph G:=L
have hCL: C=L:= by rfl
have CCut_dense: cut_dense G C (κ^(Nat.factorial (100*k))):= by
  sorry
have COrder: C.verts.toFinset.card ≤  m* h*4^(k):= by calc
  C.verts.toFinset.card = L.verts.toFinset.card:= by rfl
  _≤ m* h*4^(1):= by exact hLorderUpperBound
  _≤ m* h*4^(k):=by gcongr; exact NeZero.one_le; exact hk.2.2.1

have HEdgeDisj: HEdge_Disjoint H:= by exact Singleton_HEdge_Disjoint hHL

have HinK: ∀ (A: Subgraph G), A ∈ H → A ≤ L:= by
  intros A hA
  have h1: A=L:= by exact Finset.mem_singleton.1 hA
  rw[h1]

have HPartitionK: (sSup H:Subgraph G)= L:= by
  rw[hHL]
  simp

have CinK: C ≤ L:= by rfl

have MinC: ∀ (A: Subgraph G), A ∈ M → A ≤ C:= by
  intros A hA
  have h1: _ := by exact hM.2.2.2 A hA
  rcases h1 with ⟨B, hB⟩
  have h2: B=L:= by exact Finset.mem_singleton.1 hB.1
  rw[h2] at hB
  rw[hCL]
  exact hB.2

have hkpos: k>0:= by calc
  k≥ 1:= by exact hk.2.2.1
  _>0:= by exact Nat.zero_lt_one

let X: Clump G p m κ pr h:=⟨L, k,  H, M, C, HEdgeDisj, hM.2.1, HCutDense, HOrderm,HOrder_le_hm , HinK, HPartitionK, hM.2.2.1, CinK, MinC, hM.1, CCut_dense, COrder, hM.2.2.2, hk.2.1, hkpos⟩
use X
repeat constructor; exact rfl
constructor
repeat
  calc
  X.k=k:= by rfl
  _≥ 1:= by exact hk.2.2.1

calc
X.k=k:= by rfl
_≤ ((sSup H: Subgraph G).verts).toFinset.card/(m/pr)+1:= by exact hk.2.2.2
_= L.verts.toFinset.card/(m/pr)+1:= by rw[HPartitionK.symm]; simp
