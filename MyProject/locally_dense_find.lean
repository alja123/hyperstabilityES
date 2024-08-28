import MyProject

import MyProject.J_bound
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
variable (iSub:Inhabited (Subgraph G))

-- only need m≥ 2p
variable (pLarge: p≥ 20)
variable (prggp: pr ≥ gg2 p)
variable (hggp: h ≥ gg1 pr)
variable (κggh: κ ≥ gg1 h)
variable (mggκ :m≥ gg2 κ )
--variable (iSP:Inhabited (SubgraphPath_implicit   G) )




/-
@[ext] structure Locally_Dense  (G: SimpleGraph V) (p m    h: ℕ ) where
  Gr: Subgraph G
  H: Finset (Subgraph G)
  H_Edge_Disjoint:  HEdge_Disjoint H -- ∀ (A B: Subgraph G),  (A∈ H)→ (B∈ H)→ (A≠ B)→ (A.edgeSet ∩ B.edgeSet = ∅)
  H_Cut_Dense: HCut_Dense_Family H p --∀ (A: Subgraph G), A ∈ H → cut_dense G A p
  H_Order: HOrder_ge_m_Family H m -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_Order_Upper_Bound: HOrder_le_hm_Family H m h -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_In_K: FamilyContained_in_Graph H Gr--∀ (A: Subgraph G), A ∈ H → A ≤ Gr
  H_Partition_K: sSup H= Gr-/



lemma cut_dense_nonempty_edgeset
(D: Subgraph G)
(hcd: cut_dense G D p )
(ord: D.verts.toFinset.card≥ (p*2))
:
Nonempty D.edgeSet:= by

have hne: D.edgeSet.toFinset.card>0:= by
      calc
        D.edgeSet.toFinset.card
        ≥ D.verts.toFinset.card^2/(p*2):=by
          refine Nat.div_le_of_le_mul ?_
          apply cut_dense_edges_lower_bound
          assumption
        _≥ (p*2)^2/(p*2):= by
          gcongr
        _= (p*2)*(p*2)/(p*2):= by ring_nf
        _=(p*2):=by
          apply  Nat.mul_div_left (p * 2)
          apply mul_pos
          assumption
          simp
        _>0:=by
          apply mul_pos
          assumption
          simp
have hne2: D.edgeSet.toFinset≠ ∅ := by
      exact card_positive_implies_nonempty_finset hne
simp at hne2
exact Set.nonempty_iff_ne_empty'.mpr hne2

lemma cut_dense_nonempty_edgeset_m
(D: Subgraph G)
(hcd: cut_dense G D p )
(ord: D.verts.toFinset.card≥ m)
:
Nonempty D.edgeSet:= by
apply cut_dense_nonempty_edgeset
exact pPositive
repeat assumption
calc
  D.verts.toFinset.card ≥ m:= by assumption
  _≥ 10000*κ^3:= by
    apply gg1_1
    apply gg2_gg1
    repeat assumption
  _≥ 2*κ^1:= by
    gcongr
    simp
    assumption
    simp
  _≥ 2*h:= by
    ring_nf
    gcongr
    apply gg1_ge
    repeat assumption
  _≥ 2*pr:= by
    ring_nf
    gcongr
    apply gg1_ge
    repeat assumption
  _≥ p * 2:=by
    ring_nf
    gcongr
    apply gg2_ge
    repeat assumption


lemma locally_dense_find
(H: Subgraph G)
:
∃ (L : Locally_Dense G p m h),
∃ (R: Subgraph G),
L.Gr⊔ R =  H
∧ (∀ (D: Subgraph G), (D ≤ R)→ (D.verts.toFinset.card≥ m)→ (D.verts.toFinset.card≤   h*m)→ (¬ (cut_dense G D p )))
:= by

let S: Set ℕ := {n | ∃ (L : Locally_Dense G p m h), L.Gr ≤  H∧ L.Gr.edgeSet.toFinset.card=n}
have Sboundedabove: BddAbove S:=by
  refine bddAbove_def.mpr ?_
  use H.edgeSet.toFinset.card
  intro y hy
  dsimp [S] at hy
  rcases hy with ⟨L, hL, hL2⟩
  rw[hL2.symm]
  gcongr
  simp
  exact subgraph_implies_edgesets_subsets hL

let max: ℕ := sSup S

have max_in_S: max ∈ S:=by
  refine Nat.sSup_mem ?h₁ Sboundedabove
  use 0
  dsimp[S]
  simp only [card_eq_zero]

  let H': Finset (Subgraph G):=∅
  let Gr:Subgraph G:= sSup H'
  have H_Edge_Disjoint:  HEdge_Disjoint H':= by
    intro Hi _ hHi
    exfalso
    have con: ¬(H'=∅):= by exact ne_empty_of_mem hHi
    exact con rfl
  have H_Cut_Dense: HCut_Dense_Family H' p:=by
    intro Hi hHi
    exfalso
    have con: ¬(H'=∅):= by exact ne_empty_of_mem hHi
    exact con rfl
  have H_Order: HOrder_ge_m_Family H' m:= by
    intro Hi hHi
    exfalso
    have con: ¬(H'=∅):= by exact ne_empty_of_mem hHi
    exact con rfl
  have  H_Order_Upper_Bound: HOrder_le_hm_Family H' m h := by
    intro Hi hHi
    exfalso
    have con: ¬(H'=∅):= by exact ne_empty_of_mem hHi
    exact con rfl
  have H_In_K: FamilyContained_in_Graph H' Gr:= by
    intro Hi hHi
    exfalso
    have con: ¬(H'=∅):= by exact ne_empty_of_mem hHi
    exact con rfl
  have H_Partition_K: sSup H'= Gr:= by dsimp[Gr];
  let L:Locally_Dense G p m h:=  ⟨Gr, H',H_Edge_Disjoint ,H_Cut_Dense,H_Order, H_Order_Upper_Bound, H_In_K, H_Partition_K⟩
  use L
  constructor
  dsimp[Gr]
  simp
  intro Hi hHi
  exfalso
  have con: ¬(H'=∅):= by exact ne_empty_of_mem hHi
  exact con rfl
  dsimp[L]
  dsimp[Gr]
  simp
  intro Hi hHi
  exfalso
  have con: ¬(H'=∅):= by exact ne_empty_of_mem hHi
  exact con rfl


have maxmax: ∀ (n: ℕ), n ∈ S → n ≤ max:=by
  intro n hn
  exact ConditionallyCompleteLattice.le_csSup S n Sboundedabove hn

dsimp [S] at max_in_S
rcases max_in_S with ⟨L, hL, hL2⟩

let R:Subgraph G:= H.deleteEdges L.Gr.edgeSet
use L
use R

have h5: L.Gr.verts⊆ H.verts := by
  apply  subgraphs_vertex_sets_subsets G
  exact hL

have h6: ∀ (u v: V), L.Gr.Adj u v→  H.Adj u v := by
  intro u v huv
  exact subgraph_implies_adjacency_inherited hL huv



constructor

dsimp [R]
ext x y
constructor
unfold Subgraph.deleteEdges
intro h
simp at h
rcases h with j|j
exact h5 j
exact j
intro h
simp
right
exact h
simp
constructor
intro h
rcases h with j|j
exact h6 x y j
exact j.1
intro h
by_cases case: L.Gr.Adj x y
left
exact case
right
simp at case
constructor
exact h
exact case


intro D hD1 hD2 hD4
by_contra hD5

have hinterempty:∀ (Hi: Subgraph G), Hi∈ L.H→ Hi.edgeSet∩ D.edgeSet = ∅:= by
  by_contra h
  simp at h
  rcases h with ⟨Hi, h1, h2⟩
  have hnonemp: Set.Nonempty (Hi.edgeSet ∩ D.edgeSet):=by
    exact Set.nonempty_iff_ne_empty.mpr h2
  let e: Sym2 V := hnonemp.some
  simp at e
  have he1: e∈ Hi.edgeSet ∩ D.edgeSet:= by
    exact Set.Nonempty.some_mem hnonemp

  simp at he1
  have he2: e∈ Hi.edgeSet:=by
    exact he1.1
  have he88: e∈ D.edgeSet:=by
    exact he1.2
  have h66: Hi≤ L.Gr:= by
    apply L.H_In_K
    exact h1
  have edgescont3: Hi.edgeSet⊆ L.Gr.edgeSet:= by
    exact subgraph_implies_edgesets_subsets h66

  have h89: e∈ L.Gr.edgeSet:= by
    exact edgescont3 he2
  have edgescont: D.edgeSet⊆ R.edgeSet:= by
    exact subgraph_implies_edgesets_subsets hD1
  have he3: e∈ R.edgeSet:= by
    exact edgescont he88
  have ex: ∃ (u v: V), e=s(u,v):= by
    exact Sym2_to_tuple e
  rcases ex with ⟨u, v, hex⟩
  rw[hex] at he2
  rw[hex] at he3
  dsimp[R] at he3
  simp at he3
  simp at he2
  have hh:¬L.Gr.Adj u v:= by exact he3.2
  rw[hex] at h89
  simp at h89
  exact hh h89


/-
have hDout: D∉ L.H:= by
  by_contra cont
  have hinL: D≤ L.Gr:= by
    apply L.H_In_K
    exact cont
  have edgescont: D.edgeSet⊆ L.Gr.edgeSet:= by
    exact subgraph_implies_edgesets_subsets hinL
  have oneedge: Nonempty D.edgeSet:= by

  let e: Sym2 V := oneedge.some
  have he1: e∈ D.edgeSet:= by
    exact Subtype.coe_prop oneedge.some
  have he2: e∈ L.Gr.edgeSet:=by
    exact edgescont he1
  have edgescont: D.edgeSet⊆ R.edgeSet:= by
    exact subgraph_implies_edgesets_subsets hD1
  have he3: e∈ R.edgeSet:= by
    exact edgescont he1
  have ex: ∃ (u v: V), e=s(u,v):= by
    exact Sym2_to_tuple e
  rcases ex with ⟨u, v, hex⟩
  rw[hex] at he2
  rw[hex] at he3
  dsimp[R] at he3
  simp at he3
  simp at he2
  have hh:¬L.Gr.Adj u v:= by exact he3.2
  exact hh he2
-/
let H':Finset (Subgraph G):= L.H ∪ {D}
--have H'_card:H'.card=L.H.card+1:= by
--  dsimp[H']
--  exact Finset_add_one_element hDout

let Gr': Subgraph G:= L.Gr⊔ D

have H_Partition_K: sSup H'= Gr':= by
  dsimp[H', Gr']
  rw[L.H_Partition_K.symm]
  simp
  exact sup_comm D (sSup ↑L.H)

have H_Edge_Disjoint:  HEdge_Disjoint H':= by
  unfold HEdge_Disjoint
  intros A B hA hB hAB
  dsimp [H'] at hA hB
  simp at hA hB
  rcases hA with case|case
  rcases hB with case2|case2
  apply L.H_Edge_Disjoint
  repeat assumption
  have h3: A≤ L.Gr:= by
    apply L.H_In_K
    exact case
  rw[case2]
  apply hinterempty
  exact case

  rcases hB with case2|case2
  rw[case]
  rw[Set.inter_comm]
  apply hinterempty
  exact case2


  rw[case.symm] at case2
  exact (hAB (id case2.symm)).elim


have H_Cut_Dense: HCut_Dense_Family H' p:= by
  intro A hA
  dsimp[H'] at hA
  simp at hA
  rcases hA with case|case
  apply L.H_Cut_Dense
  exact case
  rw[case]
  exact hD5

have H_Order: HOrder_ge_m_Family H' m:= by
  intro A hA
  dsimp[H'] at hA
  simp at hA
  rcases hA with case|case
  apply L.H_Order
  exact case
  rw[case]
  exact hD2

have H_Order_Upper_Bound: HOrder_le_hm_Family H' m h:= by
  intro A hA
  dsimp[H'] at hA
  simp at hA
  rcases hA with case|case
  apply L.H_Order_Upper_Bound
  exact case
  rw[case]
  exact hD4

have H_In_K: FamilyContained_in_Graph H' Gr':= by
  intro A hA
  dsimp[H'] at hA
  simp at hA
  dsimp[Gr']
  rcases hA with case|case
  refine le_sup_of_le_left ?inl.h
  apply L.H_In_K
  exact case
  rw[case]
  exact le_sup_right'

let L': Locally_Dense G p m h:=
  {Gr:=Gr'
  , H:=H'
  , H_Edge_Disjoint:=H_Edge_Disjoint
  , H_Cut_Dense:=H_Cut_Dense
  , H_Order:=H_Order
  , H_Order_Upper_Bound:=H_Order_Upper_Bound
  , H_In_K:=H_In_K
  , H_Partition_K:=H_Partition_K
  }

have hfin: L'.Gr.edgeSet.toFinset.card∈  S:= by
  dsimp[S]
  use L'
  constructor
  dsimp[L']
  dsimp[Gr']
  simp
  constructor
  exact hL
  have h2: R≤ H:= by
    dsimp[R]
    exact Subgraph.deleteEdges_le L.Gr.edgeSet
  exact Preorder.le_trans D R H hD1 h2
  dsimp[L']


have hmore: L'.Gr.edgeSet.toFinset.card>L.Gr.edgeSet.toFinset.card:= by
  dsimp [L']
  dsimp[Gr']
  simp only [Subgraph.edgeSet_sup, Set.toFinset_union,
    gt_iff_lt]
  apply card_lt_card
  simp
  refine Set.ssubset_iff_subset_ne.mpr ?h.a
  constructor
  simp

  have oneedge: Nonempty D.edgeSet:= by
    apply cut_dense_nonempty_edgeset_m
    exact κPositive
    exact pPositive
    exact hPositive
    exact prPositive
    repeat assumption


  let e: Sym2 V := oneedge.some
  have he1: e∈ D.edgeSet:= by
    exact Subtype.coe_prop oneedge.some
  have he5: e∈ L.Gr.edgeSet∪ D.edgeSet:= by
    simp
    right
    exact he1

  apply Ne.symm
  apply ne_of_mem_of_not_mem' he5

  by_contra he2
  have edgescont: D.edgeSet⊆ R.edgeSet:= by
    exact subgraph_implies_edgesets_subsets hD1
  have he3: e∈ R.edgeSet:= by
    exact edgescont he1
  have ex: ∃ (u v: V), e=s(u,v):= by
    exact Sym2_to_tuple e
  rcases ex with ⟨u, v, hex⟩
  rw[hex] at he2
  rw[hex] at he3
  dsimp[R] at he3
  simp at he3
  simp at he2
  have hh:¬L.Gr.Adj u v:= by exact he3.2
  exact hh he2


have neg: ¬(∀ n: ℕ, n∈ S→  n ≤ max):= by
  simp
  use L'.Gr.edgeSet.toFinset.card
  constructor
  exact hfin
  rw[hL2.symm]
  exact hmore

exact neg maxmax
/-
@[ext] structure Locally_Dense  (G: SimpleGraph V) (p m    h: ℕ ) where
  Gr: Subgraph G
  H: Finset (Subgraph G)
  H_Edge_Disjoint:  HEdge_Disjoint H -- ∀ (A B: Subgraph G),  (A∈ H)→ (B∈ H)→ (A≠ B)→ (A.edgeSet ∩ B.edgeSet = ∅)
  H_Cut_Dense: HCut_Dense_Family H p --∀ (A: Subgraph G), A ∈ H → cut_dense G A p
  H_Order: HOrder_ge_m_Family H m -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_Order_Upper_Bound: HOrder_le_hm_Family H m h -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_In_K: FamilyContained_in_Graph H Gr--∀ (A: Subgraph G), A ∈ H → A ≤ Gr
  H_Partition_K: sSup H= Gr-/
