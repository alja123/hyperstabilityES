import MyProject

import MyProject.clumps_BSet

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
variable {p m κ pr h: ℕ}
variable (pPositive: p>0)
variable (iSub:Inhabited (Subgraph G))


lemma clump_Hi_contained_in_three_graphs
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS  HBip: Subgraph G)
(S B M: Set V)
--(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hS: S= Hi.verts \ M)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= bipartite_induce Hi  B M)
(hHS: HS= Hi.induce S)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
--(hHi: Hi∈ K.H)
: (Hi).edgeSet⊆    (HB.edgeSet)∪ (HBip.edgeSet)∪ (HS.edgeSet)
:= by
intro e he
have hex:  ∃ (a b :V), e=s(a,b):=by exact Sym2_to_tuple e
rcases hex with ⟨a, b, habe⟩
rw [habe]
simp
rw [habe] at he
have HiAdj: Hi.Adj a b:= by exact he

have hBcomp: (Hi.verts \ BSetPlusM K)=Hi.verts \ B:= by
  rw[hB]
  exact Set.diff_self_inter.symm
have hBcomp': ∀(x:V), (x∈ Hi.verts)→ (x∉ B)→ (x∈ (Hi.verts \ BSetPlusM K)):= by
  intro x hx hnx
  rw[hBcomp]
  simp
  exact ⟨hx, hnx⟩

have hbHi: b∈ Hi.verts:= by
  have h1: Hi.Adj a b:= by exact HiAdj
  exact Hi.edge_vert (id (Subgraph.adj_symm Hi HiAdj))
have haHi: a∈ Hi.verts:= by
  have h1: Hi.Adj a b:= by exact HiAdj
  exact Hi.edge_vert he

by_cases haB: a∈ B
by_cases hbB: b∈ B
by_cases haM: a∈ M

left
left
rw[hHB]
have h2:(a ∈ B ∧ b ∈ M) ∨ (b ∈ B ∧ a ∈ M):= by
  right
  exact ⟨hbB, haM⟩
exact ⟨h2,  HiAdj⟩

by_cases hbM: b∈ M

left
left
rw[hHB]
have h2:(a ∈ B ∧ b ∈ M) ∨ (b ∈ B ∧ a ∈ M):= by
  left
  exact ⟨haB, hbM⟩
exact ⟨h2,  HiAdj⟩

right
rw [hHS]
simp
constructor
rw[hS]
exact Set.mem_diff_of_mem haHi haM
constructor
rw[hS]
exact Set.mem_diff_of_mem hbHi hbM
exact he

have hb': b∈  (Hi.verts \ BSetPlusM K):= by
  apply hBcomp'
  exact hbHi
  exact hbB
left; right
rw [hBip]
simp
constructor
right
constructor
constructor
exact hbHi
exact hbB
exact haHi
exact he


have hb': a∈  (Hi.verts \ BSetPlusM K):= by
  apply hBcomp'
  exact haHi
  exact haB
left; right
rw [hBip]
simp
constructor
left
constructor
constructor
exact haHi
exact haB
exact hbHi
exact he





lemma clump_count_Hi_edges_via_Bgraph_fixed
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HB HBip: Subgraph G)
(S B M: Set V)
--(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hS: S= Hi.verts \ M)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= bipartite_induce Hi  B M)
(hHS: HS= Hi.induce S)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
--(hHi: Hi∈ K.H)
: (Hi).edgeSet.toFinset.card≤ HB.edgeSet.toFinset.card+((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card)+HS.edgeSet.toFinset.card:= by

calc
(Hi).edgeSet.toFinset.card≤ ((HB.edgeSet)∪ (HBip.edgeSet)∪ (HS.edgeSet)).toFinset.card:=by
  gcongr
  have h1: Hi.edgeSet ⊆ (HB.edgeSet ∪ HBip.edgeSet∪ (HS.edgeSet)):= by
    exact clump_Hi_contained_in_three_graphs Hi HS HBip S B M hS hB hHB hHS hBip
  exact Set.toFinset_subset_toFinset.mpr h1
_= (((HB.edgeSet) ∪ (HBip.edgeSet)).toFinset  ∪ (HS.edgeSet).toFinset).card := by
  congr
  exact Set.toFinset_union (HB.edgeSet ∪ HBip.edgeSet) HS.edgeSet
_= ((HB.edgeSet).toFinset ∪ (HBip.edgeSet).toFinset  ∪ (HS.edgeSet).toFinset).card := by
  congr
  exact Set.toFinset_union HB.edgeSet HBip.edgeSet
_≤ ((HB.edgeSet).toFinset ∪ (HBip.edgeSet).toFinset ).card+ (HS.edgeSet).toFinset.card:= by
  exact card_union_le (HB.edgeSet.toFinset ∪ HBip.edgeSet.toFinset) HS.edgeSet.toFinset
_≤ (HB.edgeSet).toFinset.card+  (HBip.edgeSet).toFinset.card+ (HS.edgeSet).toFinset.card:= by
  gcongr
  exact card_union_le HB.edgeSet.toFinset HBip.edgeSet.toFinset
_≤  HB.edgeSet.toFinset.card+((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card)+HS.edgeSet.toFinset.card:=by
  gcongr
  --rw[hBip]
  have h1:_:=by apply edges_in_bipartite_induced_upper_bound hBip
  have h2:Hi.verts\ B=Hi.verts\ BSetPlusM K:= by
    rw[hB]
    exact Set.diff_self_inter
  rw [h2] at h1
  simp at h1
  simp
  exact h1


lemma clump_count_Hi_edges_decompose_into_three_graphs
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HB HBip: Subgraph G)
(S B M: Set V)
--(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hS: S= Hi.verts \ M)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= bipartite_induce Hi  B M)
(hHS: HS= Hi.induce S)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
--(hHi: Hi∈ K.H)
: (Hi).edgeSet.toFinset.card≤ HB.edgeSet.toFinset.card+HBip.edgeSet.toFinset.card+HS.edgeSet.toFinset.card:= by

calc
(Hi).edgeSet.toFinset.card≤ ((HB.edgeSet)∪ (HBip.edgeSet)∪ (HS.edgeSet)).toFinset.card:=by
  gcongr
  have h1: Hi.edgeSet ⊆ (HB.edgeSet ∪ HBip.edgeSet∪ (HS.edgeSet)):= by
    exact clump_Hi_contained_in_three_graphs Hi HS HBip S B M hS hB hHB hHS hBip
  exact Set.toFinset_subset_toFinset.mpr h1
_= (((HB.edgeSet) ∪ (HBip.edgeSet)).toFinset  ∪ (HS.edgeSet).toFinset).card := by
  congr
  exact Set.toFinset_union (HB.edgeSet ∪ HBip.edgeSet) HS.edgeSet
_= ((HB.edgeSet).toFinset ∪ (HBip.edgeSet).toFinset  ∪ (HS.edgeSet).toFinset).card := by
  congr
  exact Set.toFinset_union HB.edgeSet HBip.edgeSet
_≤ ((HB.edgeSet).toFinset ∪ (HBip.edgeSet).toFinset ).card+ (HS.edgeSet).toFinset.card:= by
  exact card_union_le (HB.edgeSet.toFinset ∪ HBip.edgeSet.toFinset) HS.edgeSet.toFinset
_≤ (HB.edgeSet).toFinset.card+  (HBip.edgeSet).toFinset.card+ (HS.edgeSet).toFinset.card:= by
  gcongr
  exact card_union_le HB.edgeSet.toFinset HBip.edgeSet.toFinset

lemma Hi_eq_Bi_means_HBip_empty
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HBip: Subgraph G)
(S B M: Set V)
--(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hB: B= Hi.verts∩ BSetPlusM K)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
--(hHi: Hi∈ K.H)
(hHicontained:Hi.verts⊆ B)
:  HBip.edgeSet=∅:= by
refine Set.eq_empty_iff_forall_not_mem.mpr ?_
intro x
have h1: HBip.verts= ((Hi.verts)\ B) ∪ (Hi.verts):= by
  rw[hBip]
  exact rfl
have hex:  ∃ (a b :V), x=s(a,b):=by exact Sym2_to_tuple x
rcases hex with ⟨a, b, habe⟩
rw [habe]
simp
--by_contra hc
rw[hBip]  --at hc
unfold bipartite_induce-- at hc
simp
intro h3
have h2:¬((a ∈ Hi.verts ∧ a ∉ B) ∧ b ∈ Hi.verts ∨ (b ∈ Hi.verts ∧ b ∉ B) ∧ a ∈ Hi.verts):= by
  simp
  constructor
  intro hb1 hb2
  have h4:a∈ B:=by exact hHicontained hb1
  exact fun a_1 ↦ hb2 (hHicontained hb1)

  intro hb1 hb2
  have h4:b∈ B:=by exact hHicontained hb1
  exact fun a_1 ↦ hb2 (hHicontained hb1)

exfalso
exact h2 h3




lemma Hi_eq_Bi_means_HBip_zero_edges
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HBip: Subgraph G)
(S B M: Set V)
--(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hB: B= Hi.verts∩ BSetPlusM K)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
--(hHi: Hi∈ K.H)
(hHicontained:Hi.verts ∩ BSetPlusM K = Hi.verts)
:  HBip.edgeSet.toFinset.card=0:= by
have h1: Hi.verts⊆ B:= by
  rw[hB, hHicontained]
have h2: HBip.edgeSet=∅:= by
  exact Hi_eq_Bi_means_HBip_empty Hi HBip S B M hB hBip h1
have h2: HBip.edgeSet.toFinset=∅ := by
  exact Set.toFinset_eq_empty.mpr h2
exact card_eq_zero.mpr h2

lemma clump_most_edges_of_Hi_in_Bgraph_Case_fewedgesoutsideS_fixed
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HB HBip: Subgraph G)
(S B M: Set V)
(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hS: S= Hi.verts \ M)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= bipartite_induce Hi  B M)
(hHS: HS= Hi.induce S)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
(hHi: Hi∈ K.H)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
(pLarge: p≥ 20)
: p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2
:= by
calc
p^2*(Hi).edgeSet.toFinset.card
_≤ p^2*(HB.edgeSet.toFinset.card+((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card)+ HS.edgeSet.toFinset.card):= by
  gcongr
  #check clump_count_Hi_edges_via_Bgraph_fixed
  apply clump_count_Hi_edges_via_Bgraph_fixed Hi HB HBip S B M hS hB  hHB hHS hBip
_≤ p^2*(HB.edgeSet.toFinset.card+2*p*(2*HS.edgeSet.toFinset.card)+HS.edgeSet.toFinset.card):= by
  #check clump_HS_edges_lower_bound_BS
  have hS':S = Hi.verts \ (sSup ↑K.M: Subgraph G).verts:=by
    rw[hS, hM]
    exact Set.diff_self_inter
  have h1:_:= by exact clump_HS_edges_lower_bound_BS Hi HS S hS' hHS hHi
  gcongr
_= p^2*HB.edgeSet.toFinset.card+(4*p^3+p^2)*HS.edgeSet.toFinset.card:= by
  ring_nf
_≤ p^2*HB.edgeSet.toFinset.card+p^4*HS.edgeSet.toFinset.card:= by
  gcongr
  calc
    (4*p^3+p^2)≤(4*p^3+p^3):= by
      gcongr
      exact pPositive
      simp
    _= 5*p^3:= by
      ring_nf
    _≤ 20*p^3:= by
      gcongr
      simp
    _≤ p*p^3:= by
      gcongr
    _= p^4:= by
      ring_nf
_≤ p^2*(HB).edgeSet.toFinset.card+ (HS.verts.toFinset.card)^2:= by
  gcongr
_≤ p^2*(HB).edgeSet.toFinset.card+ (Hi.verts.toFinset.card)^2:= by
  gcongr
  have h1: HS≤ Hi:= by
    rw[hHS]
    have h2: S⊆ Hi.verts:= by
      rw[hS]
      exact Set.diff_subset Hi.verts M
    exact induced_subgraph_subgraph h2
  exact subgraphs_vertex_subsets G HS Hi h1
_=  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2:= by
  ring_nf




lemma clump_most_edges_of_Hi_in_Bgraph_Case_fewedgesoutsideS_fixed_alternatenumbers
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HB HBip: Subgraph G)
(S B M: Set V)
(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hS: S= Hi.verts \ M)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= bipartite_induce Hi  B M)
(hHS: HS= Hi.induce S)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
(hHi: Hi∈ K.H)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
(pLarge: p≥ 20)
: 4*p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2*4
:= by
have pPositive:p>0:= by
  calc
    p≥ 20:= by exact pLarge
    _>0:= by
      simp

calc
4*p^2*(Hi).edgeSet.toFinset.card
_≤ 4*p^2*(HB.edgeSet.toFinset.card+((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card)+ HS.edgeSet.toFinset.card):= by
  gcongr
  #check clump_count_Hi_edges_via_Bgraph_fixed
  apply clump_count_Hi_edges_via_Bgraph_fixed Hi HB HBip S B M hS hB  hHB hHS hBip
_≤ 4*p^2*(HB.edgeSet.toFinset.card+2*p*(2*HS.edgeSet.toFinset.card)+HS.edgeSet.toFinset.card):= by
  #check clump_HS_edges_lower_bound_BS
  have hS':S = Hi.verts \ (sSup ↑K.M: Subgraph G).verts:=by
    rw[hS, hM]
    exact Set.diff_self_inter
  have h1:_:= by exact clump_HS_edges_lower_bound_BS Hi HS S hS' hHS hHi
  gcongr
_= 4*p^2*HB.edgeSet.toFinset.card+(4*4*p^3+4*p^2)*HS.edgeSet.toFinset.card:= by
  ring_nf
_≤ 4*p^2*HB.edgeSet.toFinset.card+p^4*HS.edgeSet.toFinset.card:= by
  gcongr
  calc
    (4*4*p^3+4*p^2)≤(4*4*p^3+4*p^3):= by
      gcongr
      exact pPositive
      simp
    _= 20*p^3:= by
      ring_nf
    _≤ p*p^3:= by
      gcongr
    _= p^4:= by
      ring_nf

_≤ 4*p^2*(HB).edgeSet.toFinset.card+ (HS.verts.toFinset.card)^2:= by
  gcongr
_≤ 4*p^2*(HB).edgeSet.toFinset.card+ (Hi.verts.toFinset.card)^2:= by
  gcongr
  have h1: HS≤ Hi:= by
    rw[hHS]
    have h2: S⊆ Hi.verts:= by
      rw[hS]
      exact Set.diff_subset Hi.verts M
    exact induced_subgraph_subgraph h2
  exact subgraphs_vertex_subsets G HS Hi h1
_=  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2*4:= by
  ring_nf



lemma clump_most_edges_of_Hi_in_Bgraph_fixed
{K: Clump G p m κ pr h}
(Hi HB HBip: Subgraph G)
(S B M: Set V)
(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hS: S= Hi.verts \ M)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= bipartite_induce Hi  B M)
(hHS: HS= Hi.induce S)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)))
(hHi: Hi∈ K.H)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(pLarge: p≥ 20)
: 4*p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2*4
:= by
have hS':S = Hi.verts \ (sSup ↑K.M: Subgraph G).verts:=by
    rw[hS, hM]
    exact Set.diff_self_inter

by_cases hDifferenceOrder: 2*p*S.toFinset.card≥  m
have hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2:= by
  #check clump_few_edges_outside_M

  exact clump_few_edges_outside_M iSub Hi HS S hS' hHS hHi hDifferenceOrder mggpr prggp pPositive



exact clump_most_edges_of_Hi_in_Bgraph_Case_fewedgesoutsideS_fixed_alternatenumbers Hi HB  HBip S B M hM hS hB hHB hHS hBip   hHi hfewedgeshoutsideHS pLarge


#check clump_few_edges_outside_B_case_S_Small
have hcont: Hi.verts ⊆ BSet K:= by
  apply clump_few_edges_outside_B_case_S_Small Hi HS S hS' _ hHi
  have h3:   2 * p * S.toFinset.card < m:= by exact Nat.gt_of_not_le hDifferenceOrder
  exact Nat.le_of_not_ge hDifferenceOrder

have h2:B=Hi.verts:= by
    rw[hB]
    have h4: BSetPlusM K= BSet K∪ (sSup ↑K.M: Subgraph G).verts:= by
      exact rfl
    rw[h4]
    have h5: Hi.verts⊆ (BSet K ∪ (sSup ↑K.M:Subgraph G).verts):= by
      calc
      Hi.verts⊆ BSet K:= by exact hcont
      _⊆  (BSet K ∪ (sSup ↑K.M:Subgraph G).verts):= by
        exact Set.subset_union_left (BSet K) (sSup ↑K.M:Subgraph G).verts
    have h6: Hi.verts ∩ (BSet K ∪ (sSup ↑K.M:Subgraph G).verts) ⊆  Hi.verts:= by
      exact Set.inter_subset_left Hi.verts (BSet K ∪ (sSup ↑K.M:Subgraph G).verts)
    have h7:  Hi.verts⊆ Hi.verts ∩ (BSet K ∪ (sSup ↑K.M:Subgraph G).verts):= by
      exact      Set.subset_inter (fun ⦃a⦄ a ↦ a) h5
    exact Set.eq_of_subset_of_subset h6 h7

rw [hB] at h2

#check lower_bound_vertices_by_edges
calc
4*p^2*(Hi).edgeSet.toFinset.card
≤  4*p^2*(HB.edgeSet.toFinset.card+HBip.edgeSet.toFinset.card+HS.edgeSet.toFinset.card):= by
  gcongr
  exact clump_count_Hi_edges_decompose_into_three_graphs Hi HB HBip S B M hS hB hHB hHS hBip
_=HB.edgeSet.toFinset.card*p^2*4+4*p^2*HBip.edgeSet.toFinset.card+4*p^2*HS.edgeSet.toFinset.card:= by
  ring_nf
_=HB.edgeSet.toFinset.card*p^2*4+4*p^2*0+4*p^2*HS.edgeSet.toFinset.card:= by
  congr
  exact Hi_eq_Bi_means_HBip_zero_edges Hi HBip S B M hB   hBip h2
_≤ HB.edgeSet.toFinset.card*p^2*4+4*p^2*0+4*p^2*(HS.verts.toFinset.card)^2:= by
  gcongr
  exact lower_bound_vertices_by_edges_weaker HS
_= HB.edgeSet.toFinset.card*p^2*4+(2*p*HS.verts.toFinset.card)^2:=by
  ring_nf
_= HB.edgeSet.toFinset.card*p^2*4+(2*p*S.toFinset.card)^2:=by
  congr
  repeat   rw[hHS];  exact rfl
  rw[hHS];
  exact HEq.refl fun a ↦ propDecidable (a ∈ (Hi.induce S).verts)
_≤ HB.edgeSet.toFinset.card*p^2*4+(m)^2:=by
  gcongr
  exact Nat.le_of_not_ge hDifferenceOrder
_≤ HB.edgeSet.toFinset.card*p^2*4+(Hi.verts.toFinset.card)^2:=by
  gcongr
  apply K.H_Order
  exact hHi
_=  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2*4:=by
  ring_nf






lemma clump_most_edges_of_Hi_in_Bgraph_simplified
(K: Clump G p m κ pr h)
(Hi HB: Subgraph G)
(hHB: HB= bipartite_induce Hi  (Hi.verts∩ BSetPlusM K) (Hi.verts∩(sSup K.M: Subgraph G).verts))
(hHi: Hi∈ K.H)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(pLarge: p≥ 20)
: 4*p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2*4
:= by
let M:=  Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts
have hM: M=Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts:=by exact rfl
let S:= Hi.verts \ M
have hS: S= Hi.verts \ M:=by exact rfl
let B := Hi.verts ∩ BSetPlusM K
have hB: B= Hi.verts ∩ BSetPlusM K:=by exact rfl
let HS := Hi.induce S
have hHS: HS = Hi.induce S:=by exact rfl
let HBip := bipartite_induce Hi (Hi.verts \ B) Hi.verts
have hBip: HBip = bipartite_induce Hi (Hi.verts \ B) Hi.verts:=by exact rfl
apply clump_most_edges_of_Hi_in_Bgraph_fixed
exact pPositive
exact iSub
exact hM
exact hS
exact hB
rw[hB, hM]
exact hHB
exact hHS
repeat assumption

/-

lemma clump_most_edges_of_Hi_in_Bgraph_simplified
{K: Clump G p m κ pr h}
{Hi HB: Subgraph G}
{B M: Set V}
(hM: M= Hi.verts∩(sSup K.M: Subgraph G).verts)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= bipartite_induce Hi  B M)
(hHi: Hi∈ K.H)
: 4*p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2*4
:= by
let S: Set V:= Hi.verts \ M
let HS: Subgraph G:= Hi.induce S
let HBip: Subgraph G:= bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts)
let hS: S= Hi.verts \ M:= by exact rfl
let hHS: HS= Hi.induce S:= by exact rfl
let hBip: HBip= bipartite_induce Hi ((Hi.verts)\ B) (Hi.verts):= by exact rfl






lemma edges_in_clump
{K: Clump G p m κ pr h}
:K.Gr.edgeSet.toFinset.card= ∑ Hi in K.H, (Hi: Subgraph G).edgeSet.toFinset.card:= by
rw[K.H_Partition_K.symm]
--simp
have h1: (sSup ↑K.H: Subgraph G).edgeSet =⋃ (Hi ∈ K.H), (Hi: Subgraph G).edgeSet:= by
  exact Subgraph.edgeSet_sSup (↑K.H:Set G.Subgraph)
have h2: (sSup ↑K.H: Subgraph G).edgeSet.toFinset =(⋃ (Hi ∈ K.H), (Hi: Subgraph G).edgeSet).toFinset:= by
  exact Set.toFinset_inj.mpr h1

have h3: (⋃ (Hi ∈ K.H), (Hi: Subgraph G).edgeSet).toFinset=⋃ (Hi ∈ K.H), ((Hi: Subgraph G).edgeSet.toFinset):=by
  exact?
rw[h2]



lemma clump_most_edges_in_Bgraph
{K: Clump G p m κ pr h}
{HB: Subgraph G}
{B M: Set V}
(hM: M= (sSup K.M: Subgraph G).verts)
(hB: B=  BSetPlusM K)
(hHB: HB= bipartite_induce K.Gr  B M)
 : 4*p*(K.Gr).edgeSet.toFinset.card≤  (K.Gr).edgeSet.toFinset.card+(HB).edgeSet.toFinset.card*p*4


have heq: Hi=HB:= by
  rw[hHB]

  rw[h2]
  -----FIX THIS
  exact Subgraph.induce_self_verts.symm
calc
p^2*Hi.edgeSet.toFinset.card
= Hi.edgeSet.toFinset.card * p ^ 2:=by
  ring_nf
_= HB.edgeSet.toFinset.card * p ^ 2:=by
  rw[heq]
_≤ Hi.verts.toFinset.card ^ 2 + HB.edgeSet.toFinset.card * p ^ 2:=by
  exact Nat.le_add_left (HB.edgeSet.toFinset.card * p ^ 2) (Hi.verts.toFinset.card ^ 2)
-/








lemma clump_BcapM_order_improved
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi: Subgraph G)
(hHi: Hi∈ K.H)
(pLarge: p≥ 20)
(mLarge: m≥ 20)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
: 2*p*(Hi.verts ∩ (sSup K.M: Subgraph G).verts).toFinset.card≥  Hi.verts.toFinset.card:= by



let S:Set V:=(Hi.verts \ (sSup K.M: Subgraph G).verts)
have hSe:∃ (S:Set V), S= Hi.verts \ (sSup K.M: Subgraph G).verts:= by
  use S
rcases hSe with ⟨S, hS⟩

have hDisjoint: Disjoint S (sSup K.M: Subgraph G).verts:= by
  rw[hS]
  exact Set.disjoint_sdiff_left
let HS: Subgraph G:= Hi.induce S
by_contra hc


have hc: 2 * p * (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card < Hi.verts.toFinset.card:= by
  exact Nat.gt_of_not_le hc
have hc'':2 * p * (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card ≤  Hi.verts.toFinset.card:= by
  gcongr


have hc3:  (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card ≤  Hi.verts.toFinset.card/(2*p)+1:= by
  apply Nat_div_ge_simpler
  calc
    (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card*(2 * p)=2 * p * (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card:= by ring_nf
    _≤  Hi.verts.toFinset.card:= by exact hc''
  exact Nat.succ_mul_pos 1 pPositive





have heq:(Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card+ S.toFinset.card=  Hi.verts.toFinset.card:= by
  rw[hS]
  have h1: _:= by apply Set_card_sum_intersection_difference ((sSup ↑K.M: Subgraph G).verts) (Hi.verts)
  simp_rw[h1.symm]
  simp

have hs1: S.toFinset.card≥ Hi.verts.toFinset.card-Hi.verts.toFinset.card/(2*p)-1:= by
  apply Nat.sub_le_of_le_add
  apply Nat.sub_le_of_le_add
  calc
  Hi.verts.toFinset.card
  =(Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card+ S.toFinset.card:= by
    exact heq.symm
  _≤  1 + Hi.verts.toFinset.card / (2 * p)+S.toFinset.card:= by
    gcongr
    ring_nf
    ring_nf at hc3
    exact hc3
  _= S.toFinset.card+1 + Hi.verts.toFinset.card / (2 * p):= by
    ring_nf



have h2:
@Set.toFinset V (Hi.verts \ (sSup ↑K.M: Subgraph G).verts) (Hi.verts.fintypeDiffLeft (sSup ↑K.M: Subgraph G).verts)
=S.toFinset:= by
  rw[hS]
  simp



have hc1: m≤ 2 * p * (S).toFinset.card := by
  calc
   2 * p * (S).toFinset.card ≥  2 * p * (Hi.verts.toFinset.card-Hi.verts.toFinset.card/(2*p)-1):= by
    gcongr
  _≥ 2 * p * (Hi.verts.toFinset.card/2):=by
    gcongr
    apply minus_two_quarters_halves
    gcongr
    calc
      2*p≥ 2*20:= by
        gcongr
      _=40:= by
        ring_nf
      _≥ 4:= by
        simp

    calc
      Hi.verts.toFinset.card / 4≥ m/4:= by
        gcongr
        apply K.H_Order
        assumption
      _≥ 20/4:= by
        gcongr
      _≥ 1:= by
        simp



  _≥ 2 * p * (m/2):=by
    gcongr
    apply K.H_Order
    exact hHi
  _≥ 2*2*(m/2):=by
    gcongr
    calc
      p≥ 20:= by assumption
      _≥ 2:= by simp
  _=4*(m/2):=by
    ring_nf
  _≥ m:= by
    apply four_times_half_ge
    calc
      m≥ 20:= by
        assumption
      _≥ 4:= by
        simp
    --




  /-m≤ Hi.verts.toFinset.card:= by
    apply K.H_Order
    exact hHi
  _= (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card+ S.toFinset.card:= by
    rw[heq.symm]

  _≤  2 * p * (S).toFinset.card := by-/
   --calc
  --m≤2*p*(Hi.verts \ (sSup K.M: Subgraph G).verts).toFinset.card:= by exact Nat.le_of_not_lt hc
  --_= 2*p*(S).toFinset.card:= by congr

--have hc':  (S:Set V).toFinset.card ≥  (m/(2*p)):= by exact Nat.div_le_of_le_mul hc1


--have hSS:  (HS.verts) =(S):= by exact rfl
--have hSS':  (HS.verts).toFinset =(S:Set V).toFinset:= by
--  rw [hSS]



--rw [hSS'.symm] at hc'



have hedges: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2:= by
  exact clump_few_edges_outside_M iSub Hi HS S hS rfl hHi hc1 mggpr prggp pPositive

have mindegproportion: min_degree_at_least_proportion Hi p:= by
  apply cut_dense_min_degree_proportion_at_least;
  apply K.H_Cut_Dense;
  exact hHi

have Uupperbound:  2*p*(Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card ≤ Hi.verts.toFinset.card:= by
  exact hc''


have sdif: (Hi.verts \ (sSup ↑K.M:Subgraph G).verts)=(Hi.verts \ (Hi.verts∩ (sSup ↑K.M:Subgraph G).verts)):= by
  simp

have hHS:HS= Hi.induce S:= by rfl
have mindegprop2: min_degree_at_least_proportion HS (2*p):= by
  rw[hHS, hS, sdif]
  apply min_degree_proportion_delete_vertices
  exact p
  exact mindegproportion
  simp
  simp at Uupperbound
  exact Uupperbound

have pineq: 4*p< p^4:= by
  calc
    p^4= p*p*p*p:= by ring_nf
    _≥ 1*1*20*p:= by
      gcongr
      exact pPositive
      exact pPositive
    _=20*p:=by ring_nf
    _>4*p:= by
      gcongr
      simp

have hedges2: (2*p) *(2* (HS).edgeSet.toFinset.card)≥  ((HS).verts.toFinset.card)^2:=
  by
  apply edges_mindegree_proportion_lowerbound
  exact mindegprop2

have hcontra:((HS).verts.toFinset.card)^2<((HS).verts.toFinset.card)^2:= by calc
  ((HS).verts.toFinset.card)^2> (p^4) * (HS).edgeSet.toFinset.card:= by
    exact hedges
  _≥ (4*p)*(HS).edgeSet.toFinset.card:= by
    gcongr
   _= 2*p*(2*(HS).edgeSet.toFinset.card):= by ring_nf
  _≥ ((HS).verts.toFinset.card)^2:= by exact hedges2
simp at hcontra
