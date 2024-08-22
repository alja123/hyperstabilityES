import MyProject

import MyProject.clumps_basics
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
variable {p m κ pr h: ℕ}
variable (iSub:Inhabited (Subgraph G))




lemma Finset_add_one_element
{S:Finset V}
{x:V}
(hx: x ∉ S)
: (S ∪ {x}).card= S.card+1:= by
have hdisj: Disjoint S {x}:= by
  apply Finset.disjoint_singleton_right.2
  exact hx
exact Finset.card_disjoint_union hdisj



lemma Finset_add_one_element_mem
{M:Finset (Subgraph G)}
{R Y: Subgraph G}
(hY: Y∈ M∪ {R})
(hYninM: Y∉  M):
Y=R:= by
have h1: (Y∈ M) ∨  (Y∈ {R}):=by
    apply Finset.mem_union.1
    exact hY
have h2:(Y∈ {R}):= by
    have h3: ¬ (Y∈ M):= by exact hYninM
    exact Or.resolve_left h1 h3
exact   Finset.mem_singleton.1 h2





lemma Vertex_disjoint_add_one_graph
(M:Finset (Subgraph G))
(R: Subgraph G)
(hM: MVertex_Disjoint M)
(hR: Disjoint R.verts  (sSup M:Subgraph G).verts)
: MVertex_Disjoint (M ∪ {R}):= by
intro X Y hX hY hneq
by_cases hXinM: X∈ M
by_cases hYinM: Y∈ M
exact hM X Y hXinM hYinM hneq
have heqR: Y=R:= by
  exact Finset_add_one_element_mem hY hYinM
have hXM: X.verts ⊆ (sSup M:Subgraph G).verts:= by
  simp
  exact Set.subset_biUnion_of_mem hXinM
rw [heqR]
exact Set.disjoint_of_subset hXM (fun ⦃a⦄ a ↦ a) (id (Disjoint.symm hR))

by_cases hYinM: Y∈  M
have heqR: X=R:= by
  exact Finset_add_one_element_mem hX hXinM
have hYM: Y.verts ⊆ (sSup M:Subgraph G).verts:= by
  simp
  exact Set.subset_biUnion_of_mem hYinM
rw [heqR]
exact Set.disjoint_of_subset (fun ⦃a⦄ a ↦ a) hYM hR

have hXR:X=R:= by exact Finset_add_one_element_mem hX hXinM
have hYR:Y=R:= by exact Finset_add_one_element_mem hY hYinM
rw [hXR,hYR] at hneq
exact (hneq rfl).elim



lemma Near_regular_add_one_graph
{M:Finset (Subgraph G)}
{R: Subgraph G}
{pm:ℕ }
(hM: MNear_Regular M m pm)
(hR: near_regular R m pm)
: MNear_Regular (M ∪ {R}) m pm:= by
intro X hX
by_cases hXinM: X∈ M
exact hM X hXinM
have heqR: X=R:= by
  exact Finset_add_one_element_mem hX hXinM
rw [heqR]
exact hR




lemma MGraphsinH_add_one_graph
{M H:Finset (Subgraph G)}
{R Hi: Subgraph G}
(hH: Hi∈ H)
(hM: Mgraphs_in_H M H)
(hR: R≤  Hi)
: Mgraphs_in_H (M∪ {R}) H := by
intro X hX
by_cases hXinM: X∈ M
exact hM X hXinM
have heqR: X=R:= by
  exact Finset_add_one_element_mem hX hXinM
rw [heqR]
use Hi



lemma clump_few_edges_outside_M
--{p m κ pm : ℕ}
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(S: Set V)
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(pPositive: p>0)
: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2:= by

have hDifferenceOrder:  (S:Set V).toFinset.card ≥  (m/(2*p)):= by exact  Nat.div_le_of_le_mul hDifferenceOrder

have hSS:  (Hi.induce S).verts =(S):= by exact rfl
rw [hHS.symm] at hSS
have hSS':  (HS.verts).toFinset =(S:Set V).toFinset:= by
  rw [hSS]

rw [hSS'.symm] at hDifferenceOrder

have hDisjoint: Disjoint S (sSup K.M: Subgraph G).verts:= by
  rw[hS]
  exact Set.disjoint_sdiff_left

by_contra hc2
--have prgg4p : pr/(2*p) ≫ p^4:= by sorry
--have mggpr' : m/(2*p) ≫ pr/(2*p):= by sorry
--have pr'eq: (m / (2 * p))/(pr / (2 * p)) =m/pr:= by sorry
have hc2: (p^4) * (HS).edgeSet.toFinset.card≥ ((HS).verts.toFinset.card)^2:= by exact Nat.le_of_not_lt hc2
have hex:  ∃ (H': Subgraph G), H' ≤ HS ∧ near_regular H' m pr:= by
  --rw[pr'eq.symm];
  apply near_regular_subgraph2 -- mggpr' prgg4p hc2 hDifferenceOrder
  assumption
  exact mggpr

  have prggp': pr≥ gg1 ( (p^4)):=by
    apply gg2_1
    assumption
    assumption
  exact prggp'
  repeat assumption
  --apply gg1_pos
  exact Nat.pos_pow_of_pos 4 pPositive
  repeat assumption
  --sorry
  calc
    HS.verts.toFinset.card ≥ m / (2 * p):= by
      exact hDifferenceOrder
    _≥  m / (2 * p ^ 4):= by
      gcongr
      calc
        p^4=p*p*p*p:= by ring_nf
        _≥ p*1*1*1:= by
          gcongr
          repeat assumption
        _= p:= by ring_nf


  --
rcases hex with ⟨R, hR⟩
let M':Finset (Subgraph G):=K.M∪ {R}



have hRninM: R∉ K.M:= by
    intro hRinM
    have vertssubs: R.verts ⊆ (sSup K.M: Subgraph G).verts:= by
      simp
      exact Set.subset_biUnion_of_mem hRinM
    have vertsdisj: Disjoint S R.verts:=by
      exact Set.disjoint_of_subset (fun ⦃a⦄ a ↦ a) vertssubs hDisjoint
    rw [hSS.symm] at vertsdisj
    have hsubgr: R≤ HS:= by exact hR.left
    have hsubs: R.verts ⊆ HS.verts:= by apply subgraphs_vertex_sets_subsets; exact hsubgr
    have Nonemp1: R.verts.Nonempty:= by
      have h7:R.verts.toFinset.card>0:= by
        calc
          R.verts.toFinset.card≥ m/pr:= by
            exact hR.2.1
          _≥ 1:= by
            refine (Nat.one_le_div_iff ?hb).mpr ?_
            calc
              pr≥ gg2 p:= by
                exact prggp
              _>0:= by
                apply gg2_pos
                exact pPositive
            apply gg1_ge
            assumption
            calc
              pr≥ gg2 p:= by
                exact prggp
              _>0:= by
                apply gg2_pos
                exact pPositive
          _>0:= by simp
      have h8: R.verts.toFinset.Nonempty:= by
        exact card_pos.mp h7
      exact Set.toFinset_nonempty.mp h8


    have hneg:  HS.verts∩  R.verts≠ ∅:= by
      rw [←Set.nonempty_iff_ne_empty]
      refine Set.inter_nonempty_iff_exists_left.mpr ?_
      let x:V:= Nonemp1.some
      have hx: x∈ R.verts:= by exact Set.Nonempty.some_mem Nonemp1
      use x
      constructor
      exact hsubs hx
      exact hx
    have hneg: ¬ (Disjoint HS.verts R.verts):= by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact hneg
    exact hneg vertsdisj
have hM'card: M'.card> K.k:= by calc
    M'.card=(K.M ∪ {R}).card:= by exact rfl
    _= (K.M.card + 1):= by exact Finset_add_one_element   hRninM
    _> K.k:= by congr; rw [K.M_Size]; exact lt_add_one K.k

have hDisjSym: Disjoint  R.verts (sSup K.M: Subgraph G).verts := by
  have h1: R≤ HS:= by exact hR.left
  have h1: R.verts ⊆ HS.verts:= by apply subgraphs_vertex_sets_subsets; exact h1
  rw [hSS] at h1
  exact Set.disjoint_of_subset h1 (fun ⦃a⦄ a ↦ a) hDisjoint

have M'VertexDisjoint: MVertex_Disjoint M':= by
  exact Vertex_disjoint_add_one_graph K.M R (K.M_Vertex_Disjoint) hDisjSym

have M'NearReg: MNear_Regular M' m pr:= by
  exact Near_regular_add_one_graph   (K.M_Near_Regular) hR.right

have SsubsH: S⊆ Hi.verts:= by
  rw [hS]; exact Set.diff_subset Hi.verts ((sSup ↑K.M: Subgraph G).verts: Set V)

have hRH: R≤ Hi:= by calc
  R≤ HS:= by exact hR.left
  _≤ Hi:= by rw[hHS]; exact induced_subgraph_subgraph SsubsH

have M'graphs_in_H: Mgraphs_in_H M' K.H:= by
  exact MGraphsinH_add_one_graph  hHi (K.M_graphs_in_H)  hRH

have hneg: (∃ (M': Finset (Subgraph G)), M'.card > K.k ∧ (MVertex_Disjoint M')∧ (MNear_Regular M'  m pr)∧ (Mgraphs_in_H M' K.H)):=
  by
  use M';

exact K.k_Maximal hneg









lemma clump_BcapM_order
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi: Subgraph G)
(hHi: Hi∈ K.H)
: 2*p*(Hi.verts ∩ (sSup K.M: Subgraph G).verts).toFinset.card≥  m:= by



let S:Set V:=(Hi.verts \ (sSup K.M: Subgraph G).verts)
have hSe:∃ (S:Set V), S= Hi.verts \ (sSup K.M: Subgraph G).verts:= by
  use S
rcases hSe with ⟨S, hS⟩

have hDisjoint: Disjoint S (sSup K.M: Subgraph G).verts:= by
  rw[hS]
  exact Set.disjoint_sdiff_left
let HS: Subgraph G:= Hi.induce S
by_contra hc


have hc: 2 * p * (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card < m:= by
  exact Nat.gt_of_not_le hc

have hc3:  (Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card < m/(2*p)+1:= by
  sorry
have heq:(Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card+ S.toFinset.card=  Hi.verts.toFinset.card:= by
  sorry

have hs1: S.toFinset.card≥ m-m/(2*p)-1:= by
  sorry




have h2:
@Set.toFinset V (Hi.verts \ (sSup ↑K.M: Subgraph G).verts) (Hi.verts.fintypeDiffLeft (sSup ↑K.M: Subgraph G).verts)
=S.toFinset:= by
  rw[hS]
  simp



have hc1: m≤ 2 * p * (S).toFinset.card := by
  sorry
  --calc
  --m≤2*p*(Hi.verts \ (sSup K.M: Subgraph G).verts).toFinset.card:= by exact Nat.le_of_not_lt hc
  --_= 2*p*(S).toFinset.card:= by congr

have hc':  (S:Set V).toFinset.card ≥  (m/(2*p)):= by exact Nat.div_le_of_le_mul hc1


have hSS:  (HS.verts) =(S):= by exact rfl
have hSS':  (HS.verts).toFinset =(S:Set V).toFinset:= by
  rw [hSS]



rw [hSS'.symm] at hc'



have hedges: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2:= by
  exact clump_few_edges_outside_M Hi HS S hS rfl hHi hc1

have mindegproportion: min_degree_at_least_proportion Hi p:= by
  apply cut_dense_min_degree_proportion_at_least;
  apply K.H_Cut_Dense;
  exact hHi

have Uupperbound:  2*p*(Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card ≤ Hi.verts.toFinset.card:= by
  calc
  2*p*(Hi.verts ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card ≤m:=
    by sorry
  _≤   Hi.verts.toFinset.card:=
    by
    apply K.H_Order
    exact hHi



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

have pineq: 4*p< p^4:= by sorry

have hedges2: (2*p) *(2* (HS).edgeSet.toFinset.card)≥  ((HS).verts.toFinset.card)^2:=
  by
  apply edges_mindegree_proportion_lowerbound
  exact mindegprop2

have hcontra:((HS).verts.toFinset.card)^2<((HS).verts.toFinset.card)^2:= by calc
  ((HS).verts.toFinset.card)^2> (p^4) * (HS).edgeSet.toFinset.card:= by
    exact hedges
  _>(4*p)*(HS).edgeSet.toFinset.card:= by
    gcongr
    sorry
   _= 2*p*(2*(HS).edgeSet.toFinset.card):= by ring_nf
  _≥ ((HS).verts.toFinset.card)^2:= by exact hedges2

sorry

lemma diff_diff_eq_int
(S T R: Set V)
(SinR: S⊆ R)
: S∩ T= S\ (R\ T):= by
sorry

lemma clump_few_edges_outside_B_case_S_Small
--{p m κ pm : ℕ}
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(S: Set V)
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hSsize: 2*p*S.toFinset.card≤ m)
--(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
: Hi.verts ⊆ BSet K:= by

refine Set.inter_eq_right.mp ?_
ext x
constructor
intro h
have h1: x∈ Hi.verts:= by exact Set.mem_of_mem_inter_right h
exact h1

intro h
simp
constructor
have hBsetmem:  x ∈ (K.Gr).verts∧ (((K.Gr.neighborSet x)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m):= by
  constructor
  have h2: Hi.verts⊆ K.Gr.verts:= by
    have h3: Hi≤ K.Gr:= by
      apply K.H_In_K
      exact hHi
    apply subgraphs_vertex_sets_subsets
    exact h3
  exact h2 h

  calc
  (K.Gr.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p*2
  _≥(Hi.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p*2:= by
    gcongr
    have h5: Hi.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts ⊆ K.Gr.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts:= by
      gcongr
      refine Subgraph.neighborSet_subset_of_subgraph ?H.h x
      exact K.H_In_K Hi hHi
    have h6: (Hi.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts).toFinset ⊆ (K.Gr.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts).toFinset:=by
      apply Set.toFinset_subset_toFinset.2
      exact h5
    exact h6
  _=(Hi.neighborSet x \ S).toFinset.card * p*2:=by
    rw[hS]
    have h4: Hi.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts=Hi.neighborSet x \ (Hi.verts \ (sSup ↑K.M: Subgraph G).verts):=by
      apply diff_diff_eq_int
      exact Subgraph.neighborSet_subset_verts Hi x

    simp_rw[h4]
    simp
  _≥ ((Hi.neighborSet x).toFinset.card- S.toFinset.card) * p*2:= by
   gcongr
   apply neighborset_delete_vertices_card
  _=((Hi.neighborSet x).toFinset.card- S.toFinset.card) * (p*2):=
    by ring_nf
  _= (Hi.neighborSet x).toFinset.card*(p*2)- S.toFinset.card * (p*2):=by
    exact Nat.mul_sub_right_distrib (Hi.neighborSet x).toFinset.card S.toFinset.card (p * 2)
  _= (Hi.neighborSet x).toFinset.card*(p*2)- 2*p*S.toFinset.card:=by
    ring_nf
  _≥ (Hi.neighborSet x).toFinset.card*(p*2)- m:=by
    gcongr
  _= ((Hi.neighborSet x).toFinset.card*p)*2- m:=by
    ring_nf
  _≥ (Hi.verts.toFinset.card)*2-m:=by
    gcongr
    sorry
  _= m:= by
    sorry


exact hBsetmem


exact h




lemma clump_BS_complement_in_S
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(S : Set V)
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
--(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
:  Hi.verts \ (BSetPlusM K)⊆ S:= by
rw[hS]
gcongr
have h1: BSetPlusM K= BSet K∪ (sSup ↑K.M: Subgraph G).verts:= by
  exact rfl
rw [h1]
exact Set.subset_union_right (BSet K) (sSup ↑K.M: Subgraph G).verts


lemma Hi_vertices_in_K_verts
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(hHi: Hi∈ K.H)
(v:V)
(hv1: v∈ Hi.verts)
: v∈ K.Gr.verts:= by
have h1: Hi≤ K.Gr:= by
  apply K.H_In_K
  exact hHi
have h2: Hi.verts ⊆  K.Gr.verts:= by
  apply subgraphs_vertex_sets_subsets
  exact h1
exact h2 hv1


lemma or_form_of_implies
{p q: Prop}
(hpq: ¬p∨¬q)
: p→ ¬ q:= by
have h: (¬p∨¬q)=(p→ ¬q):=by
  simp
  exact Iff.symm Decidable.imp_iff_not_or
rw [h.symm]
exact hpq

lemma v_outside_BS_property
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(S : Set V)
(v:V)
(hHi: Hi∈ K.H)
(hv1: v∈ Hi.verts)
(hv2:v∉ BSet K)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
--(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
: (((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 < m):= by
have h1: ¬ (v ∈ (K.Gr).verts∧ (((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m)):= by
  exact hv2

have h1: (¬ (v ∈ (K.Gr).verts))∨ (¬(((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m)):= by
  exact    (Decidable.not_and_iff_or_not (v ∈ K.Gr.verts)          ((K.Gr.neighborSet v ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p * 2 ≥ m)).mp      hv2
have h2: v∈ (K.Gr).verts:= by
  exact Hi_vertices_in_K_verts Hi Hi hHi v hv1
--have h1': (¬ (v ∈ (K.Gr).verts))→ ((((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m)):= by
--  exact fun a ↦ (a h2).elim
have h1'': ( (v ∈ (K.Gr).verts))→ (¬(((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m)):= by
  exact fun a ↦ or_form_of_implies h1 h2

have h3: (¬(((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m)):= by
 exact h1'' h2
exact Nat.gt_of_not_le (h1'' h2)

lemma subtract_one_mult
(a b:ℕ):
a*b-b=(a-1)*b:= by
calc
a*b-b=a*b-1*b:= by
  ring_nf
_=(a-1)*b:= by
  exact (Nat.mul_sub_right_distrib a 1 b).symm

lemma subtract_one_mult_from_two
(b:ℕ):
2*b-b=b:= by
calc
2*b-b=2*b-1*b:= by
  ring_nf
_=(2-1)*b:= by
  exact (Nat.mul_sub_right_distrib 2 1 b).symm
_=1*b:= by
  exact rfl
_=b:= by
  ring_nf

lemma e_not_in_union_left
{A B: Set V}
{e:V}
(h: e∉ A∪ B)
: e∉ A:= by
have h1: A ⊆ A∪ B:= by
  exact Set.subset_union_left A B
exact fun a ↦ h (h1 a)

lemma e_not_in_union_right
{A B: Set V}
{e:V}
(h: e∉ A∪ B)
: e∉ B:= by
have h1: B ⊆ A∪ B:= by
  exact Set.subset_union_right A B
exact fun a ↦ h (h1 a)

lemma clump_HS_larger_than_BS
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(S : Set V)
(v:V)
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
(hv1: v∈ Hi.verts)
(hv2:v∉ BSetPlusM K)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
--(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
: 2*p*HS.degree v≥ Hi.verts.toFinset.card:= by
sorry/-
have h1:  (((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 < m):= by
  apply v_outside_BS_property Hi HS S v hHi
  exact hv1
  exact e_not_in_union_left hv2
have h1:  (((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≤  m):= by
  exact Nat.le_of_succ_le h1


have hmindegprop: min_degree_at_least_proportion Hi p := by
  apply cut_dense_min_degree_proportion_at_least
  apply K.H_Cut_Dense
  apply hHi

have h2: p*(Hi.degree v)≥ Hi.verts.toFinset.card:= by
  apply hmindegprop
  exact hv1

--have h3: (((Hi.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 < m)
calc
2*p*HS.degree v= 2*p*(Hi.induce S).degree v:= by rw[hHS]
_= 2*p*(Hi.induce (Hi.verts \ (sSup K.M: Subgraph G).verts)).degree v:= by rw[hS]
_≥ 2*p*(Hi.degree v-  ((sSup K.M: Subgraph G).verts ∩ (Hi.neighborSet v)).toFinset.card):= by
  gcongr
  apply degree_delete_vertices2
  refine (Set.mem_diff v).mpr ?bc.hv.a
  constructor
  exact hv1
  have h1: ¬ (v∈ (BSet K)∪ ((sSup ↑K.M: Subgraph G).verts)):= by exact hv2
  have h2:  ((sSup ↑K.M: Subgraph G).verts)⊆  (BSet K)∪ ((sSup ↑K.M: Subgraph G).verts):= by
    exact    Set.subset_union_right (BSet K) (sSup ↑K.M: Subgraph G).verts
  exact fun a ↦ hv2 (h2 a)
_= (2*p)*(Hi.degree v-  ((sSup K.M: Subgraph G).verts ∩ (Hi.neighborSet v)).toFinset.card):= by
  ring_nf
_= (2*p)*Hi.degree v-  (2*p)*((sSup K.M: Subgraph G).verts ∩ (Hi.neighborSet v)).toFinset.card:=by
  exact    Nat.mul_sub_left_distrib (2 * p) (Hi.degree v)      ((sSup ↑K.M: Subgraph G).verts ∩ Hi.neighborSet v).toFinset.card
_= (2*p)*Hi.degree v-  ((sSup K.M: Subgraph G).verts ∩ (Hi.neighborSet v)).toFinset.card*p*2:=by
  ring_nf
_≥ (2*p)*Hi.degree v-m:=by
  have h1':((sSup K.M: Subgraph G).verts ∩ (Hi.neighborSet v))⊆  ((sSup ↑K.M:Subgraph G).verts∩ K.Gr.neighborSet v ) :=by
    gcongr
    have h2: Hi≤ K.Gr:=by exact K.H_In_K Hi hHi
    exact Subgraph.neighborSet_subset_of_subgraph h2 v
  have h2: ((sSup K.M: Subgraph G).verts ∩ (Hi.neighborSet v)).toFinset.card≤   ((sSup ↑K.M:Subgraph G).verts∩ K.Gr.neighborSet v ).toFinset.card:= by
    gcongr
    simp
    simp at h1'
    gcongr
    have h3: Hi≤ K.Gr:= by exact K.H_In_K Hi hHi
    have h4: (Hi.neighborSet v) ⊆ (K.Gr.neighborSet v):= by exact      Subgraph.neighborSet_subset_of_subgraph h3 v
    exact Set.toFinset_subset_toFinset.mpr h4
  gcongr
  calc
  ((sSup ↑K.M:Subgraph G).verts ∩ Hi.neighborSet v).toFinset.card * p * 2
  ≤ ((sSup ↑K.M:Subgraph G).verts ∩ K.Gr.neighborSet v).toFinset.card * p * 2:= by
    gcongr
  _=(K.Gr.neighborSet v ∩ (sSup ↑K.M:Subgraph G).verts).toFinset.card  * p * 2:= by
    have h6: (sSup ↑K.M:Subgraph G).verts ∩ K.Gr.neighborSet v=K.Gr.neighborSet v ∩ (sSup ↑K.M:Subgraph G).verts:=by
      exact Set.inter_comm (sSup ↑K.M:Subgraph G).verts (K.Gr.neighborSet v)
    simp_rw[h6]
  _≤  m:= by exact h1

_= 2*(p*Hi.degree v)-  m:= by
  ring_nf
_≥2*Hi.verts.toFinset.card- m:=by
  have h1: 2*(p*Hi.degree v)≥ 2*Hi.verts.toFinset.card:= by
    gcongr
  gcongr
_≥ 2*Hi.verts.toFinset.card-Hi.verts.toFinset.card:= by
  gcongr
  apply K.H_Order
  exact hHi
_= Hi.verts.toFinset.card:= by
  exact subtract_one_mult_from_two (Hi.verts.toFinset.card)
-/


/-
lemma clump_HS_larger_than_BS
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(S : Set V)
(v:V)
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
(hv1: v∈ Hi.verts)
(hv2:v∉ BSet K)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
--(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
: 2*p*HS.degree v≥ Hi.verts.toFinset.card:= by
sorry
-/

lemma Sum_split_set
(S T: Set V)
(f:V→ ℕ)
: ∑ (v∈ S), f v= ∑ (v∈ (S∩ T:Set V)), f v+ ∑ (v∈ (S\T:Set V)), f v:= by
symm
calc
∑ (v∈ (S∩ T:Set V)), f v+ ∑ (v∈ (S\T:Set V)), f v=
∑ (v∈ S.toFinset ∩ T.toFinset), f v+ ∑ (v∈ (S\T:Set V)), f v:=by
  congr
  exact Set.toFinset_inter S T
_=∑ (v∈ S.toFinset ∩ T.toFinset), f v+ ∑ (v∈ (S.toFinset\T.toFinset)), f v:=by
  congr
  exact Set.toFinset_diff S T
_=∑ (v∈ S), f v:=by
  exact sum_inter_add_sum_diff S.toFinset T.toFinset fun x ↦ f x

lemma Sum_cont_leq_set
{S T: Set V}
(hST: S⊆ T)
(f:V→ ℕ)
: ∑ (v∈ S), f v≤  ∑ (v∈ (T:Set V)), f v:= by
calc
∑ (v∈ S), f v= ∑ (v∈ S.toFinset), f v:= by
  exact rfl
_≤ ∑ (v∈ T.toFinset), f v:= by
  have h1: S.toFinset⊆ T.toFinset:= by
    exact Set.toFinset_subset_toFinset.mpr hST
  exact sum_le_sum_of_ne_zero fun x a a_1 ↦ h1 a


lemma clump_HS_edges_lower_bound_BS
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS: Subgraph G)
(S : Set V)
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
--(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
: ((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card)≤  2*p*(2*HS.edgeSet.toFinset.card)
:= by
sorry /-
calc
2*p*(2*HS.edgeSet.toFinset.card)= 2*p*∑ (v∈ HS.verts), HS.degree v:= by
  congr
  symm
  apply Handshaking_lemma_subgraphs HS
_≥2*p*∑ (v∈ ((Hi.verts)\ (BSetPlusM K): Set V)), HS.degree v:= by
  gcongr
  have h1: ((Hi.verts)\ (BSetPlusM K): Set V)⊆ S:= by
    rw[hS]
    have h2: BSetPlusM K= BSet K∪ (sSup ↑K.M: Subgraph G).verts:= by
      exact rfl
    rw [h2]
    gcongr
    exact Set.subset_union_right (BSet K) (sSup ↑K.M: Subgraph G).verts
  have h3: S=HS.verts:=by
    rw[hHS]
    exact rfl
  rw[h3] at h1
  have h4:_:= by exact Sum_cont_leq_set h1 (fun v ↦ HS.degree v)
  simp
  simp at h4
  exact h4
_=∑ (v∈ ((Hi.verts)\ (BSetPlusM K): Set V)), 2*p*HS.degree v:= by
  exact mul_sum (Hi.verts \ BSetPlusM K).toFinset (fun i ↦ HS.degree i) (2 * p)
_≥∑ (v∈ ((Hi.verts)\ (BSetPlusM K): Set V)), Hi.verts.toFinset.card:= by
  gcongr  with x hx
  have h6: Hi.verts \ BSetPlusM K⊆ Hi.verts:= by
    exact Set.diff_subset Hi.verts (BSetPlusM K)
  have h7: x∈ (Hi.verts \ BSetPlusM K):= by exact Set.mem_toFinset.mp hx
  apply clump_HS_larger_than_BS Hi HS S x hS hHS hHi
  exact h6 h7
  exact Set.not_mem_of_mem_diff h7
_=  ((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card):= by
  exact sum_const_nat fun x ↦ congrFun rfl
-/



@[simps]
def bipartite_induce (G' : G.Subgraph) (s t: Set V) : G.Subgraph where
  verts := s∪ t
  Adj u v := ((u ∈ s ∧ v ∈ t)∨(v ∈ s ∧ u ∈ t))   ∧ G'.Adj u v
  adj_sub :=  by
    intro u v h
    have h1: G'.Adj u v:= by exact h.2
    exact Subgraph.Adj.adj_sub h1
  edge_vert := by
    intro u v h
    simp
    have h2:  (u ∈ s ∧ v ∈ t ∨ v ∈ s ∧ u ∈ t):= by exact h.1
    rcases h2 with  ⟨h3, h4⟩ | ⟨h3, h4⟩
    exact Or.intro_left (u ∈ t) h3
    exact Or.inr h4
  symm   := by
    intro u v h
    have h1: G'.Adj u v:= by exact h.2
    have h1: G'.Adj v u:= by exact id (Subgraph.adj_symm G' h1)
    have h2: ((v ∈ s ∧ u ∈ t) ∨ (u ∈ s ∧ v ∈ t))↔ ((u ∈ s ∧ v ∈ t) ∨ (v ∈ s ∧ u ∈ t)):= by
      exact Or.comm
    rw [h2]
    constructor
    exact h.1
    exact h1
--#align simple_graph.subgraph.induce SimpleGraph.Subgraph.induce




lemma edges_in_bipartite_induced_upper_bound
--{p m κ pr : ℕ}
{B H: Subgraph G}
{S T: Set V}
(hBip: B= (bipartite_induce H S T))
--(hHi: Hi∈ K.H)
: B.edgeSet.toFinset.card≤ S.toFinset.card*T.toFinset.card:= by
sorry

lemma clump_most_edges_in_Bgraph
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS HB HBip: Subgraph G)
(S B: Set V)
--(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= Hi.induce B)
--(hHS: HS= Hi.induce S)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ (BSetPlusM K)) (Hi.verts)))
--(hHi: Hi∈ K.H)
: (Hi).edgeSet⊆    (HB.edgeSet)∪ (HBip.edgeSet)
:= by
#check Sym2 V
--apply Sym2.forall.1
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
left
rw[hHB]
exact ⟨haB, hbB,  HiAdj⟩

have hb': b∈  (Hi.verts \ BSetPlusM K):= by
  apply hBcomp'
  exact hbHi
  exact hbB
right
rw [hBip]
simp
constructor
right
constructor
constructor
exact hbHi
exact Set.not_mem_of_mem_diff (hBcomp' b hbHi hbB)
exact haHi
exact he


have ha': a∈  (Hi.verts \ BSetPlusM K):= by
  apply hBcomp'
  exact haHi
  exact haB
right
rw [hBip]
simp
constructor
left
constructor
constructor
exact haHi
exact Set.not_mem_of_mem_diff (hBcomp' a haHi haB)
exact hbHi
exact he



lemma clump_count_Hi_edges_via_Bgraph
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HB HBip: Subgraph G)
(S B: Set V)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ (BSetPlusM K)) (Hi.verts)))
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= Hi.induce B)
: (Hi).edgeSet.toFinset.card≤ HB.edgeSet.toFinset.card+((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card)
:=by
calc
(Hi).edgeSet.toFinset.card≤ ((HB.edgeSet)∪ (HBip.edgeSet)).toFinset.card:=by
  gcongr
  have h1: Hi.edgeSet ⊆ (HB.edgeSet ∪ HBip.edgeSet):= by
    exact clump_most_edges_in_Bgraph Hi Hi HB HBip S B hB hHB hBip
  exact Set.toFinset_subset_toFinset.mpr h1
_= ((HB.edgeSet).toFinset∪  (HBip.edgeSet).toFinset).card:= by
  congr
  exact Set.toFinset_union HB.edgeSet HBip.edgeSet
_≤ (HB.edgeSet).toFinset.card+ (HBip.edgeSet).toFinset.card:= by
  exact card_union_le HB.edgeSet.toFinset HBip.edgeSet.toFinset
_≤  HB.edgeSet.toFinset.card+((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card):=by
  gcongr
  --rw[hBip]
  have h1:_:=by apply edges_in_bipartite_induced_upper_bound hBip
  simp at h1
  simp
  exact h1


lemma clump_most_edges_of_Hi_in_Bgraph_Case_fewedgesoutsideS
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi HS HB HBip: Subgraph G)
(S B: Set V)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= Hi.induce B)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ (BSetPlusM K)) (Hi.verts)))
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
--(hDifferenceOrder: 2*p*S.toFinset.card≥  m)
(hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2)
: p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2
:= by
calc
p^2*(Hi).edgeSet.toFinset.card
_≤ p^2*(HB.edgeSet.toFinset.card+((Hi.verts)\ (BSetPlusM K)).toFinset.card*(Hi.verts.toFinset.card)):= by
  gcongr
  apply clump_count_Hi_edges_via_Bgraph Hi HB HBip S B hBip hB hHB
_≤ p^2*(HB.edgeSet.toFinset.card+2*p*(2*HS.edgeSet.toFinset.card)):= by
  #check clump_HS_edges_lower_bound_BS
  have h1:_:= by exact clump_HS_edges_lower_bound_BS Hi HS S hS hHS hHi
  gcongr
_= p^2*HB.edgeSet.toFinset.card+4*p^3*HS.edgeSet.toFinset.card:= by
  ring_nf
_≤ p^2*HB.edgeSet.toFinset.card+p^4*HS.edgeSet.toFinset.card:= by
  sorry
_≤ p^2*(HB).edgeSet.toFinset.card+ (HS.verts.toFinset.card)^2:= by
  gcongr
_≤ p^2*(HB).edgeSet.toFinset.card+ (Hi.verts.toFinset.card)^2:= by
  gcongr
  have h1: HS≤ Hi:= by
    rw[hHS]
    have h2: S⊆ Hi.verts:= by
      rw[hS]
      exact Set.diff_subset Hi.verts (sSup ↑K.M:Subgraph G).verts
    exact induced_subgraph_subgraph h2
  exact subgraphs_vertex_subsets G HS Hi h1
_=  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2:= by
  ring_nf






lemma clump_most_edges_of_Hi_in_Bgraph
{K: Clump G p m κ pr h}
(Hi HS HB HBip: Subgraph G)
(S B: Set V)
(hB: B= Hi.verts∩ BSetPlusM K)
(hHB: HB= Hi.induce B)
(hBip: HBip= (bipartite_induce Hi ((Hi.verts)\ (BSetPlusM K)) (Hi.verts)))
(hS: S= Hi.verts \ (sSup K.M: Subgraph G).verts)
(hHS: HS= Hi.induce S)
(hHi: Hi∈ K.H)
: p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2
:= by
by_cases hDifferenceOrder: 2*p*S.toFinset.card≥  m
have hfewedgeshoutsideHS: (p^4) * (HS).edgeSet.toFinset.card< ((HS).verts.toFinset.card)^2:= by
  exact clump_few_edges_outside_M Hi HS S hS hHS hHi hDifferenceOrder
exact clump_most_edges_of_Hi_in_Bgraph_Case_fewedgesoutsideS Hi HS HB HBip S B hB hHB hBip hS hHS hHi hfewedgeshoutsideHS

#check clump_few_edges_outside_B_case_S_Small
have hcont: Hi.verts ⊆ BSet K:= by
  apply clump_few_edges_outside_B_case_S_Small Hi HS S hS _ hHi
  have h3:   2 * p * S.toFinset.card < m:= by exact Nat.gt_of_not_le hDifferenceOrder
  exact Nat.le_of_not_ge hDifferenceOrder
have heq: Hi=HB:= by
  rw[hHB]
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
  rw[h2]
  exact Subgraph.induce_self_verts.symm
calc
p^2*Hi.edgeSet.toFinset.card
= Hi.edgeSet.toFinset.card * p ^ 2:=by
  ring_nf
_= HB.edgeSet.toFinset.card * p ^ 2:=by
  rw[heq]
_≤ Hi.verts.toFinset.card ^ 2 + HB.edgeSet.toFinset.card * p ^ 2:=by
  exact Nat.le_add_left (HB.edgeSet.toFinset.card * p ^ 2) (Hi.verts.toFinset.card ^ 2)


/-  by_contra hc2
  have hc2: (p^4) * (HS).edgeSet.toFinset.card≥ ((HS).verts.toFinset.card)^2:= by exact Nat.le_of_not_lt hc2
  have hex:  ∃ (H': Subgraph G), H' ≤ HS ∧ near_regular H' (pm):= by
    apply near_regular_subgraph hc2 hc'
  rcases hex with ⟨R, hR⟩
  let M':Finset (Subgraph G):=K.M∪ {R}
  have hRninM: R∉ K.M:= by
    intro hRinM
    have vertssubs: R.verts ⊆ (sSup K.M: Subgraph G).verts:= by
      simp
      exact Set.subset_biUnion_of_mem hRinM
    have vertsdisj: Disjoint S R.verts:=by
      exact Set.disjoint_of_subset (fun ⦃a⦄ a ↦ a) vertssubs hDisjoint
    rw [hSS.symm] at vertsdisj
    have hsubgr: R≤ HS:= by exact hR.left
    have hsubs: R.verts ⊆ HS.verts:= by apply subgraphs_vertex_sets_subsets; exact hsubgr
    have Nonemp1: R.verts.Nonempty:= by sorry
    have hneg:  HS.verts∩  R.verts≠ ∅:= by
      rw [←Set.nonempty_iff_ne_empty]
      refine Set.inter_nonempty_iff_exists_left.mpr ?_
      let x:V:= Nonemp1.some
      have hx: x∈ R.verts:= by exact Set.Nonempty.some_mem Nonemp1
      use x
      constructor
      exact hsubs hx
      exact hx
    have hneg: ¬ (Disjoint HS.verts R.verts):= by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact hneg
    exact hneg vertsdisj
  have hM'card: M'.card= K.k+1:= by calc
    M'.card=(K.M ∪ {R}).card:= by exact rfl
    _= (K.M.card + 1):= by exact Finset_add_one_element K.M R hRninM
    _= K.k+1:= by congr; exact K.M_Size

sorry
-/
/-
lemma clump_R2_upper_bound
{p m κ pm : ℕ}
{K: Clump G p m κ pm }
(hI: I⊆ BSet K)
(Hi: Subgraph G)
(hHi: Hi∈ K.H)
:
2*p*(Hi.induce (Hi.verts\(sSup K.M: Subgraph G).verts)).edgeSet.toFinset.card≤ m := by
let H:Subgraph G:= Hi.induce (Hi.verts\(sSup K.M: Subgraph G).verts)
by_contra hc


have hc: 2*p*H.edgeSet.toFinset.card> m := by exact  Nat.gt_of_not_le hc
have hc: (2*p)*(H).edgeSet.toFinset.card≥  m := by
  gcongr

have hOrder: H.verts.card≥
have hex:  ∃ (H': Subgraph G), H' ≤ H ∧ near_regular H' (pm):= by
  apply near_regular_subgraph hc
-/
