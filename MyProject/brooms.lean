import MyProject

import MyProject.locally_dense_find
import MyProject.paths_in_cytdense
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
variable (iSP:Inhabited (SubgraphPath_implicit   G) )




lemma dense_graph_in_broom
(p d: ℕ )
(H: Subgraph G)
(N: Set V)
(hOrder: H.verts.toFinset.card ≤ 2*d)
(N_cont: N⊆ H.verts)
(hN: ∀ (v: V), v∈ N→4*p*H.degree v ≥ d)
(Norder: N.toFinset.card = d/(4*p))
(pPositive: p>0)
:
64*p^2*(H.edgeSet.toFinset.card)≥   d^2
--32*p*p*(2*H.edgeSet.toFinset.card)≥   d^2
:=by
calc
64*p^2*(H.edgeSet.toFinset.card)
=32*p*p *(2*H.edgeSet.toFinset.card):= by ring_nf
_=32*p*p *∑ (v∈ H.verts), H.degree v:= by
  congr
  symm;
  exact Handshaking_lemma_subgraphs H
_≥ 32*p*p *∑ (v∈ N), H.degree v:= by
  gcongr
  exact Sum_cont_leq_set N_cont fun v ↦ H.degree v
_= (8*p)*(4*p*∑ (v∈ N), H.degree v):= by
  ring_nf
_=(8*p)*∑ (v∈ N), 4*p*H.degree v:= by
  congr
  apply mul_sum
_≥ (8*p)*∑ (v∈ N), d:= by
  gcongr with i hi;
  have hi: i ∈ N:= by exact Set.mem_toFinset.mp hi
  apply hN
  exact hi
_=(8*p)*((N.toFinset.card)*d):= by
  congr 1
  exact sum_const_nat fun x ↦ congrFun rfl
_= (8*p)*(d/(4*p)*d):= by
  rw[ Norder]
_=d*(2*(4*p)*(d/(4*p))):=by
  ring_nf
_≥ d*d:= by
  gcongr
  refine twice_times_fraction_ge d (4 * p) ?bc.hb ?bc.hm
  apply mul_pos
  exact Nat.zero_lt_succ 3
  exact pPositive
  sorry--d ≥ 2 * (4 * p)
_=  d^2:= by ring_nf






 lemma long_path_in_sparse_graph
(H: Subgraph G)
(v: V)

(hv: v∈ H.verts)
(k d: ℕ )
(hk:k ≤ d)
(min_degree: ∀ v : V, v∈ H.verts → p*H.degree v ≥ d)
(no_dense_subgraphs: ¬ (∃ (D : Subgraph G), D≤ H∧ D.verts.toFinset.card≤ 2*d∧ 64*p^2*D.edgeSet.toFinset.card≥  d^2))
--∀ (D : Subgraph G), D≤ H→ D.verts.toFinset.card≤ 2*d→ γ*D.edgeSet.toFinset.card≤ d^2)
:
∃ (w: V), ∃ (P: SubgraphPath H v w),
P.Wa.length=k
∧
4*p*((H.neighborSet w)\ {x:V| x∈ P.Wa.support}).toFinset.card ≥ d
:= by
induction' k with k IH
simp
use v
let W: Walk G v v:= Walk.nil
have Wpath: W.IsPath:= by exact Walk.IsPath.nil
have Wingraph: W.toSubgraph≤ H:= by
  dsimp[W]
  simp
  exact hv

let P: SubgraphPath H v v:=
  {Wa:=W, Wa_Is_Path:=Wpath, Wa_In_H:=Wingraph}
use P
constructor
dsimp[P, W]
calc
  4 * p * ((H.neighborSet v).toFinset
  \ filter (fun x ↦ x ∈ P.Wa.support) univ).card
  ≥ 4 * p * (
    (H.neighborSet v).toFinset.card
   - (filter (fun x ↦ x ∈ P.Wa.support) univ
  ).card):=by
     gcongr
     exact le_card_sdiff (filter (fun x ↦ x ∈ P.Wa.support) univ) (H.neighborSet v).toFinset
  _= 4 * p * ((H.neighborSet v).toFinset.card - 1):=by
    congr
    dsimp[P, W]
    simp
    refine (Fintype.exists_unique_iff_card_one fun x ↦ x = v).mp ?_
    exact exists_unique_eq
  _= 4 * p * (H.degree v-1):= by
    simp
    left
    congr
  _= 4 * p * H.degree v - 4 * p*1:= by
    exact Nat.mul_sub_left_distrib (4 * p) (H.degree v) 1
  _=4 * (p * H.degree v) - 4 * p:=by
    ring_nf
  _≥4*d-4*p:= by
    gcongr
    apply min_degree
    exact hv
  _≥ d:= by
    sorry -- d>4*p

---------------induction

have kled: k ≤ d:= by exact Nat.le_of_succ_le hk

have hex:
  ∃ (w: V), ∃ (P: SubgraphPath H v w),
  P.Wa.length=k
  ∧
  4*p*((H.neighborSet w)\ {x:V| x∈ P.Wa.support}).toFinset.card ≥ d:=by
    apply IH
    repeat assumption

rcases hex with ⟨w, P, hP1, hP2⟩

by_cases
  case:
  ∃ (y: V),
  y∈ (H.neighborSet w \ {x | x ∈ P.Wa.support})
  ∧ 4*p*((H.neighborSet y)\ {x:V| x∈ P.Wa.support∨ x=w∨ x=y}).toFinset.card ≥ d

rcases case with ⟨y, hy1, hy2⟩

have adj: H.Adj w y:= by
  simp at hy1
  exact hy1.1

have evw: G.Adj w y:= by
  exact Subgraph.Adj.adj_sub adj

let Q:Walk G v y:= Walk.append (P.Wa) (evw.toWalk)

use y
have hcont: Q.toSubgraph≤ H:= by
  dsimp [Q]
  simp
  constructor
  exact P.Wa_In_H
  exact subgraphOfAdj_le_of_adj H adj


have hlen: Q.length+1=k+1+1:= by
  calc
    Q.length+1
    =P.Wa.length+ evw.toWalk.length+1:= by
      congr
      exact Walk.length_append P.Wa evw.toWalk
    _=k+1+1:= by
      congr



have hpath: Q.IsPath:= by
  dsimp[Q]
  apply append_paths
  exact P.Wa_Is_Path
  refine Walk.IsPath.cons ?Qpath.hp ?Qpath.hu
  exact Walk.IsPath.nil
  simp
  exact Adj.ne' (id (adj_symm G evw))
  have h2: evw.toWalk.support.tail=[y]:= by
    simp
  rw[h2]
  simp
  simp at hy1
  exact hy1.2

use {Wa:=Q, Wa_Is_Path:=hpath, Wa_In_H:=hcont}

simp
simp at hlen
constructor
exact hlen
simp at hy2
dsimp[Q]
simp
exact hy2


---------second case
exfalso
simp only [Set.mem_diff, Set.mem_setOf_eq, Set.toFinset_diff,
  Set.toFinset_setOf, ge_iff_le, not_exists, not_and, not_le, and_imp] at case

have Ncard: (H.neighborSet w \ {x | x ∈ P.Wa.support}).toFinset.card≥ d/(4*p):= by
  exact Nat.div_le_of_le_mul hP2


have Nex:
  ∃ (S: Finset V),
  (S⊆ (H.neighborSet w \ {x | x ∈ P.Wa.support}).toFinset)
  ∧ S.card =d/(4*p):= by
    exact exists_smaller_set (H.neighborSet w \ {x | x ∈ P.Wa.support}).toFinset (d / (4 * p)) Ncard

rcases Nex with ⟨N, hN1, hN2⟩
--let N: Set V:=FN.toSet

let D: Subgraph G:=H.induce {x:V| x∈ P.Wa.support ∨ x∈ N}

have hdverts:  D.verts.toFinset    = ((P.Wa.support).toFinset ∪ N):= by
      congr
      dsimp[D]
      ext x
      simp


have NinD: N⊆ D.verts.toFinset:= by
  rw[hdverts]
  exact subset_union_right P.Wa.support.toFinset N
/-
have NinH: N.toSet⊆ H.verts:= by
  rw [← @Set.subset_toFinset]
  have h1: D.verts.toFinset⊆ H.verts.toFinset:=by
    simp only [Set.subset_toFinset, Set.coe_toFinset]
    have h2: D≤ H:=by
      dsimp[D]
      exact?
    exact subgraphs_vertex_sets_subsets G
  exact?
-/

have hNinH: N.toSet⊆ H.verts:= by
    calc
      N.toSet⊆ (H.neighborSet w \ {x | x ∈ P.Wa.support}):= by
        refine Set.subset_toFinset.mp ?_
        exact hN1
      _⊆H.neighborSet w:=by
        exact Set.diff_subset (H.neighborSet w) {x | x ∈ P.Wa.support}
      _⊆ H.verts:= by
        exact Subgraph.neighborSet_subset_verts H w

have D_order_upperbound: D.verts.toFinset.card≤ 2*d:= by
  calc
    D.verts.toFinset.card
    = ((P.Wa.support).toFinset ∪ N).card:= by
      congr
    _≤ P.Wa.support.toFinset.card + N.card:= by
      exact card_union_le P.Wa.support.toFinset N
    _= P.Wa.support.length + N.card:= by
      congr
      --simp
      refine List.toFinset_card_of_nodup ?_
      refine (Walk.isPath_def P.Wa).mp ?_
      exact P.Wa_Is_Path
    _= P.Wa.length+1 + N.card:= by
      congr
      simp
    _≤  k +1+ d/(4*p):= by
      gcongr
      exact Nat.le_of_eq hP1
      exact Nat.le_of_eq hN2
    _≤ d + d:= by
      gcongr
      exact Nat.div_le_self d (4 * p)
    _=2*d:= by
      ring_nf


have contra1:(∃ (D : Subgraph G), D≤ H∧ D.verts.toFinset.card≤ 2*d∧ 64*p^2*D.edgeSet.toFinset.card≥  d^2):= by
  use D
  constructor
  dsimp[D]
  refine induced_subgraph_subgraph ?h.left.hS
  intro x hx
  simp at hx
  rcases hx with case|case
  have h1:_:= by exact P.Wa_In_H
  have h2: x∈ P.Wa.toSubgraph.verts:= by
    exact (Walk.mem_verts_toSubgraph P.Wa).mpr case
  have h3: P.Wa.toSubgraph.verts⊆ H.verts:= by
    apply subgraphs_vertex_sets_subsets
    exact h1
  exact h3 h2
  have h1: N.toSet⊆ H.verts:= by
    calc
      N.toSet⊆ (H.neighborSet w \ {x | x ∈ P.Wa.support}):= by
        refine Set.subset_toFinset.mp ?_
        exact hN1
      _⊆H.neighborSet w:=by
        exact Set.diff_subset (H.neighborSet w) {x | x ∈ P.Wa.support}
      _⊆ H.verts:= by
        exact Subgraph.neighborSet_subset_verts H w

  exact h1 case
  constructor
  exact D_order_upperbound

  apply dense_graph_in_broom p d D N
  exact D_order_upperbound
  have h1: N.toSet⊆ D.verts:= by
    refine Set.subset_toFinset.mp ?_
    rw[hdverts]
    exact subset_union_right P.Wa.support.toFinset N
  exact h1

  intro x hx
  dsimp [D]
  --simp
  unfold Subgraph.degree
  calc
    4 * p * Fintype.card ↑((H.induce {x | x ∈ P.Wa.support ∨ x ∈ N}).neighborSet x)
    =4*p*(((H.induce {x | x ∈ P.Wa.support ∨ x ∈ N}).neighborSet x).toFinset.card):= by
      simp

    _= 4 * p * ((H.neighborSet x).toFinset ∩ (P.Wa.support.toFinset ∪ N)).card:= by
      --simp
      --left
      congr
      ext u
      simp
      aesop

    _≥  4 * p * ((H.neighborSet x).toFinset ∩ P.Wa.support.toFinset).card:= by
      gcongr
      exact subset_union_left P.Wa.support.toFinset N

    _=  4 * p * ((H.neighborSet x).toFinset.card - ((H.neighborSet x).toFinset\ P.Wa.support.toFinset).card):= by
      congr
      exact finset_subtract_intersection (H.neighborSet x).toFinset P.Wa.support.toFinset
    _=4 * p * (H.neighborSet x).toFinset.card - 4 * p *((H.neighborSet x).toFinset\ P.Wa.support.toFinset).card:= by
      exact
        Nat.mul_sub_left_distrib (4 * p) (H.neighborSet x).toFinset.card
          ((H.neighborSet x).toFinset \ P.Wa.support.toFinset).card
    _=4 * (p * (H.neighborSet x).toFinset.card) - 4 * p *((H.neighborSet x).toFinset\ P.Wa.support.toFinset).card:= by
      ring_nf
    _≥ 4*d- 2*d:=by
      gcongr 4*?_-?_
      rw [@Subgraph.finset_card_neighborSet_eq_degree]
      apply min_degree
      exact hNinH hx

      calc
        4 * p * ((H.neighborSet x).toFinset \ P.Wa.support.toFinset).card
        ≤   4 * p * (((H.neighborSet x).toFinset \ (filter (fun x_1 ↦ x_1 ∈ P.Wa.support ∨ x_1 = w ∨ x_1 = x) univ))∪ {w,x}).card:=by
          gcongr
          intro u hu
          simp
          simp at hu
          by_cases c1: u=w
          left
          exact c1
          by_cases c2: u=x
          right
          right
          exact c2
          right
          left
          exact ⟨hu.1, hu.2, c1, c2 ⟩
        _≤   4 * p * (((H.neighborSet x).toFinset \ (filter (fun x_1 ↦ x_1 ∈ P.Wa.support ∨ x_1 = w ∨ x_1 = x) univ)).card+ ({w,x}:Finset V).card):=by
          gcongr
          exact
            card_union_le
              ((H.neighborSet x).toFinset \
                filter (fun x_1 ↦ x_1 ∈ P.Wa.support ∨ x_1 = w ∨ x_1 = x) univ)
              {w, x}
        _=4 * p * ((H.neighborSet x).toFinset \ (filter (fun x_1 ↦ x_1 ∈ P.Wa.support ∨ x_1 = w ∨ x_1 = x) univ)).card+ 4 * p *({w,x}:Finset V).card:= by
          ring_nf
        _≤ d+ 4 * p *2:= by
          gcongr
          apply LT.lt.le
          apply case
          have h3:  N.toSet ⊆ H.neighborSet w:= by
             calc
              N.toSet⊆ (H.neighborSet w \ {x | x ∈ P.Wa.support}):= by
                refine Set.subset_toFinset.mp ?_
                exact hN1
              _⊆H.neighborSet w:=by
                exact Set.diff_subset (H.neighborSet w) {x | x ∈ P.Wa.support}
          exact h3 hx
          by_contra contr
          have h7: x∉ (H.neighborSet w \ {x | x ∈ P.Wa.support}).toFinset:= by
            simp
            intro a
            exact contr
          have h8: x∉ N:= by
            exact fun a ↦ h7 (hN1 hx)
          exact h7 (hN1 hx)




          exact card_le_two



        _≤  d+d:=by
          gcongr d+?_
          sorry-- 4 * p * 2 ≤ d
        _=2*d:= by
          ring_nf




    _= 2*(2*d)-2*d:=by
      ring_nf
    _=2*d:=by
      exact twice_minus_once (2 * d)
    _≥  1*d:=by
      gcongr
      exact NeZero.one_le
    _=d:=by
      ring_nf

  simp
  exact hN2
  exact pPositive






exact no_dense_subgraphs contra1
/-
structure SubgraphPath
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_Is_Path: Wa.IsPath
  Wa_In_H: Wa.toSubgraph≤ H
-/
