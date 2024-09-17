--import MyProject

import hyperstabilityES.lemmas.paths_in_cutdense
  --import hyperstabilityES.lemmas.SimpleGraph
set_option linter.unusedVariables false

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

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




lemma subgraph_walk_two_vertices
(H: Subgraph G)
(v w: V)
(hadj: H.Adj v w)
: ∃ (P: SubgraphWalk H v w), P.Wa.length= 1:= by
have h2: G.Adj v w:= by exact Subgraph.Adj.adj_sub hadj
let W:G.Walk v w:= h2.toWalk
have h3: W.length=1:= by
    dsimp[W]

have inH: W.toSubgraph≤ H:=by
    dsimp [W]
    simp
    unfold subgraphOfAdj
    simp
    constructor
    simp
    refine Set.insert_subset_iff.mpr ?left.a
    constructor
    exact H.edge_vert hadj
    simp
    exact H.edge_vert (id (Subgraph.adj_symm H hadj))
    simp
    intro x y hxy
    have h3: H.Adj x y=H.Adj y x:= by exact      Eq.propIntro (fun a ↦ id (Subgraph.adj_symm H a)) fun a ↦ id (Subgraph.adj_symm H a)
    rename_i
      h3_1
    simp_all only [gt_iff_lt,
      Walk.length_cons,
      Walk.length_nil,
      zero_add,
      eq_iff_iff,
      W]
    unhygienic
      aesop_cases
        hxy
    ·
      simp_all only [iff_true]
    ·
      simp_all only [iff_true]


let P: SubgraphWalk H v w:= ⟨W,inH⟩
use P




lemma Cut_Dense_N1_size
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(v: V)
(v_in_H: v ∈ H.verts)
(Nd : Set V)
(hNd:Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ 1})
:
(p*(Nd).toFinset.card≥ H.verts.toFinset.card)
:=by
let N: Set V:=H.neighborSet v

have Nsize: p*(N).toFinset.card≥ H.verts.toFinset.card:=by
  --dsimp [N]
  have h1: (N).toFinset.card= H.degree v:=by
    dsimp[N]
    exact Subgraph.finset_card_neighborSet_eq_degree
  rw[h1]
  exact cut_dense_min_degree G v_in_H H_cut_dense

have hcont: N ⊆ Nd:=by
  intro w
  intro hw
  rw[hNd]
  dsimp[N] at hw
  simp
  unfold Subgraph.neighborSet at hw
  simp at hw
  have h2: ∃ (P: SubgraphWalk H v w), P.Wa.length= 1:=by
    exact subgraph_walk_two_vertices H v w hw
  rcases h2 with ⟨ P, hP⟩
  use P
  exact Nat.le_of_eq hP

calc
 p * Nd.toFinset.card
≥   p * N.toFinset.card:= by gcongr; simp; exact hcont
_≥ H.verts.toFinset.card:= by exact Nsize


lemma simpleunionbound
(A B : Finset V)
:
(A ∪ B).card =  A.card+(B\ A).card:= by
rw[add_comm]
calc
(A ∪ B).card= (A ∪ (B\ A)).card:= by
  simp
_=A.card+(B\ A).card:= by
  refine card_union_of_disjoint ?_
  exact disjoint_sdiff

_=(B\ A).card+A.card:= by
  exact Nat.add_comm A.card (B \ A).card



lemma simpleunionbound2
(A B : Finset V)
(disj: A ∩ B = ∅)
:
(A ∪ B).card =  A.card+(B).card:= by
refine card_union_of_disjoint ?_
exact disjoint_iff_inter_eq_empty.mpr disj

lemma Cut_Dense_Nd_size
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(d: ℕ )
(v: V)
(v_in_H: v ∈ H.verts)
--(Nd : Set V)
--(hNd:Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d+1})
--(hsmall: 2*Nd.toFinset.card≤ H.verts.toFinset.card)
:
∀ (Nd : Set V),
(Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d+1})
→
( 2*Nd.toFinset.card≤ H.verts.toFinset.card)
→
(4*p*(Nd).toFinset.card≥ (d+1)*H.verts.toFinset.card)
:= by
induction' d with d hd
intro Nd hNd hsmall

simp only [  zero_add, one_mul ]
simp only [zero_add] at hNd
calc
  4*p*(Nd).toFinset.card
  ≥ 1*p*(Nd).toFinset.card:= by
    gcongr
    exact NeZero.one_le
  _= p*(Nd).toFinset.card := by
    ring_nf
  _≥H.verts.toFinset.card:=by
    apply Cut_Dense_N1_size
    repeat assumption

intro Nd hNd hsmall
let N1: Set V:= {w | ∃ (P: SubgraphWalk H v w), P.Wa.length ≤ d + 1}
have N1small: 2*N1.toFinset.card≤ H.verts.toFinset.card:=by
  have h1: 2*N1.toFinset.card≤ 2*Nd.toFinset.card:=by
    gcongr
    simp
    exact Nd_in_Nd' H N1 (d + 1) rfl hNd
  exact Nat.le_trans h1 hsmall


have cont: N1⊆ Nd:= by
  exact Nd_in_Nd' H N1 (d + 1) rfl hNd
have hN1: N1={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d+1}:=by rfl
have N1size: 4*p*(N1).toFinset.card≥ (d+1)*H.verts.toFinset.card:=by
  apply hd N1 hN1 N1small
have diff_size: 4*p*(Nd\ N1).toFinset.card≥ H.verts.toFinset.card:= by
  apply Cut_Dense_expansion
  repeat assumption


have h2: Nd=N1∪ (Nd\ N1):= by
  exact (Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) cont).symm

have h2: Nd=Nd∪ N1:= by exact (Set.union_eq_self_of_subset_right cont).symm



calc
4 * p * (Nd.toFinset.card)
=4 * p * ((Nd∪ N1).toFinset.card):= by
  simp_rw [h2.symm]
_=4 * p * ((Nd.toFinset ∪ N1.toFinset).card):= by
  simp
_=4 * p * ((N1.toFinset ∪ Nd.toFinset).card):= by
  rw[Finset.union_comm]
_=4 * p * (N1.toFinset.card+ (Nd.toFinset \ N1.toFinset).card)
:= by
  congr
  apply simpleunionbound (N1.toFinset) (Nd.toFinset)

_=4 * p * (N1.toFinset.card+ ((Nd \ N1).toFinset).card):=by
  congr
  simp

_=(4 * p * N1.toFinset.card+ 4 * p * (Nd\ N1).toFinset.card):=by
  ring_nf
_≥ (d+1)*H.verts.toFinset.card+H.verts.toFinset.card:= by
  gcongr
_= (d+1+1)*H.verts.toFinset.card:= by
  ring_nf





lemma Cut_Dense_expand_to_everything
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(v: V)
(v_in_H: v ∈ H.verts)
(Nd : Set V)
(hNd:Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ 4*p+1})
:
2*Nd.toFinset.card> H.verts.toFinset.card
:=by
by_contra  contr
simp only [  not_lt] at contr

have h1: (4*p*(Nd).toFinset.card≥ (4*p+1)*H.verts.toFinset.card):= by
  apply Cut_Dense_Nd_size
  repeat assumption

have h2: (4*p*(Nd).toFinset.card< (4*p+1)*H.verts.toFinset.card):= by
  calc
  4*p*(Nd).toFinset.card
  ≤  4*p*H.verts.toFinset.card:= by
    gcongr
    simp
    exact Nd_in_verts H Nd (4 * p + 1) hNd
  _< (4*p+1)*H.verts.toFinset.card:= by
    gcongr
    --0 < H.verts.toFinset.card
    refine card_pos.mpr ?bc.a0.a
    simp
    use v
    exact lt_add_one (4 * p)

have h3: ¬ (4*p*(Nd).toFinset.card≥ (4*p+1)*H.verts.toFinset.card):= by
  exact Nat.not_le_of_lt h2
exact h3 h1



lemma Cut_Dense_walk_connected
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
:
∃ (P: SubgraphWalk H u v), P.Wa.length≤ 10*p
:=by


let Nu: Set V:= {w | ∃ (P: SubgraphWalk H u w), P.Wa.length ≤ 4*p+1}
let Nv: Set V:= {w | ∃ (P: SubgraphWalk H v w), P.Wa.length ≤ 4*p+1}

have Nu_large: 2*Nu.toFinset.card> H.verts.toFinset.card:= by
  apply Cut_Dense_expand_to_everything
  repeat assumption
  dsimp [Nu]

have Nv_large: 2*Nv.toFinset.card> H.verts.toFinset.card:= by
  apply Cut_Dense_expand_to_everything H H_cut_dense v v_in_H Nv
  repeat assumption
  dsimp [Nv]

have Nucont: Nu.toFinset⊆ H.verts.toFinset := by
  simp
  exact Nd_in_verts H Nu (4 * p + 1) rfl

have Nvcont: Nv.toFinset⊆ H.verts.toFinset := by
  simp
  exact Nd_in_verts H Nv (4 * p + 1) rfl

have h1: (Nu.toFinset ∩ Nv.toFinset).Nonempty := by
  by_contra cont
  simp at cont
  have h2: 2*(Nu.toFinset ∪ Nv.toFinset).card> 2*H.verts.toFinset.card:= by
    calc
      2*((Nu.toFinset ∪ Nv.toFinset).card)
      =
      2*(Nu.toFinset.card+  Nv.toFinset.card):= by
        congr
        exact simpleunionbound2 Nu.toFinset Nv.toFinset cont

      _=2*Nu.toFinset.card+ 2*Nv.toFinset.card:= by
        ring_nf
      _> H.verts.toFinset.card+ H.verts.toFinset.card:= by
        gcongr
      _=2*H.verts.toFinset.card:= by
        ring_nf
  have h3: ¬(2*(Nu.toFinset ∪ Nv.toFinset).card> 2*H.verts.toFinset.card):= by
    simp only [ gt_iff_lt, Nat.ofNat_pos, mul_lt_mul_left,
      not_lt]
    gcongr
    simp
    constructor
    exact Nd_in_verts H Nu (4 * p + 1) rfl
    exact Nd_in_verts H Nv (4 * p + 1) rfl
  exact h3 h2

have h2: ∃  (w: V), w∈ Nu.toFinset ∩ Nv.toFinset:= by
  exact h1
rcases h2 with ⟨w, hw⟩
simp at hw
let ⟨hw1, hw2 ⟩:= hw

have h3: ∃ (P1: SubgraphWalk H u w), P1.Wa.length ≤ 4*p+1:= by
  exact hw1
have h4: ∃ (P2: SubgraphWalk H v w), P2.Wa.length ≤ 4*p+1:= by
  exact hw2

rcases  h3 with ⟨P1, hP1⟩
rcases  h4 with ⟨P2, hP2⟩

--let P2rev: Walk G w v:= P2.Wa.reverse

let Q: Walk G u v:= Walk.append (P1.Wa) (P2.Wa.reverse)


have hcont: Q.toSubgraph≤ H:= by
  dsimp [Q]
  simp
  constructor
  exact P1.Wa_In_H
  exact P2.Wa_In_H


have hlen: Q.length≤ 10*p:= by
  calc
    Q.length≤ P1.Wa.length+ P2.Wa.length:= by
      dsimp [Q]
      simp
    _≤ (4*p+1)+(4*p+1):= by
      gcongr
    _=8*p+2:= by
      ring_nf
    _≤ 8*p+2*p:=by
      gcongr
      exact Nat.le_mul_of_pos_right 2 pPositive
    _=10*p:= by
      ring_nf

use ⟨ Q, hcont⟩






lemma Cut_Dense_path_connected
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
:
∃ (P: SubgraphPath H u v), P.Wa.length≤ 10*p
:=by
have hWalk: ∃ (W: SubgraphWalk H u v), W.Wa.length≤ 10*p:= by
  apply Cut_Dense_walk_connected H H_cut_dense u v v_in_H u_in_H
  repeat assumption
rcases hWalk with ⟨W, hW⟩

let P: Walk G u v := W.Wa.bypass

have hpath: P.IsPath:= by exact Walk.bypass_isPath W.Wa

have hlength: P.length≤ 10*p:= by
  calc
    P.length
    ≤W.Wa.length:= by
      exact Walk.length_bypass_le W.Wa
    _≤ 10*p:= by exact hW

have Wa_sub: W.Wa.toSubgraph≤ H:= by
  exact W.Wa_In_H

have edge_cont: P.edges⊆ W.Wa.edges:= by
  dsimp[P]
  exact Walk.edges_bypass_subset W.Wa

have vert_cont: P.support⊆ W.Wa.support:= by
  dsimp[P]
  exact Walk.support_bypass_subset W.Wa


have edge_cont2: P.toSubgraph.edgeSet=List.toFinset (P.edges):= by
  simp

have vert_cont2: P.toSubgraph.verts=List.toFinset (P.support):= by
  simp

have edge_cont_3: P.toSubgraph.edgeSet⊆ H.edgeSet:= by
  calc
  P.toSubgraph.edgeSet=List.toFinset (P.edges):=by
    exact edge_cont2
  _⊆ List.toFinset (W.Wa.edges):= by
    simp only [List.coe_toFinset]
    exact edge_cont
  _=W.Wa.toSubgraph.edgeSet:= by
    simp
  _⊆ H.edgeSet:=by
    exact subgraph_implies_edgesets_subsets Wa_sub


have edge_cont_4: P.toSubgraph.verts⊆ H.verts:= by
  calc
  P.toSubgraph.verts=List.toFinset (P.support):=by
    simp
  _⊆ List.toFinset (W.Wa.support):= by
    --simp only [List.coe_toFinset]
    dsimp[P]
    simp only [List.coe_toFinset]
    exact vert_cont
  _=W.Wa.toSubgraph.verts:= by
    simp
  _⊆ H.verts:=by
    apply  subgraphs_vertex_sets_subsets G
    repeat assumption

have Psub: P.toSubgraph≤ H:= by
  constructor
  exact edge_cont_4
  intro x y hxy

  exact Subgraph.mem_edgeSet.mp (edge_cont_3 hxy)

use ⟨P, hpath ,Psub⟩



lemma append_paths
(u v w : V)
(P: Walk G u v)
(Q: Walk G v w)
(Ppath: P.IsPath)
(Qpath: Q.IsPath)
(disj: P.support.Disjoint Q.support.tail)

--(supportint: P.support ∩ Q.support = {v})
:
(Walk.append P Q).IsPath
:=by
refine Walk.IsPath.mk' ?h
rw [@Walk.support_append]
refine List.Nodup.append ?h.d₁ ?h.d₂ ?h.dj
exact Ppath.support_nodup
have h1: Q.support.Nodup:= by exact Qpath.support_nodup

have h2: List.Sublist (Q.support.tail)  (Q.support):= by exact List.tail_sublist Q.support
exact List.Nodup.sublist h2 h1


exact disj

lemma subgraphwalk_end_in_H
(H: Subgraph G)
(u v: V)
(W: SubgraphWalk H u v)
:
v∈ H.verts:= by
have h1: v∈ W.Wa.toSubgraph.verts:= by
  simp
have h2: W.Wa.toSubgraph.verts⊆ H.verts:= by
  apply subgraphs_vertex_sets_subsets G
  exact W.Wa_In_H
exact h2 h1

lemma subgraphpath_end_in_H
(H: Subgraph G)
(u v: V)
(W: SubgraphPath H u v)
:
v∈ H.verts:= by
have h1: v∈ W.Wa.toSubgraph.verts:= by
  simp
have h2: W.Wa.toSubgraph.verts⊆ H.verts:= by
  apply subgraphs_vertex_sets_subsets G
  exact W.Wa_In_H
exact h2 h1


lemma Cut_dense_long_path
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u: V)
(u_in_H: u ∈ H.verts)
(d: ℕ)
(hd: p*d < H.verts.toFinset.card)
:
∃ (v: V), ∃ (P: SubgraphPath H u v), P.Wa.length+1= d+1
:=by
induction' d with d hd1 hd2
use u
let W: Walk G u u:= Walk.nil.{u}

have leng: W.length=0:= by exact rfl
have path: W.IsPath:= by exact Walk.IsPath.nil
have sub: W.toSubgraph≤ H:= by
  dsimp [W]
  exact (singletonSubgraph_le_iff u H).mpr u_in_H
use ⟨W, path, sub⟩
simp

have hex: ∃  (v: V), ∃ (P: SubgraphPath H u v), (P.Wa.length+1 = d+1):= by
  apply hd1
  calc
  p * d ≤ p*(d+1):= by
    gcongr
    exact Nat.le_add_right d 1
  _< H.verts.toFinset.card:= by
    exact hd


rcases hex with ⟨v, ⟨P, hP⟩⟩


have v_in_H: v ∈ H.verts:= by
  apply subgraphpath_end_in_H
  exact P


let N: Set V:=H.neighborSet v



have Nsize: p*(N).toFinset.card≥ H.verts.toFinset.card:=by
  --dsimp [N]
  have h1: (N).toFinset.card= H.degree v:=by
    dsimp[N]
    exact Subgraph.finset_card_neighborSet_eq_degree
  rw[h1]
  exact cut_dense_min_degree G v_in_H H_cut_dense


have nbigger: p*(N).toFinset.card>p*(P.Wa.length+1):= by
    rw[hP]
    calc
    p * N.toFinset.card
    ≥ H.verts.toFinset.card:= by
      exact Nsize
    _> p * (d+1):= by exact hd



have nbigger: (N).toFinset.card>P.Wa.length+1:= by
  exact (Nat.mul_lt_mul_left pPositive).mp nbigger


have nbiggersupport: (N).toFinset.card>P.Wa.support.length:= by
  rw[Walk.length_support]
  exact nbigger



have hex2: ∃  (w: V), w∈ N ∧ w ∉ P.Wa.support:= by
  have h2:  (N).toFinset.card>P.Wa.support.toFinset.card:= by
    calc
    (N).toFinset.card>P.Wa.support.length:= by
      exact nbiggersupport
    _≥P.Wa.support.toFinset.card:= by exact List.toFinset_card_le P.Wa.support
  have hnonemp: Finset.Nonempty ((N).toFinset\ (P.Wa.support.toFinset)):= by
    have h3:((N).toFinset\ (P.Wa.support.toFinset)).card>0:= by
      calc
        ((N).toFinset\ (P.Wa.support.toFinset)).card≥ (N).toFinset.card-P.Wa.support.toFinset.card:= by
          exact le_card_sdiff P.Wa.support.toFinset N.toFinset
        _>0:= by
          exact Nat.zero_lt_sub_of_lt h2
    exact card_pos.mp h3
  simp at hnonemp
  rcases hnonemp with ⟨w, hw⟩
  use w
  simp at hw
  exact hw


rcases hex2 with ⟨w, ⟨hw1, hw2⟩⟩
dsimp[N] at hw1
simp at hw1
have h2: ∃ (P1: SubgraphWalk H v w), P1.Wa.length = 1:= by
  exact subgraph_walk_two_vertices H v w hw1

have evw: G.Adj v w:= by
  exact Subgraph.Adj.adj_sub hw1

let Q:Walk G u w:= Walk.append (P.Wa) (evw.toWalk)

use w
have hcont: Q.toSubgraph≤ H:= by
  dsimp [Q]
  simp
  constructor
  exact P.Wa_In_H
  exact subgraphOfAdj_le_of_adj H hw1


have hlen: Q.length+1=d+1+1:= by
  calc
    Q.length+1
    =P.Wa.length+ evw.toWalk.length+1:= by
      congr
      exact Walk.length_append P.Wa evw.toWalk
    _=d+1+1:= by
      congr
      simp at hP
      exact hP



have hpath: Q.IsPath:= by
  dsimp[Q]
  apply append_paths
  exact P.Wa_Is_Path
  refine Walk.IsPath.cons ?Qpath.hp ?Qpath.hu
  exact Walk.IsPath.nil
  simp
  exact Adj.ne' (id (adj_symm G evw))
  have h2: evw.toWalk.support.tail=[w]:= by
    simp
  rw[h2]
  simp
  exact hw2




use ⟨Q, hpath, hcont⟩
