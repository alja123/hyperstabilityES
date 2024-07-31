import MyProject

import MyProject.path_sequence_construct
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
variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}




structure SubgraphWalk
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_In_H: Wa.toSubgraph≤ H

structure SubgraphPath
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_Is_Path: Wa.IsPath
  Wa_In_H: Wa.toSubgraph≤ H

--def pathlength (P: SubgraphPath G u v): ℕ:= P.Wa.length

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



lemma No_edges_outside_neighborhood
(H: Subgraph G)
(v x y: V)
(v_in_H: v ∈ H.verts)
(d: ℕ )
(Nd Nd': Set V)
(hNd:Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d})
(hNd':Nd' ={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d+1})
(hx: x ∈ Nd)
(hxy: H.Adj x y)
:
y∈ Nd'
:=by
rw[hNd']
simp
rw[hNd] at hx
simp at hx
rcases hx with ⟨w, hw⟩
--let d: ℕ:= w.Wa.length
have hxy2: G.Adj x y:= by exact Subgraph.Adj.adj_sub hxy
let wxy:G.Walk x y:= hxy2.toWalk
let W: G.Walk v y:= Walk.append w.Wa wxy
have Wlength: W.length ≤ d+1:=by
  calc
    W.length = w.Wa.length + wxy.length:= by exact Walk.length_append w.Wa wxy
    _ ≤ d+1:= by
      gcongr
      dsimp [wxy]
      exact NeZero.one_le
have inH: W.toSubgraph≤ H:=by
  dsimp [W]
  simp
  constructor

  exact w.Wa_In_H
  exact subgraphOfAdj_le_of_adj H hxy
use ⟨W, inH ⟩




lemma union_diff_lemma
(H Nd Nd' C B: Set V)
(hNd':  Nd'⊆ H)
(hNd:  Nd⊆ Nd')
(hC:C=H\ Nd')
(hB:B=H\ Nd)
:
B=C∪ (Nd'\ Nd)
:=by
  rw [hB, hC]
  ext w
  constructor
  simp
  intro h h2
  by_cases cas: w ∈ Nd'
  right
  constructor
  repeat assumption
  left
  constructor
  repeat assumption
  simp
  intro h
  by_cases cas: w ∈ Nd'

  aesop
  have h1: w∉  Nd:=by exact fun a ↦ cas (hNd a)
  aesop





lemma Nd_in_verts
(H: Subgraph G)
(Nd: Set V)
(d: ℕ )
(hNd:Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d})
:
Nd⊆ H.verts
:=by
rw[hNd]
intro w hw
simp at hw
rcases hw with ⟨P, hP⟩
have h1:_:=by exact P.Wa_In_H
have h2: w∈ P.Wa.toSubgraph.verts:=by
  simp
have h3: P.Wa.toSubgraph.verts ⊆  H.verts:=by
  apply  subgraphs_vertex_sets_subsets G
  exact h1

exact h3 h2


lemma Nd_in_Nd'
(H: Subgraph G)
(Nd: Set V)
(d: ℕ )
(hNd:Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d})
(hNd':Nd' ={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d+1})
:
Nd⊆ Nd'
:=by
rw[hNd, hNd']
simp
intro w hw
intro h2
use hw
exact Nat.le_succ_of_le h2


lemma interedges_contained_union
(H: Subgraph G)
(A B C D: Finset V)
(hBCD: B⊆ C∪ D)
:
Rel.interedges (H.Adj) A B ⊆ (Rel.interedges (H.Adj) A C)∪ (Rel.interedges (H.Adj) A D)
:=by
intro ⟨x,y ⟩
intro h
unfold Rel.interedges
simp
unfold Rel.interedges at h
simp at h
aesop
exact mem_union.mp (hBCD right_1)



lemma Cut_Dense_expansion
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(v: V)
(v_in_H: v ∈ H.verts)
(d: ℕ )
(Nd Nd': Set V)
(hNd:Nd={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d})
(hNd':Nd' ={w: V| ∃ (P: SubgraphWalk H v w), P.Wa.length≤ d+1})
(hsmall: 2*Nd.toFinset.card≤ H.verts.toFinset.card)
:
(4*p*(Nd'\ Nd).toFinset.card≥ H.verts.toFinset.card)
:=by
let C: Set V:=H.verts\ Nd'

have empty_Nd_C: (Rel.interedges (H.Adj) (Nd.toFinset) (C.toFinset))=∅  := by
  unfold Rel.interedges
  dsimp [C]
  --rw[hNd]
  simp
  refine filter_eq_empty_iff.mpr ?_
  intro ⟨a, b ⟩
  intro hab
  simp
  simp at hab
  by_contra contr
  have hc:b∈ Nd':=by
    apply No_edges_outside_neighborhood
    exact v_in_H
    exact hNd
    repeat assumption
    exact hab.1
    exact contr
  aesop


have upperbound2: (Rel.interedges (H.Adj) (Nd.toFinset) ((Nd'\ Nd).toFinset)).card≤ (Nd.toFinset.card)* ((Nd'\ Nd).toFinset.card)  := by
  exact Rel.card_interedges_le_mul H.Adj Nd.toFinset (Nd' \ Nd).toFinset

by_contra contr
simp only [ ge_iff_le, not_le] at contr

let B: Set V:= H.verts\ Nd

have hcont0: B=C∪ (Nd'\ Nd):=by
  apply union_diff_lemma (H.verts) Nd Nd' C B
  apply Nd_in_verts; exact hNd'
  apply Nd_in_Nd'; exact hNd; exact hNd'
  exact rfl
  exact rfl

have hcont1: B.toFinset=C.toFinset∪ (Nd'\ Nd).toFinset:=by
  simp_rw [hcont0]
  simp





have hcont:Rel.interedges (H.Adj) (Nd.toFinset) (B.toFinset)⊆ Rel.interedges (H.Adj) (Nd.toFinset) ((Nd'\ Nd).toFinset) ∪ Rel.interedges (H.Adj) (Nd.toFinset) (C.toFinset):=by
  --rw[hcont1]
  --simp
  apply interedges_contained_union H (Nd.toFinset) (B.toFinset) ((Nd'\ Nd).toFinset) (C.toFinset)
  rw[hcont1]
  simp
  rw[union_comm]

have B_lower: 2*B.toFinset.card≥ H.verts.toFinset.card:=by
  dsimp [B]
  --simp
  calc
    2 *( (H.verts \ Nd).toFinset.card)=2 * ((H.verts).toFinset.card-Nd.toFinset.card):=by
      congr
      simp only [Set.toFinset_diff]
      refine card_sdiff ?_
      simp
      exact Nd_in_verts H Nd d hNd
    _=2 * (H.verts).toFinset.card-2*Nd.toFinset.card:=by
      exact Nat.mul_sub_left_distrib 2 H.verts.toFinset.card Nd.toFinset.card
    _≥ 2 * (H.verts).toFinset.card-(H.verts).toFinset.card:= by
      gcongr

    _=2 * (H.verts).toFinset.card-1*(H.verts).toFinset.card:=by
      ring_nf
    _=(2-1)*(H.verts).toFinset.card:=by
      exact (Nat.mul_sub_right_distrib 2 1 H.verts.toFinset.card).symm
    _=H.verts.toFinset.card:=by
      simp


have hineq1: 4*p*(Rel.interedges (H.Adj) (Nd.toFinset) (B.toFinset)).card≤ 2*(Nd.toFinset.card)*(B.toFinset.card):=by
  calc
    4*p*(Rel.interedges (H.Adj) (Nd.toFinset) (B.toFinset)).card
    ≤ 4*p*(( Rel.interedges (H.Adj) (Nd.toFinset) ((Nd'\ Nd).toFinset) ∪ Rel.interedges (H.Adj) (Nd.toFinset) (C.toFinset)).card):=by
      gcongr
    _≤ 4*p*((Rel.interedges (H.Adj) (Nd.toFinset) ((Nd'\ Nd).toFinset)).card+ (Rel.interedges (H.Adj) (Nd.toFinset) (C.toFinset)).card):=by
      gcongr
      exact
        card_union_le (Rel.interedges H.Adj Nd.toFinset (Nd' \ Nd).toFinset)
          (Rel.interedges H.Adj Nd.toFinset C.toFinset)
    _≤ 4*p*(((Nd.toFinset.card)* (Nd'\ Nd).toFinset.card)+ 0):=by
      gcongr (4*p*(?_+?_))
      simp
      exact empty_Nd_C

    _= (Nd.toFinset.card)* (4*p*((Nd'\ Nd).toFinset.card)):=by
      ring_nf
    _≤ (Nd.toFinset.card)*(H.verts.toFinset.card):=by
      gcongr
    _≤ (Nd.toFinset.card)*(2*B.toFinset.card):=by
      gcongr
    _=2* (Nd.toFinset.card)*(B.toFinset.card):=by
      ring_nf





have hineq2: p*(Rel.interedges (H.Adj) (Nd.toFinset) (B.toFinset)).card≥ (Nd.toFinset.card)*(B.toFinset.card):=by
  apply H_cut_dense
  dsimp[B]
  simp
  apply Nd_in_verts; exact hNd



have hstrict: 4*(Nd.toFinset.card)*(B.toFinset.card)≤ 2*(Nd.toFinset.card)*(B.toFinset.card):=by
  calc
    2*(Nd.toFinset.card)*(B.toFinset.card)≥  4*p*(Rel.interedges (H.Adj) (Nd.toFinset) (B.toFinset)).card:= by exact hineq1
    _=4*(p*(Rel.interedges (H.Adj) (Nd.toFinset) (B.toFinset)).card):=by ring_nf
    _≥  4*((Nd.toFinset.card)*(B.toFinset.card)):= by gcongr (4*(?_))
    _=4*(Nd.toFinset.card)*(B.toFinset.card):= by ring_nf


have hstrict2: 4*(Nd.toFinset.card)*(B.toFinset.card)> 2*(Nd.toFinset.card)*(B.toFinset.card):=by
  gcongr
  -- 0 < B.toFinset.card
  sorry
  --  0 < Nd.toFinset.card
  sorry
  exact Nat.lt_of_sub_eq_succ rfl

have hstr3: ¬( 4*(Nd.toFinset.card)*(B.toFinset.card)> 2*(Nd.toFinset.card)*(B.toFinset.card)):=by
  exact Nat.not_lt.mpr hstrict

exact   hstr3 hstrict2




--
