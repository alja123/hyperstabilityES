import MyProject

import MyProject.long_path_avoiding
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 40000

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

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}



theorem cut_dense_existence
(q: ℕ )--p≫ q
(H: Subgraph G)
(HEdges: q*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
:∃ (D: Subgraph G), D ≤ H ∧ cut_dense G D p:= by


sorry


noncomputable def  v (H: Subgraph G):ℕ := H.verts.toFinset.card
noncomputable def e (H: Subgraph G):ℕ := H.verts.toFinset.card

theorem not_cut_dense_two_cases
(q s n: ℕ )--p≫ q
(H: Subgraph G)
(HEdges: q*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
(not_cut_dense : ¬cut_dense G H p)
:∃(B: Subgraph G),
(B≤  H)
∧
s*(v H)^2 *(e B)+(v B)*(v H)*(e H)≥ s*(v B)*(v H)*(e H)+(v B)^2*(e B)
:= by
unfold cut_dense at not_cut_dense
simp at not_cut_dense
rcases not_cut_dense with ⟨AS, BS, hUnion, hNotCut⟩


let A: Subgraph G:= H.induce AS

let B: Subgraph G:= H.induce BS


have hedgesum: (e A)+(e B) + (Rel.interedges H.Adj AS BS).card
≥ (e H):= by
  sorry

have hedgesum2: p*(e A)+p*(e B) + (v A)*(v B)
≥ p*(e H):= by
  sorry


have A_upperbound: 2*(e A) + (v A)≤ (v A)*(v A):=by sorry
have B_upperbound: 2*(e B) + (v B)≤ (v B)*(v B):=by sorry


have cont1: s*(v H)^2 *(e B)+(v B)*(v H)*(e H)
< s*(v B)*(v H)*(e H)+(v B)^2*(e B):=by
  sorry

have cont2: s*(v H)^2 *(e A)+(v A)*(v H)*(e H)
< s*(v A)*(v H)*(e H)+(v A)^2*(e A):=by
  sorry

/-
theorem near_regular_subgraph
(H: Subgraph G)
(HEdges: p*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
(HOrder: H.verts.toFinset.card≥ m):
∃ (H': Subgraph G), H' ≤ H ∧ near_regular H' (m/pr):= by
 sorry

def cut_dense (G : SimpleGraph V)(H: Subgraph G)(k : ℕ ): Prop :=
∀ (A B: Finset V), (H.verts.toFinset= A ∪ B)→  k*(Rel.interedges H.Adj A B).card ≥ A.card*B.card

-/
