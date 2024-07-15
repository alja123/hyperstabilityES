import MyProject

import MyProject.cut_dense_add_vertices
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

theorem Handshaking_lemma_subgraphs
(H: Subgraph G)
: ∑ (v∈ H.verts), H.degree v = 2 * (H.edgeSet.toFinset.card) :=by
let U:= { x // x ∈ H.verts }
let K:SimpleGraph U:=H.coe
simp at K
simp at U
#check sum_degrees_eq_twice_card_edges K


let f: U→ ℕ := fun x=> K.degree x
--let m:ℕ := 2 * (K.edgeFinset.card)
--have h0: 2 * (filter (fun x ↦ x ∈ K.edgeSet) univ).card = 2 * (K.edgeFinset.card):= by simp;
have h1:  _:= by  exact sum_degrees_eq_twice_card_edges K


have h3: K.edgeFinset.card= H.edgeSet.toFinset.card:= by
  sorry
--  simp
--  have h2: ((K.edgeSet): Set (Sym2 V))=H.edgeSet:= by
--    simp
rw[h3.symm]

--have ha: ∑ v : U, K.degree v=∑ v : U, f v:= by
--  simp
--rw [ha] at h1

have h4: ∀ (v:U), K.degree v = H.degree v:= by
  intro v
  exact Subgraph.coe_degree H v

have h7: ∀ (v:U), H.degree v = K.degree v:= by
  intro v
  exact (Subgraph.coe_degree H v).symm

--have h5: ∑ v ∈ H.verts.toFinset, H.degree v=∑ v ∈ H.verts, H.degree v:=by
--  simp



rw [h1.symm]
--rw [h5]


have h6: ∑ v ∈ H.verts.toFinset, H.degree v = ∑ v : U, H.degree v:= by
  refine sum_subtype H.verts.toFinset ?h fun a ↦ H.degree a
  intro x
  exact Set.mem_toFinset
rw[h6]
congr
ext x
rw[h7 x]

sorry



theorem cut_dense_edges_lower_bound
{H: Subgraph G}
{k:ℕ }
(hCutDense: cut_dense G H k)
: (k*2)*(H.edgeSet.toFinset.card) ≥ (H.verts.toFinset.card)^2:= by
#check cut_dense_min_degree
calc
(k*2)*(H.edgeSet.toFinset.card)=k*(2*(H.edgeSet.toFinset.card)):= by ring_nf
_=k*(∑ (v∈ H.verts), H.degree v):= by congr; symm; exact Handshaking_lemma_subgraphs H
_=(∑ (v∈ H.verts), k*(H.degree v)):= by exact mul_sum H.verts.toFinset (fun i ↦ H.degree i) k
_≥ ∑ (v∈ H.verts), (H.verts.toFinset.card):= by
  gcongr with i hi;
  have hi: i ∈ H.verts:= by exact Set.mem_toFinset.mp hi
  exact cut_dense_min_degree G hi  hCutDense
_=(H.verts.toFinset.card)*(H.verts.toFinset.card):= by exact sum_const_nat fun x ↦ congrFun rfl
_=(H.verts.toFinset.card)^2:= by ring_nf

end SimpleGraph
