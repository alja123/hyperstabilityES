
import MyProject

import MyProject.CovM_bound
 --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
variable (p m κ pr h γ α : ℕ)
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (hI:Inhabited (Clump G p m κ pr h))
variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}

def edges_interedges_set
(H: Subgraph G)
(A B: Set V)
:Set (Sym2 V):=
(Set.image Sym2.mk (Rel.interedges H.Adj A.toFinset B.toFinset))

noncomputable def edges_interedges_finset
(H: Subgraph G)
(A B: Finset V)
:Finset (Sym2 V):=
(Finset.image Sym2.mk (Rel.interedges H.Adj A B))


--lemma bipartite_induce_edge_bound
lemma edges_deleteVerts_contained_in
(H: Subgraph G)
(S: Set V)
:
H.edgeSet⊆
(H.deleteVerts S).edgeSet
∪ (edges_interedges_set H S H.verts):=by
--∪ (Set.image Sym2.mk (Rel.interedges H.Adj H.verts.toFinset S.toFinset)) :=by
unfold edges_interedges_set
intro e  he
have h1: ∃ (a b: V), e=s(a,b):=by
  exact Sym2_to_tuple e
rcases h1 with ⟨a, b, hab⟩
rw[hab] at he
rw[hab]
simp
simp at he
unfold Rel.interedges
simp
have haH:a∈H.verts:=by
  exact H.edge_vert he
have hbH:b∈H.verts:=by
  exact H.edge_vert (id (Subgraph.adj_symm H he))

have h3: H.Adj b a:=by
  exact id (Subgraph.adj_symm H he)

by_cases ha: a∉  S
by_cases hb: b∉ S
left
rename_i
  inst
  inst_1
  inst_2
aesop_subst
  hab
simp_all only [gt_iff_lt,
  not_false_eq_true,
  and_self]

right
aesop
right
aesop



/-
lemma Sym2_mk_bound
(E: Finset (V× V))
:
  (Finset.image Sym2.mk E).card ≤ E.card
 :=by
exact card_image_le
-/

lemma edges_interedges_set_card_eq
(H: Subgraph G)
(A B: Set V)
:
(edges_interedges_set H A B).toFinset.card=(edges_interedges_finset H A.toFinset B.toFinset).card
 :=by
unfold edges_interedges_set
unfold edges_interedges_finset
congr
simp


lemma edges_interedges_set_bound_finset
(H: Subgraph G)
(A B: Finset V)
:
(edges_interedges_finset H A B).card≤ A.card*B.card
:=by
calc
(edges_interedges_finset H A B).card
≤ (Rel.interedges H.Adj A B).card:=by
  unfold edges_interedges_finset
  exact card_image_le
_≤ A.card*B.card:=by
  exact Rel.card_interedges_le_mul H.Adj A B


lemma edges_interedges_set_bound_set
(H: Subgraph G)
(A B: Set V)
:
(edges_interedges_set H A B).toFinset.card≤ A.toFinset.card*B.toFinset.card:=by
calc
(edges_interedges_set H A B).toFinset.card
=(edges_interedges_finset H A.toFinset B.toFinset).card:=by
  exact edges_interedges_set_card_eq H A B
_≤ A.toFinset.card*B.toFinset.card:=by
  exact edges_interedges_set_bound_finset H A.toFinset B.toFinset




lemma edges_deleteVerts_bound
(H: Subgraph G)
(S: Set V)
:
H.edgeSet.toFinset.card≤
(H.deleteVerts S).edgeSet.toFinset.card
+ S.toFinset.card*H.verts.toFinset.card:=by
calc
H.edgeSet.toFinset.card≤
((H.deleteVerts S).edgeSet
∪ (edges_interedges_set H S H.verts)).toFinset.card:=by
  gcongr
  refine Set.toFinset_subset_toFinset.mpr ?_
  exact edges_deleteVerts_contained_in H S
_=((H.deleteVerts S).edgeSet.toFinset
∪ (edges_interedges_set H S H.verts).toFinset).card:=by
  congr
  exact Set.toFinset_union (H.deleteVerts S).edgeSet (edges_interedges_set H S H.verts)
_≤ ((H.deleteVerts S).edgeSet.toFinset).card
+ (edges_interedges_set H S H.verts).toFinset.card:=
  by exact
    card_union_le (H.deleteVerts S).edgeSet.toFinset (edges_interedges_set H S H.verts).toFinset
_≤ (H.deleteVerts S).edgeSet.toFinset.card
+ S.toFinset.card*H.verts.toFinset.card:=by
  gcongr
  exact edges_interedges_set_bound_set H S H.verts



def JClump (i: ℕ ) (Ord: List (Clump G p m κ pr h)): Subgraph G:=
(CovM p m κ pr h (Ord.get! i)).deleteVerts ((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i)))



lemma edges_in_JClump_1
(i s t: ℕ )
(Ord: List (Clump G p m κ pr h))
(S: Set V)
(J Cv: Subgraph G)
(hCv: Cv= CovM p m κ pr h (Ord.get! i))
(hJ: J= JClump p m κ pr h hI i Ord)
(hS: S= ((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i))))
(hk: s*(S).toFinset.card* Cv.verts.toFinset.card≤ t*Cv.edgeSet.toFinset.card)
:
s*J.edgeSet.toFinset.card + t*Cv.edgeSet.toFinset.card≥ s*Cv.edgeSet.toFinset.card
:=by
rw[hJ]
unfold JClump
--rw[hCv]
rw[hS.symm]
rw[hCv.symm]
--rw[hS.symm] at hk
calc
s * Cv.edgeSet.toFinset.card
≤s * ((Cv.deleteVerts S).edgeSet.toFinset.card+ S.toFinset.card*Cv.verts.toFinset.card):=by
  gcongr
  exact edges_deleteVerts_bound Cv S
_=s * (Cv.deleteVerts S).edgeSet.toFinset.card+ s*S.toFinset.card*Cv.verts.toFinset.card:=by
  ring_nf
_≤ s * (Cv.deleteVerts S).edgeSet.toFinset.card + t*Cv.edgeSet.toFinset.card:=by
  gcongr


lemma edges_in_JClump_2
(i: ℕ )
(Ord: List (Clump G p m κ pr h))
--(Ord_Sparse: clump_list_sparse_up_to_n p m κ pr h α hI (Ord.length) Li )
(K: Clump G p m κ pr h)
(hK: K=   (Ord.get! i))
(J Cv: Subgraph G)
(hJ: J= JClump p m κ pr h hI i Ord)


(S: Set V)
(hCv: Cv= CovM p m κ pr h (Ord.get! i))
(hS: S= ((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i))))

(hk: α*(S).toFinset.card* Cv.verts.toFinset.card≤ p^2*4* Cv.edgeSet.toFinset.card)
--s=alpha, t=p^2*4
:
p^2*4*α*J.edgeSet.toFinset.card
+
p^2*4*p^2*4*Cv.edgeSet.toFinset.card
+
p*2*α *K.Gr.edgeSet.toFinset.card
≥
p^2*4*α*K.Gr.edgeSet.toFinset.card
:=by

calc
p^2*4*α*J.edgeSet.toFinset.card
+
p^2*4*p^2*4*Cv.edgeSet.toFinset.card
+
p*2*α *K.Gr.edgeSet.toFinset.card
=

p^2*4*(α *J.edgeSet.toFinset.card
+
p^2*4*Cv.edgeSet.toFinset.card)
+
p*2*α *K.Gr.edgeSet.toFinset.card
:=by ring_nf

_≥
p^2*4*(α *Cv.edgeSet.toFinset.card)
+
p*2*α *K.Gr.edgeSet.toFinset.card
:=by
  gcongr

  apply edges_in_JClump_1-- p m κ pr h γ α hI pPositive mPositive hPositive prPositive hJ hCv hS hk
  exact hCv
  exact hJ
  exact hS
  exact hk

_=
α *(p^2*4*Cv.edgeSet.toFinset.card
+
p*2*K.Gr.edgeSet.toFinset.card)
  :=by ring_nf

_≥ α *(p^2*4*K.Gr.edgeSet.toFinset.card)
:=by
  gcongr
  apply edges_in_CovM
  rw[hK]
  exact hCv


_=p^2*4*α*K.Gr.edgeSet.toFinset.card
:=by ring_nf







lemma Gr_edges_lower_bound
(K: Clump G p m κ pr h)
:
p*2*K.Gr.edgeSet.toFinset.card≥  m*K.Gr.verts.toFinset.card
:=by
calc
p*2*K.Gr.edgeSet.toFinset.card
=
p*2*(∑ (Hi∈ K.H), Hi.edgeSet.toFinset.card)
:=by
  congr
  exact CovM_edgessum_equals_union_HB_final_Gr p m κ pr h K rfl


_=(∑ (Hi∈ K.H), p*2*Hi.edgeSet.toFinset.card)
:=by
  exact mul_sum K.H (fun i ↦ i.edgeSet.toFinset.card) (p * 2)

_≥ (∑ (Hi∈ K.H), Hi.verts.toFinset.card^2)
:=by
  gcongr  with Hi hHi
  apply cut_dense_edges_lower_bound
  apply K.H_Cut_Dense
  exact hHi

_= (∑ (Hi∈ K.H), Hi.verts.toFinset.card*Hi.verts.toFinset.card)
:=by
  congr with Hi hHi
  ring_nf

_≥ (∑ (Hi∈ K.H), m*Hi.verts.toFinset.card)
:=by
  gcongr with Hi hHi
  apply K.H_Order
  exact hHi


_=m*(∑ (Hi∈ K.H), Hi.verts.toFinset.card)
:=by
  exact (mul_sum K.H (fun i ↦ i.verts.toFinset.card) m).symm

_≥ m*K.Gr.verts.toFinset.card
:=by
  gcongr
  --K.Gr.verts.toFinset.card ≤ ∑ Hi ∈ K.H, Hi.verts.toFinset.card
  sorry


lemma edges_in_CovM_lower_bound
(K: Clump G p m κ pr h)
(Cv: Subgraph G)
(hCv: Cv= CovM p m κ pr h K)
:
p^2*4*Cv.edgeSet.toFinset.card≥  m*Cv.verts.toFinset.card
:=by
calc
p^2*4*Cv.edgeSet.toFinset.card
≥
p^2*4*K.Gr.edgeSet.toFinset.card
-
p*2*K.Gr.edgeSet.toFinset.card
:=by
  refine Nat.sub_le_of_le_add ?h
  rw[hCv]
  exact edges_in_CovM p m κ pr h K (CovM p m κ pr h K) rfl

_=(p^2*4-p*2)*K.Gr.edgeSet.toFinset.card
:=by
  exact (Nat.mul_sub_right_distrib (p ^ 2 * 4) (p * 2) K.Gr.edgeSet.toFinset.card).symm

_≥ p*2*K.Gr.edgeSet.toFinset.card
:=by
  gcongr
  --p * 2 ≤ p ^ 2 * 4 - p * 2
  sorry
_≥ m*K.Gr.verts.toFinset.card
:=by
  apply Gr_edges_lower_bound

_≥ m*Cv.verts.toFinset.card
:=by
  gcongr
  simp
  have h1: Cv≤ K.Gr:=by
    sorry
  apply subgraphs_vertex_sets_subsets
  exact h1


lemma edges_in_CovM_lower_bound_sparse_list
(i: ℕ )
(Ord: List (Clump G p m κ pr h))
(Ord_Sparse: clump_list_sparse_up_to_n p m κ pr h α hI (Ord.length) Li )
(K: Clump G p m κ pr h)
(Cv: Subgraph G)
(hK: K=   (Ord.get! i))
(S: Set V)
(hCv: Cv= CovM p m κ pr h (Ord.get! i))
(hS: S= ((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i))))
:
p^2*4*Cv.edgeSet.toFinset.card≥  α * (S).toFinset.card*Cv.verts.toFinset.card
--α *(S).toFinset.card* Cv.verts.toFinset.card≤ p*Cv.edgeSet.toFinset.card
:=by
calc
p^2*4*Cv.edgeSet.toFinset.card

≥

m*Cv.verts.toFinset.card
:=by exact edges_in_CovM_lower_bound p m κ pr h (Ord.get! i) Cv hCv

_≥
 α * (S).toFinset.card*Cv.verts.toFinset.card
:=by
  gcongr
  -- α * S.toFinset.card ≤ m (should follow from Ord_Sparse)
  sorry




lemma edges_in_JClump_3
(i: ℕ )
(Ord: List (Clump G p m κ pr h))
(Ord_Sparse: clump_list_sparse_up_to_n p m κ pr h α hI (Ord.length) Li )
(K: Clump G p m κ pr h)
(hK: K=   (Ord.get! i))

(Cv: Subgraph G)
(S: Set V)
(hCv: Cv= CovM p m κ pr h (Ord.get! i))
(hS: S= ((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i))))

(J: Subgraph G)
(hJ: J= JClump p m κ pr h hI i Ord)
:
p^2*4*α*J.edgeSet.toFinset.card
+
(p*4*α) *K.Gr.edgeSet.toFinset.card
≥
p^2*4*α*K.Gr.edgeSet.toFinset.card
:=by
--let S:=((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i)))
--have hS: S= ((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i))):=by
--  exact rfl
--let Cv:=  CovM p m κ pr h (Ord.get! i)
--have hCv: Cv= CovM p m κ pr h (Ord.get! i):=by
--  exact rfl


have hk: α*(S).toFinset.card* Cv.verts.toFinset.card≤ p^2*4* Cv.edgeSet.toFinset.card:=by
  exact edges_in_CovM_lower_bound_sparse_list p m κ pr h α hI i Ord Ord_Sparse K Cv hK S hCv hS

calc
p^2*4*α*J.edgeSet.toFinset.card
+
(p*4*α) *K.Gr.edgeSet.toFinset.card

=

p^2*4*α*J.edgeSet.toFinset.card
+
(p*2*α+p*2*α) *K.Gr.edgeSet.toFinset.card
:=by ring_nf

_≥

p^2*4*α*J.edgeSet.toFinset.card
+
(p^2*4*p^2*4+ p*2*α) *K.Gr.edgeSet.toFinset.card
:=by
  have h1: p*2*α≥ p^2*4*p^2*4:=by
    sorry
  gcongr

_=

p^2*4*α*J.edgeSet.toFinset.card
+
p^2*4*p^2*4*K.Gr.edgeSet.toFinset.card
+
p*2*α *K.Gr.edgeSet.toFinset.card
:=by ring_nf

_≥

p^2*4*α*J.edgeSet.toFinset.card
+
p^2*4*p^2*4*Cv.edgeSet.toFinset.card
+
p*2*α *K.Gr.edgeSet.toFinset.card
:=by
  gcongr
  have h1: Cv≤ K.Gr:=by
    sorry
  simp
  exact subgraph_implies_edgesets_subsets h1

_≥

p^2*4*α*K.Gr.edgeSet.toFinset.card
:= by
  apply edges_in_JClump_2
  exact hK
  exact hJ
  exact hCv
  exact hS
  exact hk




lemma edges_in_JClump_4
(i: ℕ )
(Ord: List (Clump G p m κ pr h))
(Ord_Sparse: clump_list_sparse_up_to_n p m κ pr h α hI (Ord.length) Li )
(K: Clump G p m κ pr h)
(hK: K=   (Ord.get! i))
(J: Subgraph G)
(hJ: J= JClump p m κ pr h hI i Ord)
:
p*J.edgeSet.toFinset.card
+
 K.Gr.edgeSet.toFinset.card
≥
p*K.Gr.edgeSet.toFinset.card
:=by
let S:=((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i)))
have hS: S= ((BSet (Ord.get! i)) ∩ list_union  p m κ pr h (Ord.drop (i))):=by
  exact rfl
let Cv:=  CovM p m κ pr h (Ord.get! i)
have hCv: Cv= CovM p m κ pr h (Ord.get! i):=by
  exact rfl

have h1:
p^2*4*α*J.edgeSet.toFinset.card
+
(p*4*α) *K.Gr.edgeSet.toFinset.card
≥
p^2*4*α*K.Gr.edgeSet.toFinset.card
:=by
  apply edges_in_JClump_3
  repeat assumption


have h1:
p*4*α*(p*J.edgeSet.toFinset.card
+
K.Gr.edgeSet.toFinset.card)
≥
p*4*α*(p*K.Gr.edgeSet.toFinset.card)
:=by
  calc
    p*4*α*(p*J.edgeSet.toFinset.card
    +
    K.Gr.edgeSet.toFinset.card)
    =
    p^2*4*α*J.edgeSet.toFinset.card
    +
    (p*4*α) *K.Gr.edgeSet.toFinset.card
    :=by
      ring_nf
    _≥
    p^2*4*α*K.Gr.edgeSet.toFinset.card
    :=by
      exact h1
    _=
    p*4*α*(p*K.Gr.edgeSet.toFinset.card)
    :=by
      ring_nf


apply le_of_mul_le_mul_left
exact h1

-- 0 < p * 4 * α
sorry