--import MyProject

import hyperstabilityES.lemmas.cut_dense_union
 --import hyperstabilityES.lemmas.SimpleGraph
set_option linter.unusedVariables false

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph

--set_option maxHeartbeats 600000

universe u
variable {V : Type u} (G : SimpleGraph V)
variable [Fintype V] [DecidableRel G.Adj]
variable (n: ℕ )
variable (d:ℕ )
variable [Fintype (Sym2 V)]

--lemma interedges_eq_biUnion2 :
 --   interedges r s t = s.biUnion (fun x ↦ (t.filter (r x)).map ⟨(x, ·), Prod.mk.inj_left x⟩) := by
 -- ext ⟨x, y⟩; simp [mem_interedges_iff]


lemma interedges_subset
{H: Subgraph G}
{A B A' B': Finset V}
(hA: A'⊆ A)
(hB: B'⊆ B)
: (Rel.interedges H.Adj A' B') ⊆  (Rel.interedges H.Adj A B):= by
  intro x hx
  have h2: x∈ (Rel.interedges H.Adj A' B'):= by exact hx
  have h3: x.1∈ A' ∧ x.2∈ B' ∧ H.Adj x.1 x.2:= by exact Rel.mem_interedges_iff.mp h2
  have h4: x.1∈ A':= by exact h3.1
  have h5: x.2∈ B':= by exact h3.2.1
  have h4': x.1∈ A:= by exact hA h4
  have h5': x.2∈ B:= by exact hB h5
  apply Rel.mem_interedges_iff.mpr --⟨h6, h7, h3.2.2⟩
  constructor
  exact h4'
  constructor
  exact h5'
  exact h3.2.2

lemma subtract_superset {A B: Finset V}(h1: A⊆ B): A\ B=∅ := by
  ext x
  simp
  intro h
  exact h1 h

lemma subtract_subtract_set {A B C: Finset V}: (C \ B)\ A= C \ (B ∪ A):= by
have h1: C \ (B ∪ A)= (C\ B)∩ (C\ A):= by exact sdiff_union_distrib C B A
have h2: (C \ B)\ A= (C\ B)∩ (C\ A):= by exact Finset.sdiff_sdiff_left' C B A
rw [h1, h2]


lemma set_equals_union_of_difference_intersetion
{B C: Finset V}: C=(C \ B)∪  (C ∩ B):= by
have h1: C\ B= C\(C ∩ B):= by exact (sdiff_inter_self_left C B).symm
exact (sdiff_union_inter C B).symm

lemma minus_intersection_partition {A B C: Finset V}(h: C⊆ A∪ B):  C\ A⊆  C∩ B:= by
have h1: C=(C \ B)∪  (C ∩ B):= by exact set_equals_union_of_difference_intersetion
have h2: C \ A = ((C \ B)\ A) ∪  ((C ∩ B) \ A):= by calc
  C \ A = ((C \ B) ∪ (C ∩ B))\ A:= by nth_rw 1 [h1];
  _= ((C \ B)\ A) ∪  ((C ∩ B) \ A):= by exact union_sdiff_distrib (C \ B) (C ∩ B) A

have h3: (C \ B)\ A = ∅:= by calc
  (C \ B)\ A= C \ (B ∪ A):= by exact subtract_subtract_set
  _= ∅:= by
   have h4:B∪ A=A∪ B:= by exact union_comm B A
   rw [h4]
   exact subtract_superset h



calc
C \ A = ((C \ B)\ A) ∪  ((C ∩ B) \ A):= by exact h2
 _= ∅ ∪  ((C ∩ B) \ A):= by exact congrFun (congrArg Union.union h3) ((C ∩ B) \ A)
 _= (C ∩ B) \ A:= by exact empty_union ((C ∩ B) \ A)
 _⊆ C ∩ B:= by exact sdiff_subset (C ∩ B) A

lemma interedges_eq_neighbours
(H: Subgraph G)(a:V)(B:Finset V):
Rel.interedges H.Adj {a} B= (({a}:Finset V).product ((H.neighborSet a).toFinset ∩ B)):= by
ext ⟨x, y⟩
constructor
intro h
have h1: (x∈ {a})∧ (y∈ B)∧ (H.Adj x y):= by
  apply (Rel.mem_interedges_iff).mp h
have h2: x ∈ {a}:= by  exact h1.left
simp at h2
have h3: y∈ (H.neighborSet a).toFinset ∩ B:= by
  have h4: y∈ (H.neighborSet a).toFinset:= by
    have h5: H.Adj a y:= by rw [h2.symm]; exact h1.2.2
    exact Set.mem_toFinset.mpr h5
  have h6: y∈ B:= by exact h1.2.1
  exact mem_inter_of_mem h4 h6
have h2': x ∈ ({a}:Finset V):= by  exact h1.left
apply Finset.mem_product.mpr
exact ⟨h2', h3⟩

intro h
have h1: x ∈ {a} ∧ y ∈ (H.neighborSet a).toFinset ∩ B:= by
  exact Finset.mem_product.mp h
have h2: x ∈ {a}:= by exact h1.left
have h2': x = a:= by simp at h2; exact h2
have h3: y ∈ (H.neighborSet a).toFinset ∩ B:= by exact h1.right
have h4: y ∈ (H.neighborSet a).toFinset:= by exact mem_of_mem_filter y h3
have h4': y ∈ H.neighborSet a:= by exact Set.mem_toFinset.mp h4
have h5: y ∈ B:= by exact mem_of_mem_inter_right h3
have h6: H.Adj x y:= by rw [h2']; exact h4'
exact (Rel.mem_interedges_iff).mpr ⟨h2, h5, h6⟩


lemma interedges_eq_neighbours_card
(H: Subgraph G)(a:V)(B:Finset V):
(Rel.interedges H.Adj {a} B).card= ((H.neighborSet a).toFinset ∩ B).card:= by
rw [interedges_eq_neighbours]
have h1: ({a}:Finset V).card = 1:= by simp
have h2:(({a}:Finset V).product ((H.neighborSet a).toFinset ∩ B)).card= 1*((H.neighborSet a).toFinset ∩ B).card:= by
  exact card_product {a} ((H.neighborSet a).toFinset ∩ B)
rw[h2]
simp




lemma interedges_card_sum {H: Subgraph G}{A B: Finset V}: (Rel.interedges H.Adj A B).card= Finset.sum A  (fun (v:V)=> ((H.neighborSet v).toFinset  ∩ B).card):= by


let f:V→ Finset V:= fun a=>{a}
have h2: A=A.biUnion (fun a=> {a}) := by
  simp

have h2: A=A.biUnion f := by
  exact h2

have h1: Rel.interedges H.Adj A B = A.biUnion fun a=> Rel.interedges H.Adj (f a) B:= by
  nth_rewrite 1 [h2]
  exact Rel.interedges_biUnion_left H.Adj A B f

have h3: Rel.interedges H.Adj A B = A.biUnion fun a=> Rel.interedges H.Adj {a} B:= by
  exact h1

let t:V→ Finset (V× V):= fun a=> Rel.interedges H.Adj {a} B
--have h3': Rel.interedges H.Adj A B = ⋃ a∈ A,  (Rel.interedges H.Adj {a} B):= by
--  exact?
#check Finset.sum_biUnion
#check Set.PairwiseDisjoint
have hDisj:  (↑A: Set V).PairwiseDisjoint t:= by
  intro x hx y hy hneq
  simp at hx hy
  refine Rel.interedges_disjoint_left H.Adj ?hs B
  exact disjoint_singleton.mpr hneq

have h4: ∑ (a∈ A.biUnion t), 1 = ∑ a∈ A, ∑  b∈ t a, 1:= by
  exact sum_biUnion hDisj


calc
(Rel.interedges H.Adj A B).card = (A.biUnion fun a ↦ Rel.interedges H.Adj (f a) B).card:= by exact  congrArg card h1
_=∑ (a∈ A.biUnion t), 1:= by exact  card_eq_sum_ones (A.biUnion fun a ↦ Rel.interedges H.Adj (f a) B)
_= ∑ a∈ A, ∑  b∈ t a, 1:= by exact h4
_= ∑ a∈ A, (t a).card:= by congr; simp
_= ∑ a∈ A, ((H.neighborSet a).toFinset ∩ B).card:= by
  congr;
  ext a;
  exact interedges_eq_neighbours_card G H a B
