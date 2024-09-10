--import MyProject

import hyperstabilityES.lemmas.cut_dense_add_vertices
 --import hyperstabilityES.lemmas.SimpleGraph

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


def min_degree_at_least (H: Subgraph G)(d:ℕ): Prop:=
∀ (v: V), (v∈ H.verts)→ (H.degree v ≥ d)

def min_degree_at_least_proportion (H: Subgraph G)(d:ℕ): Prop:=
∀ (v: V), (v∈ H.verts)→ (d*H.degree v ≥ H.verts.toFinset.card)


lemma neighborset_delete_vertices
{H: Subgraph G}
{v: V}
{U: Set V}
(hv: v∈ H.verts\ U)
 :  (H.induce (H.verts\ U)).neighborSet v = (H.neighborSet v)\ U:= by
ext x
constructor
intro h1
refine (Set.mem_diff x).mpr ?h.mp.a
constructor
refine (Subgraph.mem_neighborSet H v x).mpr ?h.mp.a.left.a
have h2: (H.induce (H.verts \ U)).Adj v x:= by exact h1
have h3: H.induce (H.verts \ U)≤ H:= by exact Subgraph.deleteVerts_le
exact subgraph_preserves_adj G (H.induce (H.verts \ U)) H h3 v x h1
have h4: (H.induce (H.verts \ U)).neighborSet v⊆ H.verts\ U:= by calc
    (H.induce (H.verts \ U)).neighborSet v⊆ (H.induce (H.verts \ U)).verts:= by
      exact Subgraph.neighborSet_subset_verts (H.induce (H.verts \ U)) v
    _= H.verts\ U:= by exact rfl
have h5: x∈ H.verts\ U:= by exact h4 h1
exact Set.not_mem_of_mem_diff (h4 h1)

intro hx
have h6:  x ∈ H.neighborSet v:= by exact Set.mem_of_mem_diff hx
refine (Subgraph.mem_neighborSet (H.induce (H.verts \ U)) v x).mpr ?h.mpr.a
refine Subgraph.deleteVerts_adj.mpr ?h.mpr.a.a
constructor
exact Set.mem_of_mem_diff hv
constructor
exact Set.not_mem_of_mem_diff hv
constructor
exact Subgraph.Adj.snd_mem h6
constructor
exact Set.not_mem_of_mem_diff hx
exact h6

/-
lemma set_subtract_lower_bound
(S T: Finset V)
: (S\ T).card ≥  S.card-T.card:= by
#check Finset.card_sdiff
have h2: (S ∩ T)⊆ S:= by exact inter_subset_left S T
have h3: (S\ T)=(S\ (S∩ T)):= by
  exact (sdiff_inter_self_left S T).symm
have h1: (S\ T).card= S.card - (S ∩ T).card:= by
  rw [h3]
  exact card_sdiff h2
exact le_card_sdiff T S-/

lemma neighborset_delete_vertices_card
{H: Subgraph G}
{v: V}
{U: Set V}
:  ((H.neighborSet v)\ U).toFinset.card ≥  (H.neighborSet v).toFinset.card - U.toFinset.card:= by
calc
((H.neighborSet v)\ U).toFinset.card
=((H.neighborSet v).toFinset\ U.toFinset).card:= by
  congr
  simp
_≥  (H.neighborSet v).toFinset.card - U.toFinset.card:= by
  exact le_card_sdiff U.toFinset (H.neighborSet v).toFinset

lemma degree_delete_vertices
{H: Subgraph G}
{v: V}
{U: Set V}
(hv: v∈ H.verts\ U)
 :  (H.induce (H.verts\ U)).degree v≥ H.degree v- U.toFinset.card:= by
have h1: v ∈ H.verts:= by exact Set.mem_of_mem_diff hv
have h3: (H.neighborSet v).toFinset.card = H.degree v:= by exact Subgraph.finset_card_neighborSet_eq_degree
have h3': ((H.induce (H.verts\ U)).neighborSet v).toFinset.card = (H.induce (H.verts\ U)).degree v:= by
  exact  Subgraph.finset_card_neighborSet_eq_degree
have h4: (H.induce (H.verts\ U)).neighborSet v = (H.neighborSet v)\ U:= by
  exact neighborset_delete_vertices hv
rw[h3.symm, h3'.symm]
simp_rw[h4]
have h5: (H.neighborSet v \ U).toFinset=(H.neighborSet v).toFinset \ U.toFinset:= by
  exact Set.toFinset_diff (H.neighborSet v) U
rw[h5]
exact le_card_sdiff U.toFinset (H.neighborSet v).toFinset



lemma degree_delete_vertices2
{H: Subgraph G}
{v: V}
{U: Set V}
(hv: v∈ H.verts\ U)
 :  (H.induce (H.verts\ U)).degree v≥ H.degree v- (U∩ (H.neighborSet v)).toFinset.card:= by
have h1: v ∈ H.verts:= by exact Set.mem_of_mem_diff hv
have h3: (H.neighborSet v).toFinset.card = H.degree v:= by exact Subgraph.finset_card_neighborSet_eq_degree
have h3': ((H.induce (H.verts\ U)).neighborSet v).toFinset.card = (H.induce (H.verts\ U)).degree v:= by
  exact  Subgraph.finset_card_neighborSet_eq_degree
have h4: (H.induce (H.verts\ U)).neighborSet v = (H.neighborSet v)\ U:= by
  exact neighborset_delete_vertices hv
rw[h3.symm, h3'.symm]
simp_rw[h4]
have h5: (H.neighborSet v \ U).toFinset=(H.neighborSet v).toFinset \ U.toFinset:= by
  exact Set.toFinset_diff (H.neighborSet v) U
rw[h5]
have h6: (H.neighborSet v) \ U=(H.neighborSet v)\ (U∩ (H.neighborSet v)):= by
  exact Set.diff_inter_self_eq_diff.symm

have h7: (H.neighborSet v).toFinset \ U.toFinset=(H.neighborSet v).toFinset \ (U∩ (H.neighborSet v)).toFinset:= by
  calc
  (H.neighborSet v).toFinset \ U.toFinset=(H.neighborSet v \ U).toFinset:= by
    exact id h5.symm
  _=(H.neighborSet v \ (U∩ (H.neighborSet v))).toFinset:= by
    simp_rw[h6]
  _=(H.neighborSet v).toFinset \ (U∩ (H.neighborSet v)).toFinset:= by
   exact Set.toFinset_diff (H.neighborSet v) (U ∩ H.neighborSet v)
rw[h7]

apply le_card_sdiff


lemma min_degree_delete_vertices
{H: Subgraph G}
{d u:ℕ}
(h: min_degree_at_least H d)
{U: Set V}
(Uupperbound:  U.toFinset.card ≤ u)
: min_degree_at_least (H.induce (H.verts\ U)) (d- U.toFinset.card):= by
intro v
intro hv
have hv':  v∈ H.verts\ U:= by exact hv
calc
(H.induce (H.verts\ U)).degree v≥ H.degree v - U.toFinset.card:= by
  exact degree_delete_vertices hv
_≥ d - U.toFinset.card:= by gcongr; apply h v; exact Set.mem_of_mem_diff hv
--_≥ d - u:= by exact Nat.sub_le_sub_left Uupperbound d


lemma min_degree_proportion_delete_vertices
{H: Subgraph G}
{d u:ℕ}
(h: min_degree_at_least_proportion H d)
{U: Set V}
(Uupperbound:  2*d*U.toFinset.card ≤ H.verts.toFinset.card)
: min_degree_at_least_proportion (H.induce (H.verts\ U)) (2*d):= by
intro v
intro hv
have hv':  v∈ H.verts\ U:= by exact hv
calc
(2*d)  * (H.induce (H.verts \ U)).degree v≥ (2*d) *(H.degree v - U.toFinset.card):= by
  gcongr; exact degree_delete_vertices hv
_= (2*d) *H.degree v - (2*d)*U.toFinset.card:=by
  exact  Nat.mul_sub_left_distrib (2*d) (H.degree v) U.toFinset.card
_= 2*(d *H.degree v) - (2*d)*U.toFinset.card:=by ring_nf
_≥2*H.verts.toFinset.card - (2*d)*U.toFinset.card:= by
  gcongr; apply h v;
  exact Set.mem_of_mem_diff hv
_≥ 2*H.verts.toFinset.card -H.verts.toFinset.card:=
  by gcongr
_= 2*H.verts.toFinset.card -1*H.verts.toFinset.card:=
  by ring_nf
_=(2-1)*H.verts.toFinset.card:= by
  exact (Nat.mul_sub_right_distrib 2 1 H.verts.toFinset.card).symm
_= H.verts.toFinset.card:= by ring_nf
_≥ (H.induce (H.verts \ U)).verts.toFinset.card:=
  by
    have h1:  (H.induce (H.verts \ U))≤ H := by exact Subgraph.deleteVerts_le
    gcongr
    exact subgraphs_vertex_subsets G (H.induce (H.verts \ U)) H h1



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
  --simp
  dsimp [K]
  dsimp[U]

  unfold edgeFinset


  refine (card_eq_of_equiv ?i).symm
  simp
  symm
  refine Set.BijOn.equiv ?i.f ?i.h
  let f: { x // x ∈ H.verts }→ V:= fun x=> x.1
  let g: Sym2 { x // x ∈ H.verts } → Sym2 V:= fun x=> Sym2.map f x
  exact g
  constructor
  intro x hx
  have h1: ∃ (a b: { x // x ∈ H.verts }), x=s(a,b):= by
    use (Quot.out x).1
    use (Quot.out x).2
    simp

  rcases h1 with ⟨a, b, h1⟩
  rw[h1]
  rw[h1] at hx
  simp at hx
  simp
  exact hx

  constructor
  intro x  hx y hy hxy
  have hxx: ∃ (a b: { x // x ∈ H.verts }), x=s(a,b):= by
    use (Quot.out x).1
    use (Quot.out x).2
    simp
  have hyy: ∃ (c d: { x // x ∈ H.verts }), y=s(c,d):= by
    use (Quot.out y).1
    use (Quot.out y).2
    simp
  rcases hxx with ⟨a, b, hab⟩
  rcases hyy with ⟨c, d, hcd⟩
  rw[hab, hcd]
  rw[hab, hcd] at hxy
  rw[hab] at hx
  rw[hcd] at hy
  simp at hx hy hxy
  simp
  aesop

  intro x hx
  have hxx: ∃ (a b: V), x=s(a,b):= by
    use (Quot.out x).1
    use (Quot.out x).2
    simp
  rcases hxx with ⟨a, b, hab⟩
  rw[hab]
  rw[hab] at hx
  simp at hx
  simp
  have ha: a∈ H.verts:= by
    exact H.edge_vert hx
  have hb: b∈ H.verts:= by
    exact H.edge_vert (id (Subgraph.adj_symm H hx))
  use s(⟨a, ha⟩, ⟨b, hb⟩)
  simp
  exact hx

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
  --refine sum_subtype H.verts.toFinset ?h fun a ↦ H.degree a
  apply sum_subtype

  intro x
  exact Set.mem_toFinset
rw[h6]
congr
ext x
rw[h7 x]

have h8: K.degree x = (K.neighborFinset x).card:= by
  exact rfl

rw[h8]

have h9:@degree U K x (K.neighborSetFintype x)=(@neighborFinset U K x (K.neighborSetFintype x)).card
:= by exact rfl
rw[h9]

have h10: (@neighborFinset U K x (K.neighborSetFintype x))=(@neighborFinset U K x (Subgraph.coeFiniteAt x)):= by
  ext y
  simp
rw[h10]




theorem cut_dense_min_degree_proportion_at_least
{H: Subgraph G}
{k:ℕ }
(hCutDense: cut_dense G H k)
: min_degree_at_least_proportion H k:= by
intro v hv
apply cut_dense_min_degree
exact hv
exact hCutDense



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


lemma edges_mindegree_lowerbound
{H: Subgraph G}
{d:ℕ}
(h: min_degree_at_least H d)
: 2*H.edgeSet.toFinset.card ≥ (H.verts.toFinset.card)*d:= by
calc
2*H.edgeSet.toFinset.card=∑ (v∈ H.verts), H.degree v:= by symm; exact Handshaking_lemma_subgraphs H
_≥ ∑ (v∈ H.verts), d:= by
  gcongr with i hi;
  have hi: i ∈ H.verts:= by exact Set.mem_toFinset.mp hi
  exact h i hi
_=(H.verts.toFinset.card)*d:= by exact sum_const_nat fun x ↦ congrFun rfl


lemma edges_mindegree_proportion_lowerbound
{H: Subgraph G}
{d:ℕ}
(h: min_degree_at_least_proportion H d)
: d*(2*H.edgeSet.toFinset.card) ≥ (H.verts.toFinset.card)^2:= by
calc
d*(2*H.edgeSet.toFinset.card)=d*(∑ (v∈ H.verts), H.degree v):= by congr; symm; exact Handshaking_lemma_subgraphs H
_=∑ (v∈ H.verts), d*H.degree v:= by exact mul_sum H.verts.toFinset (fun i ↦ H.degree i) d
_≥ ∑ (v∈ H.verts), (H.verts.toFinset.card):= by
  gcongr with i hi;
  have hi: i ∈ H.verts:= by exact Set.mem_toFinset.mp hi
  exact h i hi
_=(H.verts.toFinset.card)*(H.verts.toFinset.card):= by exact sum_const_nat fun x ↦ congrFun rfl
_=(H.verts.toFinset.card)^2:= by ring_nf



end SimpleGraph
