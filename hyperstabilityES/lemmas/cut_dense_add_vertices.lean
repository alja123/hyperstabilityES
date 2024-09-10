--import MyProject

import hyperstabilityES.lemmas.cut_dense_union
import hyperstabilityES.lemmas.interedges_auxiliary

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

--lemma interedges_card_sum {H: Subgraph G}{A B: Finset V}: (Rel.interedges H.Adj A B).card= Finset.sum A  (fun (v:V)=> ((H.neighborSet v).toFinset  ∩ B).card):= by


lemma finset_subtract_intersection (A B: Finset V): (A∩ B).card=A.card-(A\ B).card:= by
have h1:A=(A\ B)∪ (A∩ B):= by exact set_equals_union_of_difference_intersetion
have h2: A.card=(A\ B).card+(A∩ B).card:= by exact (card_sdiff_add_card_inter A B).symm
exact Nat.eq_sub_of_add_eq' (id h2.symm)

lemma interedges_subsets_leq (H K: Subgraph G)(A B A' B': Finset V)(hHK: H≤ K)(hA: A'⊆ A)(hB: B'⊆ B):
(Rel.interedges H.Adj A' B'⊆  Rel.interedges K.Adj A B):= by
#check Finset.biUnion
calc
Rel.interedges H.Adj A' B'⊆  Rel.interedges H.Adj A B:= by exact Rel.interedges_mono hA hB
_⊆Rel.interedges K.Adj A B:= by exact interedges_subgraph_leq G H K hHK

lemma interedges_subsets_leq_card (H K: Subgraph G)(A B A' B': Finset V)(hHK: H≤ K)(hA: A'⊆ A)(hB: B'⊆ B):
((Rel.interedges H.Adj A' B').card≤   (Rel.interedges K.Adj A B).card):= by
have h1:(Rel.interedges H.Adj A' B'⊆  Rel.interedges K.Adj A B):=by exact  interedges_subsets_leq G H K A B A' B' hHK hA hB
exact card_le_of_subset h1


lemma partition_subset_partition (A B C D: Finset V) (hD: D=A∪ B) (hCD:C⊆ D): (C= (A∩ C)∪ (B∩ C)):= by
have h1:(A∩ C)∪ (B∩ C)⊆ C:= by
  have h2: (A∩ C)⊆ C:= by exact inter_subset_right A C
  have h3: (B∩ C)⊆ C:= by exact inter_subset_right B C
  exact union_subset h2 h3
have h2:C⊆ (A ∪ B)∩ C:= by
  rw[hD.symm]
  exact subset_inter hCD fun ⦃a⦄ a ↦ a
have h3: (A ∪ B)∩ C=(A∩ C)∪ (B∩ C):= by exact union_inter_distrib_right A B C
rw[h3] at h2
exact Subset.antisymm h2 h1


lemma subgraphs_vertex_sets_subsets{H K : Subgraph G}{hHK: H≤ K}: H.verts⊆ K.verts:= by
have h2: H.verts ⊆ K.verts ∧ ∀ ⦃v w : V⦄, H.Adj v w → K.Adj v w:= by exact hHK
exact h2.1

lemma subgraphs_vertex_subsets (H K : Subgraph G)(hHK: H≤ K): H.verts.toFinset⊆ K.verts.toFinset:= by
have h1:  H.verts⊆ K.verts:= by apply subgraphs_vertex_sets_subsets; exact hHK
exact Set.toFinset_subset_toFinset.mpr h1






theorem cut_dense_add_vertices_after_wlog_case1 (H: Subgraph G)(K: Subgraph G)
(HV KV A B: Finset V)(hHV: HV=H.verts.toFinset)(hKV: KV=K.verts.toFinset)
(hNonempty: Nonempty (H).verts )(k d:ℕ )
(hUnion:  KV= A∪ B)
(hWlog: 2*(A∩ HV).card≥ HV.card)
(hCase1: 2*d*KV.card*(B∩ HV).card≥ B.card*HV.card)
(HCutDense: cut_dense G H k)(KContainsH: H≤ K)
(hDegree: ∀ v ∈ K.verts \ H.verts, d * ((K.neighborSet v).toFinset ∩ HV).card ≥ H.verts.toFinset.card)
:4*k*d *(KV.card^2) *(Rel.interedges K.Adj A B).card ≥ A.card*B.card* HV.card^2:=by

calc
4*k*d *(KV.card^2) *(Rel.interedges K.Adj A B).card
≥4*k*d *(KV.card^2) *(Rel.interedges H.Adj (A∩HV) (B∩HV)).card:= by
  have h1:  (A∩HV)⊆ A:= by exact inter_subset_left A HV
  have h2: (B∩HV)⊆B:= by exact inter_subset_left B HV
  have h3: (Rel.interedges H.Adj (A∩HV) (B∩HV)).card≤ (Rel.interedges K.Adj (A) (B)).card:= by exact    interedges_subsets_leq_card G H K A B (A ∩ HV) (B ∩ HV) KContainsH h1 h2
  gcongr
_=4*d *(KV.card^2) *(k*(Rel.interedges H.Adj (A∩HV) (B∩HV)).card):= by
  ring_nf
_≥ 4*d *(KV.card^2) * ((A∩HV).card * (B∩HV).card):= by
  have h2: (A∩HV)∪ (B∩HV)= HV:= by
    symm;
    apply partition_subset_partition A B HV KV;
    exact hUnion;
    rw[hHV, hKV];
    exact subgraphs_vertex_subsets G H K KContainsH
  have h1: (k*(Rel.interedges H.Adj (A∩HV) (B∩HV)).card)≥ (A∩HV).card * (B∩HV).card:= by apply HCutDense (A∩HV) (B∩ HV); rw[hHV.symm]; exact h2.symm
  gcongr
_=2*d *(KV.card^2) * (B∩HV).card * (2*(A∩HV).card):= by
  ring_nf
_≥ 2*d*(KV.card^2) * (B∩HV).card*HV.card:= by
  gcongr
_=2*d*KV.card * (B∩HV).card*KV.card*HV.card:= by
  ring_nf
_≥ B.card *HV.card*KV.card * HV.card:= by
  gcongr
_≥ B.card *HV.card*A.card * HV.card:= by
  gcongr
  rw[hUnion]
  exact subset_union_left A B
_=A.card*B.card* HV.card^2:= by
  ring_nf





theorem cut_dense_add_vertices_after_wlog_case2 (H: Subgraph G)(K: Subgraph G)
(HV KV A B: Finset V)(hHV: HV=H.verts.toFinset)(hKV: KV=K.verts.toFinset)
(hNonempty: Nonempty (H).verts )(k d:ℕ )
(hUnion:  KV= A∪ B)
(hWlog: 2*(B∩ HV).card≥ HV.card)
(hkPositive: k≥ 1)
(hdPositive: d≥ 1 )
(hHNonempty: HV.card>0)
(hCase1: 2*d*KV.card*(A∩ HV).card< A.card*HV.card)
(HCutDense: cut_dense G H k)(KContainsH: H≤ K)
(hDegree: ∀(v: V), (v∈ K.verts\ H.verts)→ (d*((K.neighborSet v).toFinset∩ HV).card ≥ H.verts.toFinset.card))--(hDegree: ∀(v: V), (v∈ K.verts\ H.verts)→ (d*K.degree v ≥ H.verts.toFinset.card))
:4*k*d *(KV.card^2) *(Rel.interedges K.Adj A B).card ≥ A.card*B.card* HV.card^2:=by

have hALowerBound: 2*(A\HV).card ≥  A.card  := by
  calc
  2*(A\HV).card=2*(A.card-(A∩ HV).card):= by
    congr
    have h2: A.card=(A\HV).card+(A∩ HV).card:= by exact (card_sdiff_add_card_inter A HV).symm
    exact Nat.eq_sub_of_add_eq (id h2.symm)
  _= 2*A.card-2*(A∩ HV).card:= by exact Nat.mul_sub_left_distrib 2 A.card (A ∩ HV).card
  _≥   2*A.card-A.card:= by
    have h1: KV.card≥ HV.card:= by gcongr; rw[hHV, hKV]; exact      subgraphs_vertex_subsets G H K KContainsH
    have h2: 2*(A∩ HV).card*HV.card< A.card*HV.card:= by calc
      2*(A∩ HV).card*HV.card= 2*1*(A∩ HV).card*HV.card:= by simp
      _≤ 2*d*(A∩ HV).card*HV.card:= by gcongr
      _=2*d*HV.card*(A∩ HV).card:= by ring_nf
      _≤ 2*d*KV.card*(A∩ HV).card:= by gcongr
      _< A.card*HV.card:= by exact hCase1
    have h3:  2*(A∩ HV).card<  A.card:= by exact (Nat.mul_lt_mul_right hHNonempty).mp h2
    have h3:  2*(A∩ HV).card≤   A.card:= by exact Nat.le_of_succ_le h3
    have h6:  2*(A∩ HV).card≤ 2*A.card := by gcongr; exact inter_subset_left A HV
    exact Nat.sub_le_sub_left h3 (2 * A.card)
  _= 2*A.card-1*A.card:= by simp
  _=(2-1)*A.card:= by exact (Nat.mul_sub_right_distrib 2 1 A.card).symm
  _= A.card:= by simp


have hCase1Weak2: 2 * d *  (A ∩ HV).card ≤  HV.card := by
  have h1: KV.card≥ A.card:= by rw[hUnion]; gcongr; exact subset_union_left A B
  by_contra hc
  have h3: HV.card≥ 0:= by exact Nat.zero_le HV.card
  have hc: 2 * d * (A ∩ HV).card > HV.card:= by exact not_le.mp hc
  have hc: 2 * d * (A ∩ HV).card ≥  HV.card:= by  gcongr
  have h2: 2 * d * (A ∩ HV).card *KV.card ≥  HV.card*A.card:= by
    exact Nat.mul_le_mul hc h1
  --ring_nf at h2
  have h3:d * KV.card * (A ∩ HV).card * 2 ≥  A.card * HV.card:= by calc
    d * KV.card * (A ∩ HV).card * 2 = 2 * d * (A ∩ HV).card * KV.card:= by ring_nf
    _≥  HV.card * A.card:= by exact h2
    _= A.card * HV.card:= by ring_nf
  ring_nf at hCase1
  have h4: ¬(d * KV.card * (A ∩ HV).card * 2 < A.card * HV.card):= by exact Nat.not_lt.mpr h3
  exact h4 hCase1

have hUnionH: HV⊆ A∪ B:= by calc
  HV⊆ KV:= by rw[hHV, hKV]; exact subgraphs_vertex_subsets G H K KContainsH
  _=A∪ B:= by exact hUnion

have hAUpperBound: 2*(d*(HV\ B).card) ≤HV.card:= by calc
  2*(d*(HV\ B).card)≤  2*(d*(HV∩  A).card):= by
    gcongr
    have h4:A∪ B=B∪ A:= by exact union_comm A B
    rw[h4] at hUnionH
    exact minus_intersection_partition   hUnionH
  _=2*(d*(A∩  HV).card):= by
    have h1: HV∩  A= A∩ HV:= by exact inter_comm HV A
    exact congrArg (HMul.hMul 2) (congrArg (HMul.hMul d) (congrArg card h1))
  _=2 * d *  (A ∩ HV).card:= by ring_nf
  _≤HV.card:= by exact hCase1Weak2

calc
4*k*d *(KV.card^2) *(Rel.interedges K.Adj A B).card≥4*k*d *(KV.card^2) *(Rel.interedges K.Adj (A\ HV) (B∩HV)).card:= by
  gcongr
  have h1: K≤ K:= by exact Preorder.le_refl K
  have h2: (A\ HV)⊆ A:= by exact sdiff_subset A HV
  have h3: (B∩HV)⊆ B:= by exact inter_subset_left B HV
  exact interedges_subsets_leq G K K A B (A \ HV) (B ∩ HV) h1 h2 h3
_=4*k*d *(KV.card^2) *(∑ (v ∈  A\HV), ((K.neighborSet v).toFinset ∩ (B∩HV)).card):= by congr; exact  interedges_card_sum G
_=4*k*d *(KV.card^2) *(∑ (v ∈  A\HV), ((K.neighborSet v).toFinset ∩ HV∩ B).card):= by
  congr; ext v;
  have h1: B ∩ HV=HV∩ B:= by exact inter_comm B HV
  rw[h1]
  have h2: (K.neighborSet v).toFinset ∩ (HV ∩ B)=(K.neighborSet v).toFinset ∩ HV ∩ B:= by exact    (inter_assoc (K.neighborSet v).toFinset HV B).symm
  rw [h2]
_=4*k*d *(KV.card^2) *(∑ (v ∈  A\HV), (((K.neighborSet v).toFinset∩ HV).card-  (((K.neighborSet v).toFinset∩ HV)\ B).card)):= by
  congr
  ext v
  exact finset_subtract_intersection ((K.neighborSet v).toFinset ∩ HV) B

_≥ 4*k*d *(KV.card^2) *(∑ (v ∈  A\HV), (((K.neighborSet v).toFinset∩ HV).card- (HV\ B).card)):= by
  gcongr with i hi;
  have h1: ((K.neighborSet i).toFinset ∩ HV)⊆ HV := by exact    inter_subset_right (K.neighborSet i).toFinset HV
  exact sdiff_subset_sdiff h1 fun ⦃a⦄ a ↦ a


_=4*k*(KV.card^2) *(d*(∑ (v ∈  A\HV), (((K.neighborSet v).toFinset∩ HV).card-  (HV\ B).card))):= by
  ring_nf
_=4*k*(KV.card^2) *((∑ (v ∈  A\HV), d*((((K.neighborSet v).toFinset∩ HV).card- (HV\ B).card)))):= by
  congr
  exact
    mul_sum (A \ HV)
      (fun i ↦ ((K.neighborSet i).toFinset ∩ HV).card - (HV\ B).card) d
_=4*k*(KV.card^2) *(∑ (v ∈  A\HV), (d*((K.neighborSet v).toFinset∩ HV).card-  d*((HV\ B).card))):= by
  congr; ext V;
  exact    Nat.mul_sub_left_distrib d ((K.neighborSet V).toFinset ∩ HV).card      (HV\ B).card
_≥ 4*k*(KV.card^2) *(∑ (v ∈  A\HV), (HV.card-  d*(HV\ B).card)):= by
 gcongr with i hI
 rw[hHV.symm] at hDegree
 apply hDegree
 have hx: A\ HV⊆A:= by exact sdiff_subset A HV
 have h0: i∈ A:= by exact hx hI
 have h1: i∈ KV:=by rw[hUnion]; exact mem_union_left B h0
 have h2: i∈ K.verts:= by rw[hKV] at h1; exact Set.mem_toFinset.mp h1
 have h3: i∉ HV:= by
  by_contra hc
  have h3':i ∉ A\ HV:= by exact not_mem_sdiff_of_mem_right hc
  exact h3' hI
 have h3: i∉ H.verts:= by
  rw [hHV] at h3;
  by_contra hc
  have h3':i ∈ H.verts.toFinset:= by exact Set.mem_toFinset.mpr hc
  exact h3 h3'
 exact Set.mem_diff_of_mem h2 h3
_= 4*k*(KV.card^2) *((A\HV).card*(HV.card-  d*(HV\ B).card)):= by
  congr
  exact sum_const_nat fun x ↦ congrFun rfl
_= 2*k*(KV.card^2) *((A\HV).card*(2*(HV.card-  d*(HV\ B).card))):= by
  ring_nf
_= 2*k*(KV.card^2) *((A\HV).card*(2*HV.card-  2*(d*(HV\ B).card))):= by
  congr
  exact Nat.mul_sub_left_distrib 2 HV.card (d * (HV \ B).card)
_≥  2*k*(KV.card^2) *((A\HV).card*(2*HV.card- HV.card)):= by
  gcongr
_= k*(KV.card^2) *(2*((A\HV).card))*(2*HV.card- HV.card):= by
  ring_nf
_≥  k*(KV.card^2) *(A.card)*(2*HV.card- HV.card):= by
  gcongr
_=k*(KV.card^2)*A.card*(2*HV.card - 1*HV.card):= by ring_nf
_= k*(KV.card^2)*A.card*HV.card:= by
  have h1: (2*HV.card - 1*HV.card)=HV.card:= by calc
    (2*HV.card - 1*HV.card)=(2-1)*HV.card:= by exact    (Nat.mul_sub_right_distrib 2 1 HV.card).symm
    _= HV.card:= by simp
  congr
_= k*(KV.card)*KV.card*A.card*HV.card:= by ring_nf
_≥ k*KV.card*B.card*A.card*HV.card:= by gcongr; rw[hUnion]; exact subset_union_right A B
_≥ 1*KV.card*B.card*A.card*HV.card:= by gcongr
_≥1*HV.card*B.card*A.card*HV.card:= by gcongr; rw[hHV, hKV]; exact  subgraphs_vertex_subsets G H K KContainsH
_=  A.card *  B.card*HV.card^2:= by ring_nf



theorem cut_dense_add_vertices_after_wlog (H: Subgraph G)(K: Subgraph G)
(HV KV A B: Finset V)(hHV: HV=H.verts.toFinset)(hKV: KV=K.verts.toFinset)
(hNonempty: Nonempty (H).verts )(k d:ℕ )
(hUnion: KV= A∪ B)
(hWlog: 2*(A∩ HV).card≥ HV.card)
(hkPositive: k≥ 1) (hdPositive: d≥ 1) (hHNonempty: HV.card>0)
(HCutDense: cut_dense G H k)(KContainsH: H≤ K)
(hDegree: ∀ v ∈ K.verts \ H.verts, d * ((K.neighborSet v).toFinset ∩ HV).card ≥ H.verts.toFinset.card)
:4*k*d *(KV.card^2) *(Rel.interedges K.Adj A B).card ≥ A.card*B.card* HV.card^2:=by
by_cases hCase1: 2*d*KV.card*(B∩ HV).card≥ B.card*HV.card
exact cut_dense_add_vertices_after_wlog_case1 G H K HV KV A B hHV hKV hNonempty k d hUnion hWlog hCase1 HCutDense KContainsH hDegree
have hCase1: 2 * d * KV.card * (B ∩ HV).card < B.card * HV.card:= by exact not_le.mp hCase1
have h1: A∪ B= B∪ A:= by exact union_comm A B
rw[h1] at hUnion
have h3: A.card*B.card=B.card*A.card:= by exact Nat.mul_comm A.card B.card
rw[h3]
have h4: (Rel.interedges K.Adj A B).card= (Rel.interedges K.Adj B A).card:= by exact  Rel.card_interedges_comm (fun ⦃x y⦄ a ↦ id (Subgraph.adj_symm K a)) A B
rw[h4]
exact cut_dense_add_vertices_after_wlog_case2 G H K HV KV B A hHV hKV hNonempty k d hUnion hWlog hkPositive hdPositive hHNonempty hCase1 HCutDense KContainsH hDegree


theorem cut_dense_add_vertices (H: Subgraph G)(K: Subgraph G)(hNonempty: Nonempty (H).verts )(k d q:ℕ )
(HCutDense: cut_dense G H k)(KContainsH: H≤ K)
(hkPositive: k≥ 1) (hdPositive: d≥ 1) (hHNonempty: H.verts.toFinset.Nonempty)
(hDegree: ∀ v ∈ K.verts \ H.verts, d * ((K.neighborSet v).toFinset ∩  H.verts.toFinset).card ≥ H.verts.toFinset.card)
(hq: q=4*k*d*(K.verts.toFinset.card)^2/(H.verts.toFinset.card)^2+1)
:cut_dense G K q:=by
intro A B hUnion
let HV:= H.verts.toFinset
let KV:= K.verts.toFinset
have hHV: HV=H.verts.toFinset:= by rfl
have hKV: KV=K.verts.toFinset:= by rfl
have hNonempty1: HV.card >0:= by
  rw[hHV]
  exact card_pos.mpr hHNonempty
nth_rw 1 [hHV.symm] at hDegree
rw [hHV.symm, hKV.symm] at hq
have hNonempty2: (HV.card)^2 >0:= by exact Nat.pos_pow_of_pos 2 hNonempty1

by_cases hWlog: 2*(A∩ HV).card≥ HV.card

have hInterEdges:  4 * k * d * (KV.card ^ 2) * (Rel.interedges K.Adj A B).card ≥ A.card * B.card * HV.card ^ 2:= by
  exact cut_dense_add_vertices_after_wlog G H K HV KV A B hHV hKV hNonempty k d hUnion hWlog hkPositive hdPositive hNonempty1 HCutDense KContainsH hDegree
have hInterEdges:  (4 * k * d * (KV.card ^ 2)) * ((Rel.interedges K.Adj A B).card) ≥ (A.card * B.card) * (HV.card ^ 2):= by
  gcongr
rw [hq]
exact nat_div_ge  (4 * k * d * (KV.card ^ 2)) (HV.card ^ 2) ((Rel.interedges K.Adj A B).card) (A.card * B.card) hInterEdges hNonempty2



have hvCont: HV⊆ A∪ B := by calc
  HV⊆ KV:= by rw[hHV, hKV]; exact subgraphs_vertex_subsets G H K KContainsH
  _=A∪ B:= by exact hUnion
have hWlog2: (2 * (A ∩ HV).card ≥ HV.card) ∨ (2 * (B ∩ HV).card ≥ HV.card):= by
   exact incl_excl_corollary2 HV A B hvCont
have hWlog3: (2 * (B ∩ HV).card ≥ HV.card):= by
  exact Or.resolve_left hWlog2 hWlog

have hInterEdges:  4 * k * d * (KV.card ^ 2) * (Rel.interedges K.Adj A B).card ≥ A.card * B.card * HV.card ^ 2:= by
  have h1: A∪ B= B∪ A:= by exact union_comm A B
  rw[h1] at hUnion
  have h3: A.card*B.card=B.card*A.card:= by exact Nat.mul_comm A.card B.card
  rw[h3]
  have h4: (Rel.interedges K.Adj A B).card= (Rel.interedges K.Adj B A).card:= by exact  Rel.card_interedges_comm (fun ⦃x y⦄ a ↦ id (Subgraph.adj_symm K a)) A B
  rw[h4]
  exact cut_dense_add_vertices_after_wlog G H K HV KV B A hHV hKV hNonempty k d hUnion hWlog3 hkPositive hdPositive hNonempty1 HCutDense KContainsH hDegree
have hInterEdges:  (4 * k * d * (KV.card ^ 2)) * ((Rel.interedges K.Adj A B).card) ≥ (A.card * B.card) * (HV.card ^ 2):= by
  gcongr
rw [hq]
exact nat_div_ge  (4 * k * d * (KV.card ^ 2)) (HV.card ^ 2) ((Rel.interedges K.Adj A B).card) (A.card * B.card) hInterEdges hNonempty2
