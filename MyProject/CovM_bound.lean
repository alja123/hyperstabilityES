import MyProject

import MyProject.clump_order
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




lemma Bipartite_induce_edge_set
(H: Subgraph G)
(B M: Set V)
:
(bipartite_induce H (H.verts∩ B) (H.verts∩M)).edgeSet= (bipartite_induce H (B) (M)).edgeSet
:=by
ext ⟨a,b ⟩
constructor
intro hassump
dsimp [bipartite_induce]
dsimp [bipartite_induce] at hassump
simp
simp at hassump
constructor
have hassump1: ((a ∈ H.verts ∧ a ∈ B) ∧ b ∈ H.verts ∧ b ∈ M ∨ (b ∈ H.verts ∧ b ∈ B) ∧ a ∈ H.verts ∧ a ∈ M):=by
  exact hassump.1
rename_i
  inst
  inst_1
  inst_2
  x
simp_all only [gt_iff_lt,
  true_and]
unhygienic
  aesop_cases
    hassump1
·
  simp_all only [and_self,
    true_or]
·
  simp_all only [and_self,
    or_true]
exact hassump.2

simp
intro hassump hassump2
have ha: a∈ H.verts:=by
  exact H.edge_vert hassump2
have hb: b∈ H.verts:=by
  exact H.edge_vert (id (Subgraph.adj_symm H hassump2))
rename_i
  inst
  inst_1
  inst_2
  x
simp_all only [gt_iff_lt,
  true_and,
  and_self]


def CovM (K :Clump G p m κ pr h): Subgraph G:=
bipartite_induce K.Gr (BSetPlusM K) ((sSup K.M: Subgraph G).verts)




lemma clump_most_edges_of_Hi_in_Bgraph_simplified2
(K: Clump G p m κ pr h)
(Hi HB: Subgraph G)
(hHB: HB= bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts))
(hHi: Hi∈ K.H)
: 4*p^2*(Hi).edgeSet.toFinset.card≤  (Hi.verts.toFinset.card)^2+(HB).edgeSet.toFinset.card*p^2*4
:=by
have h1:_:=by exact Bipartite_induce_edge_set Hi (BSetPlusM K) ((sSup K.M: Subgraph G).verts)
rw[hHB, h1.symm]
apply clump_most_edges_of_Hi_in_Bgraph_simplified K
simp
repeat assumption

lemma CovM_equals_union_HB
(K: Clump G p m κ pr h)
(Cv: Subgraph G)
(hCv: Cv= CovM   p m κ pr h K)
:
Cv.edgeSet= (sSup {HB: Subgraph G | ∃ (Hi: Subgraph G), Hi∈ K.H ∧ HB= bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)}).edgeSet
:=by
have h2: sSup K.H=K.Gr:=by
  exact K.H_Partition_K
ext ⟨a,b ⟩
simp
constructor
intro  hassump
rw[hCv] at hassump
unfold CovM at hassump
simp at hassump
constructor
aesop

have h1: K.Gr.Adj a b:=by exact hassump.2
rw[h2.symm] at h1
simp at h1
exact h1

intro ⟨ hassump, hassump2⟩
rw[hCv]
unfold CovM
simp
constructor
aesop

rw[h2.symm]
simp
exact hassump2


lemma bipartite_induce_edge_set_subset
(H: Subgraph G)
(A B: Set V)
:
(bipartite_induce H A B).edgeSet⊆ H.edgeSet
:=by
dsimp [bipartite_induce]
intro a ha
have h1: ∃ (x y: V), a=s(x,y):=by
  exact Sym2_to_tuple a
rcases h1 with ⟨x, y, h1⟩
rw[h1] at ha
rw[h1]
simp
simp at ha
exact ha.2
---------------------------------K.Gr--
lemma Gr_edgessum_equals_union_HB
(K: Clump G p m κ pr h)
(Cv: Subgraph G)
(hCv: Cv= CovM   p m κ pr h K)
:
(Finset.biUnion K.H (fun Hi=>(Hi).edgeSet.toFinset )).card
=   ∑ (Hi∈ K.H), (Hi).edgeSet.toFinset.card
:= by
apply Finset.card_biUnion
intro Hi hHi Hj hHj hdist

have h3: Disjoint (Hi.edgeSet) (Hj.edgeSet):=by
  --unfold  Disjoint
  have h4: HEdge_Disjoint K.H:=by exact K.H_Edge_Disjoint
  unfold HEdge_Disjoint at h4
  have h5: Hi.edgeSet∩ Hj.edgeSet=∅:=by
    apply h4 Hi Hj hHi hHj hdist
  refine Set.disjoint_iff.mpr ?_
  exact Set.subset_empty_iff.mpr (h4 Hi Hj hHi hHj hdist)

simp
exact h3





lemma bigunion_comparision_one_direction_clump_Gr
(K: Clump G p m κ pr h)
(a: Sym2 V)
:
a ∈ (⋃(Hi∈ K.H), (Hi).edgeSet).toFinset → a ∈ (Finset.biUnion K.H (fun Hi=>(Hi).edgeSet.toFinset ))
:= by

intro h
refine mem_biUnion.mpr ?_

have h0: a ∈ (⋃ H ∈ K.H, (H).edgeSet):= by
  exact Set.mem_toFinset.mp h
have h1: ∃ H ∈ K.H, a ∈ (H).edgeSet:=by

  have h3:_:= by apply Set.mem_iUnion.1 h0
  rcases h3 with ⟨ x, y⟩
  have h4:_:= by apply Set.mem_iUnion.1 y
  rcases h4 with ⟨ z, h6⟩
  use x

rcases h1 with ⟨ a1, ha1⟩
have h12: a ∈  (a1).edgeSet:= by
  exact ha1.2
have h2:a ∈  (a1).edgeSet.toFinset:= by
  exact Set.mem_toFinset.mpr h12

use a1
exact ⟨ha1.1, h2⟩

lemma bigunion_comparision_clump_Gr
(K: Clump G p m κ pr h)
:
(⋃(Hi∈ K.H), (Hi).edgeSet).toFinset
=
(Finset.biUnion K.H (fun Hi=>(Hi).edgeSet.toFinset ))
:= by

ext a

constructor
exact fun a_1 ↦ bigunion_comparision_one_direction_clump_Gr p m κ pr h K a a_1


intro b
refine Set.mem_toFinset.mpr ?_
refine Set.mem_iUnion₂.mpr ?_

have h1: ∃ H ∈ K.H, a ∈ (H).edgeSet.toFinset:=by
  exact mem_biUnion.mp b

rcases h1 with ⟨ a1, ha1⟩
have h11:_:= by
  exact ha1.1
have h12:_:= by
  exact ha1.2
use a1
simp
have h12': a ∈ a1.edgeSet := by exact Set.mem_toFinset.mp h12
constructor
exact h11
simp at h12
exact h12


lemma CovM_edgessum_equals_union_firsteq_Gr
(K: Clump G p m κ pr h)
:
K.Gr.edgeSet
= (⋃ (Hi∈ K.H), (Hi).edgeSet):=by
  --congr
  rw[K.H_Partition_K.symm]
  ext ⟨a, b ⟩
  constructor
  intro hassump
  simp
  simp at hassump
  exact hassump
  simp


lemma CovM_edgessum_equals_union_firsteq_Gr_finset
(K: Clump G p m κ pr h)
:
K.Gr.edgeSet.toFinset
= (⋃ (Hi∈ K.H), (Hi).edgeSet).toFinset:=by
  rw[K.H_Partition_K.symm]
  simp



lemma CovM_edgessum_equals_union_HB_final_Gr
(K: Clump G p m κ pr h)
(hCv: Cv= CovM   p m κ pr h K)
:
K.Gr.edgeSet.toFinset.card=  ∑ (Hi∈ K.H), (Hi).edgeSet.toFinset.card
:= by

calc
K.Gr.edgeSet.toFinset.card
= (⋃ (Hi∈ K.H), (Hi).edgeSet).toFinset.card:=by
  rw[K.H_Partition_K.symm]
  simp
_=(Finset.biUnion K.H (fun Hi=>(Hi).edgeSet.toFinset )).card:=by
  congr
  exact bigunion_comparision_clump_Gr p m κ pr h K
_=  ∑ Hi ∈ K.H, (Hi).edgeSet.toFinset.card:=by
  exact Gr_edgessum_equals_union_HB p m κ pr h K Cv hCv





-------------------------------------

lemma CovM_edgessum_equals_union_HB
(K: Clump G p m κ pr h)
(Cv: Subgraph G)
(hCv: Cv= CovM   p m κ pr h K)
:
(Finset.biUnion K.H (fun Hi=>(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset )).card
=   ∑ (Hi∈ K.H), (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset.card
:= by
apply Finset.card_biUnion
intro Hi hHi Hj hHj hdist


--have h1: (bipartite_induce Hi (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts)≤  Hi:=by



have h11:  (bipartite_induce Hi (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts).edgeSet⊆   Hi.edgeSet:=by
  exact bipartite_induce_edge_set_subset Hi (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts

have h22:  (bipartite_induce Hj (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts).edgeSet⊆   Hj.edgeSet:=by
  exact bipartite_induce_edge_set_subset Hj (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts


have h3: Disjoint (Hi.edgeSet) (Hj.edgeSet):=by
  --unfold  Disjoint
  have h4: HEdge_Disjoint K.H:=by exact K.H_Edge_Disjoint
  unfold HEdge_Disjoint at h4
  have h5: Hi.edgeSet∩ Hj.edgeSet=∅:=by
    apply h4 Hi Hj hHi hHj hdist
  refine Set.disjoint_iff.mpr ?_
  exact Set.subset_empty_iff.mpr (h4 Hi Hj hHi hHj hdist)

simp
simp at h11
simp at h22
exact Set.disjoint_of_subset h11 h22 h3





lemma bigunion_comparision_one_direction_clump
(K: Clump G p m κ pr h)
(a: Sym2 V)
:
a ∈ (⋃(Hi∈ K.H), (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet).toFinset → a ∈ (Finset.biUnion K.H (fun Hi=>(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset ))
:= by

intro h
refine mem_biUnion.mpr ?_

have h0: a ∈ (⋃ H ∈ K.H, (bipartite_induce H (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts).edgeSet):= by
  exact Set.mem_toFinset.mp h
have h1: ∃ H ∈ K.H, a ∈ (bipartite_induce H (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts).edgeSet:=by

  have h3:_:= by apply Set.mem_iUnion.1 h0
  rcases h3 with ⟨ x, y⟩
  have h4:_:= by apply Set.mem_iUnion.1 y
  rcases h4 with ⟨ z, h6⟩
  use x



rcases h1 with ⟨ a1, ha1⟩
have h12: a ∈  (bipartite_induce a1 (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts).edgeSet:= by
  exact ha1.2
have h2:a ∈  (bipartite_induce a1 (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts).edgeSet.toFinset:= by
  exact Set.mem_toFinset.mpr h12

use a1
exact ⟨ha1.1, h2⟩

lemma bigunion_comparision_clump
(K: Clump G p m κ pr h)
:
(⋃(Hi∈ K.H), (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet).toFinset
=
(Finset.biUnion K.H (fun Hi=>(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset ))
:= by

ext a

constructor
exact fun a_1 ↦ bigunion_comparision_one_direction_clump p m κ pr h K a a_1


intro b
refine Set.mem_toFinset.mpr ?_
refine Set.mem_iUnion₂.mpr ?_

have h1: ∃ H ∈ K.H, a ∈ (bipartite_induce H (BSetPlusM K) (sSup ↑K.M: Subgraph G ).verts).edgeSet.toFinset:=by
  exact mem_biUnion.mp b

rcases h1 with ⟨ a1, ha1⟩
have h11:_:= by
  exact ha1.1
have h12:_:= by
  exact ha1.2
use a1
simp
constructor
exact h11
simp at h12
exact h12


lemma CovM_edgessum_equals_union_firsteq
(K: Clump G p m κ pr h)
:
(sSup {HB | ∃ Hi ∈ K.H, HB = bipartite_induce Hi (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts}).edgeSet.toFinset.card
= (⋃ (Hi∈ K.H), (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet).toFinset.card:=by
  simp





lemma CovM_edgessum_equals_union_HB_final
(K: Clump G p m κ pr h)
(Cv: Subgraph G)
(hCv: Cv= CovM   p m κ pr h K)
:
Cv.edgeSet.toFinset.card=  ∑ (Hi∈ K.H), (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset.card
:= by
have h1: Cv.edgeSet= (sSup {HB: Subgraph G | ∃ (Hi: Subgraph G), Hi∈ K.H ∧ HB= bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)}).edgeSet
:=by exact CovM_equals_union_HB p m κ pr h K Cv hCv
rw[h1]
calc
(sSup {HB | ∃ Hi ∈ K.H, HB = bipartite_induce Hi (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts}).edgeSet.toFinset.card
--=(sUnion {HB | ∃ Hi ∈ K.H, HB = bipartite_induce Hi (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts}).edgeSet.toFinset.card:=by
--  exact sSup_to_sUnion
= (⋃ (Hi∈ K.H), (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet).toFinset.card:=by
  simp
_=(Finset.biUnion K.H (fun Hi=>(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset )).card:=by
  congr
  exact bigunion_comparision_clump p m κ pr h K
_=  ∑ Hi ∈ K.H, (bipartite_induce Hi (BSetPlusM K) (sSup ↑K.M: Subgraph G).verts).edgeSet.toFinset.card:=by
  exact CovM_edgessum_equals_union_HB p m κ pr h K Cv hCv





lemma clump_most_edges_of_Hi_in_Bgraph_different_numbers
(K: Clump G p m κ pr h)
(Hi: Subgraph G)
(hHi: Hi∈ K.H)
:  p^2*4*(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset.card
+p*2*(Hi).edgeSet.toFinset.card
≥  p^2*4*(Hi).edgeSet.toFinset.card
:= by
let HB:=(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts))
have hHB: HB= (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)):= by
  exact rfl
rw[hHB.symm]
calc
p^2*4*(HB).edgeSet.toFinset.card+p*2*(Hi).edgeSet.toFinset.card
=p*2*(Hi).edgeSet.toFinset.card+(HB).edgeSet.toFinset.card*p^2*4:=by
    ring_nf
_≥   (Hi).verts.toFinset.card^2+(HB).edgeSet.toFinset.card*p^2*4
:= by
  gcongr
  apply cut_dense_edges_lower_bound
  apply K.H_Cut_Dense
  exact hHi

_≥4*p^2*(Hi).edgeSet.toFinset.card:=by
  apply clump_most_edges_of_Hi_in_Bgraph_simplified2 p m κ pr h K Hi HB
  repeat assumption
_=p^2*4*(Hi).edgeSet.toFinset.card:=by
  ring_nf


lemma edges_in_CovM
(K: Clump G p m κ pr h)
(Cv: Subgraph G)
(hCv: Cv= CovM   p m κ pr h K)
:
p^2*4*Cv.edgeSet.toFinset.card
+ p*2*K.Gr.edgeSet.toFinset.card
≥ p^2*4*K.Gr.edgeSet.toFinset.card
:=by
calc
p^2*4*Cv.edgeSet.toFinset.card + p*2*K.Gr.edgeSet.toFinset.card
=
p^2*4*(∑ (Hi∈ K.H), (bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset.card)
+
p*2*(∑ (Hi∈ K.H), (Hi).edgeSet.toFinset.card)
:=by
  congr
  exact CovM_edgessum_equals_union_HB_final p m κ pr h K Cv hCv
  exact CovM_edgessum_equals_union_HB_final_Gr p m κ pr h K hCv
_=
(∑ (Hi∈ K.H), p^2*4*(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset.card)
+
(∑ (Hi∈ K.H), p*2*(Hi).edgeSet.toFinset.card):=by
  congr
  apply mul_sum
  apply mul_sum
_=∑ (Hi∈ K.H), (p^2*4*(bipartite_induce Hi  (BSetPlusM K) ((sSup K.M: Subgraph G).verts)).edgeSet.toFinset.card+ p*2*(Hi).edgeSet.toFinset.card):=by
  exact sum_add_distrib.symm
_≥ (∑ (Hi∈ K.H), p^2*4*(Hi).edgeSet.toFinset.card):= by
  gcongr with Hi hHi
  apply clump_most_edges_of_Hi_in_Bgraph_different_numbers  p m κ pr h K Hi hHi
_=p^2*4*(∑ (Hi∈ K.H), (Hi).edgeSet.toFinset.card):= by
  exact (mul_sum K.H (fun i ↦ i.edgeSet.toFinset.card) (p ^ 2 * 4)).symm
_=p^2*4*K.Gr.edgeSet.toFinset.card:=by
  congr
  exact (CovM_edgessum_equals_union_HB_final_Gr p m κ pr h K hCv).symm







