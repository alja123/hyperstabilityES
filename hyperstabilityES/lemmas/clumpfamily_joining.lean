--import MyProject

import hyperstabilityES.lemmas.clump_decomposition
 --import hyperstabilityES.lemmas.SimpleGraph

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
variable {p m κ pr h: ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable (iSub:Inhabited (Subgraph G))
variable (pLarge: p≥ 20)
variable (prggp: pr ≥ gg2 p)
variable (hggp: h ≥ gg1 pr)
variable (κggh: κ ≥ gg1 h)
variable (mggκ :m≥ gg2 κ )



--def Clump_family_edge_disjoint
--(KFam: Finset (Clump G p m κ pr h))
--:=(∀(K1 K2: (Clump G p m κ pr h)), K1∈ KFam→ K2∈KFam→ K1≠ K2→ K1.Gr.edgeSet ∩ K2.Gr.edgeSet = ∅)


lemma clump_family_H_edge_disjoint
{K1 K2: Clump G p m κ pr h}
(KFam: Finset (Clump G p m κ pr h))
(hedge_disj: Clump_family_edge_disjoint KFam)
(hK1: K1∈ KFam)
(hK2: K2∈ KFam)
(hK1K2: K1≠ K2)
: HEdge_Disjoint (K1.H ∪ K2.H):=by
intro Hi Hj hHi hHj
by_cases h1:Hi∈ K1.H
by_cases h2:Hj∈ K1.H
apply K1.H_Edge_Disjoint
repeat assumption

have h2:Hj∈ K2.H:=by
  exact mem_of_union_elim_left K1.H K2.H Hj hHj h2
have k1: Hi≤ K1.Gr:=by
  apply K1.H_In_K Hi h1
have k2: Hj≤ K2.Gr:=by
  apply K2.H_In_K Hj h2
intro h'
have h4: K1.Gr.edgeSet ∩ K2.Gr.edgeSet = ∅:=by
  apply hedge_disj K1 K2 hK1 hK2 hK1K2
have h5: Hi.edgeSet ∩ Hj.edgeSet⊆ ∅:=by
  calc
    Hi.edgeSet ∩ Hj.edgeSet
    ⊆K1.Gr.edgeSet ∩ K2.Gr.edgeSet:=by
      gcongr
      exact subgraph_implies_edgesets_subsets k1
      exact subgraph_implies_edgesets_subsets k2
    _= ∅:=by exact h4
exact Set.subset_eq_empty h5 rfl

have ha: Hi.edgeSet ∩ Hj.edgeSet=Hj.edgeSet ∩ Hi.edgeSet:=by
  exact Set.inter_comm Hi.edgeSet Hj.edgeSet
have hb: (Hi ≠ Hj)↔ (Hj ≠ Hi):=by
  exact ne_comm
rw[hb]
rw[ha]
have h1:Hi∈ K2.H:=by
  exact mem_of_union_elim_left K1.H K2.H Hi hHi h1
by_cases h2:Hj∈  K2.H
apply K2.H_Edge_Disjoint
repeat assumption


have h2:Hj∈ K1.H:=by
  exact mem_of_union_elim_right K2.H K1.H Hj hHj h2
have k1: Hj≤ K1.Gr:=by
  apply K1.H_In_K Hj h2
have k2: Hi≤ K2.Gr:=by
  apply K2.H_In_K Hi h1
intro h'
have h4: K1.Gr.edgeSet ∩ K2.Gr.edgeSet = ∅:=by
  apply hedge_disj K1 K2 hK1 hK2 hK1K2
have h5: Hi.edgeSet ∩ Hj.edgeSet⊆ ∅:=by
  calc
    Hi.edgeSet ∩ Hj.edgeSet
    ⊆K2.Gr.edgeSet ∩ K1.Gr.edgeSet:=by
      gcongr
      exact subgraph_implies_edgesets_subsets k2
      exact subgraph_implies_edgesets_subsets k1
    _= ∅:=by exact hedge_disj K2 K1 hK2 hK1 (id (Ne.symm hK1K2))
rw[Set.inter_comm]
exact Set.subset_eq_empty h5 rfl


def Clumps_separated
(K1 K2: Clump G p m κ pr h)
:=κ^(10*Nat.factorial (100*(Nat.max K1.k K2.k)))*(BSetPlusM K1∩ BSetPlusM K2).toFinset.card< m


lemma clump_joining_max_unseparated
{K1 K2: Clump G p m κ pr h}
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
(hK1: K1∈ KFam)
(hK2: K2∈ KFam)
(hK1K2: K1≠ K2)
(hDecompose: Clump_Decomposition L KFam)
(hIntersection: ¬ Clumps_separated K1 K2)
(κggk: gg1 κ≥ (Nat.max K1.k K2.k))
:
∃ (K: Clump G p m κ pr h),
(K.Gr=K1.Gr⊔ K2.Gr)∧
(K.H=K1.H∪ K2.H)∧
(K.k≥ (Nat.max K1.k K2.k))∧
(K.k≤ K1.k+K2.k)
:=by
unfold Clumps_separated at hIntersection
simp only [  not_lt] at hIntersection
have h1: HEdge_Disjoint (K1.H ∪ K2.H):= by
  apply clump_family_H_edge_disjoint KFam
  unfold Clump_Decomposition at hDecompose
  exact hDecompose.1
  repeat assumption
apply clump_joining_max
repeat assumption



def Clump_family_separated
(KFam: Finset (Clump G p m κ pr h))
:=(∀(K1 K2: (Clump G p m κ pr h)),
K1∈ KFam→
K2∈KFam→
K1≠ K2→
Clumps_separated K1 K2)

def L_contains_wide_clump
--(KFam: Finset (Clump G p m κ pr h))
(p m κ pr h:ℕ )(G: SimpleGraph V)(L: Locally_Dense G p m h)
:=∃ (K: Clump G p m κ pr h),K.Gr≤ L.Gr∧
K.k≥ pr*pr*pr*pr*h
∧ K.k≤  4*pr*pr*pr*pr*h


def Clump_family_narrow
(KFam: Finset (Clump G p m κ pr h))
:=∀  (K: Clump G p m κ pr h),
K∈ KFam →  K.k≤ pr*pr*pr*pr*h


lemma Clump_family_replace_two_sets_stays_edgedisjoint
 (KFam KFam2: Finset (Clump G p m κ pr h))
(K1 K2 K: Clump G p m κ pr h)
(h_edge_disjoint:  Clump_family_edge_disjoint KFam)
(hK1: K1∈ KFam)
(hK2: K2∈ KFam)
(hKFam2: KFam2= KFam\ {K1, K2}∪ {K})
(hK: K.Gr=K1.Gr⊔ K2.Gr)
:  Clump_family_edge_disjoint KFam2
:=by
unfold Clump_family_edge_disjoint
rw[hKFam2]

intro k1 k2 hk1 hk2 hK1K2
simp at hk1
simp at hk2
rcases hk1 with case1|case1
rcases hk2 with case2|case2
apply h_edge_disjoint
exact case1.1
exact case2.1
exact hK1K2
rw[case2, hK]
simp
have h1: k1.Gr.edgeSet ∩ K1.Gr.edgeSet=∅:=by
  apply h_edge_disjoint
  exact case1.1
  exact hK1
  exact case1.2.1
have h2: k1.Gr.edgeSet ∩ K2.Gr.edgeSet=∅:=by
  apply h_edge_disjoint
  exact case1.1
  exact hK2
  exact case1.2.2
rw [@Set.inter_distrib_left]
rw[h1, h2]
simp

rcases hk2 with case2|case2
rw[case1, hK]
simp
have h1: k2.Gr.edgeSet ∩ K1.Gr.edgeSet=∅:=by
  apply h_edge_disjoint
  exact case2.1
  exact hK1
  exact case2.2.1
have h2: k2.Gr.edgeSet ∩ K2.Gr.edgeSet=∅:=by
  apply h_edge_disjoint
  exact case2.1
  exact hK2
  exact case2.2.2
rw [@Set.inter_distrib_right]
rw[Set.inter_comm] at h1
rw[Set.inter_comm] at h2
rw[h1, h2]
simp

exfalso
rw[case1.symm] at case2
exact hK1K2 (id case2.symm)



lemma Clump_family_improvement
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
(hDecompose: Clump_Decomposition L KFam)
(hUnSeparated: ¬ Clump_family_separated KFam)
(hNarrow: Clump_family_narrow KFam)
(hNoWideClumps: ¬ L_contains_wide_clump p m κ pr h G L )

: ∃ (KFam2: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam2
∧ KFam2.card< KFam.card
∧ Clump_family_narrow KFam2

:=by
dsimp [Clump_family_separated] at hUnSeparated
simp at hUnSeparated
rcases hUnSeparated with ⟨K1, hK1, K2, hK2, hK1K2, hUnSeparated⟩

have κggk: gg1 κ ≥ Nat.max K1.k K2.k:= by
  have h1: gg1 κ ≥ 10000*κ^5:= by
    apply gg1_6
    exact Nat.le_refl (gg1 κ)
    repeat assumption
  have h2: gg1 κ≥ pr*pr*pr*pr*h:= by
    calc
      gg1 κ≥ 10000*κ^5:= by exact h1
      _≥ 1*κ^5:= by
        gcongr
        simp
      _=κ *κ *κ*κ *κ  := by ring_nf
      _≥ h*h*h*h*h:= by
        gcongr
        apply gg1_ge;
        repeat assumption
        apply gg1_ge;
        repeat assumption
        apply gg1_ge;
        repeat assumption
        apply gg1_ge;
        repeat assumption
        apply gg1_ge;
        repeat assumption
        --
      _≥ pr*pr*pr*pr*h:= by
        gcongr
        apply gg1_ge;
        repeat assumption
        apply gg1_ge;
        repeat assumption
        apply gg1_ge;
        repeat assumption
        apply gg1_ge;
        repeat assumption
                        --
  refine Nat.max_le_of_le_of_le ?_ ?_
  calc
    gg1 κ≥ pr*pr*pr*pr*h:= by
      exact h2
    _≥ K1.k:= by
      apply hNarrow
      assumption
  calc
    gg1 κ≥ pr*pr*pr*pr*h:= by
      exact h2
    _≥ K2.k:= by
      apply hNarrow
      assumption



have hKex: ∃ (K: Clump G p m κ pr h),
(K.Gr=K1.Gr⊔ K2.Gr)∧
(K.H=K1.H∪ K2.H)∧
(K.k≥ (Nat.max K1.k K2.k))∧
(K.k≤ K1.k+K2.k):=by
  apply clump_joining_max_unseparated
  repeat assumption
  --



rcases hKex with ⟨K, hKGr, hKH, hKk1, hKk2⟩
let KFam2:= KFam\ {K1, K2}∪ {K}
use KFam2

have hK_in_Fam2:K∈ KFam2:=by
  have h1: K∈ {K}:=by
    exact mem_singleton.2 rfl
  exact mem_union_right (KFam \ {K1, K2}) h1

constructor

unfold Clump_Decomposition
constructor
--unfold Clump_family_edge_disjoint
apply Clump_family_replace_two_sets_stays_edgedisjoint _ _ K1 K2 K
unfold Clump_Decomposition at hDecompose
exact hDecompose.1
exact hK1
exact hK2
exact rfl
exact hKGr

constructor
unfold Clump_family_contained_in_L
intro Ki hKi
by_cases hKi': Ki∈ KFam
have h1:  Clump_family_contained_in_L (L.Gr) KFam :=by
  unfold Clump_Decomposition at hDecompose
  exact hDecompose.2.1
exact h1 Ki hKi'

have h1: Ki=K:=by
  apply mem_singleton.1
  dsimp [KFam2] at hKi
  have h2: Ki∉ KFam \ {K1, K2}:=by
    exact not_mem_sdiff_of_not_mem_left hKi'
  exact mem_of_union_elim_left (KFam \ {K1, K2}) {K} Ki hKi h2
rw[h1, hKGr]
refine SemilatticeSup.sup_le K1.Gr K2.Gr L.Gr ?_ ?_
unfold Clump_Decomposition at hDecompose
unfold Clump_family_contained_in_L at hDecompose
exact hDecompose.2.1 K1 hK1
exact hDecompose.2.1 K2 hK2

unfold L_contained_in_clump_family
intro H hH
unfold Clump_Decomposition at hDecompose
unfold L_contained_in_clump_family at hDecompose
have h1: ∃ K ∈ KFam, H ≤ K.Gr:= by
  exact hDecompose.2.2 H hH
rcases h1 with ⟨Ki, hKi, hHGr⟩
by_cases hcase: Ki∈ KFam2
use Ki

have h2: Ki∈ KFam\KFam2:=by
  refine mem_sdiff.mpr ?_
  constructor
  exact hKi
  exact hcase

have h3: KFam \ KFam2⊆ {K1, K2}:=by
  dsimp [KFam2]
  calc
    KFam \ (KFam \ {K1, K2} ∪ {K})⊆
    KFam \ (KFam \ {K1, K2}):=by
      refine sdiff_subset_sdiff (fun ⦃a⦄ a ↦ a) ?hvu
      exact subset_union_left (KFam \ {K1, K2}) {K}
    _= KFam ∩ {K1, K2}:=by
      simp
    _⊆ {K1, K2}:=by
      exact inter_subset_right KFam {K1, K2}
have h3: Ki∈ {K1,K2}:=by
  exact h3 h2
simp at h3

by_cases hcase2: Ki=K1
use K
constructor
exact hK_in_Fam2
calc
  H≤ K1.Gr:=by
    rw[hcase2.symm]
    exact hHGr
  _≤K1.Gr⊔ K2.Gr:=by
    exact SemilatticeSup.le_sup_left K1.Gr K2.Gr
  _=K.Gr:=by
    exact id hKGr.symm

have hcase2: Ki=K2:=by
  exact Or.resolve_left h3 hcase2
use K
constructor
exact hK_in_Fam2
calc
  H≤ K2.Gr:=by
    rw[hcase2.symm]
    exact hHGr
  _≤K1.Gr⊔ K2.Gr:=by
    exact le_sup_right'
  _=K.Gr:=by
    exact id hKGr.symm


constructor
have KFam_at_least_2: KFam.card≥ 2:=by
  refine le_card_iff_exists_subset_card.mpr ?_
  use {K1, K2}
  constructor
  refine insert_subset hK1 ?h.left.hs
  exact singleton_subset_iff.mpr hK2
  exact card_doubleton hK1K2


dsimp[KFam2]
calc
  (KFam \ {K1, K2} ∪ {K}).card
  ≤ (KFam \ {K1, K2}).card+ ({K}:Finset (Clump G p m κ pr h)).card:=by
   exact card_union_le (KFam \ {K1, K2}) {K}
  _=(KFam \ {K1, K2}).card+ 1:=by
    congr

  _= (KFam.card - ({K1, K2}: Finset (Clump G p m κ pr h)).card)+1:=by
    congr
    refine card_sdiff ?_
    refine insert_subset hK1 ?_
    exact singleton_subset_iff.mpr hK2
  _= (KFam.card - 2)+1:=by
    congr
    exact card_doubleton hK1K2
  _= KFam.card - 1:=by
    refine ((fun {m n} ↦ Nat.pred_eq_succ_iff.mpr) ?_).symm--refine ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?h rfl).symm
    exact (Nat.sub_eq_iff_eq_add KFam_at_least_2).mp rfl
  _< KFam.card:=by
    refine Nat.sub_lt_self ?h₀ ?h₁
    exact Nat.one_pos
    exact Nat.one_le_of_lt KFam_at_least_2




unfold Clump_family_narrow
intro K' hK'
by_cases hcase: K'∈ KFam
exact hNarrow K' hcase

have hcase2: K'=K:=by
  apply mem_singleton.1
  dsimp [KFam2] at hK'
  have h2: K'∉ KFam \ {K1, K2}:=by
    exact not_mem_sdiff_of_not_mem_left hcase
  exact mem_of_union_elim_left (KFam \ {K1, K2}) {K} K' hK' h2

rw[hcase2]
have h1:  K.k ≤ 4*pr * pr *pr * pr* h:=by
  calc
    K.k ≤K1.k+K2.k:=by exact hKk2
    _≤ pr*pr*pr*pr*h+pr*pr*pr*pr*h:=by
      gcongr
      exact hNarrow K1 hK1
      exact hNarrow K2 hK2
    _=2*pr*pr*pr*pr*h:=by
      ring_nf
    _≤ 4*pr*pr*pr*pr*h:=by
      gcongr
      exact Nat.AtLeastTwo.prop

by_contra hcont
have wideclump:L_contains_wide_clump p m κ pr h G L:=by
  use K
  constructor
  calc
    K.Gr=K1.Gr⊔ K2.Gr:=by
      exact hKGr
    _≤ L.Gr:=by
      refine SemilatticeSup.sup_le K1.Gr K2.Gr L.Gr ?_ ?_
      unfold Clump_Decomposition at hDecompose
      unfold Clump_family_contained_in_L at hDecompose
      exact hDecompose.2.1 K1 hK1
      exact hDecompose.2.1 K2 hK2
  constructor
  exact Nat.le_of_not_ge hcont
  exact h1

exact hNoWideClumps wideclump


/-
lemma Initial_Clump_Decomposition
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
:
∃ (KFam: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam
-/
