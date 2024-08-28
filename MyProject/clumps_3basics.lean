import MyProject

import MyProject.clumps_basics
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
variable {p m κ pr h: ℕ}
variable (κPositive: κ >0)
variable (pPositive: p >0)


lemma M_sub_C
(K: Clump G p m κ pm h )
:
(sSup ↑K.M:Subgraph G)≤  K.C
:=by
have M_In_C:_:= by exact K.M_In_C
unfold FamilyContained_in_Graph at M_In_C
simp
exact M_In_C



lemma near_regular_nonempty
(H:Subgraph G)
(m pr: ℕ)
(hnr: near_regular H m pr)
(mggpr: m≥ gg1 pr)
(prPositive: pr>0)
:
H.verts.toFinset.card>0
:= by
calc
  H.verts.toFinset.card≥ m/pr:= by exact hnr.1
  _≥ 1:= by
    refine (Nat.one_le_div_iff ?hb).mpr ?_
    exact prPositive
    apply gg1_ge
    exact mggpr
    exact prPositive
  _>0:= by simp
/-
def near_regular (H:Subgraph G)(m pr: ℕ): Prop :=
  (H.verts.toFinset.card≥ m/pr)
  ∧ (G.cut_dense H pr)-/

lemma clump_Gr_verts_subs
(K: Clump G p m κ pm h )
:
K.Gr.verts.toFinset⊆ Finset.biUnion K.H (fun x=>x.verts.toFinset)
:= by
intro x hx
simp
rw[K.H_Partition_K.symm] at hx
simp at hx
exact hx

lemma clump_Gr_verts_bound
(K: Clump G p m κ pm h )
:
K.Gr.verts.toFinset.card ≤ ∑ Hi ∈ K.H, Hi.verts.toFinset.card
:= by
calc
  K.Gr.verts.toFinset.card
  ≤
  (Finset.biUnion K.H (fun x=>x.verts.toFinset)).card:= by
    refine card_le_of_subset ?_
    apply clump_Gr_verts_subs
  _≤
  ∑ Hi ∈ K.H, Hi.verts.toFinset.card:= by
    exact card_biUnion_le





lemma Clump_sSupM_lower_bound
(K: Clump G p m κ pr h)
:
(sSup K.M: Subgraph G).verts.toFinset.card ≥ m/pr
:= by
have h1: K.M.Nonempty:= by
  refine card_pos.mp ?_
  rw[K.M_Size]
  exact K.Nonemptyness
rcases h1 with ⟨Mi, hMi ⟩
have h2: Mi.verts.toFinset.card≥ m/pr:= by
  refine near_regular_vertices_lower_bound ?h
  apply K.M_Near_Regular
  assumption
calc
  _ ≥ Mi.verts.toFinset.card:= by
    gcongr
    simp
    apply Set.subset_biUnion_of_mem
    simp
    exact hMi
  _≥ m/pr:= by
    exact h2


lemma Clump_BSetPlusM_lower_bound
(K: Clump G p m κ pr h)
:
(BSetPlusM K).toFinset.card ≥ m/pr
:= by

calc
(BSetPlusM K).toFinset.card≥ (sSup K.M: Subgraph G).verts.toFinset.card:= by
  unfold BSetPlusM
  gcongr
  simp
_≥m/pr:= by
  exact Clump_sSupM_lower_bound K
