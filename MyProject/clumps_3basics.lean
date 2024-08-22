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
