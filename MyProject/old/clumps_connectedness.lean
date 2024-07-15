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

lemma clump_add_B_vertices_cut_dense
{K: Clump G}
{I: Set V}
{μ:ℕ }
(hI: I⊆ BSet K)
(Iorder: μ *I.toFinset.card≥ K.m):
cut_dense G (K.Full_Graph.induce (I∪ K.C.verts)) μ := by

sorry
