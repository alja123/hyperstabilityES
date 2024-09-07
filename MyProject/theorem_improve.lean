import MyProject

import MyProject.theorem_combine


open Classical
open Finset

namespace SimpleGraph



universe u
variable {V : Type u} {K : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel K.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]

variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )
variable (KComplete: K=completeGraph V)





theorem version4
(G: Subgraph K)
(ε d: ℕ )
(εPositive: ε >0)
(dPositive: d>0)

(dggε: d ≥ gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))

(no_paths: ¬ Has_length_d_path (H) (d))
(HNonempty: H.edgeSet.toFinset.card>0)
(Hedges: ε *H.edgeSet.toFinset.card ≥ d*H.verts.toFinset.card)
:
∃(Sub: Subgraph G), ∃ (Com Cov: List (Set V)),
Components_cover_graph Sub Com
∧
Components_disjoint Com
∧
No_edges_between_components Sub Com
∧
Components_covered_by_covers Sub Com Cov
∧
Covers_small (gg1 (gg1 (gg2 (gg1 ε)))) d Cov
∧
(ε *Sub.edgeSet.toFinset.card+ H.edgeSet.toFinset.card≥ ε *H.edgeSet.toFinset.card)
:= by
apply version3
repeat assumption
