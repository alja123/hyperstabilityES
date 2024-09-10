--These lines import other parts of the project
import MyProject
import MyProject.theorem_improve
open Classical
namespace SimpleGraph


--the following lines set up the context in which the main theorem will be proved. Essentially they say that V is a finite set of vertices and K is the complete graph on those vertices (and then the graphs considered in the theorem will be subgraphs of K).
universe u
variable {V : Type u} {K : SimpleGraph V}
variable [Fintype V]
variable [DecidableRel K.Adj]
variable [Fintype (Sym2 V)]
variable (iV:Inhabited V)
variable (KComplete: K=completeGraph V)




def Large_Enough :ℚ → ℕ :=fun x => large_enough (Nat.ceil (1/x))
-- This defines what "for ε>0, there exists a C..." in the statement of the theorem will mean. For the purposes of the theorem, it only matters that "Large_Enough" defines a function from ℚ to ℕ i.e. that it gives a way of assigning a natural number C to every rational number ε.
--By looking through the proof one can make this function completely explicit. It turns out to be a combination iterated exponentials and factorials (almost certainly nowhere near what the optimal bounds in the theorem should be).

theorem Main_Theorem
--the statement of the theorem starts with a list of assumptions
(G: Subgraph K)-- G is the graph about which the main theorem is about.
(ε: ℚ)
(ε_Positive: ε >0)--ε is a positive rational
(C: ℕ )
(C_large: C ≥ Large_Enough (ε) )-- C is a natural number which is large compared to (some function of) ε
(d: ℕ )
(d_geq_C: d ≥ C) -- d is a natural number which is at least C
(G_has_no_d_paths: ∀ (u v : V), ∀ (P: K.Walk u v), (P.IsPath ∧ P.toSubgraph≤ G)→ P.length < d)--This assumption says that G has no paths of length d. More precisely it reads "for any pair of vertices u and v in V, for any walk P from u to v in G which is a path, the length of P is < d".
(Hedges: (G.edgeSet.toFinset.card: ℚ) ≥ ε*d*(G.verts.toFinset.card: ℚ ))-- This says that e(G)≥ ε v(G).


:-- This colon indicates that after this the conclusion of the theorem begins. The conclusion of the theorem says that there exists a graph H that satisfies there properties (which are separated by the "and" symbols "∧")
∃(H: Subgraph K),

(H≤ G)
--The first property is that H is a subgraph of G

∧

((H.edgeSet.toFinset.card: ℚ )≥ (1-ε) *(G.edgeSet.toFinset.card: ℚ))
-- The second property says that H has at least a (1-ε) proportion of the edges of G

∧

(∀ (Comp: Subgraph K), Comp≤ H∧  Comp.Connected
  → ∃ (Cover: Finset V),
    Cover.card≤ C* d
      ∧ ∀ (u v : V), (u ∈ Comp.verts) ∧  (v ∈ Comp.verts) ∧  (H.Adj u v) →
        (u∈ Cover ∨ v∈ Cover))
--The third property says that "for every connected subgraph of H, there exists a set of vertices Cover that is at most C*d in size, such that for every pair of vertices u and v in the connected subgraph, if u and v are adjacent in H, then at least one of u or v is in Cover."


:= by--What follows is a proof of the theorem (which doesn't do anything other than reduce it to a slight variant of the theorem called "version5" and is found in the file "theorem_improve.lean")
apply version5
repeat assumption
unfold Has_length_d_path
push_neg
intro u v P
apply G_has_no_d_paths
constructor
exact P.Wa_Is_Path
exact P.Wa_In_H
repeat assumption
