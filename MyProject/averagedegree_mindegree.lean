import MyProject
import MyProject.pro



open Classical
open Finset
--open scoped BigOperators

namespace SimpleGraph


universe u
variable {V : Type u} (G : SimpleGraph V)
variable [Fintype V] [DecidableRel G.Adj]
variable (n: ℕ )
variable (d:ℕ )
variable [Fintype (Sym2 V)]


#check SimpleGraph.embed_acyclic_min_degree
#check SimpleGraph.sum_degrees_eq_twice_card_edges

--theorem average_degree_implies_min_degree_subgraph (hd: d>0)(H: Finsubgraph G)(hOrder: (⟨ H.1.verts, H.2⟩: Finset V).card =n+1)(hAverageDeg:(H.subgraph.edgeSet.card)≥ d*(n+1)): ∃ (K: Finsubgraph G), (∀ (v:V),(v∈ K.verts)→ (K.subgraph.degree v≥ d) ):= by
--#check H.2


theorem average_degree_implies_min_degree_subgraph2
(n:ℕ ):(V : Type u)→ (hV: Fintype V)→(G : SimpleGraph V)→(hd: d>0)→(hOrder: (Fintype.card V )=n+1)→(hAverageDeg:(G.edgeFinset.card)/(n+1)≥ d)→ ∃ (S: Finset V), ((induce S G).minDegree≥ d):= by
induction' n with n hi
intro V hV G hd hOrder hAverageDeg
have hOrder:Fintype.card V =  1:= by exact hOrder

have hnoedges:(∀ {c d : V}, ¬ G.Adj c d):= by
  exact fun {c d} ↦  one_vertex_implies_no_edges G hOrder
have hnoedges1: G.edgeFinset=∅:= by
  by_contra cont
  have hedge: ∃ (e:Sym2 V), (e ∈ G.edgeFinset)  := by
    by_contra cont2
    --simp at cont2
    --have h: ¬G.edgeSet = ∅:= by exact?
    have forAll: ∀(e:Sym2 V), ¬ (e ∈ G.edgeFinset):= by
      intro e  he
      have henin:e∉ G.edgeFinset:= by
        by_contra cont3
        have h:∃ (e: Sym2 V), e ∈ G.edgeFinset:= by exact Exists.intro e he
        exact cont2 h
      exact henin he

    have h2:G.edgeFinset = ∅:= by exact eq_empty_of_forall_not_mem forAll
    exact cont h2
  #check Sym2 V
  let f: Sym2 V → Prop := fun s =>  s∈ G.edgeFinset
  have hedge2: ∃ (e:Sym2 V), f e := by exact hedge
  have edgeexists: ∃ (a b : V), (f s(a,b)):= by exact Sym2.exists.mp hedge
  have edgeexists: ∃ (a b : V), (s(a,b)∈ G.edgeFinset):= by exact edgeexists
  rcases edgeexists with  ⟨a,b,hab ⟩
  simp at hab
  exact hnoedges hab

have hless: G.edgeFinset.card / (0 + 1)<d:= by calc
  G.edgeFinset.card / (0 + 1)=G.edgeFinset.card /  1:= by exact rfl
  _=G.edgeFinset.card:= by exact Nat.div_one G.edgeFinset.card
  _=0:= by exact card_eq_zero.mpr hnoedges1
  _<d := by exact hd

have hneg: ¬(G.edgeFinset.card / (0 + 1)≥ d):= by exact Nat.not_le_of_lt hless
exact (hneg hAverageDeg).elim

intro V hV G hd hOrder hAverageDeg
by_cases hcase:G.minDegree ≥ d
let VS: Finset V:= Finset.univ
let typeS:= {v // v∈ VS}
let H: SimpleGraph typeS:=induce VS G
let f: typeS → V := fun a => a.1
have hSurj: Function.Surjective f:= by
  intro b
  have hb: b∈ VS:= by exact mem_univ b
  have hf: f ⟨b, hb⟩ = b := by exact rfl
  use ⟨b, hb⟩
have hInj: Function.Injective f:= by
  intro a b hab
  have habeq:a.1=b.1:= by exact hab
  exact SetCoe.ext hab
have hHom: ∀ (a b: typeS),(H.Adj a b → G.Adj (f a) (f b)):= by
  intro a b hab
  exact hab



--have f:G≅g H:=  exact?

sorry
#check exists_minimal_degree_vertex
have hnonempty: Nonempty V:= by sorry
have hlowdeg:∃ (v: V), (G.minDegree=G.degree v):= by exact exists_minimal_degree_vertex G
rcases hlowdeg with ⟨v, hv⟩
have hvDeg: G.degree v <d:= by calc
  G.degree v=G.minDegree:= by exact id hv.symm
  _< d:= by exact Nat.gt_of_not_le hcase

--let SU: Finset V:=Finset.univ
--let SS: Finset V:= ({v}: Finset V)
let S:Finset V:= Finset.univ \ ({v}: Finset V)
let typeS:={v// v∈ S}
let G': SimpleGraph typeS:= induce S G

have hInduct1:  Fintype.card typeS = n + 1:= by sorry
have hInduct2: G'.edgeFinset.card / (n + 1) ≥ d:= by sorry

have hApplyInduct: ∃ (S:Finset typeS), (induce (↑S) G').minDegree ≥ d:= by
  apply hi
  exact hd
  exact hInduct1
  exact hInduct2

rcases hApplyInduct with ⟨S, hS⟩
let VS: Finset V:= Finset.univ

#check Finset V
let g:typeS → V:= fun a=>a
let setS':Set V:={(↑a: V)| a∈ S}
let S':Finset V := Finset.filter (·∈ setS') VS --{(↑a: V)| a∈ S}

use S'

--have hH:∀ (v:↑↑VS), (H.degree v ≥ d):= by
--  intro v
--  have hGdeg: G.degree v≥ d:= by calc
 --   G.degree v≥ G.minDegree := by exact minDegree_le_degree G ↑v
 --   _≥d:= by exact hcase
 -- have hNeigh: G.neighborFinset ↑v=↑(H.neighborFinset v):= by
  --have edgeexists: ∃ (a b : V), (e=s(a,b)):= by exact?
sorry
