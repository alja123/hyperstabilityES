--import source
import hyperstabilityES.lemmas.pro

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


theorem one_vertex_zero_edges (hOrder:Fintype.card V = 1): G.edgeFinset.card=0:= by
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

exact card_eq_zero.mpr hnoedges1

--{s(v,x)| x∈ H.neighborSet v}
theorem edges_delete_vertex (H K: Subgraph G)(v: V)(hv: v∈ H.verts) (hK: K= H.deleteVerts {v}) (E: Set (Sym2 V))(hE:E={s| v∈ s∧ (s ∈ H.edgeSet)}): K.edgeSet= H.edgeSet\ E:= by


have h1:  ∀ (e: Sym2 V), ((e∈ K.edgeSet)↔ e∈ H.edgeSet \ E):= by
  intro e
  constructor
  intro he
  have hne2: ∃(c: Sym2 V), (c=e):= by exact exists_apply_eq_apply (fun a ↦ a) e
  have hne3: ∃ (a b:V), (s(a,b)=e):= by apply Sym2.exists.1 hne2
  rcases hne3 with ⟨a, b, hab ⟩
  have he2: s(a,b)∈ K.edgeSet:= by exact Set.mem_of_eq_of_mem hab he
  have hadj: K.Adj a b := by exact he2
  have vnotinK:v∉ K.verts:= by
    have v1:v∉ H.verts\{v}:= by exact Set.not_mem_diff_of_mem rfl
    exact Eq.mpr_not (congrArg (Membership.mem v) (congrArg Subgraph.verts hK)) v1
  have hva:a∈  K.verts:= by exact K.edge_vert he2
  have hvb:b∈  K.verts:= by exact K.edge_vert (id (Subgraph.adj_symm K hadj))
  have hva2: v≠ a:= by exact Ne.symm (ne_of_mem_of_not_mem hva vnotinK)
  have hvb2: v≠ b:= by exact Ne.symm (ne_of_mem_of_not_mem hvb vnotinK)
  have vne:v∉ s(a,b):= by simp; exact Decidable.not_imp_iff_and_not.mp fun a ↦ hvb2 (a hva2)
  have vne2:¬ (v∈ e) := by exact Eq.mpr_not (congrArg (Membership.mem v) (id hab.symm)) vne
  have einE:e∈{s | v ∈ s ∧ s ∈ H.edgeSet} ↔ v ∈ e ∧ e ∈ H.edgeSet:= by exact     Set.mem_setOf
  rw [hE.symm] at einE
  have eninE:¬ (v ∈ e ∧ e ∈ H.edgeSet):= by exact not_and.mpr fun a a_1 ↦ vne2 a
  have eninE2:e∉E:= by exact (iff_false_right eninE).mp einE
  have einH:e∈ H.edgeSet:= by
    have Kadj: K.Adj a b := by exact he2
    have K2adj: (H.deleteVerts {v}).Adj a b := by rw[hK.symm]; exact Kadj
    have Hadj: (a ∈ H.verts) ∧ (a ∉ {v}) ∧ (b ∈ H.verts) ∧ (b ∉ {v}) ∧ (H.Adj a b):= by apply SimpleGraph.Subgraph.deleteVerts_adj.1; exact K2adj
    have Hadj: H.Adj a b := by exact Hadj.2.2.2.2
    exact Set.mem_of_eq_of_mem (id hab.symm) Hadj
  exact Set.mem_diff_of_mem einH eninE2

  intro he
  have einH: e∈ H.edgeSet:=by exact Set.mem_of_mem_diff he
  have einE:e∈{s | v ∈ s ∧ s ∈ H.edgeSet} ↔ v ∈ e ∧ e ∈ H.edgeSet:= by exact     Set.mem_setOf
  rw [hE.symm] at einE
  have negeinE:¬(e∈ E)↔ ¬(v ∈ e ∧ e ∈ H.edgeSet):= by exact not_congr einE
  have eninE:¬ (e∈ E):= by exact Set.not_mem_of_mem_diff he
  have enin2:¬(v ∈ e ∧ e ∈ H.edgeSet):= by
    exact    (iff_false_right eninE).mp (id (Iff.symm einE))
  have himp:e∈ H.edgeSet→  ¬ (v∈ e):= by contrapose; simp; simp at enin2; exact fun a ↦enin2 a
  have hvnine:v∉e  := by exact himp einH
  have hne2: ∃(c: Sym2 V), (c=e):= by exact exists_apply_eq_apply (fun a ↦ a) e
  have hne3: ∃ (a b:V), (s(a,b)=e):= by apply Sym2.exists.1 hne2
  rcases hne3 with ⟨a, b, hab ⟩
  have hvnine2: v∉ s(a,b) := by rw [hab]; exact himp einH
  have ha: a∈ s(a,b):= by exact Sym2.mem_mk_left a b
  have ha': a≠ v:= by exact ne_of_mem_of_not_mem ha hvnine2
  have hb: b∈ s(a,b):= by exact Sym2.mem_mk_right a b
  have hb': b≠ v:= by exact ne_of_mem_of_not_mem hb hvnine2
  have hab': s(a,b)∈ H.edgeSet:= by exact Set.mem_of_eq_of_mem hab einH
  have hab2: H.Adj a b := by exact hab'
  have hab3:G.Adj a b:= by exact Subgraph.Adj.adj_sub hab'
  have habK: K.Adj a b := by
    have h1:a∉ ({v}:Set V):= by exact ha'
    have h2:b∉ ({v}:Set V):= by exact hb'
    have h3:a∈ H.verts:=by exact Subgraph.mem_verts_if_mem_edge hab' ha
    have h4:b∈ H.verts:=by exact Subgraph.mem_verts_if_mem_edge hab' hb
    rw[hK]
    apply SimpleGraph.Subgraph.deleteVerts_adj.2
    constructor; exact h3
    constructor; exact h1
    constructor; exact h4
    constructor; exact h2
    exact hab'
  exact Set.mem_of_eq_of_mem (id hab.symm) habK


exact Set.ext h1





--{s(v,x)| x∈ H.neighborSet v}
theorem edges_vertex_equals_degree (H: Subgraph G)(v: V)(E: Set (Sym2 V))(hE:E={s| (v∈ s)∧ (s ∈ H.edgeSet)}): Fintype.card E= Fintype.card (H.neighborSet v):= by


let h: V→ Sym2 V:= fun a => s(v,a)


let g: Sym2 V → V:= fun a=> if h:v∈ a
  then   Sym2.Mem.other h
  else v

have honeway: ∀ (x: V),  (g (h x) = x):=  by
  intro x
  have h1: h x = s(v,x):= by exact rfl
  have h2: g s(v,x) = x:= by
    by_cases heq:v=x
    --rw[heq.symm]
    have ha: v∈ s(v,v):= by exact Sym2.mem_mk_right v v
    have hb: Sym2.Mem.other ha∈ s(v,v):= by exact Sym2.other_mem ha
    have hb:Sym2.Mem.other ha=v ∨ Sym2.Mem.other ha=v:= by exact Sym2.mem_iff'.mp hb
    have hb:Sym2.Mem.other ha=v:= by  simp at hb; simp; exact hb
    calc
      g s(v,x)=g s(v,v):= by exact        congrArg g (congrArg Sym2.mk (congrArg (Prod.mk v) (id heq.symm)))
      _=Sym2.Mem.other ha:= by exact dif_pos ha
      _=v:= by exact hb
      _=x:= by exact heq

    by_cases h3:v∈ s(v,x)
    have h4:g s(v,x)=Sym2.Mem.other h3:= by exact dif_pos h3
    have h6: s(v,x)=s(v, Sym2.Mem.other h3):= by exact (Sym2.other_spec h3).symm
    have h6: s(v,x)=s(v, g s(v,x)):= by rw[h4]; exact h6
    simp at h6
    have h7:x≠ v :=by exact fun a ↦ heq (id a.symm)
    have h8:¬((v = g s(v, x)) ∧ (x = v)):= by exact not_and.mpr fun a ↦ h7
    rcases h6 with ha|hb
    exact id ha.symm
    exact (h8 hb).elim
    have hv: v∈ s(v,x):= by exact Sym2.mem_mk_left v x
    exact (h3 hv).elim
  exact h2


have hotherway: ∀ (e: Sym2 V), (e ∈ E)→ (h (g e) = e):=  by
  intro e he
  --have h1: ∃ (x:Sym2 V), (x=e):= by exact exists_apply_eq_apply (fun a ↦ a) e
  --have h2: ∃ (a b:V), (s(a,b)=e):= by apply Sym2.exists.1 h1
  --rcases h2 with ⟨a, b, hab ⟩
  --rw [hab.symm]
  have hve: ((v∈ e)∧ (e ∈ H.edgeSet)) ↔ e∈ {s| (v∈ s)∧ (s ∈ H.edgeSet)} := by  exact Eq.to_iff rfl
  have hve2: (v∈ e)∧ (e ∈ H.edgeSet):=by apply hve.2; rw[hE.symm]; exact he
  let x:=Sym2.Mem.other hve2.1
  have hge:g e= x:= by exact dif_pos hve2.1
  have hhge:h (g e)= s(v,x):= by exact congrArg h hge
  have he2:e=s(v,x):= by exact (Sym2.other_spec hve2.1).symm
  rw[hhge]
  exact id he2.symm

have hImage: ∀ (x: V), (x ∈ H.neighborSet v)→  (h x∈ E):= by
  intro x hx
  let e:Sym2 V:= s(v,x)
  have he:e∈ H.edgeSet:= by exact hx
  have he2:v∈ e:= by exact Sym2.mem_mk_left v x
  have he3: v ∈ e ∧ e ∈ H.edgeSet:= by exact ⟨he2, hx⟩
  have hve: ((v∈ e)∧ (e ∈ H.edgeSet)) ↔ e∈ {s| (v∈ s)∧ (s ∈ H.edgeSet)} := by  exact Eq.to_iff rfl
  rw[hE]
  exact he3

have hImage2: ∀ (e: Sym2 V), (e ∈ E)→  (g e∈ H.neighborSet v):= by
  intro e he
  have hve: ((v∈ e)∧ (e ∈ H.edgeSet)) ↔ e∈ {s| (v∈ s)∧ (s ∈ H.edgeSet)} := by  exact Eq.to_iff rfl
  rw[hE.symm] at hve
  rw[hve.symm] at he
  have ge:g e=  Sym2.Mem.other he.1:= by exact dif_pos he.left
  let x:V:=Sym2.Mem.other he.1
  have ge:g e= x:= by exact ge
  have he2:e=s(v,x):=by exact (Sym2.other_spec he.left).symm
  have he3: s(v,x) ∈ H.edgeSet:= by rw[he2.symm]; exact he.2
  have hadj: H.Adj v x := by exact he3
  rw [ge]
  exact he3

by_cases hEemp:IsEmpty E
by_cases hNemp:IsEmpty (H.neighborSet v)
calc
  Fintype.card ↑E=0:= by exact Fintype.card_eq_zero
  _=Fintype.card ↑(H.neighborSet v):= by exact Fintype.card_eq_zero.symm
have nonemp: Nonempty ↑(H.neighborSet v):= by exact not_isEmpty_iff.mp hNemp
have hxex: ∃ (x: V), (x∈  ↑(H.neighborSet v)):= by exact nonempty_subtype.mp nonemp
rcases hxex with ⟨x, hx ⟩
have hx: h x ∈ E := by exact hImage x hx
have hnonemp1: Nonempty E:= by refine nonempty_subtype.mpr ?_; use (h x), hx
have hnonemp2:  ¬ (IsEmpty E):= by exact not_isEmpty_of_nonempty ↑E
exact (hnonemp2 hEemp).elim

by_cases hNemp:IsEmpty (H.neighborSet v)
have nonemp: Nonempty E:= by exact not_isEmpty_iff.mp hEemp
have hxex: ∃ (e: Sym2 V), (e∈  E):= by exact nonempty_subtype.mp nonemp
rcases hxex with ⟨e, he ⟩
have hx: g e ∈ ↑(H.neighborSet v) := by exact hImage2 e he
have hnonemp1: Nonempty ↑(H.neighborSet v):= by refine nonempty_subtype.mpr ?_; use (g e), hx
have hnonemp2:  ¬ (IsEmpty ↑(H.neighborSet v)):= by exact  not_isEmpty_of_nonempty ↑(H.neighborSet v)
exact (hnonemp2 hNemp).elim

have nonemp: Nonempty ↑(H.neighborSet v):= by exact not_isEmpty_iff.mp hNemp
have hxex: ∃ (x: V), (x∈  ↑(H.neighborSet v)):= by exact nonempty_subtype.mp nonemp
rcases hxex with ⟨n0, hn0 ⟩
have nonemp: Nonempty E:= by exact not_isEmpty_iff.mp hEemp
have hxex: ∃ (e: Sym2 V), (e∈  E):= by exact nonempty_subtype.mp nonemp
rcases hxex with ⟨e0, he0 ⟩

let bij: H.neighborSet v→E:= fun a=> if h1:h a ∈ E
  then  ⟨ h a, h1 ⟩
  else ⟨ e0, he0⟩
let bij2: E→ H.neighborSet v:= fun a=> if h1:g a ∈ H.neighborSet v
  then  ⟨ g a, h1 ⟩
  else ⟨ n0, hn0⟩
have hbij: Function.Bijective bij:= by
  apply Function.bijective_iff_has_inverse.mpr
  use bij2
  constructor
  intro y
  have h1:h y∈ E:= by apply hImage; exact Subtype.coe_prop y
  let hy:E:= ⟨ h y, h1 ⟩
  have hyTrue: h y =hy:= by exact rfl
  have bijy: bij y = hy:= by exact dif_pos h1
  have h2: g hy∈  H.neighborSet v:=by exact hImage2 (↑hy) h1
  let ghy: H.neighborSet v:= ⟨ g hy, h2 ⟩
  have bijgy: bij2 hy = ⟨ g hy, h2 ⟩:= by exact dif_pos h2
  have bijgy2: bij2 hy = ghy:= by exact bijgy
  have ghyTrue: g hy=ghy:= by exact rfl
  have ghyident:ghy=g (h y):= by calc
    ghy= g hy:= by exact ghyTrue
    _=g (h y):= by exact ghyTrue
  have ident2: g (h y)=y:= by apply honeway
  rw[bijy, bijgy2]
  exact SetCoe.ext (honeway ↑y)


  intro y
  let F:Set V:= H.neighborSet v
  have h1:g y∈ F:= by apply hImage2; exact Subtype.coe_prop y
  let hy:F:= ⟨ g y, h1 ⟩
  have hyTrue: g y =hy:= by exact rfl
  have bijy: bij2 y = hy:= by exact dif_pos h1
  have h2: h hy∈  E:=by exact hImage (↑hy) h1
  let ghy: E:= ⟨ h hy, h2 ⟩
  have bijgy: bij hy = ⟨ h hy, h2 ⟩:= by exact dif_pos h2
  have bijgy2: bij hy = ghy:= by exact bijgy
  have ghyTrue: h hy=ghy:= by exact rfl
  have ghyident:ghy=h (g y):= by calc
    ghy= h hy:= by exact ghyTrue
    _=h (g y):= by exact ghyTrue
  have ident2: h (g y)=y:= by apply hotherway; exact Subtype.coe_prop y
  rw[bijy, bijgy2]
  exact SetCoe.ext ident2


exact (Fintype.card_of_bijective hbij).symm






  --have hx: ∃ (x:V), x∈ H.neighborSet v∧ e=s(v,x):= by


--have hne2: ∃(c: Sym2 V), (c∈ H.edgeSet):= by exact nonempty_subtype.mp hne

--have hne3: ∃ (a b:V), (s(a,b)∈ H.edgeSet):= by apply Sym2.exists.1 hne2

theorem edges_delete_vertex_count (H K: Subgraph G)(v: V)(hv: v∈ H.verts) (hK: K= H.deleteVerts {v}):
Fintype.card (K.edgeSet) = Fintype.card (H.edgeSet)-Fintype.card (H.neighborSet v):= by
let E: Set (Sym2 V):= {s| v∈ s∧ (s ∈ H.edgeSet)}
have Eex:∃ (E:Set (Sym2 V)), (E={s| v∈ s∧ (s ∈ H.edgeSet)}):= by use E
rcases Eex with ⟨ E, hE⟩
--have hE:E={s| v∈ s∧ (s ∈ H.edgeSet)}:= by exact rfl
--let E':Set (Sym2 V):= {s| v∈ s∧ (s ∈ H.edgeSet)}
have h1: ↑K.edgeSet=↑H.edgeSet\ E:= by exact edges_delete_vertex G H K v hv hK E hE
have h2: E⊆ H.edgeSet:= by
  have hall: ∀ (e: Sym2 V),e∈ E→ e∈ H.edgeSet:= by
    intro e he
    have hand:e∈ {s| v∈ s∧ (s ∈ H.edgeSet)}↔ v ∈ e ∧ e ∈ H.edgeSet:= by exact      Set.mem_setOf
    rw [hE.symm] at hand
    have he2: v ∈ e ∧ e ∈ H.edgeSet:= by apply hand.1; exact he
    exact he2.2
  exact hall
have h2': E.toFinset ⊆ (H.edgeSet).toFinset:= by exact Set.toFinset_subset_toFinset.mpr h2
have h3: ((H.edgeSet).toFinset\ E.toFinset).card = (H.edgeSet).toFinset.card-(E).toFinset.card:= by
  exact card_sdiff h2'
have hK:  (K.edgeSet).toFinset.card=Fintype.card (K.edgeSet):= by exact Set.toFinset_card K.edgeSet
have hK': ((H.edgeSet)\ E).toFinset=((H.edgeSet).toFinset\ E.toFinset):= by
  exact  Set.toFinset_diff H.edgeSet E
have hK'': ((H.edgeSet)\ E).toFinset.card=((H.edgeSet).toFinset\ E.toFinset).card:= by exact  congrArg card hK'
have hE2:  (E).toFinset.card=Fintype.card (E):= by exact Set.toFinset_card E
have hE3:  (E).toFinset.card=Fintype.card (E):= by exact Set.toFinset_card E
have hKlessK:  (H.edgeSet).toFinset.card=Fintype.card (H.edgeSet):= by exact Set.toFinset_card H.edgeSet
have hN:  ((H.neighborSet v)).toFinset.card=Fintype.card (↑(H.neighborSet v)):= by exact Set.toFinset_card (H.neighborSet v)
#check edges_vertex_equals_degree
have hEN: Fintype.card (↑E)=Fintype.card ↑(H.neighborSet v):= by exact edges_vertex_equals_degree G H v E hE
rw [hEN.symm]
rw [hK.symm, h1]
rw [← hKlessK]
rw [hE2.symm, h3.symm]
simp


    --have h5:g s(v,x)=x:= by

theorem average_degree_implies_min_degree_subgraph
(hd: d>0)
(n: ℕ ):
(H: Subgraph G)
→ (hOrder: Fintype.card (H.verts)=n+1)
→  (hAverageDeg: Fintype.card (H.edgeSet)≥ d*(n+1))
→ ( ∃ (K: Subgraph G), (∀ (v:V),(v∈ K.verts)
→ Fintype.card (K.neighborSet v)≥d  )∧ (K≤ H)∧ (Nonempty K.verts)):= by
induction' n with n hi
intro H  hOrder hAverageDegree


have hOrder: Fintype.card ↑H.verts=1:= by exact hOrder
let H':SimpleGraph ↑H.verts:= H.coe
have hzeroedges:H'.edgeFinset.card=0:= by exact one_vertex_zero_edges H' hOrder
have hne0:Fintype.card ↑H.edgeSet>0:= by linarith
have hne: Nonempty ↑H.edgeSet:= by exact Fintype.card_pos_iff.mp hne0
have hne2: ∃(c: Sym2 V), (c∈ H.edgeSet):= by exact nonempty_subtype.mp hne

have hne3: ∃ (a b:V), (s(a,b)∈ H.edgeSet):= by apply Sym2.exists.1 hne2
rcases hne3 with ⟨a, b, hab ⟩
have ha: a ∈ H.verts:= by exact H.edge_vert hab
have hb: b ∈ H.verts:= by exact Subgraph.Adj.snd_mem hab
--have hadj: H.Adj a b:= by exact hab
--have hadj2:G.Adj a b:= by exact Subgraph.Adj.adj_sub hab
have hadj3:H'.Adj ⟨a, ha⟩  ⟨b, hb⟩  := by exact hab
have hnonemp: s(⟨a, ha⟩ , ⟨b, hb⟩)∈  H'.edgeFinset:= by exact mem_edgeFinset.mpr hab
have hnonemp2:H'.edgeFinset.card≠ 0:= by exact card_ne_zero_of_mem hnonemp
exfalso
exact hnonemp2 hzeroedges


intro H  hOrder hAverageDegree
by_cases hcase:∀ v ∈ H.verts, Fintype.card ↑(H.neighborSet v) ≥ d
use H
constructor
simp at hcase
exact hcase
constructor
simp
have hnonemp: H.verts.toFinset.Nonempty :=by
  refine card_pos.mp ?_
  calc
  _=Fintype.card ↑H.verts:= by
    simp
  _=n+1+1:= by exact hOrder
  _>0:= by simp
simp at hnonemp
exact Set.Nonempty.to_subtype hnonemp
push_neg at hcase
rcases hcase with ⟨x, hx⟩
--let xS:Set V:= {x}
let K:Subgraph G:=H.deleteVerts {x}
have KOrder:Fintype.card (K.verts)=n+1:= by calc
  Fintype.card (K.verts)=Fintype.card (H.verts \ ({x}:Set V):Set V):= by
    exact Fintype.card_congr' rfl
  _=Fintype.card (H.verts)-1:= by
    have h1: K.verts=H.verts \ ({x}:Set V):= by exact rfl
    have h2: Fintype.card ({x}:Set V)=1:=by exact rfl
    have h3: ({x}:Set V)⊆ (H.verts: Set V) := by
      have h4:x∈ H.verts:= by exact hx.1
      exact Set.singleton_subset_iff.mpr h4
    have h6:Fintype.card (H.verts)= (filter (fun x ↦ x ∈ H.verts) univ).card := by
      exact Fintype.card_subtype fun x ↦ x ∈ H.verts
    have h7: Fintype.card (H.verts)=( H.verts.toFinset).card:= by
      exact (Set.toFinset_card H.verts).symm
    have h8: Fintype.card ((H.verts: Set V) \ ({x}:Set V): Set V)=((H.verts: Set V) \ ({x}:Set V): Set V).toFinset.card:= by
      exact  (Set.toFinset_card (H.verts \ {x})).symm
    have h9: ((H.verts: Set V) \ ({x}:Set V): Set V).toFinset=(H.verts: Set V).toFinset \ ({x}:Set V).toFinset:= by
      exact Set.toFinset_diff H.verts {x}
    have h11: ({x}:Set V).toFinset⊆ (H.verts: Set V).toFinset := by
      exact   Set.toFinset_subset_toFinset.mpr h3
    have h10: ((H.verts: Set V).toFinset \ ({x}:Set V).toFinset).card=(H.verts: Set V).toFinset.card-  ({x}:Set V).toFinset.card:= by
      exact card_sdiff h11
    have h12: (H.verts: Set V).toFinset.card=Fintype.card (H.verts):= by exact id h7.symm
    have h5: Fintype.card (H.verts \ ({x}:Set V):Set V)=Fintype.card (H.verts)-1:= by calc
      Fintype.card (H.verts \ ({x}:Set V):Set V)=((H.verts: Set V) \ ({x}:Set V): Set V).toFinset.card:= by exact h8
      _=((H.verts: Set V).toFinset \ ({x}:Set V).toFinset).card:= by exact congrArg card h9
      _=(H.verts: Set V).toFinset.card-  ({x}:Set V).toFinset.card:= by exact h10
      _=(H.verts: Set V).toFinset.card-Fintype.card ({x}:Set V):= by exact rfl
      _= Fintype.card (H.verts)-Fintype.card ({x}:Set V):= by rw [h12]
      _= Fintype.card (H.verts)-1:= by exact rfl
    exact h5

  _=n+1:= by exact Nat.pred_eq_succ_iff.mpr hOrder

have  KAverageDegree: Fintype.card (↑K.edgeSet) ≥  d * (n + 1):= by calc
  Fintype.card (↑K.edgeSet)=Fintype.card (H.edgeSet)-Fintype.card (H.neighborSet x):= by
    apply edges_delete_vertex_count;
    exact hx.1;
    exact rfl;
  _≥ d*(n+1+1)-Fintype.card ↑(H.neighborSet x):=by exact    Nat.sub_le_sub_right hAverageDegree (Fintype.card ↑(H.neighborSet x))
  _≥   d*(n+1+1)-d:= by
    have h1:Fintype.card ↑(H.neighborSet x)< d:= by exact hx.2
    have h2: Fintype.card ↑(H.neighborSet x)≤ d:=by exact Nat.le_of_succ_le h1
    exact Nat.sub_le_sub_left h2 (d * (n + 1 + 1))
  _= d*(n+1):= by exact Nat.sub_eq_of_eq_add rfl


have hex44:_:= by apply hi K KOrder KAverageDegree
rcases hex44 with ⟨J, hJ1, hJ2, hJ3 ⟩
use J
constructor
exact hJ1
constructor
have hcont: K≤ H:= by
  dsimp[K]
  exact Subgraph.deleteVerts_le
exact Preorder.le_trans J K H hJ2 hcont
exact hJ3
