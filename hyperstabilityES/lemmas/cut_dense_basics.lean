--import MyProject
import hyperstabilityES.lemmas.pro
import hyperstabilityES.lemmas.Basic
--import hyperstabilityES.lemmas.Basic_results
import hyperstabilityES.lemmas.averagedegmindeg2
import Mathlib.Combinatorics.SimpleGraph.Density



set_option linter.unusedVariables false

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


--noncomputable def indicator_edge(H: Subgraph G)(a b: V): ℕ := if H.Adj a b then 1 else 0

--noncomputable def edges_accross (G : SimpleGraph V)(H: Subgraph G)(A B: Set V):ℕ :=  Finset.sum  A.toFinset fun (a:V)=> (Finset.sum B.toFinset fun (b:V)=>(indicator_edge G H a b))

--def cut_dense (G : SimpleGraph V)(H: Subgraph G)(α : ℚ): Prop :=
--∀ (A B: Set V), (V= A ∪ B)→  G.edgeDensity A.toFinset B.toFinset≥ α

--def cut_dense (G : SimpleGraph V)(H: Subgraph G)(α : ℚ): Prop :=
--∀ (A B: Finset V), (H.verts= A ∪ B)→  Rel.edgeDensity H.Adj A B≥ α
def cut_dense (G : SimpleGraph V)(H: Subgraph G)(k : ℕ ): Prop :=
∀ (A B: Finset V), (H.verts.toFinset= A ∪ B)→  k*(Rel.interedges H.Adj A B).card ≥ A.card*B.card

#check cut_dense
--set_option maxHeartbeats 600000
--set_option diagnostics true
--jjjk
lemma Cut_Dense_monotone
{H:   Subgraph G}
(a: ℕ)
{b: ℕ}
(hab: a≤ b)
(hcut_dense: cut_dense G H a)
: cut_dense G H b:= by
intro A B hUnion
calc
b * (Rel.interedges H.Adj A B).card ≥
a * (Rel.interedges H.Adj A B).card:= by
  gcongr
_≥ A.card * B.card:= by
  exact hcut_dense A B hUnion

lemma cut_dense_subgraph_monotone
{H K: Subgraph G}
{k: ℕ}
(hHK: H≤ K)
(hvertsEq: H.verts= K.verts)
(hcut_dense: cut_dense G H k)
: cut_dense G K k:= by
intro A B hUnion
have hUnion': H.verts.toFinset= A ∪ B:= by
  rw [hvertsEq]
  exact hUnion
have h1: (Rel.interedges H.Adj A B) ⊆  (Rel.interedges K.Adj A B):= by
  intro x hx
  have h2: x∈ (Rel.interedges H.Adj A B):= by exact hx
  have h3: x.1∈ A ∧ x.2∈ B ∧ H.Adj x.1 x.2:= by exact Rel.mem_interedges_iff.mp h2
  have h4: H.Adj x.1 x.2:= by exact h3.2.2
  have h5: K.Adj x.1 x.2:= by
    exact subgraph_implies_adjacency_inherited hHK h4
  exact Rel.mem_interedges_iff.mpr ⟨h3.1, h3.2.1, h5⟩


calc
k * (Rel.interedges K.Adj A B).card
≥ k * (Rel.interedges H.Adj A B).card:=by
  gcongr
_≥ A.card * B.card:=by
  exact hcut_dense A B hUnion'

theorem cut_dense_min_degree
{H: Subgraph G}
{k:ℕ }
{v:V}
(hv:v∈H.verts)
(hCutDense: cut_dense G H k)
:k*H.degree v≥  H.verts.toFinset.card:= by
let As:Set V:= {v}
let Bs:Set V:= H.verts
let Ns:Set V:= H.neighborSet v

let A:Finset V:= As.toFinset
let B:Finset V:= Bs.toFinset
let N:Finset V:= Ns.toFinset
have cont1:({v}:Set V)⊆ Bs:= by exact Set.singleton_subset_iff.mpr hv
have cont2:A⊆ B:= by exact Set.toFinset_subset_toFinset.mpr cont1
have cont3: A∪ B=B:=by apply union_eq_right.2; exact cont2
have hAunionB: H.verts.toFinset=A∪ B:= by calc
  H.verts.toFinset=B:=by exact rfl
  _=A∪ B:=by exact id cont3.symm
have hinteredges: k*(Rel.interedges H.Adj A B).card ≥  A.card*B.card:= by exact hCutDense A B hAunionB
have hAcard: A.card=1:= by exact rfl
have hBcard: B.card=H.verts.toFinset.card:= by exact rfl
rw [hAcard] at hinteredges
rw [hBcard] at hinteredges
have h1:  ↑1 * ↑H.verts.toFinset.card=  ↑H.verts.toFinset.card:= by simp
have hinteredges: k*(Rel.interedges H.Adj A B).card ≥  ↑H.verts.toFinset.card:= by calc
  k*↑(Rel.interedges H.Adj A B).card ≥  ↑1 * ↑H.verts.toFinset.card:= by exact hinteredges
  _=↑H.verts.toFinset.card:= by exact h1

have hvin:(a:V× V)→ (a∈ Rel.interedges H.Adj A B)→ (a.1=v):= by
  intro a ha
  have h1: a ∈ (A ×ˢ B):= by exact mem_of_mem_filter a ha
  have h2: a.1∈ A ∧  a.2∈ B:=by exact mem_product.mp h1
  have h3: a.1=v:= by
    have h4: a.1∈ A:= by exact h2.1
    have h5: a.1∈ ({v}:Finset V):= by exact h4
    have h6: a.1∈ ({v}:Finset V)↔ (a.1=v):= by exact mem_singleton
    apply h6.1; exact h5
  exact h3


have h:(a:V× V)→ (a∈ Rel.interedges H.Adj A B) → (a.2∈ N):= by
  intro a ha
  have h1: a ∈ (A ×ˢ B):= by exact mem_of_mem_filter a ha
  have h2: a.1∈ A ∧  a.2∈ B:=by exact mem_product.mp h1
  have h3: a.1=v:= by
    have h4: a.1∈ A:= by exact h2.1
    have h5: a.1∈ ({v}:Finset V):= by exact h4
    have h6: a.1∈ ({v}:Finset V)↔ (a.1=v):= by exact mem_singleton
    apply h6.1; exact h5
  --have h4: a.2∈ B:= by exact h2.2
  have hadj:a.1 ∈ A ∧ a.2 ∈ B ∧ H.Adj a.1 a.2:=  by exact Rel.mem_interedges_iff.mp ha
  have hadj: H.Adj a.1 a.2:= by exact hadj.2.2
  have hadj: H.Adj v a.2:= by rw[h3.symm]; exact hadj
  --have gadj: G.Adj v a.2:= by exact Subgraph.Adj.adj_sub hadj
  --have ainN: a.2∈ H.neighborSet v:= by exact hadj
  have ainN: a.2∈ N:= by exact Set.mem_toFinset.mpr hadj
  exact ainN

let f: (Rel.interedges H.Adj A B) → N:= fun a=> ⟨a.1.2, h a.1 a.2⟩
have hInj: Function.Injective f:= by
  intro a b hab
  have hainRel:a.1∈ Rel.interedges H.Adj A B:= by exact coe_mem a
  have ha1eq:a.1=⟨v, (f a).1⟩:= by exact Prod.fst_eq_iff.mp (hvin (↑a) hainRel)
  have a2:⟨v, (f a).1⟩∈  Rel.interedges H.Adj A B:= by rw[ha1eq.symm]; exact hainRel
  have haeq2:a=⟨⟨v, (f a).1⟩, a2⟩:=  by exact SetCoe.ext ha1eq

  have hbinRel:b.1∈ Rel.interedges H.Adj A B:= by exact coe_mem b
  have hb1eq:b.1=⟨v, (f b).1⟩:= by exact Prod.fst_eq_iff.mp (hvin (↑b) hbinRel)
  have b2:⟨v, (f b).1⟩∈  Rel.interedges H.Adj A B:= by rw[hb1eq.symm]; exact hbinRel
  have hbeq2:b=⟨⟨v, (f b).1⟩, b2⟩:=  by exact SetCoe.ext hb1eq

  have hfeq:(f a).1=(f b).1:= by exact congrArg Subtype.val hab
  rw [haeq2, hbeq2]
  exact Subtype.mk_eq_mk.mpr (congrArg (Prod.mk v) hfeq)

let Stype:={ x // x ∈ Rel.interedges H.Adj A B }
let S: Finset Stype:= Finset.univ
have hinj2: Set.InjOn f S:= by
  intro a _ c _ e
  exact hInj e
have cardineq:(Finset.image f S).card=  S.card:= by apply card_image_iff.2; exact hinj2
have scard:S.card =(Rel.interedges H.Adj A B).card:= by calc
  S.card =Fintype.card Stype:= by exact rfl
 _=(Rel.interedges H.Adj A B).card:=by exact  Fintype.card_coe (Rel.interedges H.Adj A B)
have imcard2:(Finset.image f S).card≤ Fintype.card  {x // x∈ N}:=by exact  card_le_univ (image f S)
have imcard3: Fintype.card  {x // x∈ N}=N.card:= by exact Fintype.card_coe N
have hcarddeg: (Rel.interedges H.Adj A B).card≤ H.degree v:= by calc
  (Rel.interedges H.Adj A B).card=S.card:= by exact id scard.symm
  _=(Finset.image f S).card:= by exact id cardineq.symm
  _≤ Fintype.card  {x // x∈ N}:= by exact imcard2
  _=N.card:= by exact imcard3
  _=H.degree v:= by exact Subgraph.finset_card_neighborSet_eq_degree


have _:k*(Rel.interedges H.Adj A B).card≥  H.verts.toFinset.card:= by exact hinteredges

calc
k*↑(H.degree v)≥ k*↑(Rel.interedges H.Adj A B).card:= by exact Nat.mul_le_mul_left k hcarddeg
_≥  ↑H.verts.toFinset.card:= by exact hinteredges
