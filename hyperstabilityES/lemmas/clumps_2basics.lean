--import MyProject

import hyperstabilityES.lemmas.clumps_connectedness
import hyperstabilityES.lemmas.clumps_connected2

 --import hyperstabilityES.lemmas.SimpleGraph

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
variable (mPositive: m >0)
variable (hPositive: h >0)
variable (prPositive: pr >0)
variable (iSub:Inhabited (Subgraph G))




def f_cont0 (H: Finset (Subgraph G)):
(Subgraph G)  → (Set (Subgraph G))
:= fun x=>  {y∈ H| x≤ y}

/-
def f_cont (H: Finset (Subgraph G)):
(Subgraph G)  → (Subgraph G)
:= fun x=> sSup (f_cont0 H x)
-/

noncomputable def f_cont (H: Finset (Subgraph G)):
(Subgraph G)  → (Subgraph G)
:= fun x=>
if h:Nonempty (f_cont0 H x) then h.some
  else sSup (f_cont0 H x)




lemma f_cont_M_contained_in_H
(H: Finset (Subgraph G))
(Mi Hi: Subgraph G)
(hHi: Hi∈ H)
(hM_in_H:   Mi≤ Hi)
: f_cont H Mi ∈ H ∧ Mi ≤ f_cont H Mi
:=by
--unfold f_cont

have h:Nonempty  (f_cont0 H Mi):=by
  refine nonempty_subtype.mpr ?_
  use Hi
  unfold f_cont0
  simp
  exact ⟨hHi, hM_in_H ⟩

have h1: (f_cont H Mi)=h.some:= by
  apply dif_pos h

have h2: (f_cont H Mi)∈ (f_cont0 H Mi):=by
  rw[h1]
  exact Subtype.coe_prop h.some

unfold f_cont0 at h2
simp at h2
exact h2



lemma f_cont_M_in_H
(H M: Finset (Subgraph G))
(MgraphsinH: Mgraphs_in_H M H)
:
(Finset.image (f_cont H) M)⊆  H:=by
refine image_subset_iff.mpr ?_
intro Mi hMi
have h1: ∃ (Hj:Subgraph G), (Hj∈ H)∧(Mi≤ Hj):=by
  exact MgraphsinH Mi hMi
rcases h1 with ⟨Hj, hHj ⟩

have h2: f_cont H Mi ∈ H ∧ Mi ≤ f_cont H Mi:= by
  exact f_cont_M_contained_in_H H Mi Hj hHj.1 hHj.2
exact h2.1

lemma M_subgraph_f_cont_M
(H M: Finset (Subgraph G))
(MgraphsinH: Mgraphs_in_H M H)
:
Mgraphs_in_H M (Finset.image (f_cont H) M):=by
unfold Mgraphs_in_H
intro Mi hMi
use (f_cont H Mi)

have h2: ∃ (Hj:Subgraph G), (Hj∈ H)∧(Mi≤ Hj):=by
  exact MgraphsinH Mi hMi
rcases h2 with ⟨Hj, hHj ⟩

constructor
exact mem_image_of_mem (f_cont H) hMi
have h1: f_cont H Mi ∈ H ∧ Mi ≤ f_cont H Mi:= by
  apply f_cont_M_contained_in_H
  exact hHj.1
  exact hHj.2


exact h1.2

/-
lemma f_cont_M_in_H
(H M: Finset (Subgraph G))
(MgraphsinH: Mgraphs_in_H M H)
:
Mgraphs_in_H  (Finset.image (f_cont H) M) H:=by
unfold Mgraphs_in_H
intro A hA
have h1: ∃ (Mi:Subgraph G), (Mi∈ M)∧((f_cont H Mi)=A):=by
  exact mem_image.mp hA
rcases h1 with ⟨Mi, hMi ⟩
use Mi
constructor

-/
/-
lemma im_f_cont_in_H
(H: Finset (Subgraph G))
(Mi Hi: Subgraph G)
(hHi: Hi∈ H)
(hM_in_H:   Mi≤ Hi)
(hHdisjoint: HEdge_Disjoint H)
: f_cont H Mi = Hi
:= by
have h1: Hi∈  f_cont0 H Mi:=by
  unfold f_cont0
  refine Set.mem_setOf.mpr ?_
  constructor
  exact hHi
  exact hM_in_H


have h1: f_cont0 H Mi⊆ {Hi}:=by
  unfold f_cont0
  refine Set.subset_singleton_iff.mpr ?_
  intro Y hY
  simp at hY

-/

/-
lemma H_smaller_than_M
(H M: Finset (Subgraph G))
(hM_in_H:  Mgraphs_in_H M H)
(hHdisjoint: HEdge_Disjoint H)
:
∃ (HM: Finset (Subgraph G)), H.card≥ M.card:=by
-/

lemma C_lower_bound_simplified
{K: Clump G p m κ pr h}
(mggpr: m≥ gg1 pr)
:  4*pr*K.C.verts.toFinset.card  ≥ m := by
have h1: K.C.verts.toFinset.card≥ m/pr:=by
  exact C_order_lower_bound
calc
4*pr*K.C.verts.toFinset.card
≥ 2*pr*K.C.verts.toFinset.card:=by
  gcongr
  exact Nat.AtLeastTwo.prop
_≥ 2*pr*(m/pr):= by
  gcongr
_≥ m:=by
  refine twice_times_fraction_ge m pr ?hb ?hm
  exact prPositive
  --m ≥ 2 * pr

  calc
   m≥10000 *pr^3:= by
      apply gg1_1 mggpr
      assumption
    _≥2*pr^1:= by
      gcongr
      simp
      exact prPositive
      simp
    _=2*pr:= by ring_nf
