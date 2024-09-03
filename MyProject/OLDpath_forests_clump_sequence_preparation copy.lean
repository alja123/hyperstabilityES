import MyProject

import MyProject.path_forests_join
import MyProject.long_path_forest

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 250000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable  [FinV: Fintype V]
variable  [DecG: DecidableRel G.Adj]
variable  [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}






def Path_forest_avoids!
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: Set V)
(k : ℕ )
:=
∀ (i: ℕ ), i< k→ (Disjoint {v:V|v∈ (Fo.P.get! i).Pa.Wa.support} Fb)




def cut_dense_list!
(HL: List (Subgraph G))
(p k: ℕ )
:=∀(i: ℕ ), (i<k)→  (cut_dense G  (HL.get! i) p)

def small_intersection_list!
(HL: List (Subgraph G))
(Fb: Set V)
(p m k: ℕ )
--(k: ℕ )
:=∀(i: ℕ ), (i<k)→
(8*p*
(Fb∩ (HL.get! i).verts).toFinset.card+(m +8*p*(2*(k)))≤ (HL.get! i).verts.toFinset.card
)


def Path_forest_long!
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(l k: ℕ )
:=
∀ (i: ℕ ), i< k→ (Fo.P.get! i).Pa.Wa.length≥ l


lemma sparse_family_monotone
(F F': Finset (Subgraph G))
(sparse: family_sparse  κ m F)
(contained: F'⊆ F)
:
family_sparse  κ m F'
:= by
intro A B h1 h2 h3
apply sparse
exact contained h1
exact contained h2
repeat assumption

lemma order_ge_m_family_monotone
(F F': Finset (Subgraph G))
(sparse: HOrder_ge_m_Family  F m)
(contained: F'⊆ F)
:
HOrder_ge_m_Family  F' m
:= by
intro A h1
apply sparse
exact contained h1
repeat assumption



lemma long_path_forest_specified_ends_simplified_altnum
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m p pr: ℕ )
(Fb: Set V)

(HL_sparse: family_sparse  κ m (HL.toFinset) )
(HL_order: HOrder_ge_m_Family (HL.toFinset) (m/pr))

(SinH: vertex_list_in_graph_list iV iSub S HL (k))---change
(EinH: vertex_list_in_graph_list iV iSub E HL (k))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length≥  k)
(Elength: E.length≥  k )
(HLlength: HL.length≥  k)


--(HLlength: HL.length> k)
(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL.get! i≤ H))

(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)
(HL_nodup: HL.Nodup)




(cutdense: cut_dense_list! iSub HL p (k))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard:
  ∀(i: ℕ ), (i<k)→
  (8*p*
  (Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))≤ (HL.get! i).verts.toFinset.card
  ))
--small_intersection_list!  iSub HL Fb p m (k))---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
(pPositive: p>0)
--(Fbcard: small_intersection_list  HL Fb p (m +8*p*(2*1*kmax)))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
(Fo.S= S.take k)
∧  (Fo.E=  E.take k)
∧ Fo.k=k
∧ Fo.P.length=k
--∧ Path_forest_avoids iV iSP Fo Fb
∧ Path_forest_avoids! iV iSP Fo Fb k---change
--∧ (Path_forest_support iV iSP Fo )⊆  41*p*k
--∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
--∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long  iV iSP Fo (m/(40*p))

∧ Fo.S.length=k
∧ Fo.E.length=k
--∧ Path_forest_in_HL iV iSub iSP HL Fo
:= by
sorry


lemma long_path_forest_specified_ends_simplified
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m p: ℕ )
(Fb: Set V)

(HL_sparse: family_sparse  κ m (HL.toFinset) )
(HL_order: HOrder_ge_m_Family (HL.toFinset) (m/pr))

(SinH: vertex_list_in_graph_list iV iSub S HL (k+1))---change
(EinH: vertex_list_in_graph_list iV iSub E HL (k+1))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k )
(HLlength: HL.length> k)


--(HLlength: HL.length> k)
(HL_in_H: ∀ (i: ℕ  ), i<k+1→  (HL.get! i≤ H))

(SoutsideFb: vertex_list_outside_set iV S Fb (k+1))
(EoutsideFb: vertex_list_outside_set iV E Fb (k+1))

(Snodup: S.Nodup)
(Enodup: E.Nodup)
(HL_nodup: HL.Nodup)




(cutdense: cut_dense_list! iSub HL p (k+1))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list!  iSub HL Fb p m (k+1))---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
(pPositive: p>0)
--(Fbcard: small_intersection_list  HL Fb p (m +8*p*(2*1*kmax)))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
(Fo.S= S.take k)
∧  (Fo.E=  E.take k)
∧ Fo.k=k
∧ Fo.P.length=k
--∧ Path_forest_avoids iV iSP Fo Fb
∧ Path_forest_avoids! iV iSP Fo Fb k---change
--∧ (Path_forest_support iV iSP Fo )⊆  41*p*k
--∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
--∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long  iV iSP Fo (m / pr / (40 * p))

∧ Fo.S.length=k
∧ Fo.E.length=k
--∧ Path_forest_in_HL iV iSub iSP HL Fo
:= by

--have Slength: S.length> k:=by exact Slen--rw [Slen]; exact lt_add_one k
--have Elength: E.length> k:= by exact Elen--rw [Elen]; exact lt_add_one k

--have  Smaxlength: S.length≤  k+1:= by exact Nat.le_of_eq Slen
--have Emaxlength: E.length≤  k+1:=by exact Nat.le_of_eq Elen


let HL':= List.take (k+1) HL
have HL'_length: HL'.length=k+1:= by
  exact List.length_take_of_le HLlength
let S':= List.take (k+1) S
have S'_length: S'.length=k+1:= by
  exact List.length_take_of_le Slength
let E':= List.take (k+1) E
have E'_length: E'.length=k+1:= by
  exact List.length_take_of_le Elength




have HLget: ∀ (i: ℕ ), (i<k+1)→ HL'.get! i= HL.get! i:= by
  intro i hi
  dsimp[HL']
  have hi1: i<(List.take (k + 1) HL).length:=by
    dsimp[HL'] at HL'_length
    rw[HL'_length]
    exact hi
  have hi2: i<HL.length:=by
    exact Nat.lt_of_lt_of_le hi HLlength
  have hte: (List.take (k + 1) HL).get ⟨ i, hi1⟩= HL.get ⟨ i, hi2⟩:= by
    refine List.IsPrefix.get_eq ?h hi1
    exact List.take_prefix (k + 1) HL
  have hte2: (List.take (k + 1) HL).get ⟨ i, hi1⟩= (List.take (k + 1) HL).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k + 1) HL) default hi1).symm
  have hte3:HL.get ⟨ i, hi2⟩= HL.get! i:= by
    simp
    exact (List.getD_eq_get HL default hi2).symm
  rw[hte2.symm, hte3.symm, hte]

have Sget: ∀ (i: ℕ ), (i<k+1)→ S'.get! i= S.get! i:= by
  intro i hi
  dsimp[S']
  have hi1: i<(List.take (k + 1) S).length:=by
    dsimp[S'] at S'_length
    rw[S'_length]
    exact hi
  have hi2: i<S.length:=by
    exact Nat.lt_of_lt_of_le hi Slength
  have hte: (List.take (k + 1) S).get ⟨ i, hi1⟩= S.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k + 1) S
  have hte2: (List.take (k + 1) S).get ⟨ i, hi1⟩= (List.take (k + 1) S).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k + 1) S) default hi1).symm
  have hte3:S.get ⟨ i, hi2⟩= S.get! i:= by
    simp
    exact (List.getD_eq_get S default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have Eget: ∀ (i: ℕ ), (i<k+1)→ E'.get! i= E.get! i:= by
  intro i hi
  dsimp[E']
  have hi1: i<(List.take (k + 1) E).length:=by
    dsimp[E'] at E'_length
    rw[E'_length]
    exact hi
  have hi2: i<E.length:=by
    exact Nat.lt_of_lt_of_le hi Elength
  have hte: (List.take (k + 1) E).get ⟨ i, hi1⟩= E.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k + 1) E
  have hte2: (List.take (k + 1) E).get ⟨ i, hi1⟩= (List.take (k + 1) E).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k + 1) E) default hi1).symm
  have hte3:E.get ⟨ i, hi2⟩= E.get! i:= by
    simp
    exact (List.getD_eq_get E default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have HLget2: ∀ (i: Fin (HL'.length) ),  HL'.get i=HL.get! i:= by
  intro i
  have h2: i.1<k+1:= by
    rw[HL'_length.symm]
    exact i.2

  have h1:HL'.get i=HL'.get! i:= by
    simp
    symm
    apply List.getD_eq_get
  rw[h1]
  rw[HLget i.1 h2]




have Esublist: E' ⊆ E:= by
  dsimp[E']
  exact List.take_subset (k + 1) E
have Ssublist:  S' ⊆ S:= by
  dsimp[S']
  exact List.take_subset (k + 1) S
have Hsublist:  HL' ⊆ HL:= by
  dsimp[HL']
  exact List.take_subset (k + 1) HL


have Esublist2: List.Sublist E' E  := by
  dsimp[E']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k + 1) E
have Ssublist2: List.Sublist S' S  := by
  dsimp[S']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k + 1) S
have HLsublist2: List.Sublist HL' HL  := by
  dsimp[HL']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k + 1) HL

have happly:_:= by
  apply long_path_forest_specified_ends iV iSub iSP H S' E' HL' k (k+1) --_ _ _ _ _ _ _ _ _ --Fb

  apply sparse_family_monotone
  exact HL_sparse
  intro x hx
  simp
  simp at hx
  exact Hsublist hx
  --exact HL_sparse. prove monoinicity
  apply order_ge_m_family_monotone
  exact HL_order
  intro x hx
  simp
  simp at hx
  exact Hsublist hx
  ---also for gem families


  --vertex_list_in_graph_list iV iSub S HL HL.length
  dsimp[HL', S']
  intro i hi
  have ilk: i<k+1:= by
    dsimp[HL'] at HL'_length
    rw[HL'_length] at hi
    exact hi
  rw[HLget i ilk]
  rw[Sget i ilk]
  apply SinH i ilk

  --vertex_list_in_graph_list iV iSub E' HL' HL'.length
  dsimp[HL', E']
  intro i hi
  have ilk: i<k+1:= by
    dsimp[HL'] at HL'_length
    rw[HL'_length] at hi
    exact hi
  rw[HLget i ilk]
  rw[Eget i ilk]
  apply EinH i ilk

  --S E disjoint
  apply List.disjoint_of_subset_left
  exact Ssublist
  apply List.disjoint_of_subset_right
  exact Esublist
  exact SE_Disjoint

  ---------lengths------
  rw[S'_length]; exact lt_add_one k
  rw[E'_length]; exact lt_add_one k
  rw[S'_length];
  rw[E'_length];
  rw[HL'_length]; exact lt_add_one k



  ----HL in H-----------
  intro i
  rw[HLget2 i]
  apply HL_in_H i
  calc
    _<HL'.length:= by exact i.2
    _=k+1:= by exact HL'_length


  exact List.Nodup.sublist HLsublist2 HL_nodup

  rw[HL'_length]
  intro i hi
  rw[Sget i]
  apply SoutsideFb
  exact hi
  exact hi

  rw[HL'_length]
  intro i hi
  rw[Eget i]
  apply EoutsideFb
  exact hi
  exact hi

  exact List.Nodup.sublist Ssublist2 Snodup
  exact List.Nodup.sublist Esublist2 Enodup

  exact Nat.le_add_right k 1
  intro i
  rw[HLget2]
  apply cutdense
  calc
    _<HL'.length:= by exact i.2
    _=k+1:= by exact HL'_length

  intro i
  rw[HLget2]
  sorry
  /-calc
    8 * p * (Fb ∩ (HL.get! ↑i).verts).toFinset.card
    + (m+8*p*(2*1*(k+1)))
    =
    8*p*
    (Fb∩ (HL.get! i).verts).toFinset.card+(m +8*p*(2*(k+1)))
    := by
      exact rfl
      --172 * p * p * (k + 1) ≤ m + 8 * p * (2 * (k + 1))

    _≤ (HL.get! i).verts.toFinset.card
    := by
      apply Fbcard i.1
      calc
        _<HL'.length:= by exact i.2
        _=k+1:= by exact HL'_length
    -/

  --m≥ 18*p
  sorry
  exact κPositive
  exact pPositive



rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh, hFoi⟩
let F:PathForest iV iSP H:= ⟨ S.take k, E.take k,  Fo.P, k, ?_, ?_, ?_, ?_, ?_⟩

use F

constructor
exact rfl--sorry --
constructor
dsimp[F]
constructor
exact rfl
constructor
exact hFod
constructor
intro i hi
apply hFoe
exact Nat.lt_of_lt_of_eq hi (id hFoc.symm)

constructor
intro i hi
apply hFoh
rw[hFoc]
exact hi

sorry

intro i hi
rw[hFoc.symm] at hi
rw[(Fo.Starts_equal i hi).symm]
rw[hFoa]
rw [Sget i]
rw[hFoc.symm]
sorry --exact Nat.lt_add_right 1 hi
sorry

intro i hi
rw[hFoc.symm] at hi
rw[(Fo.Ends_equal i hi).symm]
rw[hFob]
rw [Eget i]
rw[hFoc.symm]
sorry--
sorry
rw[hFoc.symm]
exact Fo.Graphs_equal

rw[hFoc.symm]
exact Fo.Paths_disjoint

exact hFod

    --







lemma path_forest_specified_ends_simplified_prefix
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m : ℕ )
(Fb: Set V)

(SinH: vertex_list_in_graph_list iV iSub S HL (k))---change
(EinH: vertex_list_in_graph_list iV iSub E HL (k-1))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length≥ k)
(Elength: E.length≥  k)
(HLlength: HL.length≥  k)



(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL.get! i≤ H))


(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)


(cutdense: cut_dense_list! iSub HL p (k))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list!  iSub HL Fb p m (k))---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S= S.take k
∧ Fo.E= E.take k
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids! iV iSP Fo Fb k---change
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
--∧ Path_forest_avoids! iV iSP Fo {v:V|v∈ (List.drop k S)} k---change
--∧ Path_forest_avoids!  iV iSP Fo {v:V|v∈ (List.drop k E)} k---change
∧ Fo.S.length=k
∧ Fo.E.length=k
:= by
sorry



lemma path_forest_specified_ends_simplified
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m : ℕ )
(Fb: Set V)

(SinH: vertex_list_in_graph_list iV iSub S HL (k+1))---change
(EinH: vertex_list_in_graph_list iV iSub E HL (k+1))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)
(HLlength: HL.length> k)



(HL_in_H: ∀ (i: ℕ  ), i<k+1→  (HL.get! i≤ H))


(SoutsideFb: vertex_list_outside_set iV S Fb (k+1))
(EoutsideFb: vertex_list_outside_set iV E Fb (k+1))

(Snodup: S.Nodup)
(Enodup: E.Nodup)


(cutdense: cut_dense_list! iSub HL p (k+1))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list!  iSub HL Fb p m (k+1))---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids! iV iSP Fo Fb k---change
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
--∧ Path_forest_avoids! iV iSP Fo {v:V|v∈ (List.drop k S)} k---change
--∧ Path_forest_avoids!  iV iSP Fo {v:V|v∈ (List.drop k E)} k---change
:= by



let HL':= List.take (k+1) HL
have HL'_length: HL'.length=k+1:= by
  exact List.length_take_of_le HLlength
let S':= List.take (k+1) S
have S'_length: S'.length=k+1:= by
  exact List.length_take_of_le Slength
let E':= List.take (k+1) E
have E'_length: E'.length=k+1:= by
  exact List.length_take_of_le Elength




have HLget: ∀ (i: ℕ ), (i<k+1)→ HL'.get! i= HL.get! i:= by
  intro i hi
  dsimp[HL']
  have hi1: i<(List.take (k + 1) HL).length:=by
    dsimp[HL'] at HL'_length
    rw[HL'_length]
    exact hi
  have hi2: i<HL.length:=by
    exact Nat.lt_of_lt_of_le hi HLlength
  have hte: (List.take (k + 1) HL).get ⟨ i, hi1⟩= HL.get ⟨ i, hi2⟩:= by
    refine List.IsPrefix.get_eq ?h hi1
    exact List.take_prefix (k + 1) HL
  have hte2: (List.take (k + 1) HL).get ⟨ i, hi1⟩= (List.take (k + 1) HL).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k + 1) HL) default hi1).symm
  have hte3:HL.get ⟨ i, hi2⟩= HL.get! i:= by
    simp
    exact (List.getD_eq_get HL default hi2).symm
  rw[hte2.symm, hte3.symm, hte]

have Sget: ∀ (i: ℕ ), (i<k+1)→ S'.get! i= S.get! i:= by
  intro i hi
  dsimp[S']
  have hi1: i<(List.take (k + 1) S).length:=by
    dsimp[S'] at S'_length
    rw[S'_length]
    exact hi
  have hi2: i<S.length:=by
    exact Nat.lt_of_lt_of_le hi Slength
  have hte: (List.take (k + 1) S).get ⟨ i, hi1⟩= S.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k + 1) S
  have hte2: (List.take (k + 1) S).get ⟨ i, hi1⟩= (List.take (k + 1) S).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k + 1) S) default hi1).symm
  have hte3:S.get ⟨ i, hi2⟩= S.get! i:= by
    simp
    exact (List.getD_eq_get S default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have Eget: ∀ (i: ℕ ), (i<k+1)→ E'.get! i= E.get! i:= by
  intro i hi
  dsimp[E']
  have hi1: i<(List.take (k + 1) E).length:=by
    dsimp[E'] at E'_length
    rw[E'_length]
    exact hi
  have hi2: i<E.length:=by
    exact Nat.lt_of_lt_of_le hi Elength
  have hte: (List.take (k + 1) E).get ⟨ i, hi1⟩= E.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k + 1) E
  have hte2: (List.take (k + 1) E).get ⟨ i, hi1⟩= (List.take (k + 1) E).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k + 1) E) default hi1).symm
  have hte3:E.get ⟨ i, hi2⟩= E.get! i:= by
    simp
    exact (List.getD_eq_get E default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have HLget2: ∀ (i: Fin (HL'.length) ),  HL'.get i=HL.get! i:= by
  intro i
  have h2: i.1<k+1:= by
    rw[HL'_length.symm]
    exact i.2

  have h1:HL'.get i=HL'.get! i:= by
    simp
    symm
    apply List.getD_eq_get
  rw[h1]
  rw[HLget i.1 h2]




have Esublist: E' ⊆ E:= by
  dsimp[E']
  exact List.take_subset (k + 1) E
have Ssublist:  S' ⊆ S:= by
  dsimp[S']
  exact List.take_subset (k + 1) S

have Esublist2: List.Sublist E' E  := by
  dsimp[E']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k + 1) E
have Ssublist2: List.Sublist S' S  := by
  dsimp[S']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k + 1) S

have happly:_:= by
  apply path_forest_specified_ends iV iSub iSP H S' E' HL' k (k+1) --_ _ _ _ _ _ _ _ _ --Fb

  --vertex_list_in_graph_list iV iSub S HL HL.length
  dsimp[HL', S']
  intro i hi
  have ilk: i<k+1:= by
    dsimp[HL'] at HL'_length
    rw[HL'_length] at hi
    exact hi
  rw[HLget i ilk]
  rw[Sget i ilk]
  apply SinH i ilk

  --vertex_list_in_graph_list iV iSub E' HL' HL'.length
  dsimp[HL', E']
  intro i hi
  have ilk: i<k+1:= by
    dsimp[HL'] at HL'_length
    rw[HL'_length] at hi
    exact hi
  rw[HLget i ilk]
  rw[Eget i ilk]
  apply EinH i ilk

  --S E disjoint
  apply List.disjoint_of_subset_left
  exact Ssublist
  apply List.disjoint_of_subset_right
  exact Esublist
  exact SE_Disjoint

  ---------lengths------
  rw[S'_length]; exact lt_add_one k
  rw[E'_length]; exact lt_add_one k
  rw[S'_length];
  rw[E'_length];
  rw[HL'_length]; exact lt_add_one k



  ----HL in H-----------
  intro i
  rw[HLget2 i]
  apply HL_in_H i
  calc
    _<HL'.length:= by exact i.2
    _=k+1:= by exact HL'_length



  rw[HL'_length]
  intro i hi
  rw[Sget i]
  apply SoutsideFb
  exact hi
  exact hi

  rw[HL'_length]
  intro i hi
  rw[Eget i]
  apply EoutsideFb
  exact hi
  exact hi

  exact List.Nodup.sublist Ssublist2 Snodup
  exact List.Nodup.sublist Esublist2 Enodup

  exact Nat.le_add_right k 1
  intro i
  rw[HLget2]
  apply cutdense
  calc
    _<HL'.length:= by exact i.2
    _=k+1:= by exact HL'_length

  intro i
  rw[HLget2]
  calc
    8 * p * (Fb ∩ (HL.get! ↑i).verts).toFinset.card
    + 172 * p * p * (k + 1)
    ≤
    8*p*
    (Fb∩ (HL.get! i).verts).toFinset.card+(m +8*p*(2*(k+1)))
    := by
      gcongr
      --172 * p * p * (k + 1) ≤ m + 8 * p * (2 * (k + 1))
      sorry
    _≤ (HL.get! i).verts.toFinset.card
    := by
      apply Fbcard i.1
      calc
        _<HL'.length:= by exact i.2
        _=k+1:= by exact HL'_length

  exact pPositive

rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh⟩
let F:PathForest iV iSP H:= ⟨S, E,  Fo.P, k, ?_, ?_, ?_, ?_, ?_⟩

use F

constructor
exact rfl
constructor
exact rfl
constructor
exact rfl
constructor
exact hFod
constructor
intro i hi
apply hFoe
exact Nat.lt_of_lt_of_eq hi (id hFoc.symm)
exact hFof

intro i hi
rw[hFoc.symm] at hi
rw[(Fo.Starts_equal i hi).symm]
rw[hFoa]
rw [Sget i]
rw[hFoc.symm]
exact Nat.lt_add_right 1 hi

intro i hi
rw[hFoc.symm] at hi
rw[(Fo.Ends_equal i hi).symm]
rw[hFob]
rw [Eget i]
rw[hFoc.symm]
exact Nat.lt_add_right 1 hi

rw[hFoc.symm]
exact Fo.Graphs_equal

rw[hFoc.symm]
exact Fo.Paths_disjoint

exact hFod

    --



/-
structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  (Paths_disjoint: paths_disjoint iSP  P k)  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))
  (P_length: P.length=k)-/

--def Path_forest_long
--{H: Subgraph G}
--(Fo: PathForest iV iSP H)
--(l: ℕ )
--:=
--∀ (i: ℕ ), i< Fo.k→ (Fo.P.get! i).Pa.Wa.length≥ l

/-OLD::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
lemma long_path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(HL_sparse: family_sparse  κ m (HL.toFinset) )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (172*p*p*kmax))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long  iV iSP Fo (m/40*p)
:= by
--#check clump_path_sequence_gives_path
sorry



NEW::::::::::::::::::::::::::::::::::::::::::::::::
lemma long_path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(HL_sparse: family_sparse  κ m (HL.toFinset) )
(HL_order: HOrder_ge_m_Family (HL.toFinset) (2*m))

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)
(HL_nodup: HL.Nodup)
(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (m +8*p*(2*1*kmax)))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
--∧ (Path_forest_support iV iSP Fo )⊆  41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long  iV iSP Fo (m/(40*p))
∧ Path_forest_in_HL iV iSub iSP HL Fo
:= by

-/

lemma finset_disjoint_left
(v: V)
(T S: Finset V)
(disj: Disjoint S T)
(hv: v∈ S)
:
v∉ T:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine not_disjoint_iff.mpr ?_
  use v
exact h2 disj

lemma finset_disjoint_right
(v: V)
(S T: Finset V)
(disj: Disjoint S T)
(hv: v∈ T)
:
v∉ S:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine not_disjoint_iff.mpr ?_
  use v
exact h2 disj


lemma finset_disjoint_left_list
(v: V)
(T: List V)
(S: Finset V)
(disj: Disjoint S T.toFinset)
(hv: v∈ S)
:
v∉ T:= by
have h1: v∉ T.toFinset:= by exact   finset_disjoint_right v T.toFinset S (id (Disjoint.symm disj)) hv
by_contra cont
have h2: v∈ T.toFinset:= by exact List.mem_toFinset.mpr cont
exact h1 h2


lemma finset_disjoint_right_list
(v: V)
(T: List V)
(S: Finset V)
(disj: Disjoint T.toFinset S )
(hv: v∈ S)
:
v∉ T:= by
have h1: v∉ T.toFinset:= by exact finset_disjoint_right v T.toFinset S disj hv
by_contra cont
have h2: v∈ T.toFinset:= by exact List.mem_toFinset.mpr cont
exact h1 h2



lemma find_pairs_in_M_list
(Ord: List (Clump G p m κ pr h))
(Ver: List V)
(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)--possibly just subgraph list??
(k: ℕ )
(LM_length: LM.length≥ k)
(Ord_length: Ord.length≥ k)
(hk: 2*k+Ver.length+2≤ m/pr)
:
∃ (S E: List V),
(S.length=k)
∧ (E.length=k)
∧ (List.Disjoint S E)
∧ (List.Disjoint Ver S )
∧ (List.Disjoint E Ver )
∧ (S.Nodup)
∧ (E.Nodup)
∧ (∀ (i: ℕ ), i<k→ (S.get! i)∈ (LM.get! i).verts)
∧ (∀ (i: ℕ ), i<k→ (E.get! i)∈ (LM.get! i).verts)
:= by
induction' k with k IH
use []
use []
constructor
exact rfl
constructor
exact rfl
constructor
exact List.disjoint_nil_left []
constructor
exact List.disjoint_nil_right Ver
constructor
exact List.disjoint_nil_left Ver
constructor
exact List.nodup_nil
constructor
exact List.nodup_nil
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi

-----------induction-------------

have LM_length': LM.length≥ k:= by
  exact Nat.le_of_succ_le LM_length
have Ord_length': Ord.length≥ k:= by
  exact Nat.le_of_succ_le Ord_length
have hk': 2 * k + Ver.length + 2 ≤ m / pr:= by
  calc
     2 * k + Ver.length + 2
     ≤2 * (k+1) + Ver.length + 2:= by
        gcongr
        exact Nat.le_add_right k 1
     _≤ m / pr:= by exact hk

have ind: _:= by exact IH LM_length' Ord_length' hk'

rcases ind with ⟨S, ind2 ⟩
rcases ind2 with ⟨E, Sl, El, SEd, VSd, EVd, Snd, End, Sget, Eget ⟩


have hkl: k<Ord.length:= by exact Ord_length
have hkm: k<LM.length:= by exact LM_length

have MinOrd:LM.get! k ∈ (Ord.get! k).M:= by
  unfold M_list_in_clump_list at LM_in_M
  have h2:_:= by exact  LM_in_M k  hkl
  simp at h2
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h2
  exact h2



have hcutdense:   near_regular (LM.get! k) m pr:= by
  apply (Ord.get! k).M_Near_Regular
  exact MinOrd
  --apply LM_in_M k MinOrd

have hcard:    (LM.get! k).verts.toFinset.card≥ m/pr:= by
  exact M_order_lower_bound MinOrd

have diff:  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)).card≥ 2:= by
  calc
    ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)).card
    ≥
    (LM.get! k).verts.toFinset.card
    -(S.toFinset∪ E.toFinset∪ Ver.toFinset).card:= by
      exact le_card_sdiff (S.toFinset ∪ E.toFinset ∪ Ver.toFinset) (LM.get! k).verts.toFinset
    _≥  (LM.get! k).verts.toFinset.card
    -(S.toFinset.card+ E.toFinset.card+ Ver.toFinset.card):= by
      gcongr
      exact card_union_3 S.toFinset E.toFinset Ver.toFinset
    _≥ (m/pr) -((k+1)+(k+1) + Ver.length):= by
      gcongr
      calc
        S.toFinset.card
        ≤ S.length:= by exact List.toFinset_card_le S
        _= k := by exact Sl
        _≤ k+1:= by exact Nat.le_add_right k 1
      calc
        E.toFinset.card
        ≤ E.length:= by exact List.toFinset_card_le E
        _= k := by exact El
        _≤ k+1:= by exact Nat.le_add_right k 1
      exact List.toFinset_card_le Ver
    _= m/pr- (2*(k+1)+Ver.length):= by ring_nf
    _≥ 2:= by exact Nat.le_sub_of_add_le' hk

have hex: ∃ ( T: Finset V), T⊆ ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset))∧ T.card=2:= by
  exact
    exists_smaller_set ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset)) 2
      diff
rcases hex with ⟨T, hT1, hT2⟩
rw [@card_eq_two] at hT2
rcases hT2 with ⟨s, e, hse1, hse2 ⟩
have sinT: s∈ T:= by rw[hse2]; exact mem_insert_self s {e}
have einT: e∈ T:= by rw[hse2]; simp


have sin2: s∈ ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  exact hT1 sinT
have ein2: e∈ ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  exact hT1 einT

have Tsubs: (LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset)⊆  (LM.get! k).verts.toFinset:= by
  exact sdiff_subset (LM.get! k).verts.toFinset (S.toFinset ∪ E.toFinset ∪ Ver.toFinset)
have  sin3: s∈ (LM.get! k).verts.toFinset:= by
  exact Tsubs (hT1 sinT)
have  ein3: e∈ (LM.get! k).verts.toFinset:= by
  exact Tsubs (hT1 einT)

have Sint2: Disjoint S.toFinset  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  --refine disjoint_iff_inter_eq_empty.mp ?_
  simp
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  simp at ha
  intro h5 h6 h7
  exfalso
  exact h6 ha


have Sint3: Disjoint E.toFinset  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  --refine disjoint_iff_inter_eq_empty.mp ?_
  simp
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  simp at ha
  intro h5 h6 h7
  exfalso
  exact h7 ha

have Sint4: Disjoint Ver.toFinset  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  --refine disjoint_iff_inter_eq_empty.mp ?_
  simp
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  simp at ha
  intro h5 h6 h7
  exact ha


let S':List V:= S++[s]
let E':List V:= E++[e]
use S'
use E'
--Slength
constructor
dsimp[S']
simp
exact Sl
--Elength
constructor
dsimp[E']
simp
exact El
--Disjointness SE
constructor
dsimp[S', E']
simp
constructor
constructor
exact SEd

exact
  finset_disjoint_left_list s E
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint3)) (hT1 sinT)
constructor
exact
  finset_disjoint_left_list e S
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint2)) (hT1 einT)

exact id (Ne.symm hse1)
constructor
---disjointness S Ver
dsimp[S']
simp
constructor
exact VSd

exact
  finset_disjoint_left_list s Ver
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint4)) (hT1 sinT)

constructor
---disjointness E Ver
dsimp[E']
simp
constructor
exact EVd

exact
  finset_disjoint_left_list e Ver
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint4)) (hT1 einT)

constructor
--S'nodup---
dsimp[S']
refine
  List.Nodup.append Snd ?h.right.right.right.right.right.left.d₂
    ?h.right.right.right.right.right.left.dj
exact List.nodup_singleton s
simp
exact
  finset_disjoint_left_list s S
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint2)) (hT1 sinT)


constructor
--E'nodup---
dsimp[E']
refine List.nodup_middle.mpr ?h.right.right.right.right.right.right.left.a
simp
constructor
exact
  finset_disjoint_left_list e E
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint3)) (hT1 einT)

exact End
--in graphs
constructor
dsimp[S']
intro i hi
by_cases case: i<k
have h1: (S ++ [s]).get! i =S.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id Sl.symm)
rw[h1]
apply   Sget i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (S ++ [s]).get! k =[s].get! (k-S.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right S [s] default k
  exact Nat.le_of_eq Sl
rw[Sl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
simp only [Set.mem_toFinset] at sin3
exact sin3


dsimp[E']
intro i hi
--simp
by_cases case: i<k
have h1: (E ++ [e]).get! i =E.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id El.symm)
rw[h1]
apply   Eget i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (E ++ [e]).get! k =[e].get! (k-E.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right E [e] default k
  exact Nat.le_of_eq El
rw[El] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
simp only [Set.mem_toFinset] at ein3
exact ein3




lemma add_Ver_to_M_list
(H: Subgraph G)
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)

(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k)
(Ord_length: Ord.length> k)
(Ver_length: Ver.length> k)
(S_length: S.length> k)
:
∃ (HL: List  (Subgraph G)),
(HL.length=k)
∧ (cut_dense_list! iSub HL γ k)
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! i).verts)
∧ (∀ (i: ℕ ), i<k→ (S.get! i)∈ (HL.get! i).verts)
∧ (∀ (i: ℕ ), i<k→ (HL.get! i)≤ H)


:= by
unfold Vertex_list_in_clump_list_BSetPlusM at VerInOrd


induction' k with k IH
use []
constructor
exact rfl
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi

sorry
-----------induction-------------


have LM_length': LM.length> k:= by
  exact Nat.lt_of_succ_lt LM_length
have Ord_length': Ord.length> k:= by
  exact Nat.lt_of_succ_lt Ord_length
have Ver_length': Ver.length> k:= by
  exact Nat.lt_of_succ_lt Ver_length
have S_length': S.length> k:= by
  exact Nat.lt_of_succ_lt S_length
have hSinLM: ∀ i < k, S.get! i ∈ (LM.get! i).verts:= by
  intro i hi
  apply hSML i
  exact Nat.lt_add_right 1 hi
have ind: _:= by exact IH hSinLM LM_length' Ord_length' Ver_length' S_length'

rcases ind with ⟨HL, HLl, Hcd,VerHL,SHL, InH  ⟩


have hkl: k<Ord.length:= by exact Ord_length'
have hkm: k<LM.length:= by exact LM_length'




have MinOrd:LM.get! k ∈ (Ord.get! k).M:= by
  unfold M_list_in_clump_list at LM_in_M
  have h2:_:= by exact  LM_in_M k  hkl
  simp at h2
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h2
  exact h2


have MinOrd:Ver.get! k ∈  BSetPlusM (Ord.get! k) ∩ BSetPlusM (Ord.get! (k + 1)):= by
  apply VerInOrd
  exact Nat.lt_sub_of_add_lt Ord_length
have MinOrd2:Ver.get! k ∈  BSetPlusM (Ord.get! k):= by
  exact Set.mem_of_mem_inter_left MinOrd

have Hi_ex: ∃ (Hi: Subgraph G), Hi∈  (Ord.get! k).H ∧ Ver.get! k∈ Hi.verts:= by
  sorry
rcases Hi_ex with ⟨Hi, hHi, hVerHi⟩


let K:Subgraph G:= (Ord.get! k).C ⊔Hi
have Kcut_dense: cut_dense G K γ:= by
  apply clump_add_Hi_cut_dense
  exact mPositive
  exact pPositive
  exact κPositive
  exact iSub
  --γ ≥ 16 * κ ^ (2 * (100 * (Ord.get! k).k).factorial)
  sorry
  exact hHi
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry


let HL':List (Subgraph G):= HL++[K]
use HL'

constructor
dsimp[HL']
simp
exact HLl


-----cutdense
constructor
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
apply   Hcd i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
exact Kcut_dense

constructor
----Ver in HL
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact VerHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]
exact Set.mem_union_right (Ord.get! k).C.verts hVerHi

----S in HL
constructor
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact SHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]

have hSinMM: S.get! k ∈(LM.get! k).verts:= by
  apply hSML k
  exact lt_add_one k

unfold M_list_in_clump_list at LM_in_M
have hMM: LM.get! k ∈ (Ord.get! k).M:= by
  have h55:_:=by
    apply LM_in_M k
    exact Ord_length'
  simp at h55
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h55
  exact h55
have In_C:(LM.get! k).verts⊆ (Ord.get! k).C.verts:= by
  sorry
exact Set.mem_union_left Hi.verts (In_C hSinMM)

sorry
--exact Set.mem_union_right (Ord.get! k).C.verts hVerHi




lemma set_disjoint_to_tail_disjoint
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1}⊆ Fb)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j))
:= by

intro i j hi hj
unfold tail_disjoint_imp

apply Fb_disj_to_tail_disj

exact (F2.P.get! j).Pa.Wa_Is_Path
calc
  {v | v ∈ (F1.P.get! i).Pa.Wa.support} \ {(F2.P.get! j).s}
  ⊆ {v | v ∈ (F1.P.get! i).Pa.Wa.support} := by
    exact Set.diff_subset {v | v ∈ (F1.P.get! i).Pa.Wa.support} {(F2.P.get! j).s}
  _⊆ {v:V| v∈ Path_forest_support iV iSP F1}:= by
    simp
    unfold Path_forest_support
    simp
    intro a ha
    have h78:F1.P.get! i ∈ F1.P:= by
      simp
      have h2: F1.P.getD i default=F1.P.get ⟨ i,_⟩:= by
        refine List.getD_eq_get F1.P default ?_
        rw[F1.P_length ]
        exact Nat.lt_of_lt_of_le hi F1k
      rw[h2]
      exact
        List.get_mem F1.P i
          (Eq.mpr (id (congrArg (fun _a ↦ i < _a) F1.P_length)) (Nat.lt_of_lt_of_le hi F1k))
    use F1.P.get! i
  _⊆ Fb:= by
    exact F1_in_Fb

apply F2_avoids_Fb
exact hj




lemma single_path_forest_tail_disjoint
(F1 : PathForest iV iSP H)
(k: ℕ )
(F1k: F1.k≥ k)
:
( ∀(i j: ℕ ), (i< j)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
:= by
intro i j hi hj
have hpathsdisjoint:_:=by exact F1.Paths_disjoint
unfold paths_disjoint at hpathsdisjoint
unfold tail_disjoint_imp
have hj': j<F1.k:= by
  exact Nat.lt_of_lt_of_le hj F1k
have h2:_:= by exact hpathsdisjoint i j hi hj'
simp at h2
intro x hx hx2
have hh2: x∈ {v | v ∈ (F1.P.get! j).Pa.Wa.support}:= by
  simp
  exact List.mem_of_mem_tail hx2
have hh3: x∈ {v | v ∈ (F1.P.get! i).Pa.Wa.support}:= by
  simp
  exact hx
have neg: ¬ (Disjoint {v | v ∈ (F1.P.get! i).Pa.Wa.support} {v | v ∈ (F1.P.get! j).Pa.Wa.support}):= by
  refine Set.Nonempty.not_disjoint ?_
  refine Set.inter_nonempty.mpr ?_
  use x
exact neg (hpathsdisjoint i j hi hj')























lemma add_Ver_to_M_list_starts
(H: Subgraph G)
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)

(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k+1→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k+1)
(Ord_length: Ord.length> k+1)
(Ver_length: Ver.length> k)
(S_length: S.length> k+1)
:
∃ (HL: List  (Subgraph G)),
(HL.length=k+1)
∧ (cut_dense_list! iSub HL γ (k+1))
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! (i+1)).verts)
∧ (∀ (i: ℕ ), i<k+1→ (S.get! (i))∈ (HL.get! i).verts)
∧ (∀ i < k + 1, HL.get! i ≤ H)--need to add extra assumptions for this

:= by
unfold Vertex_list_in_clump_list_BSetPlusM at VerInOrd


induction' k with k IH
let K:Subgraph G:= (Ord.get! 0).C
use [K]
constructor
exact rfl
constructor
intro i hi
--cutdense
sorry
constructor
intro i hi

sorry
sorry
-----------induction-------------

have LM_length'': LM.length> k+1:= by
  exact Nat.lt_of_succ_lt LM_length
have LM_length': LM.length> k:= by
  exact Nat.lt_of_succ_lt LM_length''
have Ord_length'': Ord.length> k+1:= by
  exact Nat.lt_of_succ_lt Ord_length
have Ord_length': Ord.length> k:= by
  exact Nat.lt_of_succ_lt Ord_length''
have Ver_length': Ver.length> k:= by
  exact Nat.lt_of_succ_lt Ver_length
have S_length'': S.length> k+1:= by
  exact Nat.lt_of_succ_lt S_length
have S_length': S.length> k:= by
  exact Nat.lt_of_succ_lt S_length''
have hSinLM: ∀ i < k+1, S.get! (i) ∈ (LM.get! i).verts:= by
  intro i hi
  apply hSML i
  exact Nat.lt_add_right 1 hi
have ind: _:= by exact IH hSinLM LM_length'' Ord_length'' Ver_length' S_length''

rcases ind with ⟨HL, HLl, Hcd,VerHL,SHL , InH ⟩


have hkl: k<Ord.length:= by exact Ord_length'
have hkm: k<LM.length:= by exact LM_length'
have hkm': k+1<LM.length:= by exact LM_length''




have MinOrd:LM.get! k ∈ (Ord.get! k).M:= by
  unfold M_list_in_clump_list at LM_in_M
  have h2:_:= by exact  LM_in_M k  hkl
  simp at h2
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h2
  exact h2


have MinOrd:Ver.get! k ∈  BSetPlusM (Ord.get! k) ∩ BSetPlusM (Ord.get! (k + 1)):= by
  apply VerInOrd
  exact Nat.lt_sub_of_add_lt Ord_length''
have MinOrd2:Ver.get! k ∈  BSetPlusM (Ord.get! (k+1)):= by
  exact Set.mem_of_mem_inter_right MinOrd

have Hi_ex: ∃ (Hi: Subgraph G), Hi∈  (Ord.get! (k+1)).H ∧ Ver.get! k∈ Hi.verts:= by
  sorry
rcases Hi_ex with ⟨Hi, hHi, hVerHi⟩


let K:Subgraph G:= (Ord.get! (k+1)).C ⊔Hi
have Kcut_dense: cut_dense G K γ:= by
  apply clump_add_Hi_cut_dense
  exact mPositive
  exact pPositive
  exact κPositive
  --γ ≥ 16 * κ ^ (2 * (100 * (Ord.get! k).k).factorial)
  exact iSub
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

let HL':List (Subgraph G):= HL++[K]
use HL'

constructor
dsimp[HL']
simp
exact HLl


-----cutdense
constructor
dsimp[HL']
intro i hi
by_cases case: i<k+1
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
apply   Hcd i case

have hi2: i=k+1:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! (k+1) =[K].get! ((k+1)-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default (k+1)
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
exact Kcut_dense

constructor
----Ver in HL
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! (i+1) =HL.get! (i+1) := by
  simp
  apply List.getD_append
  calc
    i+1 < k+1:= by
      exact Nat.add_lt_add_right case 1
    _= HL.length:= by
      exact HLl.symm
rw[h1]
exact VerHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! (k+1) =[K].get! ((k+1)-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default (k+1)
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]
exact Set.mem_union_right (Ord.get! (k + 1)).C.verts hVerHi

----S in HL
constructor
dsimp[HL']
intro i hi
by_cases case: i<k+1
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact SHL i case

have hi2: i=k+1:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! (k+1) =[K].get! ((k+1)-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default (k+1)
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]

have hSinMM: S.get! (k+1) ∈(LM.get! (k+1)).verts:= by
  apply hSML (k+1)
  exact lt_add_one (k + 1)

unfold M_list_in_clump_list at LM_in_M
have hMM: LM.get! (k + 1) ∈ (Ord.get! (k + 1)).M:= by
  have h55:_:=by
    apply LM_in_M (k + 1)
    exact Ord_length''
  simp at h55
  simp
  have h3: LM.getD (k + 1) default=LM.get ⟨(k + 1), hkm' ⟩:= by
    exact List.getD_eq_get LM default hkm'
  have h4: LM.getD (k + 1) ⊥=LM.get ⟨(k + 1), hkm' ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm'
  rw[h3]
  rw[h4] at h55
  exact h55
have In_C:(LM.get! (k + 1)).verts⊆ (Ord.get! (k + 1)).C.verts:= by
  sorry
exact Set.mem_union_left Hi.verts (In_C hSinMM)
--in H
sorry






lemma add_Ver_to_M_list_starts_alt
(H: Subgraph G)
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)
(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k+1+1→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k+1+1)
(Ord_length: Ord.length> k+1+1)
(Ver_length: Ver.length> k+1)
(S_length: S.length> k+1+1)
:
∃ (HL: List  (Subgraph G)),
(HL.length=k)
∧ (cut_dense_list! iSub HL γ (k))
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! (i)).verts)
∧ (∀ (i: ℕ ), i<k→ (S.tail.get! (i))∈ (HL.get! i).verts)
∧ (∀ i < k , HL.get! i ≤ H)

:=by
have hex:_:= by
  apply add_Ver_to_M_list_starts _  _ iSub  H Ord Ver S LM LM_in_M VerInOrd (k+1) _ LM_length Ord_length Ver_length S_length
  use γ
  exact κPositive
  exact pPositive
  exact mPositive
  exact hSML




rcases hex with ⟨HL, HLl, Hcd,VerHL,SHL , InH ⟩
use HL.tail

have htail_get: ∀ i < k, (HL.tail).get! i = HL.get! (i+1):= by
  intro i hi
  simp
  sorry
have stail_get: ∀ i < k, (S.tail).get! i = S.get! (i+1):= by
  intro i hi
  simp
  sorry

constructor
sorry
constructor
intro i hi
rw[htail_get i hi]
apply Hcd
simp
exact Nat.lt_add_right 1 hi

constructor
intro i hi
rw[htail_get i hi]
apply VerHL
exact Nat.lt_add_right 1 hi

constructor
intro i hi
rw[htail_get i hi]
rw[stail_get i hi]
apply SHL (i+1)
simp
exact Nat.lt_add_right 1 hi

sorry






lemma set_disjoint_left
(v: V)
(T S: Set V)
(disj: Disjoint S T)
(hv: v∈ S)
:
v∉ T:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine Set.not_disjoint_iff.mpr ?_
  use v
exact h2 disj

lemma set_disjoint_right
(v: V)
(S T: Set V)
(disj: Disjoint S T)
(hv: v∈ T)
:
v∉ S:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine Set.not_disjoint_iff.mpr ?_
  use v
exact h2 disj



lemma path_forest_support_iff
(F1: PathForest iV iSP H)
(x: V)
:
x∈  {v | ∃ Pi ∈ F1.P, v ∈ Pi.Pa.Wa.support}
↔
∃  (i :ℕ ), i< F1.P.length ∧  x∈  {v | v ∈ (F1.P.get! i).Pa.Wa.support}
:= by
constructor
intro h
simp at h
simp
rcases h with ⟨Pi, hPi, hx⟩
have hjex: ∃ (j: Fin (F1.P.length)), F1.P.get j=Pi:= by
  exact List.mem_iff_get.mp hPi
rcases hjex with ⟨j, hj⟩
use j
constructor
exact j.isLt
have h4: F1.P.get! ↑j=F1.P.get j:= by
  simp
  apply List.getD_eq_get
rw[h4]
rw[hj]
exact hx

intro h
simp at h
simp
rcases h with ⟨i, hi, hx⟩
use (F1.P.get! i)
constructor
have h4: F1.P.getD i default=F1.P.get ⟨i, ?_⟩ := by
  apply List.getD_eq_get
simp
rw[h4]
refine List.get_mem F1.P i ?h.left.refine_1
exact hi
exact hx



lemma path_forest_support_iff_neg
(F1: PathForest iV iSP H)
(x: V)
:
x∉   {v | ∃ Pi ∈ F1.P, v ∈ Pi.Pa.Wa.support}
↔
∀   (i :ℕ ), i< F1.P.length →   x∉   {v | v ∈ (F1.P.get! i).Pa.Wa.support}
:= by
have h1:_:=by exact path_forest_support_iff iV iSP F1 x
by_contra cont
simp at cont
push_neg at cont
simp at h1
simp_all only [gt_iff_lt]
unhygienic
  aesop_cases
    cont
· simp_all only [iff_true]
  unhygienic
    with_reducible
      aesop_destruct_products
  simp_all only
· simp_all only [iff_true]
  unhygienic
    with_reducible
      aesop_destruct_products
  simp_all only

/-lemma Fb_disj_to_tail_disj
(Fb: Set V)
{a b c d:V}
(P: Walk G a b)
(Q: Walk G c d)
(QIsPath: Q.IsPath)
(hFb: {v:V|v∈ P.support}\ {c}⊆ Fb)
(disj: Disjoint {v:V|v∈ Q.support}  Fb)
:
P.support.Disjoint Q.support.tail-/



/-( hdisj11: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
( hdisj22: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)))
( hdisj33: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)))
( hdisj12: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)))
( hdisj21: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)))
( hdisj13: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)))
( hdisj31: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F1.P.get! j)))
( hdisj23: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)))
( hdisj32: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)))

-/


/-
lemma clump_path_sequence_gives_path
(H: Subgraph G)
(KFam: Finset (Clump G p m κ pr h))
(Seq: ClumpPathSequence iI iV α KFam)
(k: ℕ )
:
Has_length_d_path (Clump_Family_Union KFam) (h*m)
:=by


have ex_pairs: _:= by
  apply find_pairs_in_M_list iI iV iSub Seq.Ord Seq.Ver Seq.LM Seq.LM_in_M k

have ex_HS:_:=by
  apply add_Ver_to_M_list iI iV iSub Seq.Ord Seq.Ver Seq.LM Seq.LM_in_M k

have ex_HE:_:=by
  apply add_Ver_to_M_list iI iV iSub Seq.Ord Seq.Ver.tail Seq.LM Seq.LM_in_M k


rcases ex_pairs with ⟨S, E, hS, hE, hSE, hSVer, hEVer, hSNoDup, hENoDup, hSInLM, hEInLM⟩
rcases ex_HS with ⟨HS, hHS, hcutdenseS, hLMS, hVerS, Ver_in_HS⟩
rcases ex_HE with ⟨HE, hHE, hcutdenseE, hLME, hVerE, Ver_in_HL⟩




have SinH: vertex_list_in_graph_list iV iSub S HS HS.length:= by
  sorry

have EinH: vertex_list_in_graph_list iV iSub E HE HE.length:= by
  sorry

have VerinHS: vertex_list_in_graph_list iV iSub Seq.Ver HS HS.length:= by
  sorry--This should match lemma earlier--no?
have VerinHE: vertex_list_in_graph_list iV iSub Seq.Ver HE HE.length:= by
  sorry--This should match lemma earlier



have HS_in_H: ∀ (i: Fin (HS.length) ), (HS.get i≤ H):= by
  sorry

have HE_in_H: ∀ (i: Fin (HE.length) ), (HE.get i≤ H):= by
  sorry


have LM_cut_dense:  cut_dense_list  Seq.LM κ:= by
  sorry
have LM_in_H: ∀ (i: Fin (Seq.LM.length) ), (Seq.LM.get i≤ H):= by
  sorry
have SinLM: vertex_list_in_graph_list iV iSub S Seq.LM Seq.LM.length:= by
  sorry
have EinLM: vertex_list_in_graph_list iV iSub E Seq.LM Seq.LM.length:= by
  sorry

let Fb: Set V:= {v: V|v∈ E}

have SoutsideFb: vertex_list_outside_set iV S Fb (HS.length):= by
  sorry
have Ver_EoutsideFb: vertex_list_outside_set iV Seq.Ver Fb (HS.length):= by
  sorry

have Fbcard: small_intersection_list  HS Fb κ (172*κ*κ*k):= by
  sorry

have VerNoDup: Seq.Ver.Nodup:= by
  exact Seq.VerNoDup

have klek: k≤ k:= by
  exact Nat.le_refl k



have hF1Ex: _:= by
  apply path_forest_specified_ends iV iSub iSP H Seq.Ver S HS  k k _ _ _ _ _ _ _ _ _ Fb
  repeat assumption
  --
  sorry; sorry; sorry; sorry; sorry; assumption

rcases hF1Ex with ⟨F1, hF1a, hF1b, hF1c, hF1d, hF1e, hF1f, hF1g, hF1h⟩


let Fb2: Set V:= {v: V|v∈ S}∪ {v:V| v∈ Path_forest_support iV iSP F1}

have SoutsideFb: vertex_list_outside_set iV E Fb2 (HE.length):= by
  sorry
have Ver_EoutsideFb: vertex_list_outside_set iV Seq.Ver Fb2 (HE.length):= by
  sorry

have Fbcard: small_intersection_list  HE Fb2 κ (172*κ*κ*k):= by
  sorry


have hF2Ex: _:= by
  apply path_forest_specified_ends iV iSub iSP H E Seq.Ver HE  k k _ _ _ _ _ _ _ _ _ Fb2
  repeat assumption
  --
  sorry; sorry; sorry; sorry; sorry; assumption

rcases hF2Ex with ⟨ F2, hF2a , hF2b, hF2c, hF2d, hF2e, hF2f, hF2g, hF2h⟩


let Fb3: Set V:=  {v:V| v∈ Path_forest_support iV iSP F1}∪ {v:V| v∈ Path_forest_support iV iSP F2}

have SoutsideFb: vertex_list_outside_set iV S Fb3 (Seq.LM.length):= by
  sorry
have EoutsideFb: vertex_list_outside_set iV E Fb3 (Seq.LM.length):= by
  sorry

have Fbcard: small_intersection_list  Seq.LM Fb3 κ (172*κ*κ*k):= by
  sorry

have LM_sparse: family_sparse k k Seq.LM.toFinset:= by
  sorry

have hF3Ex: _:= by
  apply long_path_forest_specified_ends iV iSub iSP H S E.tail Seq.LM  k k _ _ _ _ _ _ _ _ _ _ Fb3
  repeat assumption
  --
  sorry; sorry; sorry; sorry; sorry; assumption

rcases hF3Ex with ⟨F3, hF3a, hF3b, hF3c, hF3d, hF3e, hF3f, hF3g, hF3h, hF3i⟩



have Path_ex: _:= by
  apply join_three_forests iV iSP H F2 F1 F3 _ _ _ k k
  sorry;sorry;sorry;sorry;sorry;sorry;sorry;sorry;sorry;
  sorry;sorry;sorry;sorry;sorry;
  --F1.E = F2.S
  rw[hF1a, hF2b]
  rw[hF1b, hF3a]
  rw[hF2a, hF3b]

  --

rcases Path_ex with ⟨P, hP1⟩

sorry


-/



 /-
lemma Dense_list_implies_path_sequence_with_M
(KFam: Finset (Clump G p m κ pr h))
(KFamNonempty: KFam.Nonempty)
--(t: ℕ)
--(ht: t≤ h*pr)
--(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
Nonempty (ClumpPathSequence iI iV κ KFam)
:=by-/

/-def family_sparse
(β m : ℕ )(MFam: Finset (Subgraph G))
:=
∀ (M1 M2: Subgraph G),
(M1∈ MFam)
→ (M2∈ MFam)
→ (M1≠ M2)
→ ((β *(M1.verts∩ M2.verts).toFinset.card)≤  m)



structure ClumpPathSequence
 (β : ℕ )(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (LM_Sparse: family_sparse β m (LM.toFinset) )
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
  (hlength: Ord.length ≥  h*pr)
  (hlengthM: LM.length=Ord.length)
  (hlengthVer: Ver.length=Ord.length-1)
  --(LM_NoDup: LM.Nodup)-/


/-lemma path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (172*p*p*kmax))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
:= by-/

/-

lemma join_three_forests
(H: Subgraph G)
(F1 F2 F3: PathForest iV iSP H)
(hF1_F2: F1.E=F2.S)
(hF2_F3: F2.E=F3.S)
(hF3_F1: F3.E=F1.S.tail)

(t tmax: ℕ )

( hdisj11: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
( hdisj22: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)))
( hdisj33: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)))
( hdisj12: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)))
( hdisj21: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)))
( hdisj13: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)))
( hdisj31: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F1.P.get! j)))
( hdisj23: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)))
( hdisj32: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)))

(Slength: tmax < F1.S.length)

(ht: t<tmax)
(pos1: tmax<F1.k)
(pos2: tmax<F2.k)
(pos3: tmax<F3.k)


:
∃ (P: SubgraphPath H (F1.S.get! 0) (F3.E.get! (t))),
{v:V|v∈ P.Wa.support}=Path_forest_support_until_t iV iSP  F1 (t+1)∪ Path_forest_support_until_t iV iSP  F2 (t+1)∪ Path_forest_support_until_t iV iSP  F3 (t+1)
-/


/-simp only [Walk.mem_support_append_iff]
have h5:  {v | v ∈ P.Wa.support ∨ v ∈ Q.Wa.support}= {v | v ∈ P.Wa.support} ∪ {v | v ∈ Q.Wa.support}:= by

rw[h5]
rw[hP1, hQ2]

unfold Path_forest_support_until_t
ext v
constructor
intro h
simp
simp at h

aesop
-/

--#check SimpleGraph.append_paths



/-
structure SubgraphPath_implicit
(G: SimpleGraph V) where
  H: Subgraph G
  s: V
  e: V
  Pa: SubgraphPath H s e



variable (iSP:Inhabited (SubgraphPath_implicit   G) )



def starts_equal
(S : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s)


def ends_equal
(E : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((E.get! i)=(P.get! i).e)

def graphs_equal
(H : Subgraph G)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((P.get! i).H≤ H)


def paths_disjoint
 (P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i j: ℕ ), i< j→ j< k→ (Disjoint {v:V|v∈ (P.get! i).Pa.Wa.support} {v:V|v∈ (P.get! j).Pa.Wa.support})


structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  (Paths_disjoint: paths_disjoint iSP  P k)  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))
  (P_length: P.length=k)

def Path_forest_support
{H: Subgraph G}
(Fo: PathForest iV iSP H)
: Set V
:={v: V| ∃ (Pi: SubgraphPath_implicit G), Pi∈ Fo.P∧  (v∈ Pi.Pa.Wa.support)}





def Path_forest_avoids
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: Set V)
:=
∀ (i: ℕ ), i< Fo.k→ (Disjoint {v:V|v∈ (Fo.P.get! i).Pa.Wa.support} Fb)

def Path_forest_avoids_list
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: List V)
:=
∀ (i: ℕ ), i< Fo.k→ (List.Disjoint ((Fo.P.get! i).Pa.Wa.support) Fb)


def cut_dense_list
(HL: List (Subgraph G))
(p: ℕ )
:=∀(i: Fin (HL.length)),  (cut_dense G  (HL.get i) p)

def small_intersection_list
(HL: List (Subgraph G))
(Fb: Set V)
(p e: ℕ )
--(k: ℕ )
:=∀(i: Fin (HL.length)),
(8*p*
(Fb∩ (HL.get i).verts).toFinset.card+e≤ (HL.get i).verts.toFinset.card
)

def vertex_list_in_graph_list
(S: List V)
(HL: List (Subgraph G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∈ (HL.get! i).verts


def vertex_list_outside_set
(S: List V)
(Fb: Set V)
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∉ Fb

structure SubgraphWalk
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_In_H: Wa.toSubgraph≤ H

structure SubgraphPath
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_Is_Path: Wa.IsPath
  Wa_In_H: Wa.toSubgraph≤ H

-/
