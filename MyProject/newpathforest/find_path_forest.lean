import MyProject

--import MyProject.path_forests_join
import MyProject.long_path_forest
import MyProject.path_forest.path_forests

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
(p m k pr: ℕ )
--(k: ℕ )
:=∀(i: ℕ ), (i<k)→
(8*p*
(Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))≤ (HL.get! i).verts.toFinset.card
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



----------------------------------------------------------------------------------------------------------------------------------------------




--Used
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


(Slength: S.length=  k)
(Elength: E.length=  k )
(HLlength: HL.length=  k)


(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL.get! i≤ H))

(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)
(HL_nodup: HL.Nodup)




(cutdense: cut_dense_list! iSub HL p (k))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list! iSub HL Fb p m (k) pr)
(pPositive: p>0)
--(Fbcard: small_intersection_list  HL Fb p (m +8*p*(2*1*kmax)))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
--new assumptions:
--(kPositive: k>0)
--(prPositive: pr>0)
(mggp: m ≥ 18 * p)
(κprop: 8 * p * k * m ≤ κ * (m / (2 * pr)))
:
∃ (Fo: PathForest iV iSP H),
(Fo.S= S)
∧  (Fo.E=  E)
∧ Fo.k=k
∧ Fo.P.length=k
--∧ Path_forest_avoids iV iSP Fo Fb
∧ Path_forest_avoids! iV iSP Fo Fb (k)---change
--∧ (Path_forest_support iV iSP Fo )⊆  41*p*k
--∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
--∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long!  iV iSP Fo (m / pr / (40 * p)) (k)

∧ Fo.S.length=k
∧ Fo.E.length=k
--∧ Path_forest_in_HL iV iSub iSP HL Fo



:= by






have HLget2: ∀ (i: Fin (HL.length) ),  HL.get i=HL.get! i:= by
  intro i
  simp
  calc
    _=HL.get ⟨ i.1, i.2⟩ := by exact rfl
    _=_:= by exact (List.getD_eq_get HL default i.isLt).symm


have happly:_:= by
  apply long_path_forest_specified_ends iV iSub iSP H S E HL (k) (k) --_ _ _ _ _ _ _ _ _ --Fb

  apply sparse_family_monotone
  exact HL_sparse
  intro x hx
  simp
  simp at hx
  exact  hx
  --exact HL_sparse. prove monoinicity
  apply order_ge_m_family_monotone
  exact HL_order
  intro x hx
  simp
  simp at hx
  exact  hx
  ---also for gem families


  --vertex_list_in_graph_list iV iSub S HL HL.length
  intro i hi
  apply SinH i
  exact Nat.lt_of_lt_of_eq hi HLlength
  --vertex_list_in_graph_list iV iSub E' HL' HL'.length
  intro i hi
  apply EinH i
  exact Nat.lt_of_lt_of_eq hi HLlength

  --S E disjoint

  exact SE_Disjoint

  ---------lengths------
  exact Nat.le_of_eq (id Slength.symm)
  exact Nat.le_of_eq (id Elength.symm)
  exact Nat.le_of_eq Slength
  exact Nat.le_of_eq Elength
  exact Nat.le_of_eq (id HLlength.symm)



  ----HL in H-----------
  intro i
  rw[HLget2 i]
  apply HL_in_H i
  calc
    _<HL.length:= by exact i.2
    _=k:= by exact HLlength


  exact HL_nodup


  intro i hi
  apply SoutsideFb
  exact Nat.lt_of_lt_of_eq hi HLlength


  intro i hi
  apply EoutsideFb
  exact Nat.lt_of_lt_of_eq hi HLlength

  exact Snodup
  exact Enodup

  simp
  intro i
  rw[HLget2]
  apply cutdense
  calc
    _<HL.length:= by exact i.2
    _=k:= by exact HLlength

  intro i
  rw[HLget2]
  calc
    8 * p * (Fb ∩ (HL.get! ↑i).verts).toFinset.card
    + (8 * p * k * m / κ+8*p*(2*1*(k)))
    ≤
    8*p*
    (Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))
    := by
      gcongr 8*p*(Fb∩ (HL.get! i).verts).toFinset.card+(?_ +8*p*(2*(k)))
      refine Nat.div_le_of_le_mul ?bc.bc.a
      exact κprop
      --172 * p * p * (k + 1) ≤ m + 8 * p * (2 * (k + 1))

    _≤ (HL.get! i).verts.toFinset.card
    := by
      apply Fbcard i.1
      calc
        _<HL.length:= by exact i.2
        _=k:= by exact HLlength


  --m≥ 18*p
  exact mggp
  exact κPositive
  exact pPositive



rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh, hFoi⟩





use Fo

constructor
exact hFoa
constructor
exact hFob
constructor
exact hFoc
--exact hFod
constructor
exact hFod
constructor
intro i hi
apply hFoe
rw[hFoc]
exact hi

constructor
intro i hi
apply hFoh
rw[hFoc]
exact hi

constructor
rw[hFoa]
exact Slength
rw[hFob]
exact Elength









lemma path_forest_specified_ends_simplified_prefix
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m : ℕ )
(Fb: Set V)

(SinH: vertex_list_in_graph_list iV iSub S HL (k))---change
(EinH: vertex_list_in_graph_list iV iSub E HL (k))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length= k)
(Elength: E.length=  k)
(HLlength: HL.length=  k)



(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL.get! i≤ H))


(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)


(cutdense: cut_dense_list! iSub HL p (k))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list!  iSub HL Fb p m (k) pr) ---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
--new
(kBig: k>1)
(mbig1: 172 * p * p * k ≤ m / (2 * pr) + 8 * p * (2 * k))
:

∃ (Fo: PathForest iV iSP H),
Fo.S= S
∧ Fo.E= E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids! iV iSP Fo Fb (k)---change
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
--∧ Path_forest_avoids! iV iSP Fo {v:V|v∈ (List.drop k S)} k---change
--∧ Path_forest_avoids!  iV iSP Fo {v:V|v∈ (List.drop k E)} k---change
∧ Fo.S.length=k
∧ Fo.E.length=k
:= by


have HLget2: ∀ (i: Fin (HL.length) ),  HL.get i=HL.get! i:= by
  intro i
  simp
  calc
    _=HL.get ⟨ i.1, i.2⟩ := by exact rfl
    _=_:= by exact (List.getD_eq_get HL default i.isLt).symm



have happly:_:= by
  apply path_forest_specified_ends_altk iV iSub  H S E HL (k) (k) --_ _ _ _ _ _ _ _ _ --Fb



  --vertex_list_in_graph_list iV iSub S HL HL.length
  intro i hi
  apply SinH i
  exact Nat.lt_of_lt_of_eq hi HLlength
  --vertex_list_in_graph_list iV iSub E' HL' HL'.length
  intro i hi
  apply EinH i
  apply Nat.lt_of_lt_of_eq hi
  simp

  --S E disjoint

  exact SE_Disjoint

  ---------lengths------
  exact Nat.le_of_eq (id Slength.symm)
  exact Nat.le_of_eq (id Elength.symm)
  exact Nat.le_of_eq Slength
  exact Nat.le_of_eq Elength
  exact Nat.le_of_eq (id HLlength.symm)



  ----HL in H-----------
  intro i
  rw[HLget2 i]
  apply HL_in_H i
  calc
    _<HL.length:= by exact i.2
    _=k:= by exact HLlength





  intro i hi
  apply SoutsideFb
  exact Nat.lt_of_lt_of_eq hi HLlength


  intro i hi
  apply EoutsideFb
  apply Nat.lt_of_lt_of_eq hi
  simp

  exact Snodup
  exact Enodup

  simp
  intro i
  rw[HLget2]
  apply cutdense
  calc
    _<HL.length:= by exact i.2
    _=k:= by exact HLlength

  intro i
  rw[HLget2]
  calc
    8 * p * (Fb ∩ (HL.get! ↑i).verts).toFinset.card
    + (172*p*p*k)
    ≤
    8*p*
    (Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))
    := by
      gcongr 8*p*(Fb∩ (HL.get! i).verts).toFinset.card+(?_)

    _≤ (HL.get! i).verts.toFinset.card
    := by
      apply Fbcard i.1
      calc
        _<HL.length:= by exact i.2
        _=k:= by exact HLlength



  --m≥ 18*p
  --exact mggp
  --exact κPositive
  exact pPositive
  exact iSP




rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh⟩





use Fo

constructor
exact hFoa
constructor
exact hFob
constructor
exact hFoc
--exact hFod
constructor
exact hFod
constructor
intro i hi
apply hFoe
rw[hFoc]
exact hi

constructor
exact hFof

constructor
rw[hFoa]
exact Slength
rw[hFob]
exact Elength
