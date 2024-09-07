
import MyProject

import MyProject.gg
import MyProject.path.path_forest_clump_sequence2

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 200000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable  [FinV: Fintype V]
variable  [DecG: DecidableRel G.Adj]
variable  [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h  : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
 variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (pLarge: p≥ 20)
variable (prggp: pr ≥ gg2 p)
variable (hggp: h ≥ gg1 pr)
variable (κggh: κ ≥ gg1 h)
variable (mggκ :m≥ gg2 κ )
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )



lemma find_numbers_for_path
(p m κ pr h : ℕ)
( κPositive: κ >0)
(pPositive: p >0)
(mPositive: m >0)
(hPositive: h >0)
(prPositive: pr >0)
(γPositive: γ >0)
(pLarge: p≥ 20)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
:
∃ (k γ : ℕ ),
(pr*pr*pr*h>k+8)
∧(pr*pr*pr*h+1≤ 4*k+100)
∧(k>2)
∧( 8 * γ *(82 * γ * k+2*k)≤ m/(2*pr))
∧( 2 * (k + 4) + (4*k+100) + 2≤  m / pr)
∧(pr≤ γ)
∧( 172 * γ * γ  * k ≤ m / (2 * pr) + 8 * γ  * (2 * k))
∧( γ * 32 + γ * k * 24≤ m/(2*pr))
∧( γ * k * 16 + γ ^ 2 * k * 328 ≤ m/(2*pr))
∧( γ >0)
∧( m ≥ 18 * γ)
∧( m ≥ 18 * pr)
∧( 8 * pr * k * m ≤ κ  * (m / (2 * pr)))
∧( γ ≥ 16 * κ ^ (2 * (100 * (5*pr*pr*pr * pr * h)).factorial))
∧( p ≥ 20)
∧( m ≥ 20)
∧(m ≥ gg1 pr)
∧( pr ≥ gg2 p)
∧(h ≥p)
∧(κ ≥ h)
∧ (k=(pr*pr*pr*h-9))
:=by
use (pr*pr*pr*h-9)
use (gg1 κ )
constructor
refine Nat.add_lt_of_lt_sub ?h.left.h
rw [Nat.sub_succ']
refine Nat.sub_succ_lt_self (pr * pr * pr * h - 8) 0 ?h.left.h.h
simp
calc
  pr*pr*pr*h≥ 1*1*1*h:= by
    gcongr
    repeat exact prPositive
  _=h:= by ring_nf
  _≥ 10000:= by
    apply gg1_large2
    exact prPositive
    exact hggp
  _>8:= by simp
constructor

gcongr ?_+?_
calc
  4 * (pr * pr * pr * h - 9)
  = (pr * pr * pr * h - 9)+3 * (pr * pr * pr * h - 9)
  := by ring_nf
  _≥ (pr * pr * pr * h - 9)+1 * (pr * pr * pr * h - 9):= by
    gcongr
    simp
  _=(pr * pr * pr * h - 9)+(pr * pr * pr * h - 9):= by
    ring_nf
  _≥ (pr * pr * pr * h - 9)+9:= by
    gcongr
    refine Nat.le_sub_of_add_le ?bc.h
    calc
       pr * pr * pr * h≥ 10000*1*1*1:= by
        gcongr
        apply gg1_large2
        exact pPositive
        apply gg2_gg1
        exact prggp
        exact pPositive
        exact prPositive
        exact prPositive
        exact hPositive
      _≥ 18*1*1*1:= by
        gcongr
        simp
      _=9+9:= by ring_nf
  _=   pr * pr * pr * h := by
    apply Nat.sub_add_cancel
    calc
       pr * pr * pr * h≥ 10000*1*1*1:= by
        gcongr
        apply gg1_large2
        exact pPositive
        apply gg2_gg1
        exact prggp
        exact pPositive
        exact prPositive
        exact prPositive
        exact hPositive
      _≥ 9*1*1*1:= by
        gcongr
        simp
      _=9:= by ring_nf
simp

constructor
apply Nat.le_sub_of_add_le
calc
       pr * pr * pr * h≥ 10000*1*1*1:= by
        gcongr
        apply gg1_large2
        exact pPositive
        apply gg2_gg1
        exact prggp
        exact pPositive
        exact prPositive
        exact prPositive
        exact hPositive
      _≥ 12*1*1*1:= by
        gcongr
        simp
      _=_:= by ring_nf

constructor
rw [Nat.le_div_iff_mul_le]
ring_nf
calc
  gg1 κ * pr * (pr ^ 3 * h - 9) * 32 + gg1 κ ^ 2 * pr * (pr ^ 3 * h - 9) * 1312
  ≤ gg1 κ * pr * (pr ^ 3 * h) * 32 + gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 1312:= by
    gcongr
    simp
    simp
  _=gg1 κ^1 * pr * (pr ^ 3 * h) * 32 + gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 1312:= by
    ring_nf
  _≤gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 1312+ gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 1312:= by
    gcongr
    apply gg1_pos
    exact κPositive
    simp
    simp
  _= gg1 κ ^ 2 * pr ^ 4 * h^1 * 2624:= by
    ring_nf
  _≤ gg1 κ ^2* h^4*h^2*10000:= by
    gcongr
    apply gg1_ge
    exact hggp
    exact prPositive
    exact hPositive
    simp
    simp
  _=gg1 κ ^2* h^6*10000:= by
    ring_nf
  _≤ gg1 κ ^2* κ ^6*10000:= by
    gcongr
    apply gg1_ge
    exact κggh
    exact hPositive
  _≤ m:= by
    apply gg2_7
    exact mggκ
    exact κPositive
apply mul_pos
simp
exact prPositive

constructor
rw [Nat.le_div_iff_mul_le]
ring_nf
calc
  pr * 110 + pr * (pr ^ 3 * h - 9) * 6
  ≤ pr^1 *1* 110 + pr * (pr ^ 3 * h) * 6:= by
    gcongr ?_*110+?_
    ring_nf
    simp
    gcongr
    simp
  _≤ pr^4 *h* 110 + pr * (pr ^ 3 * h) * 6:= by
    gcongr
    exact prPositive
    simp
    exact hPositive
  _=pr^4 *h* 116:= by
    ring_nf
  _≤ h^4*h*10000:= by
    gcongr
    apply gg1_ge
    exact hggp
    exact prPositive
    simp
  _=h^5*10000:= by
    ring_nf
  _≤ κ^5*10000:= by
    gcongr
    apply gg1_ge
    exact κggh
    exact hPositive
  _≤ m:= by
    rw[mul_comm]
    apply gg1_6
    apply gg2_gg1
    exact mggκ
    exact κPositive
    exact κPositive
exact prPositive

constructor
calc
  gg1 κ≥ κ := by
    apply gg1_ge
    simp
    exact κPositive
  _≥ h:= by
    apply gg1_ge
    exact κggh
    exact hPositive
  _≥ pr:= by
    apply gg1_ge
    exact hggp
    exact prPositive

constructor
calc
  172 * gg1 κ * gg1 κ * (pr * pr * pr * h - 9)
  ≤ 172 * gg1 κ * gg1 κ * (pr * pr * pr * h):=by
    gcongr
    simp
  _≤m / (2 * pr):=by
    rw [Nat.le_div_iff_mul_le]
    ring_nf
    calc
      gg1 κ ^ 2 * pr ^ 4 * h * 344
      ≤ gg1 κ ^ 2 * h ^ 4 * h * 10000:=by
        gcongr
        apply gg1_ge
        exact hggp
        exact prPositive
        simp
      _≤ gg1 κ ^ 2 * h ^ 5 * h * 10000:=by
        gcongr
        exact hPositive
        simp
      _=gg1 κ ^ 2 * h ^ 6 * 10000:=by
        ring_nf
      _≤ gg1 κ ^ 2 * κ  ^ 6 * 10000:=by
        gcongr
        apply gg1_ge
        exact κggh
        exact hPositive
      _≤ m:=by
        apply gg2_7
        exact mggκ
        exact κPositive

    apply mul_pos
    simp
    exact prPositive
  _≤ m / (2 * pr) + 8 * gg1 κ * (2 * (pr * pr * pr * h - 9)):= by
    simp

constructor
rw [Nat.le_div_iff_mul_le]
ring_nf
calc
  gg1 κ * pr * 64 + gg1 κ * pr * (pr ^ 3 * h - 9) * 48
  ≤
  gg1 κ * pr * 64 + gg1 κ * pr * (pr ^ 3 * h ) * 48:= by
    gcongr
    simp
  _=gg1 κ * pr^1*1 * 64 + gg1 κ * pr * (pr ^ 3 * h ) * 48:= by
    ring_nf
  _≤ gg1 κ * pr^4 *h* 64 + gg1 κ * pr * (pr ^ 3 * h ) * 48:= by
    gcongr
    exact prPositive
    simp
    exact hPositive
  _=gg1 κ * pr^4 *h* 112:= by
    ring_nf
  _=gg1 κ^1 * pr^4 *h^1* 112:=by
    ring_nf
  _≤ gg1 κ^2 * h^4 *h^2* 10000:= by
    gcongr
    apply gg1_pos
    exact κPositive
    simp
    apply gg1_ge
    exact hggp
    exact prPositive
    exact hPositive
    simp
    simp
  _=gg1 κ^2 * h^6* 10000:=by ring_nf
  _≤ gg1 κ ^ 2 * κ  ^ 6 * 10000:=by
        gcongr
        apply gg1_ge
        exact κggh
        exact hPositive
  _≤ m:=by
        apply gg2_7
        exact mggκ
        exact κPositive
apply mul_pos
simp
exact prPositive

constructor
rw [Nat.le_div_iff_mul_le]
ring_nf
calc
  gg1 κ * pr * (pr ^ 3 * h - 9) * 32 + gg1 κ ^ 2 * pr * (pr ^ 3 * h - 9) * 656
  ≤ gg1 κ * pr * (pr ^ 3 * h) * 32 + gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 656:= by
    gcongr
    simp
    simp
  _=gg1 κ^1 * pr * (pr ^ 3 * h) * 32 + gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 656:= by
    ring_nf
  _≤gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 32+ gg1 κ ^ 2 * pr * (pr ^ 3 * h) * 656:= by
    gcongr
    apply gg1_pos
    exact κPositive
    simp
  _= gg1 κ ^ 2 * pr ^ 4 * h^1 * 688:= by
    ring_nf
  _≤ gg1 κ ^ 2 * h ^ 4 * h^2 * 10000:= by
    gcongr
    apply gg1_ge
    exact hggp
    exact prPositive
    exact hPositive
    simp
    simp
  _=gg1 κ^2 * h^6* 10000:=by ring_nf
  _≤ gg1 κ ^ 2 * κ  ^ 6 * 10000:=by
        gcongr
        apply gg1_ge
        exact κggh
        exact hPositive
  _≤ m:=by
        apply gg2_7
        exact mggκ
        exact κPositive
apply mul_pos
simp
exact prPositive

constructor
apply gg1_pos
exact κPositive

constructor
-- m ≥ 18 * gg1 κ
calc
  18*gg1 κ=gg1 κ^1*1^6*18:=by ring_nf
  _≤ gg1 κ ^2* κ ^6*10000:=by
    gcongr
    exact gg1_pos κPositive
    simp
    exact κPositive
    simp
  _≤ m:=by
    exact gg2_7 mggκ κPositive


constructor
--m ≥ 18 * pr
calc
  m≥ κ :=by
    exact gg2_ge mggκ κPositive
  _≥ h:=by
    exact gg1_ge κggh hPositive
  _≥ 10000*pr^3:=by
    exact gg1_1 hggp prPositive
  _≥ 18*pr^1:=by
    gcongr
    simp
    exact prPositive
    simp
  _=_:=by  ring_nf


constructor
calc
  8 * pr * (pr * pr * pr * h - 9) * m
  ≤ 8 * pr * (pr * pr * pr * h) * m:= by
    gcongr
    simp
  _=8*pr^4*h*(m):= by ring_nf
  _=8*pr^4*h*(2*pr*m/(2*pr)):= by
    congr
    refine (Nat.mul_div_right m ?_).symm
    apply mul_pos
    simp
    exact prPositive

  _≤ 8*pr^4*h*(2*(2*pr)*(m/(2*pr))):=by
    gcongr
    apply div_assoc_le1
    apply mul_pos
    simp
    exact prPositive
    --m ≥ 2 * pr
    calc
      m≥ κ :=by
        exact gg2_ge mggκ κPositive
      _≥ h:=by
        exact gg1_ge κggh hPositive
      _≥ 10000*pr^3:=by
        exact gg1_1 hggp prPositive
      _≥ 2*pr^1:=by
        gcongr
        simp
        exact prPositive
        simp
      _=_:=by  ring_nf
  _=32*pr^5*h*(m/(2*pr)):= by
    ring_nf
  _≤ κ * (m / (2 * pr)):= by
    gcongr
    --32 * pr ^ 5 * h ≤ κ
    calc
      32 * pr ^ 5 * h
      ≤ 32*h^5*h:=by
        gcongr
        exact gg1_ge hggp prPositive
      _=h^6*32:=by
        ring_nf
      _≤h ^ 16 * 75557863725914323419136:=by
        gcongr
        exact hPositive
        simp
        simp
      _≤ κ :=by
        exact gg1_4 κggh hPositive

constructor
calc
--gg1 κ ≥ 16 * κ ^ (2 * (100 * (5 * pr * pr * pr * pr * h)).factorial)
  16 * κ ^ (2 * (100 * (5 * pr * pr * pr * pr * h)).factorial)
  _=16 * κ ^ (2 * (100 * (5 * pr^4  * h)).factorial):=by
    ring_nf
  _≤16 * κ ^ (2 * (100 * (5 * h^4 * h)).factorial):=by
    gcongr
    exact κPositive
    apply gg1_ge
    exact hggp
    exact prPositive
  _=16 * κ ^ (2 * (100 * (5 * h^5)).factorial):=by
    ring_nf
  _≤ 16 * κ ^ (2 * (100 * (5 *κ ^5)).factorial):=by
    gcongr
    exact κPositive
    apply gg1_ge
    exact κggh
    exact hPositive
  _≤ gg1 κ :=by
    apply gg1_7
    simp
    exact κPositive


constructor
exact pLarge

constructor
calc
  m≥ 10000:= by
    apply gg1_large2
    exact κPositive
    apply gg2_gg1
    exact mggκ
    exact κPositive
  _≥ 20 := by simp

constructor
calc
  m≥ κ := by
    apply gg2_ge
    exact mggκ
    exact κPositive
  _≥ h:= by
    apply gg1_ge
    exact κggh
    exact hPositive
  _≥ gg1 pr:= by
    exact hggp

constructor
exact prggp

constructor
calc
  h≥ pr:= by
    apply gg1_ge
    exact hggp
    exact prPositive
  _≥ p:= by
    apply gg2_ge
    exact prggp
    exact pPositive

constructor
apply gg1_ge
exact κggh
exact hPositive

simp


lemma clump_path_sequence_gives_path3
(H: Subgraph G)
(KFam: Finset (Clump G p m κ pr h))
(Seq: ClumpPathSequence iI iV κ  KFam)
(Seqlen: Seq.Ord.length=h* pr*pr*pr+1)
(LM_in_H:∀ (i :ℕ ), i< Seq.LM.length →  Seq.LM.get! i ≤ H)
(narrow: Clump_family_narrow' Seq.Ord.toFinset)
(Seq_in_H:∀ (i:ℕ ), i < Seq.Ord.length→  (Seq.Ord.get! i).Gr ≤ H)
:
∃  (u v: V), ∃  (P: SubgraphPath H u v), P.Wa.length ≥  h*m
:=by
have hex:_:=by
  apply find_numbers_for_path p m κ pr h
  repeat assumption
rcases hex with ⟨k, γ  ,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14 ,a15,a16,a17,a18,a19,a20, a21⟩
have ex: ∃  (u v: V), ∃  (P: SubgraphPath H u v), P.Wa.length ≥  (k - 3 + 1) * (m / pr / (40 * pr))-1:= by
  apply clump_path_sequence_gives_path2
  exact κPositive
  exact pPositive
  exact mPositive
  exact prPositive
  exact iSP
  exact a3



  calc
    Seq.Ord.length=h* pr*pr*pr+1:=by exact Seqlen
    _≥ pr*pr*pr*h:= by ring_nf; simp
    _>k+8:=by exact a1

  rw[Seqlen]
  ring_nf
  ring_nf at a2
  rw[mul_comm]
  exact a2

  exact a4
  repeat assumption

  intro i hi
  apply LM_in_H
  rw[Seq.hlengthM]
  rw[Seqlen]
  calc
    i<k:= by exact hi
    _≤ k+8:= by simp
    _< pr*pr*pr*h:= by exact a1
    _≤ _:= by ring_nf; simp

  repeat assumption




  --
rcases ex with ⟨u,v,P,Pl⟩
use u
use v
use P
calc
  P.Wa.length ≥ (k - 3 + 1) * (m / pr / (40 * pr)) - 1:= by
    exact Pl
  _=(pr * pr * pr * h - 9 - 3 + 1) * (m / pr / (40 * pr)) - 1:= by
    rw[a21]
  _≥ h*m:= by sorry





lemma clump_path_sequence_gives_path4
(H: Subgraph G)
(KFam: Finset (Clump G p m κ pr h))
(Seq: ClumpPathSequence iI iV κ  KFam)
(Fam_in_H':∀ (i : (Clump G p m κ pr h) ), i∈ KFam →  i.Gr≤ H)
(narrow': Clump_family_narrow' KFam)
:
∃  (u v: V), ∃  (P: SubgraphPath H u v), P.Wa.length ≥  h*m
:= by







have narrow: Clump_family_narrow' Seq.Ord.toFinset:= by
  intro Ki hi
  apply narrow'
  have Ord_eq_KFam: Seq.Ord.toFinset⊆  KFam:= by
    exact Seq.Ord_eq_KFam
  exact Ord_eq_KFam hi




have Seq_in_H:∀ (i:ℕ ), i < Seq.Ord.length→  (Seq.Ord.get! i).Gr ≤ H:=by
  intro i hi
  apply Fam_in_H'
  have get: Seq.Ord.get! i ∈ Seq.Ord.toFinset:= by
    simp
    have eq: Seq.Ord.getD i default=Seq.Ord.get ⟨ i, ?_⟩ :=by
      refine List.getD_eq_get Seq.Ord default ?_
    rw[eq]
    refine List.get_mem Seq.Ord i ?refine_1
    exact hi
  have Ord_eq_KFam: Seq.Ord.toFinset⊆  KFam:= by
    exact Seq.Ord_eq_KFam
  exact Ord_eq_KFam get

have LM_in_H:∀ (i :ℕ ), i< Seq.LM.length →  Seq.LM.get! i ≤ H:= by
  intro i hi
  have h1: Seq.LM.get! i≤ (Seq.Ord.get! i).Gr:= by
    refine M_in_Gr p m κ pr h (Seq.Ord.get! i) (Seq.LM.get! i) ?hM
    have hii: i< Seq.Ord.length:= by
      rw[Seq.hlengthM.symm]
      exact hi
    have h2:_:= by exact  Seq.LM_in_M i hii
    simp
    simp at h2
    have h3: Seq.LM.getD i ⊥=Seq.LM.get ⟨ i, hi ⟩ := by
      exact List.getD_eq_get Seq.LM ⊥ hi
    have h4: Seq.LM.getD i default =Seq.LM.get ⟨ i, hi ⟩ := by
      exact List.getD_eq_get Seq.LM default hi
    rw[h3] at h2
    rw[h4]
    exact h2
  have h2: (Seq.Ord.get! i).Gr≤ H:= by
    apply Seq_in_H
    rw[Seq.hlengthM.symm]
    exact hi
  exact Preorder.le_trans (Seq.LM.get! i) (Seq.Ord.get! i).Gr H h1 h2




apply clump_path_sequence_gives_path3
exact κPositive
exact pPositive
exact mPositive
exact hPositive
exact prPositive
repeat assumption
exact Seq.hlength
repeat assumption
/-
def M_list_in_clump_list
  (ML: List (Subgraph G))
  (Ord: List (Clump G p m κ pr h))
  : Prop:=
  ∀ (i: ℕ ), i< Ord.length→ ((ML.get! i)∈  ((Ord.get! i).M))


structure ClumpPathSequence
 (β : ℕ )(KFam: Finset (Clump G p m κ pr h))   where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (LM_Sparse: family_sparse β m (LM.toFinset) )
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
  (hlength: Ord.length =  h*pr*pr*pr+1)
  (hlengthM: LM.length=Ord.length)
  (hlengthVer: Ver.length=Ord.length-1)
  (LM_NoDup: LM.Nodup)
  --(LM_In_H: ∀ (i: Fin (LM.length)), (LM.get i)≤ H )
-/
