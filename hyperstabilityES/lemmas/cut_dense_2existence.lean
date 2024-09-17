--import MyProject

import hyperstabilityES.lemmas.cut_dense_existence
import hyperstabilityES.lemmas.cut_dense_add_vertices

  --import hyperstabilityES.lemmas.SimpleGraph
set_option linter.unusedVariables false

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats  450000

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
--variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
--variable (iSP:Inhabited (SubgraphPath_implicit   G) )

--variable {prggp: pr≫ p}
--variable {mggpr: m≫ pr}





/-lemma big_inequality
(a b h A B H p: ℚ )
(pPositive: p>0)
(notcutdense: a+b+ε*p *A*B≥ h)
(cardsum: A+B=H)
(Hdensity: h/H^2≥ p)

(BleH: B≤ H)
(AleH: A≤ H)
(Bpositive: B>0)
(Apositive: A>0)
(Hpositive: H>0)
(epos: ε>0)
:
a/A^2≥ (h/H^2)*(H/A)*(1-ε *B/A)
∨
b/B^2≥ (h/H^2)*(H/B)*(1-ε *A/B)




lemma small_inequality
(a b h A B H p: ℚ )
(pPositive: p>0)
(notcutdense: a+b+p*A*B/4≥ h)
(cardsum: A+B=H)
(Hdensity: h/H^2≥ p)
(b_small: b≤ B^2)
(Bsmall: B≤ p*H/4)
(Bpositive: B>0)
(Apositive: A>0)
(Hpositive: H>0)
(hnonneg: h≥ 0)
(HlargerthanA: H≥ A)
:
a/A^2≥ (h/H^2)*(H/A)
-/

lemma order_strict_decrease
(H: Subgraph G)
(A B: Finset V)
(h: vv H= v A+v B)
(hpos: v A>0)
:
H.verts.toFinset.card>B.card
:= by
unfold v at h
unfold vv at h
unfold v at hpos
have h1: (H.verts.toFinset.card :ℚ )> (B.card:ℚ):= by
  calc
    (H.verts.toFinset.card :ℚ )= (A.card :ℚ )+ (B.card:ℚ ):= by exact h
    _> 0+(B.card:ℚ ):= by
      gcongr
    _= B.card:= by
      ring_nf
simp at h1
simp
exact h1


lemma combined_inequality
(a b h A B H p ε : ℚ )
(pPositive: p>0)
(notcutdense: a+b+ε*p *A*B≥ h)
(cardsum: A+B=H)
(Hdensity: h/H^2≥ p)
(pSmall: p≤ 1)

(Bpositive: B>0)
(Apositive: A>0)
(Hpositive: H>0)
(b_small: b≤ B^2)
(a_small: a≤ A^2)



(hnonneg: h≥ 0)

(epos: ε>0)
(esmall: ε≤ 1/4)
:
(
(A≥  p*H/4)
∧
(a/A^2≥ (h/H^2)*(H/A)*(1-ε *B/A))
)
∨
(
(B≥  p*H/4)
∧
b/B^2≥ (h/H^2)*(H/B)*(1-ε *A/B)
)
:= by

have ple3: p≤ 3:= by
  calc
    p≤ 1:= by
      assumption
    _≤ 3:= by
      exact rfl

have BleH: B≤ H:= by
  calc
    B= H-A:= by linarith
    _≤ H-0:= by
      gcongr
    _=H:= by ring_nf

have AleH: A≤ H:= by
  calc
    A= H-B:= by linarith
    _≤ H-0:= by
      gcongr
    _=H:= by ring_nf

have notcutdense_weak: a+b+p*A*B/4≥ h:= by
  calc
    a+b+p*A*B/4=a+b+(1/4)*p*A*B:=by ring_nf
    _≥ a+b+ε*p*A*B:= by
      gcongr

    _≥ h:= by
      assumption


by_cases hAc: B≤  p*H/4

have hin: a/A^2≥ (h/H^2)*(H/A):= by
  apply small_inequality a b h A B H p
  repeat assumption

have haux: ε *B/A>0:= by
  refine div_pos ?ha Apositive
  exact Left.mul_pos epos Bpositive

have hin2: (a/A^2≥  (h/H^2)*(H/A)*(1-ε *B/A)):= by
  calc
    a/A^2≥ (h/H^2)*(H/A):= by
      assumption
    _= (h/H^2)*(H/A)*(1-0):=by ring_nf
    _≥  (h/H^2)*(H/A)*(1-ε *B/A):= by
      gcongr

have Alarge:A≥  p*H/4:= by
  calc
    A= H-B:= by linarith
    _≥ H-p*H/4:= by
      gcongr
    _≥ H-1*H/4:= by
      gcongr
    _=3*H/4:= by ring_nf
    _≥ p*H/4:= by
      gcongr

left
exact ⟨ Alarge, hin2 ⟩



by_cases hBc: A≤  p*H/4


have hin: b/B^2≥ (h/H^2)*(H/B):= by
  apply small_inequality b a h B A H p
  repeat assumption
  rw[add_comm b a]
  rw[mul_assoc, mul_comm  B A, ←mul_assoc]
  assumption
  rw[add_comm B A]
  repeat assumption

have haux: ε *A/B>0:= by
  apply div_pos-- ?ha Bpositive
  exact Left.mul_pos epos Apositive
  exact Bpositive

have hin2: (b/B^2≥  (h/H^2)*(H/B)*(1-ε *A/B)):= by
  calc
    b/B^2≥ (h/H^2)*(H/B):= by
      assumption
    _= (h/H^2)*(H/B)*(1-0):=by ring_nf
    _≥  (h/H^2)*(H/B)*(1-ε *A/B):= by
      gcongr

have Blarge:B≥  p*H/4:= by
  calc
    B= H-A:= by linarith
    _≥ H-p*H/4:= by
      gcongr
    _≥ H-1*H/4:= by
      gcongr
    _=3*H/4:= by ring_nf
    _≥ p*H/4:= by
      gcongr

right
exact ⟨ Blarge, hin2 ⟩


simp at  hAc
simp at hBc

have hlarge: _:= by
  apply big_inequality a b h A B H p
  repeat assumption

rcases hlarge with case|case


left
constructor
apply le_of_lt
exact hBc
exact case

right
constructor
apply le_of_lt
exact hAc
exact case



noncomputable def dens (H: Subgraph G):ℚ := (ee H)/(vv H)^2--(H.edgeSet.toFinset.card: ℚ )/(H.verts.toFinset.card:ℚ )^2




lemma combined_inequality_graph
(H: Subgraph G)
(p': ℕ )
(p'Positive: p'≠ 0)
(not_cut_dense: ¬ cut_dense G H p')
(ε: ℚ)
(q: ℚ )
(hq: q=(32/(p'*ε) ))
(εPositive: ε>0)
--(hp: p=1/(p': ℚ ))
(Hlarge: H.verts.toFinset.card≥ 20)
(H_edges: dens H≥ (32/(p'*ε) ))
(pe_bound: 32/(p'*ε)≤  1 )
--(epos: ε>0)
(esmall: ε≤ 1/4)
:
∃ (K: Subgraph G),
(K≤ H)
∧
(vv K≥  q*(vv H)/4)
∧
(
(dens K≥ (dens H)*(vv H / vv K)*(1-ε *(vv H-vv K)/ (vv K)))
)
:= by

have Exnotcutdense:∃(A B: Finset V),(Disjoint A B) ∧ (H.verts.toFinset= A ∪ B)∧ (vv H= v A+v B)∧(p'*eBip H A B≤  16*(v A)*(v B))∧v A>0∧v B>0
:=by
  apply cut_dense_negationRat
  exact Hlarge
  exact not_cut_dense


rcases Exnotcutdense with ⟨ AS, BS, ABdisjoint, ABunion, ABcard, Interedges, Anonempty, Bnonempty ⟩
have enonzero: ε≠ 0:= by
  exact Ne.symm (ne_of_lt εPositive)

have CutDense_inequality:_:= by
  apply cut_dense_negation_interedges H AS BS
  exact ABunion

have cutdenseinequality2:  e H AS + e H BS + (32/p') * v AS * v BS ≥ ee H:= by
  calc
    ee H≤ e H AS + e H BS + 2 * eBip H AS BS := by
      exact CutDense_inequality
    _=e H AS + e H BS + 2 * 1* eBip H AS BS:= by
      ring_nf
    _=e H AS + e H BS + 2 * ((p': ℚ )/(p': ℚ ))*eBip H AS BS:= by
      congr
      refine (div_self ?_).symm
      exact Nat.cast_ne_zero.mpr p'Positive
    _=e H AS + e H BS + 2 * ((p': ℚ )*eBip H AS BS)/(p': ℚ ):= by
      ring_nf
    _≤ e H AS + e H BS + 2*(16 * v AS * v BS ) /p' := by
      gcongr
    _= e H AS + e H BS + (32/p') * v AS * v BS := by
      ring_nf

--let q: ℚ :=(32/(p'*ε) )
have cutdenseinequality3:  e H AS + e H BS + ε *q* v AS * v BS ≥ ee H:= by
  calc
  e H AS + e H BS +  ε*q * v AS * v BS
  =e H AS + e H BS + (32/p')*(ε/ε) * v AS * v BS:= by
    rw[hq]
    ring_nf
  _= e H AS + e H BS + (32/p')*(1) * v AS * v BS:= by
    congr
    apply  div_self
    exact enonzero
  _=e H AS + e H BS + (32/p') * v AS * v BS := by
    ring_nf
  _≥ ee H:= by
    exact cutdenseinequality2

have qPositive: q>0:= by
  rw[hq]
  apply div_pos
  exact rfl
  apply mul_pos
  simp
  exact Nat.zero_lt_of_ne_zero p'Positive
  exact εPositive


let GA:= H.induce AS
let GB:= H.induce BS

let a: ℚ := e H AS
let b: ℚ := e H BS
let h: ℚ := ee H
let A: ℚ := v AS
let B: ℚ := v BS
let Hv: ℚ := vv H



have main:_:= by
  apply combined_inequality a b h A B Hv q ε
  exact qPositive
  dsimp[a,b,h,A,B]
  exact cutdenseinequality3
  dsimp [A, B, Hv]
  exact ABcard.symm
  unfold dens at H_edges
  rw[hq]
  exact H_edges
  rw[hq]
  exact pe_bound
  dsimp[B]
  exact Bnonempty
  exact Anonempty
  dsimp[Hv]
  unfold vv
  simp only [ Nat.cast_pos]
  exact Nat.zero_lt_of_lt Hlarge
  dsimp[b, B]
  unfold e
  unfold v
  have h2: (H.induce ↑BS).edgeSet.toFinset.card≤ BS.card^2:= by
    calc
      (H.induce ↑BS).edgeSet.toFinset.card
      ≤ (H.induce ↑BS).verts.toFinset.card^2:= by
        exact lower_bound_vertices_by_edges_weaker (H.induce ↑BS)
      _= BS.card^2:= by
        congr
        simp
  apply Nat.cast_le.2
  exact h2

  have h2: (H.induce ↑AS).edgeSet.toFinset.card≤ AS.card^2:= by
    calc
      (H.induce ↑AS).edgeSet.toFinset.card
      ≤ (H.induce ↑AS).verts.toFinset.card^2:= by
        exact lower_bound_vertices_by_edges_weaker (H.induce ↑AS)
      _= AS.card^2:= by
        congr
        simp
  apply Nat.cast_le.2
  exact h2

  dsimp[h]
  unfold ee
  exact Nat.cast_nonneg H.edgeSet.toFinset.card

  exact εPositive
  exact esmall



  --
have Hvers: H.verts=AS∪ BS:= by
  --simp at ABunion
  --simp
  ext x
  constructor
  intro hx
  have h1: x∈ H.verts.toFinset:= by
    simp
    exact hx
  have h2: x∈ AS∪ BS:= by
    rw[ABunion.symm]
    exact h1
  exact h2
  intro hx
  simp only [   mem_coe] at hx
  rw[ABunion.symm] at hx
  simp at hx
  exact hx



have vvA: vv (H.induce ↑AS)= v AS:= by
  unfold vv
  unfold v
  simp

have vvB: vv (H.induce ↑BS)= v BS:= by
  unfold vv
  unfold v
  simp

have eeA: ee (H.induce ↑AS)= e H AS:= by
  unfold ee
  unfold e
  simp

have eeB: ee (H.induce ↑BS)= e H BS:= by
  unfold ee
  unfold e
  simp



have vv2: vv H - vv (H.induce ↑AS)= v BS:= by
  calc
    vv H - vv (H.induce ↑AS)
    = vv H - v AS:= by
      unfold vv
      unfold v
      simp
    _= v BS:= by
      exact (eq_sub_of_add_eq' (id ABcard.symm)).symm


have vv2B: vv H - vv (H.induce ↑BS)= v AS:= by
  calc
    vv H - vv (H.induce ↑BS)
    = vv H - v BS:= by
      unfold vv
      unfold v
      simp
    _= v AS:= by
      exact sub_eq_iff_eq_add.mpr ABcard

rcases main with caseA|caseB

use H.induce AS
constructor
refine induced_subgraph_subgraph ?h.left.hS
rw[Hvers]
simp

constructor
rw[vvA]
dsimp [A, Hv] at caseA
exact caseA.1

unfold dens
rw[vv2]
rw[vvA, eeA]
exact caseA.2

----caseB

use H.induce BS
constructor
apply induced_subgraph_subgraph
rw[Hvers]
simp

constructor
rw[vvB]
dsimp [B, Hv] at caseB
exact caseB.1

unfold dens
rw[vv2B]
rw[vvB, eeB]
exact caseB.2








lemma combined_inequality_graph_alt
(H: Subgraph G)
(p': ℕ )
(p'Positive: p'≠ 0)
(not_cut_dense: ¬ cut_dense G H p')
(ε: ℚ)
(q: ℚ )
(qPositive: q>0)
(hq: q≥ (32/(p'*ε) ))
(qUpper: q≤ 1)
(εPositive: ε>0)
(Hlarge: H.verts.toFinset.card≥ 20)
(H_edges: dens H≥ q)
(pe_bound: 32/(p'*ε)≤  1 )
(esmall: ε≤ 1/4)
:
∃ (K: Subgraph G),
(K≤ H)
∧
(vv K≥  q*(vv H)/4)
∧
(
(dens K≥ (dens H)*(vv H / vv K)*(1-ε *(vv H-vv K)/ (vv K)))
)
∧
(K.verts.toFinset.card< H.verts.toFinset.card)
:= by

have Exnotcutdense:∃(A B: Finset V),(Disjoint A B) ∧ (H.verts.toFinset= A ∪ B)∧ (vv H= v A+v B)∧(p'*eBip H A B≤  16*(v A)*(v B))∧v A>0∧v B>0
:=by
  apply cut_dense_negationRat
  exact Hlarge
  exact not_cut_dense


rcases Exnotcutdense with ⟨ AS, BS, ABdisjoint, ABunion, ABcard, Interedges, Anonempty, Bnonempty ⟩
have enonzero: ε≠ 0:= by
  exact Ne.symm (ne_of_lt εPositive)

have CutDense_inequality:_:= by
  apply cut_dense_negation_interedges H AS BS
  exact ABunion

have cutdenseinequality2:  e H AS + e H BS + (32/p') * v AS * v BS ≥ ee H:= by
  calc
    ee H≤ e H AS + e H BS + 2 * eBip H AS BS := by
      exact CutDense_inequality
    _=e H AS + e H BS + 2 * 1* eBip H AS BS:= by
      ring_nf
    _=e H AS + e H BS + 2 * ((p': ℚ )/(p': ℚ ))*eBip H AS BS:= by
      congr
      refine (div_self ?_).symm
      exact Nat.cast_ne_zero.mpr p'Positive
    _=e H AS + e H BS + 2 * ((p': ℚ )*eBip H AS BS)/(p': ℚ ):= by
      ring_nf
    _≤ e H AS + e H BS + 2*(16 * v AS * v BS ) /p' := by
      gcongr
    _= e H AS + e H BS + (32/p') * v AS * v BS := by
      ring_nf

--let q: ℚ :=(32/(p'*ε) )
have cutdenseinequality3:  e H AS + e H BS + ε *q* v AS * v BS ≥ ee H:= by
  calc
  e H AS + e H BS +  ε*q * v AS * v BS
  ≥ e H AS + e H BS +  ε*(32/(p'*ε )) * v AS * v BS:= by
    gcongr
  _= e H AS + e H BS + (32/p')*(ε/ε) * v AS * v BS:= by
    ring_nf
  _= e H AS + e H BS + (32/p')*(1) * v AS * v BS:= by
    congr
    apply  div_self
    exact enonzero
  _=e H AS + e H BS + (32/p') * v AS * v BS := by
    ring_nf
  _≥ ee H:= by
    exact cutdenseinequality2

--have qPositive: q>0:= by
  --
  /-rw[hq]
  apply div_pos
  exact rfl
  apply mul_pos
  simp
  exact Nat.zero_lt_of_ne_zero p'Positive
  exact εPositive-/


let GA:= H.induce AS
let GB:= H.induce BS

let a: ℚ := e H AS
let b: ℚ := e H BS
let h: ℚ := ee H
let A: ℚ := v AS
let B: ℚ := v BS
let Hv: ℚ := vv H



have main:_:= by
  apply combined_inequality a b h A B Hv q ε
  exact qPositive
  dsimp[a,b,h,A,B]
  exact cutdenseinequality3
  dsimp [A, B, Hv]
  exact ABcard.symm
  unfold dens at H_edges
  exact H_edges
  exact qUpper
  dsimp[B]
  exact Bnonempty
  exact Anonempty
  dsimp[Hv]
  unfold vv
  simp only [ Nat.cast_pos]
  exact Nat.zero_lt_of_lt Hlarge
  dsimp[b, B]
  unfold e
  unfold v
  have h2: (H.induce ↑BS).edgeSet.toFinset.card≤ BS.card^2:= by
    calc
      (H.induce ↑BS).edgeSet.toFinset.card
      ≤ (H.induce ↑BS).verts.toFinset.card^2:= by
        exact lower_bound_vertices_by_edges_weaker (H.induce ↑BS)
      _= BS.card^2:= by
        congr
        simp
  apply Nat.cast_le.2
  exact h2

  have h2: (H.induce ↑AS).edgeSet.toFinset.card≤ AS.card^2:= by
    calc
      (H.induce ↑AS).edgeSet.toFinset.card
      ≤ (H.induce ↑AS).verts.toFinset.card^2:= by
        exact lower_bound_vertices_by_edges_weaker (H.induce ↑AS)
      _= AS.card^2:= by
        congr
        simp
  apply Nat.cast_le.2
  exact h2

  dsimp[h]
  unfold ee
  exact Nat.cast_nonneg H.edgeSet.toFinset.card

  exact εPositive
  exact esmall



  --
have Hvers: H.verts=AS∪ BS:= by
  --simp at ABunion
  --simp
  ext x
  constructor
  intro hx
  have h1: x∈ H.verts.toFinset:= by
    simp
    exact hx
  have h2: x∈ AS∪ BS:= by
    rw[ABunion.symm]
    exact h1
  exact h2
  intro hx
  simp only [   mem_coe] at hx
  rw[ABunion.symm] at hx
  simp at hx
  exact hx



have vvA: vv (H.induce ↑AS)= v AS:= by
  unfold vv
  unfold v
  simp

have vvB: vv (H.induce ↑BS)= v BS:= by
  unfold vv
  unfold v
  simp

have eeA: ee (H.induce ↑AS)= e H AS:= by
  unfold ee
  unfold e
  simp

have eeB: ee (H.induce ↑BS)= e H BS:= by
  unfold ee
  unfold e
  simp



have vv2: vv H - vv (H.induce ↑AS)= v BS:= by
  calc
    vv H - vv (H.induce ↑AS)
    = vv H - v AS:= by
      unfold vv
      unfold v
      simp
    _= v BS:= by
      exact (eq_sub_of_add_eq' (id ABcard.symm)).symm


have vv2B: vv H - vv (H.induce ↑BS)= v AS:= by
  calc
    vv H - vv (H.induce ↑BS)
    = vv H - v BS:= by
      unfold vv
      unfold v
      simp
    _= v AS:= by
      exact sub_eq_iff_eq_add.mpr ABcard

rcases main with caseA|caseB

use H.induce AS
constructor
refine induced_subgraph_subgraph ?h.left.hS
rw[Hvers]
simp

constructor
rw[vvA]
dsimp [A, Hv] at caseA
exact caseA.1

unfold dens
rw[vv2]
rw[vvA, eeA]
constructor
exact caseA.2

simp only [Subgraph.induce_verts, toFinset_coe]
apply order_strict_decrease
rw[add_comm] at ABcard
exact ABcard
simp
exact Bnonempty

----caseB

use H.induce BS
constructor
apply induced_subgraph_subgraph
rw[Hvers]
simp

constructor
rw[vvB]
dsimp [B, Hv] at caseB
exact caseB.1

unfold dens
rw[vv2B]
rw[vvB, eeB]
constructor
exact caseB.2

simp only [Subgraph.induce_verts, toFinset_coe]
apply order_strict_decrease
exact ABcard
simp
exact Anonempty


structure density_improving_list
(ε β  n q : ℚ ) where
  L: List (Subgraph G)
  Nested: ∀ (i: ℕ ), i+1< L.length→ L.get! (i)≥ L.get! (i+1)
  Density_Increase: ∀ (i: ℕ ), i+1< L.length→
    dens (L.get! (i+1))≥ (dens (L.get! (i)))*(vv (L.get! (i)) / vv (L.get! (i+1)))*(1-ε *(vv (L.get! (i))-vv (L.get! (i+1)))/ (vv (L.get! (i+1))))
  --Strictily_Decreasing:  ∀ (i: ℕ ), i+1< L.length→ vv (L.get! (i))> vv (L.get! (i+1))
  Strictily_Decreasing:  ∀ (i: ℕ ), i+1< L.length→ (L.get! (i)).verts.toFinset.card>  (L.get! (i+1)).verts.toFinset.card
  Order_decrease:  ∀ (i: ℕ ), i+1< L.length→ vv (L.get! (i+1))≥  q*(vv (L.get! (i))/4)
  --LargeLimit: ℕ
  --DenseLimit: ℕ
  Large: ∀ (i: ℕ ), i+1<L.length→  vv (L.get! i)≥ β  * n
  Dense: ∀ (i: ℕ ), i+1<L.length→  dens (L.get! i)≥ q





def large {iSub: Inhabited (Subgraph G)}{ε β  n q : ℚ } (Li: density_improving_list iSub ε β  n q)
:=
(∀ (i: ℕ ), i<Li.L.length→ vv (Li.L.get! i)≥ β  * n)

def dense {iSub: Inhabited (Subgraph G)}{ε β  n q : ℚ } (Li: density_improving_list iSub ε β  n q)
:=  (∀ (i: ℕ ), i<Li.L.length→ dens (Li.L.get! i)≥ q)



lemma LiLarge
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(βSmall: β≤ 1)
(Li: density_improving_list iSub ε β  n q)
(i: ℕ )
(hget0: vv (Li.L.get! 0)=  n)
(hi: i< Li.L.length)
:
vv (Li.L.get! i)≥ (q/4)*β  * n
:=by
by_cases case: i+1<Li.L.length
calc
  vv (Li.L.get! i)≥ β  * n:= by
    apply Li.Large
    exact case
  _=1*β  * n:=by
    ring_nf
  _≥ (q/4)*β  * n:= by
    gcongr

by_cases case2: i=0
rw[case2, hget0]
calc
  q / 4 * β * n≤ 1*1*n:= by
    gcongr
  _= n:= by
    ring_nf

simp at case
simp at case2
have ipos: i>0:= by exact Nat.zero_lt_of_ne_zero case2
have heq: i+1=Li.L.length:= by
  exact (Nat.le_antisymm case hi).symm
have him: i-1+1<Li.L.length:= by
  rw[heq.symm]
  simp
  refine Nat.sub_one_lt_of_le ipos ?h₁
  exact Nat.le_refl i
have hii: i=i-1+1:= by
  exact (Nat.sub_eq_iff_eq_add ipos).mp rfl
calc
  vv (Li.L.get! i)≥ q*(vv (Li.L.get! (i-1))/4):= by
    rw[hii]
    apply Li.Order_decrease (i-1) him
  _≥ q*((β *n)/4):=by
    gcongr
    exact Li.Large (i - 1) him
  _=q / 4 * β * n:= by
    ring_nf




lemma improving_list_vv_positive
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(βSmall: β≤ 1)
(Li: density_improving_list iSub ε β  n q)
(hget0: vv (Li.L.get! 0)=  n)
(i: ℕ )
(hi: i< Li.L.length)
:
vv (Li.L.get! i)>0
:= by
calc
  vv (Li.L.get! i)≥ (q/4)*β  * n:= by
    apply  LiLarge
    repeat assumption


  _>0:= by
    apply mul_pos
    apply mul_pos
    exact div_pos qPositive rfl
    exact βPositive

    exact nPositive

lemma extendible_improving_list_vv_positive
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)

(Li: density_improving_list iSub ε β  n q)
(Ext: large Li)
(i: ℕ )
(hi: i< Li.L.length)
:
vv (Li.L.get! i)>0
:= by
calc
  vv (Li.L.get! i)≥ β  * n:= by
    apply  Ext
    exact hi
  _>0:= by
    apply mul_pos
    exact βPositive
    exact nPositive

lemma improving_list_vv_positive_getD
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(βSmall: β≤ 1)
(Li: density_improving_list iSub ε β  n q)
(hget0: vv (Li.L.get! 0)=  n)
(i: ℕ )
(hi: i< Li.L.length)
:
vv (Li.L.getD i default)>0
:= by
have h1: vv (Li.L.get! i)>0:= by
  exact improving_list_vv_positive iSub ε β n q βPositive nPositive qPositive qSmall βSmall Li hget0 i hi
simp at h1
exact h1

lemma extendible_improving_list_vv_positive_getD
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)

(Li: density_improving_list iSub ε β  n q)
(Ext: large Li)
(i: ℕ )
(hi: i< Li.L.length)
:
vv (Li.L.getD i default)>0
:= by
have h1: vv (Li.L.get! i)>0:= by
  exact extendible_improving_list_vv_positive iSub ε β n q βPositive nPositive Li Ext i hi
simp at h1
exact h1

lemma vv_nonneg
(H: Subgraph G)
:
vv H≥ 0
:= by
unfold vv
exact Nat.cast_nonneg H.verts.toFinset.card


lemma ee_nonneg
(H: Subgraph G)
:
ee H≥ 0
:= by
unfold ee
exact Nat.cast_nonneg H.edgeSet.toFinset.card

lemma dens_nonneg
(H: Subgraph G)
:
dens H≥ 0
:= by
unfold dens
refine div_nonneg ?ha ?hb
exact ee_nonneg H
exact sq_nonneg (vv H)

lemma nested_graphs_vv_increase
(H K : Subgraph G)
(hHK: H≤ K)
:
vv H≤ vv K
:= by
unfold vv
simp only [ Nat.cast_le]
gcongr
simp
apply subgraphs_vertex_sets_subsets G
exact hHK

lemma improving_list_vv_le_n
(ε β  n q : ℚ  )
(Li: density_improving_list iSub ε β  n q)
(hget0: vv (Li.L.get! 0)=  n)
(i: ℕ )
(hi: i< Li.L.length)
:
 vv (Li.L.get! i)≤   n
:= by
induction' i with i HI
exact le_of_eq hget0
calc
vv (Li.L.get! (i + 1)) ≤
vv (Li.L.get! (i)) :=by
  apply nested_graphs_vv_increase
  apply Li.Nested
  exact hi
_≤n:=by
  apply HI
  exact Nat.lt_of_succ_lt hi


lemma improving_list_nested_in_0
(ε β  n q : ℚ  )
(Li: density_improving_list iSub ε β  n q)
(i: ℕ )
(hi: i< Li.L.length)
:
(Li.L.get! i)≤(Li.L.get! 0)
:= by
induction' i with i HI
exact Preorder.le_refl (Li.L.get! 0)

calc
(Li.L.get! (i + 1)) ≤
(Li.L.get! (i)) :=by
  apply Li.Nested
  exact hi
_≤(Li.L.get! (0)):=by
  apply HI
  exact Nat.lt_of_succ_lt hi

lemma improving_list__weakening_Large
(ε β  n q : ℚ  )
(Li: density_improving_list iSub ε β  n q)
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(i: ℕ )
(hk: i+1< Li.L.length)
(Large: large Li)
:
dens (Li.L.get! (i+1))≥ (dens (Li.L.get! (i)))*(vv (Li.L.get! (i)) / vv (Li.L.get! (i+1)))*(1-ε *(vv (Li.L.get! (i))-vv (Li.L.get! (i+1)))/ (β *n))

:= by
calc
dens (Li.L.get! (i+1))
≥ (dens (Li.L.get! (i)))
*(vv (Li.L.get! (i)) / vv (Li.L.get! (i+1)))
*(1-ε *(vv (Li.L.get! (i))-vv (Li.L.get! (i+1)))/ (vv (Li.L.get! (i+1)))):= by
  apply Li.Density_Increase
  exact hk

_≥ (dens (Li.L.get! (i)))
*(vv (Li.L.get! (i)) / vv (Li.L.get! (i+1)))
*(1-ε *(vv (Li.L.get! (i))-vv (Li.L.get! (i+1)))/ (β *n)):= by
  gcongr
  apply mul_nonneg
  apply dens_nonneg
  apply div_nonneg
  exact vv_nonneg (Li.L.get! i)
  exact vv_nonneg (Li.L.get! (i + 1))


  apply mul_nonneg
  exact gt_implies_gte_rational ε 0 εPositive
  simp only [sub_nonneg]

  apply nested_graphs_vv_increase
  apply Li.Nested
  exact hk

  apply Large
  exact hk


lemma improving_list__weakening
(ε β  n q : ℚ  )
(Li: density_improving_list iSub ε β  n q)
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(βSmall: β≤ 1)
(hget0: vv (Li.L.get! 0)=  n)
(i: ℕ )
(hk: i+1< Li.L.length)
--(hk2: i+1< Li.L.length)
:
dens (Li.L.get! (i+1))≥ (dens (Li.L.get! (i)))*(vv (Li.L.get! (i)) / vv (Li.L.get! (i+1)))*(1-ε *(vv (Li.L.get! (i))-vv (Li.L.get! (i+1)))/ ((q/4)*β *n))

:= by
calc
dens (Li.L.get! (i+1))
≥ (dens (Li.L.get! (i)))
*(vv (Li.L.get! (i)) / vv (Li.L.get! (i+1)))
*(1-ε *(vv (Li.L.get! (i))-vv (Li.L.get! (i+1)))/ (vv (Li.L.get! (i+1)))):= by
  apply Li.Density_Increase
  exact hk

_≥ (dens (Li.L.get! (i)))
*(vv (Li.L.get! (i)) / vv (Li.L.get! (i+1)))
*(1-ε *(vv (Li.L.get! (i))-vv (Li.L.get! (i+1)))/ ((q/4)*β *n)):= by
  gcongr
  apply mul_nonneg
  apply dens_nonneg
  apply div_nonneg
  exact vv_nonneg (Li.L.get! i)
  exact vv_nonneg (Li.L.get! (i + 1))


  apply mul_nonneg
  exact gt_implies_gte_rational ε 0 εPositive
  simp only [sub_nonneg]

  apply nested_graphs_vv_increase
  apply Li.Nested
  exact hk

  apply LiLarge
  repeat assumption







lemma improving_list_total_density
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(Li: density_improving_list iSub ε β  n q)
(εβ: ε*4/(β*q)≤ 1/2)
(βSmall: β≤ 1)
(hget0: vv (Li.L.get! 0)=  n)
(k: ℕ )
(hk: k< Li.L.length)
:
dens (Li.L.get! (k))≥ (dens (Li.L.get! (0)))*(vv (Li.L.get! (0)) / vv (Li.L.get! (k)))*(1-ε *(vv (Li.L.get! (0))-vv (Li.L.get! (k)))/ ((q/4)*β* n))

:= by
induction' k with k IH
calc
  dens (Li.L.get! 0)
  ≥ dens (Li.L.get! 0):= by
    simp
  _=dens (Li.L.get! 0)*1:= by
    ring_nf
  _=dens (Li.L.getD 0 default) * (vv (Li.L.getD 0 default) / vv (Li.L.getD 0 default)):= by
    congr
    exact List.get!_eq_getD Li.L 0
    refine (div_self ?_).symm
    have h1: vv (Li.L.getD 0 default)>0:= by
      apply improving_list_vv_positive_getD
      repeat assumption
      --exact Nat.zero_lt_of_lt hk


    exact Ne.symm (ne_of_lt h1)

  _=dens (Li.L.getD 0 default) * vv (Li.L.getD 0 default) / vv (Li.L.getD 0 default):= by
    ring_nf
  _=dens (Li.L.get! 0) * (vv (Li.L.get! 0) / vv (Li.L.get! 0)) * (1 - ε * (vv (Li.L.get! 0) - vv (Li.L.get! 0)) / ((q/4)*β * n)):= by
    field_simp


-----induction
have kle1: k+1< Li.L.length:= by
  exact hk--Nat.lt_of_succ_lt hk
have kle2: k< Li.L.length:= by
  exact Nat.lt_of_succ_lt kle1

calc
dens (Li.L.get! (k + 1))
≥
(dens (Li.L.get! (k)))
*(vv (Li.L.get! (k)) / vv (Li.L.get! (k+1)))
*(1-ε *(vv (Li.L.get! (k))-vv (Li.L.get! (k+1)))/ ((q/4)*β *n))  := by
  apply improving_list__weakening
  repeat assumption



_≥
(
(dens (Li.L.get! (0)))
*(vv (Li.L.get! (0)) / vv (Li.L.get! (k)))
*(1-ε *(vv (Li.L.get! (0))-vv (Li.L.get! (k)))/ ((q/4)*β* n))
)
*(vv (Li.L.get! (k)) / vv (Li.L.get! (k+1)))
*(1-ε *(vv (Li.L.get! (k))-vv (Li.L.get! (k+1)))/ ((q/4)*β *n))  := by
  gcongr --?_*(vv (Li.L.get! (k)) / vv (Li.L.get! (k+1)))*(1-ε *(vv (Li.L.get! (k))-vv (Li.L.get! (k+1)))/ (β *n))
  --should just be a calculation
  simp only [ sub_nonneg]
  calc
    ε * (vv (Li.L.get! k) - vv (Li.L.get! (k + 1))) / (q / 4 * β * n)
    ≤ ε *(vv (Li.L.get! k) - 0) / (q / 4 * β * n):= by
      gcongr
      exact vv_nonneg (Li.L.get! (k + 1))

    _=ε *(vv (Li.L.get! k)) / (q / 4 * β * n):= by
      ring_nf
    _≤ε *(n) / (q / 4 * β * n):= by
      gcongr
      apply improving_list_vv_le_n
      repeat assumption
    _=ε  / (q / 4 * β )*(n/n):= by
      field_simp
      linarith
    _=ε  / (q / 4 * β )*(1):= by
      congr
      field_simp
    _=ε*4/(β*q):= by
      field_simp
      linarith
    _≤ 1/2:= by
      exact εβ
    _≤ 1:= by
      exact half_le_self rfl

  apply div_nonneg
  exact vv_nonneg (Li.L.get! k)
  exact vv_nonneg (Li.L.get! (k + 1))

  apply IH
  exact Nat.lt_of_succ_lt hk


_=

(dens (Li.L.get! (0)))
*(vv (Li.L.get! (0)) / vv (Li.L.get! (k+1)))
*(vv (Li.L.get! (k)) / vv (Li.L.get! (k)))
*(1- ε *(vv (Li.L.get! (0))-vv (Li.L.get! (k+1)))/((q/4)*β * n)
+ ε^2 *(vv (Li.L.get! (0))-vv (Li.L.get! (k)))*(vv (Li.L.get! (k))-vv (Li.L.get! (k+1)))/ ((q/4)*β* n)^2)
:= by
  ring_nf
_≥
(dens (Li.L.get! (0)))
*(vv (Li.L.get! (0)) / vv (Li.L.get! (k+1)))
*(vv (Li.L.get! (k)) / vv (Li.L.get! (k)))
*(1- ε *(vv (Li.L.get! (0))-vv (Li.L.get! (k+1)))/((q/4)*β * n)
+ 0):= by
  gcongr
  apply mul_nonneg
  apply mul_nonneg
  apply dens_nonneg
  apply div_nonneg
  apply vv_nonneg
  apply vv_nonneg
  apply div_nonneg
  apply vv_nonneg
  apply vv_nonneg
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  exact sq_nonneg ε
  simp only [sub_nonneg]
  rw[hget0]
  apply improving_list_vv_le_n
  repeat assumption
  simp only [sub_nonneg]
  apply nested_graphs_vv_increase
  apply Li.Nested
  exact  hk
  have h1:((β * n) ^ 2).inv=1/((β * n) ^ 2):= by
    apply eq_one_div_of_mul_eq_one_left
    refine (IsUnit.mul_eq_one_iff_eq_inv ?_).mpr rfl
    refine isUnit_iff_exists_inv.mpr ?h.a
    refine Exists.intro ?h.a.w ?h.a.h
    exact (1/(β * n)^2)
    field_simp
  have h1:(((q / 4 * β * n) ^ 2)).inv=1/(((q / 4 * β * n) ^ 2)):= by
    apply eq_one_div_of_mul_eq_one_left
    refine (IsUnit.mul_eq_one_iff_eq_inv ?_).mpr rfl
    apply isUnit_iff_exists_inv.mpr
    use  (1/((q / 4 * β * n) ^ 2))
    field_simp


  rw[h1]
  apply div_nonneg
  exact rfl
  exact sq_nonneg (q / 4 * β * n)

  --apply div_nonneg
  --exact rfl
  --exact sq_nonneg (β * n)

_=
(dens (Li.L.get! (0)))
*(vv (Li.L.get! (0)) / vv (Li.L.get! (k+1)))
*(1)
*(1- ε *(vv (Li.L.get! (0))-vv (Li.L.get! (k+1)))/((q/4)*β * n)
+ 0)
:= by
  congr
  refine div_self ?_
  have h1:vv (Li.L.get! k)>0:= by
    apply improving_list_vv_positive
    repeat assumption
  exact Ne.symm (ne_of_lt h1)
_=
dens (Li.L.get! 0)
* (vv (Li.L.get! 0) / vv (Li.L.get! (k + 1)))
* (1 - ε * (vv (Li.L.get! 0) - vv (Li.L.get! (k + 1))) / ((q/4)*β * n)):= by
  ring_nf

lemma inv_eq
(q:ℚ)
(hq: q> 0)
:
q.inv=1/q
:=by
apply eq_one_div_of_mul_eq_one_left
refine (IsUnit.mul_eq_one_iff_eq_inv ?_).mpr rfl
apply isUnit_iff_exists_inv.mpr
use  (1/q)
field_simp


lemma improving_list_total_density2
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(Li: density_improving_list iSub ε β  n q)
(εβ: ε*4/(β*q)≤ 1/2)
(βSmall: β≤ 1)
(hn: vv (Li.L.get! (0))=n)
(k: ℕ )
(hk: k< Li.L.length)

:
dens (Li.L.get! (k))≥ (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))*(1-ε*4 /(β*q) )
:= by
calc
dens (Li.L.get! (k))≥ (dens (Li.L.get! (0)))*(vv (Li.L.get! (0)) / vv (Li.L.get! (k)))*(1-ε *(vv (Li.L.get! (0))-vv (Li.L.get! (k)))/ ((q/4)*β* n)):= by
  exact    improving_list_total_density iSub ε β n q βPositive nPositive εPositive qPositive qSmall Li εβ  βSmall hn k hk
_=(dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))*(1-ε *((n-vv (Li.L.get! (k)))/ ((q/4)*β* n))):= by
  rw[hn]
  ring_nf
_≥ (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))*(1-(ε*4)/(β*q)):= by
  gcongr
  apply mul_nonneg
  apply mul_nonneg
  apply ee_nonneg
  rw [hn]
  rw[inv_eq]
  apply div_nonneg
  exact rfl
  exact sq_nonneg n
  exact sq_pos_of_pos nPositive
  apply div_nonneg
  exact gt_implies_gte_rational n 0 nPositive
  apply vv_nonneg
  calc
    ε * ((n - vv (Li.L.get! k)) / (q / 4 * β * n))
    ≤ε * ((n - 0) / (q / 4 * β * n)):=by
      gcongr
      apply vv_nonneg
    _=(ε  / (q / 4 * β))*(n/n):=by
      ring_nf
    _=(ε  / (q / 4 * β))*(1):=by
      congr
      field_simp
    _=ε * 4 / (β * q):=by
      field_simp
      ring_nf




lemma improving_list_total_density3
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(βSmall: β≤ 1)
(εβ: ε*4/(β*q)≤ 1/2)
(Li: density_improving_list iSub ε β  n q)
(hn: vv (Li.L.get! (0))=n)
(k: ℕ )
(hk: k< Li.L.length)
:
dens (Li.L.get! (k))≥ (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))/2
:= by
calc
dens (Li.L.get! (k))
≥ (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))*(1-ε*4/(β*q) )
:= by
  apply improving_list_total_density2 iSub ε β n q _ _ _ _ _ _ _ _ _ k
  repeat assumption-- βPositive nPositive εPositive qPositive qSmall Li hn k hk hk2
_≥
 (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))*(1/2):= by
  gcongr
  apply mul_nonneg
  apply dens_nonneg
  apply div_nonneg
  exact gt_implies_gte_rational n 0 nPositive
  apply vv_nonneg
  refine le_tsub_of_add_le_left ?h.h
  refine le_sub_iff_add_le.mp ?h.h.a
  ring_nf
  calc
    ε * β⁻¹ * q⁻¹ * 4 =ε*4/(β*q):=by ring_nf
    _≤ 1/2 :=by exact εβ
_= (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))/2:= by
  ring_nf




lemma improving_list_total_density4
(ε β  n q : ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(βSmall: β≤ 1)
(εβ: ε*4/(β*q)≤ 1/2)

(Li: density_improving_list iSub ε β  n q)
(hn: vv (Li.L.get! (0))=n)
(k: ℕ )
(hk: k< Li.L.length)
:
dens (Li.L.get! (k))≥ (dens (Li.L.get! (0)))/2
:= by
calc
dens (Li.L.get! (k))
≥ (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))/2
:= by
  apply improving_list_total_density3 iSub ε β n q
  repeat assumption--βPositive nPositive εPositive qPositive qSmall εβ Li hn k hk hk2
_≥ (dens (Li.L.get! (0)))*(1)/2
:= by
  gcongr
  apply dens_nonneg
  refine (one_le_div ?hab.h.hb).mpr ?hab.h.a
  exact improving_list_vv_positive iSub ε β n q βPositive nPositive qPositive qSmall βSmall Li hn k hk
  apply improving_list_vv_le_n
  repeat assumption
_=(dens (Li.L.get! (0)))/2
:= by
  ring_nf




lemma dens_le_1
(H: Subgraph G)
(nonemp: vv H>0)
:
dens H≤ 1
:= by
unfold dens
refine (div_le_one ?hb).mpr ?_
exact sq_pos_of_pos nonemp
unfold ee
unfold vv

calc
(H.edgeSet.toFinset.card:ℚ )≤
↑(H.verts.toFinset.card*H.verts.toFinset.card)
:= by
  refine nat_le_rat H.edgeSet.toFinset.card (H.verts.toFinset.card * H.verts.toFinset.card) ?hle
  calc
    H.edgeSet.toFinset.card≤  H.verts.toFinset.card^2:= by
      exact lower_bound_vertices_by_edges_weaker H
    _= H.verts.toFinset.card* H.verts.toFinset.card:= by
      ring_nf
_= ↑H.verts.toFinset.card*↑H.verts.toFinset.card
:= by
  simp
_=
↑H.verts.toFinset.card ^ 2
:= by
  ring_nf




lemma improving_list_order_lower_bound
(ε β  n q δ: ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(qPositive: q>0)
(qSmall: q/4≤ 1)
(βSmall: β≤ 1)
(εβ: ε*4/(β*q)≤ 1/2)

(Li: density_improving_list iSub ε β  n q)
(hDense: dens (Li.L.get! (0))≥ δ )
(hn: vv (Li.L.get! (0))=n)
(k: ℕ )
(hk: k< Li.L.length)
:
vv (Li.L.get! (k)) ≥ n*δ/2--n*(dens (Li.L.get! (0)))/2
--dens (Li.L.get! (k))≥ (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))/2
:= by
have hup: 1≥ (n*δ/2)/ (vv (Li.L.get! (k))):= by
  calc
    1≥dens (Li.L.get! (k)):= by
      apply dens_le_1
      apply improving_list_vv_positive
      repeat assumption
      --exact Nat.lt_of_succ_lt hk

    _≥ (dens (Li.L.get! (0)))*(n / vv (Li.L.get! (k)))/2:= by
      apply improving_list_total_density3
      repeat assumption


    _=(n*(dens (Li.L.get! (0)))/2)/ (vv (Li.L.get! (k))):= by
      ring_nf
    _≥ (n*δ/2)/ (vv (Li.L.get! (k))):= by
      gcongr
      exact vv_nonneg (Li.L.get! k)



have h2: vv (Li.L.get! (k))>0:= by
      apply improving_list_vv_positive
      repeat assumption
      --exact Nat.lt_of_succ_lt hk

simp
simp at hup
--field_simp
field_simp at hup
calc
  n * δ / 2 =
  n * δ / 2 *1:= by
    ring_nf
  _=  n * δ / 2*( (vv (Li.L.getD k default))/ (vv (Li.L.getD k default))):= by
    congr
    symm
    apply div_self
    simp at h2
    exact Ne.symm (ne_of_lt h2)
  _=(n * δ / (2 * vv (Li.L.getD k default)))*(vv (Li.L.getD k default)):= by
    field_simp
  _≤ 1*vv (Li.L.getD k default):= by
    gcongr
    apply vv_nonneg
  _= vv (Li.L.getD k default):= by
    ring_nf








lemma improving_list_vv_get_upper_bound
(ε β  n q : ℚ  )
(Li: density_improving_list iSub ε β  n q)
(i: ℕ )
(hi: i+1< Li.L.length)
:
 (Li.L.get! (i+1)).verts.toFinset.card≤    (Li.L.get! (0)).verts.toFinset.card-i
:= by
induction' i with i HI
simp only [zero_add,   tsub_zero]
apply Nat.le_of_lt
apply Li.Strictily_Decreasing
exact hi

calc
  (Li.L.get! (i + 1 + 1)).verts.toFinset.card
  ≤ (Li.L.get! (i + 1)).verts.toFinset.card-1:=by
    have h1: (Li.L.get! (i + 1 + 1)).verts.toFinset.card<(Li.L.get! (i + 1)).verts.toFinset.card:= by
      apply Li.Strictily_Decreasing
      exact hi
    exact Nat.le_sub_one_of_lt h1
  _≤
  (Li.L.get! 0).verts.toFinset.card - i-1:= by
    gcongr
    apply HI
    exact Nat.lt_of_succ_lt hi







lemma improving_list_vv_get_upper_bound2
(ε β  n q : ℚ  )
(Li: density_improving_list iSub ε β  n q)
(hi: ((Li.L.get! (0)).verts.toFinset.card+1+1)< Li.L.length)
:
(Li.L.get! ((Li.L.get! (0)).verts.toFinset.card+1+1)).verts.toFinset.card<0:= by --≤    (Li.L.get! (0)).verts.toFinset.card-i

calc
(Li.L.get! ((Li.L.get! (0)).verts.toFinset.card+1+1)).verts.toFinset.card<(Li.L.get! ((Li.L.get! (0)).verts.toFinset.card+1)).verts.toFinset.card:= by
  apply Li.Strictily_Decreasing
  exact hi
_≤ (Li.L.get! (0)).verts.toFinset.card-(Li.L.get! (0)).verts.toFinset.card:= by
  apply improving_list_vv_get_upper_bound
  exact Nat.lt_of_succ_lt hi
_=0:= by exact Nat.sub_self (Li.L.get! 0).verts.toFinset.card



lemma vge20
(H: Subgraph G)
(h: vv H≥ 20)
:
H.verts.toFinset.card≥ 20
:= by
unfold vv at h
simp at h
simp
exact h

theorem cut_dense_existence0
--(δ: ℕ )--p≫ q
(ε β  n q δ: ℚ  )
(βPositive: β>0)
(nPositive: n>0)
(εPositive: ε>0)
(qPositive: q>0)
(δPositive: δ>0)
(qSmall: q/4≤ 1)
(βSmall: β ≤ 1)
(εβ: ε*4/(β*q)≤ 1/2)
(dpe: δ / 2 ≥ 32 / (↑p * ε))
(dq: δ / 2 ≥q)
(db: (δ/2)≥ β )
(δSmall: δ / 2 ≤ 1)
(εSmall: ε ≤ 1/4)
(εδ: ε≤ δ/2)
(nd: n≥ 40/δ)
(H: Subgraph G)
(HEdges: dens H≥ δ )
(Hvertices: vv H=n)
--q*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
:∃ (D: Subgraph G), D ≤ H ∧ (vv D≥ ε * n) ∧ cut_dense G D p:= by

let S:Set ℕ := {k: ℕ| ∃ (Li: density_improving_list iSub ε β  n q),  (Li.L.get! (0)=H) ∧ (Li.L.length=k+1) }

--have S_bounded_by_n: Bdd

let k:= sSup S

have Snonempty:  S.Nonempty:= by
  use 0
  dsimp[S]
  refine Exists.intro ?h.w ?h.h --simp only [List.get!_eq_getD]
  refine
    { L := ?h.w.L, Nested := ?_, Density_Increase := ?h.w.Density_Increase,
      Strictily_Decreasing := ?h.w.Strictily_Decreasing, Order_decrease := ?h.w.Order_decrease,
      Large := ?h.w.Large, Dense := ?h.w.Dense }
  exact [H]
  repeat intro i hi;  simp at hi
  simp


have Sboundedabove: BddAbove S:=by
  refine bddAbove_def.mpr ?_
  use (H).verts.toFinset.card+1+1
  intro k hk
  by_contra cont
  simp only [not_le] at cont
  dsimp[S] at hk
  rcases hk with ⟨Li, hLi1, hLi2 ⟩
  have h1: (Li.L.get! ((H).verts.toFinset.card+1+1)).verts.toFinset.card<0:= by
    rw[hLi1.symm]
    apply improving_list_vv_get_upper_bound2
    rw[hLi2]
    rw[hLi1]
    exact Nat.lt_add_right 1 cont
  have h2: ¬ ((Li.L.get! ((H).verts.toFinset.card+1+1)).verts.toFinset.card<0):= by
    simp
  exact h2 h1


have kmax1: k∈ S:= by
  dsimp[k]
  exact Nat.sSup_mem Snonempty Sboundedabove

have kmax3:k+1∉ S:= by
  have kmax2: ∀ (i:ℕ ), i>k→ i∉ S:= by
    dsimp [k]
    exact fun i a ↦ not_mem_of_csSup_lt a Sboundedabove
  apply kmax2
  exact lt_add_one k

--have hex:  ∃ (Li: density_improving_list iSub ε β  n q),  (Li.L.get! (0)=H) ∧ (Li.L.length=k+1)∧ (Li.LargeLimit=k+1):= by
dsimp[S] at kmax1
--simp only [List.get!_eq_getD] at kmax1
rcases kmax1 with ⟨Li, hLi1, hLi2 ⟩


have hlarge:vv (Li.L.get! (k))≥ n*δ/2:= by
  apply improving_list_order_lower_bound
  repeat assumption
  rw[hLi1]
  assumption
  rw[hLi1]
  assumption
  rw [hLi2]
  simp





have hdense: dens (Li.L.get! (k))≥ δ /2:= by
  calc
    dens (Li.L.get! (k))
    ≥ dens (Li.L.get! (0))/2:= by
      apply improving_list_total_density4
      repeat assumption
      rw[hLi1]
      assumption
      rw [hLi2]
      simp
    _≥ δ /2:= by gcongr; rw[hLi1]; exact HEdges



by_contra cont
push_neg at cont





have KnewEx:
∃ (K: Subgraph G),
(K≤ (Li.L.get! (k)))
∧
(vv K≥  (δ/2)*(vv (Li.L.get! (k)))/4)
∧
(
(dens K≥ (dens (Li.L.get! (k)))*(vv (Li.L.get! (k)) / vv K)*(1-ε *(vv (Li.L.get! (k))-vv K)/ (vv K)))
)
∧ (K.verts.toFinset.card< (Li.L.get! (k)).verts.toFinset.card)
:= by
  apply combined_inequality_graph_alt (Li.L.get! (k)) p _ _ ε (δ/2)
  --δ / 2 ≥ 32 / (↑p * ε)
  simp
  exact δPositive
  exact  dpe
  --δ / 2 ≤ 1
  exact δSmall
  exact εPositive
  --(Li.L.get! k).verts.toFinset.card ≥ 20
  apply vge20
  calc
    vv (Li.L.get! k) ≥
    n*δ/2:= by exact hlarge
    _≥ 40/δ*δ/2:= by
      gcongr
    _=40/2*(δ/δ):= by
      ring_nf
    _= 20*1:= by
      congr
      refine div_self ?_
      exact Ne.symm (ne_of_lt δPositive)
    _=20:= by ring_nf

  exact hdense
  -- 32 / (↑p * ε) ≤ 1
  calc
    32 / (↑p * ε)≤ δ/2:= by exact dpe
      _≤ 1:= by exact δSmall
  --ε ≤ 1 / 4
  exact εSmall
  exact Nat.not_eq_zero_of_lt pPositive
  --¬G.cut_dense (Li.L.get! k) p
  apply cont
  rw[hLi1.symm]
  apply improving_list_nested_in_0
  rw[hLi2]
  exact lt_add_one k
  --vv (Li.L.get! k) ≥ ε * n
  calc
    vv (Li.L.get! k) ≥
     n*δ/2:= by exact hlarge
     _=(δ/2)*n:= by ring_nf
      _≥ ε * n:=by
      gcongr






rcases KnewEx with ⟨K, Ksub, Kord, Kden, Kstrict ⟩

let L: List (Subgraph G):=Li.L++[K]

have Llength: L.length=Li.L.length+1:= by
  dsimp[L]
  calc
  L.length=Li.L.length+[K].length:= by
    exact List.length_append Li.L [K]
  _= Li.L.length+1:= by
    congr


have Llength2: L.length=k+1+1:= by
  rw[Llength]
  exact congrFun (congrArg HAdd.hAdd hLi2) 1

have Lget:  ∀ (i: ℕ ), i< k+1→ L.get! (i)= Li.L.get! (i):=by
  intro i hi
  dsimp [L]
  simp
  rw [List.getD_append]
  rw[hLi2]
  exact hi


have LgetN:L.get! (k+1)=K:= by
  dsimp [L]
  simp
  rw [List.getD_append_right]
  rw[hLi2]
  simp
  rw[hLi2]


have Nested: ∀ (i: ℕ ), i+1< L.length→ L.get! (i)≥ L.get! (i+1):= by
  intro i hi
  by_cases case: i+1<k+1
  rw[Lget i _];
  rw[Lget (i+1) _];
  apply Li.Nested
  rw[hLi2]
  exact case
  exact case
  exact Nat.lt_of_succ_lt case
  --neg----------
  simp at case
  have ipeq: i  = k := by
    rw[Llength2] at hi
    simp at hi
    refine Nat.le_antisymm ?h₁ case
    exact Nat.le_of_lt_succ hi
  rw[ipeq]
  rw[Lget k _];
  rw[LgetN]
  exact Ksub
  simp


have Strictily_Decreasing:  ∀ (i: ℕ ), i+1< L.length→ (L.get! (i)).verts.toFinset.card>  (L.get! (i+1)).verts.toFinset.card:=by
  intro i hi
  by_cases case: i+1<k+1
  rw[Lget i _];
  rw[Lget (i+1) _];
  apply Li.Strictily_Decreasing
  rw[hLi2]
  exact case
  exact case
  exact Nat.lt_of_succ_lt case
  --neg----------
  simp at case
  have ipeq: i  = k := by
    rw[Llength2] at hi
    simp at hi
    apply Nat.le_antisymm
    exact Nat.le_of_lt_succ hi
    exact case
  rw[ipeq]
  rw[Lget k _];
  rw[LgetN]
  exact Kstrict
  simp

have Density_Increase: ∀ (i: ℕ ), i+1< L.length→
    dens (L.get! (i+1))≥ (dens (L.get! (i)))*(vv (L.get! (i)) / vv (L.get! (i+1)))*(1-ε *(vv (L.get! (i))-vv (L.get! (i+1)))/ (vv (L.get! (i+1)))):= by
      intro i hi
      by_cases case: i+1<k+1
      rw[Lget i _];
      rw[Lget (i+1) _];
      apply Li.Density_Increase
      rw[hLi2]
      exact case
      exact case
      exact Nat.lt_of_succ_lt case
      --neg----------
      simp at case
      have ipeq: i  = k := by
        rw[Llength2] at hi
        simp at hi
        apply Nat.le_antisymm _ case
        exact Nat.le_of_lt_succ hi
      rw[ipeq]
      rw[Lget k _];
      rw[LgetN]
      exact Kden
      simp

have   Order_decrease:  ∀ (i: ℕ ), i+1< L.length→ vv (L.get! (i+1))≥  q*(vv (L.get! (i))/4):= by
      intro i hi
      by_cases case: i+1<k+1
      rw[Lget i _];
      rw[Lget (i+1) _];
      apply Li.Order_decrease
      rw[hLi2]
      exact case
      exact case
      exact Nat.lt_of_succ_lt case
      --neg----------
      simp at case
      have ipeq: i  = k := by
        rw[Llength2] at hi
        simp at hi
        apply Nat.le_antisymm _ case
        exact Nat.le_of_lt_succ hi
      rw[ipeq]
      rw[Lget k _];
      rw[LgetN]
      calc
        vv K ≥ _:= by exact Kord
        _=δ / 2 * (vv (Li.L.get! k) / 4):= by ring_nf
        _≥ q * (vv (Li.L.get! k) / 4):= by
          gcongr
          apply div_nonneg
          apply vv_nonneg
          simp


      simp

have   Large: ∀ (i: ℕ ), i+1<L.length→ vv (L.get! i)≥ β  * n:= by
  intro i hi
  by_cases case: i+1<k+1
  rw[Lget i _];
  apply Li.Large
  rw[Llength] at hi
  rw[hLi2]
  exact case
  exact Nat.lt_of_succ_lt case
  --neg----------
  simp at case
  have ipeq: i  = k := by
        rw[Llength2] at hi
        simp at hi
        apply Nat.le_antisymm _ case
        exact Nat.le_of_lt_succ hi
  rw[ipeq]
  rw[Lget k _];
  calc
    vv (Li.L.get! k)
    ≥ _:= by exact hlarge
    _=(δ/2)*n:= by
      ring_nf
    _≥ β * n:= by
      gcongr
  exact lt_add_one k


have   Dense: ∀ (i: ℕ ), i+1<L.length→ dens (L.get! i)≥ q:= by
  intro i hi
  by_cases case: i+1<k+1
  rw[Lget i _];
  apply Li.Dense
  rw[Llength] at hi
  rw[hLi2]
  exact case
  exact Nat.lt_of_succ_lt case
  --neg----------
  simp at case
  have ipeq: i  = k := by
        rw[Llength2] at hi
        simp at hi
        apply Nat.le_antisymm _ case
        exact Nat.le_of_lt_succ hi
  rw[ipeq]
  rw[Lget k _];
  calc
    dens (Li.L.get! k)
    ≥ _:= by exact hdense
    _≥ q:= by
      gcongr
  exact lt_add_one k

let Li': density_improving_list iSub ε β  n q:=⟨L, Nested,  Density_Increase, Strictily_Decreasing, Order_decrease, Large, Dense⟩


have hcont: k+1∈ S:= by
  dsimp[S]
  use Li'
  constructor
  dsimp [Li', L]
  simp
  rw[List.getD_append]
  simp at hLi1
  rw[hLi1]
  rw[hLi2]
  simp

  dsimp[Li']
  exact Llength2--

exact kmax3 hcont


/-lemma vPos_imp_verts_pos
(A: Finset V)
(h:v  A>0)
:
A.toFinset.card>0
:= by
unfold v at h
exact h
-/
lemma vAPos_imp_vertsB_decrease
(H: Subgraph G)
(A B: Finset V)
(h: vv H= v A+v B)
(hpos: v A>0)
:
H.verts.toFinset.card>B.card
:= by
unfold v at h
unfold vv at h
unfold v at hpos
have h1: (H.verts.toFinset.card :ℚ )> (B.card:ℚ):= by
  calc
    (H.verts.toFinset.card :ℚ )= (A.card :ℚ )+ (B.card:ℚ ):= by exact h
    _> 0+(B.card:ℚ ):= by
      gcongr
    _= B.card:= by
      ring_nf
simp at h1
simp
exact h1



theorem cut_dense_existence1
--d=1/δ
--1/n<<1/p≪  ε  << δ
--β=δ/2
--q=8ε/β = 16ε/δ=16*64/pδ^2
--eps=64/pδ
(n δ : ℚ)
--(ε β  n q δ: ℚ  )
--(βPositive: β>0)
(nPositive: n>0)
--(εPositive: ε>0)
--(qPositive: q>0)
(δPositive: δ>0)
(δSmall: δ≤ 1)
--(qSmall: q/4≤ 1)
--(βSmall: β ≤ 1)
--(εβ: ε*4/(β*q)≤ 1/2)
--(dpe: δ / 2 ≥ 32 / (↑p * ε))
--(dq: δ / 2 ≥q)
--(db: (δ/2)≥ β )
--(δSmall: δ / 2 ≤ 1)
--(εSmall: ε ≤ 1/4)
--(εδ: ε≤ δ/2)--p ≥ 128d^2
(pd:  256 / (p * δ ^ 2) ≤ 1)
(pd2: (↑p)⁻¹ * δ⁻¹ ^ 2 * 1024 ≤ δ * (1 / 2) )--2048 / (p * δ ^ 3) ≤ 1)
(pd3: 64 / (↑p * δ) ≤ 1 / 4)
(pd4: 64 / (↑p * δ) ≤ δ  / 2)
--(pd2: 256 / (↑p * δ) ≤ 1)
(nd: n≥ 40/δ)
(H: Subgraph G)
(HEdges: dens H≥ δ )
(Hvertices: vv H=n)
--q*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
:∃ (D: Subgraph G), D ≤ H ∧ (vv D≥ (64/(p*δ)) * n) ∧ cut_dense G D p:= by
let β := δ/2
let ε := 64/(p*δ)
let q := 16*64/(p*δ^2)
have βPositive: β>0:= by
  apply div_pos
  exact δPositive
  simp
have εPositive: ε>0:= by
  apply div_pos
  simp
  apply mul_pos
  simp
  exact pPositive
  exact δPositive
have qPositive: q>0:= by
  apply div_pos
  simp
  apply mul_pos
  simp
  exact pPositive
  exact sq_pos_of_pos δPositive
have qSmall: q/4≤ 1:= by
  dsimp[q]
  field_simp
  ring_nf
  field_simp
  exact pd
have βSmall: β ≤ 1:= by
  dsimp[β]
  apply (div_le_one ?_).2
  exact Preorder.le_trans δ 1 2 δSmall rfl
  simp
have εβ: ε*4/(β*q)≤ 1/2:= by
  dsimp[ε, β, q]
  field_simp
  ring_nf
  field_simp

have dpe: δ / 2 = 32 / (↑p * ε):= by
  dsimp[ε]
  field_simp
  ring_nf

have dpe: δ / 2 ≥  32 / (↑p * ε):= by
  exact le_of_eq (id dpe.symm)

have dq: δ / 2 ≥  q:= by
  dsimp[q]
  field_simp
  ring_nf
  exact pd2
have db: (δ/2)≥ β := by
  dsimp[β]
  exact (div_le_div_left δPositive rfl rfl).mpr rfl
have δSmall: δ / 2 ≤ 1:= by
  apply (div_le_one ?_).2
  exact Preorder.le_trans δ 1 2 δSmall rfl
  simp

have εSmall: ε ≤ 1/4:= by
  dsimp[ε]
  exact pd3
have εδ: ε≤ δ/2:= by
  dsimp[ε, β]
  exact pd4

apply  cut_dense_existence0 iSub ε β  n q δ
repeat assumption






/-
lemma improving_list_vv_get_upper_bound_one_step
(ε β  n q : ℚ  )
(Li: density_improving_list iSub ε β  n q)
(i: ℕ )
(hi: i+1< Li.L.length)
:
vv (Li.L.get! (i))≥   vv (Li.L.get! (i+1))+1
:=by
have h1: vv (Li.L.get! (i))>   vv (Li.L.get! (i+1)):=by
  apply Li.Strictily_Decreasing
  exact hi
have h2: (Li.L.get! (i)).verts.toFinset.card>   (Li.L.get! (i+1)).verts.toFinset.card:=by
  by_contra cont
  have h3: ¬ (vv (Li.L.get! (i))>   vv (Li.L.get! (i+1))):= by
    simp only [gt_iff_lt, not_lt]
    simp only [ gt_iff_lt, not_lt] at      cont
    unfold vv
    simp only [List.get!_eq_getD, Set.toFinset_card, Fintype.card_ofFinset, Nat.cast_le]
    simp at cont
    exact cont
  exact h3 h1


have h4:  (Li.L.get! (i)).verts.toFinset.card≥    (Li.L.get! (i+1)).verts.toFinset.card+1:= by
  exact h2
unfold vv
simp only [ ge_iff_le]
simp only [ge_iff_le] at h4
simp at h4
simp
apply?




-/










/-


lemma combined_inequality_graph
(H: Subgraph G)
(p': ℕ )
(p'Positive: p'≠ 0)
(not_cut_dense: ¬ cut_dense G H p')
(ε: ℚ)
(q: ℚ )
(hq: q≥ (32/(p'*ε) ))
(εPositive: ε>0)
--(hp: p=1/(p': ℚ ))
(Hlarge: H.verts.toFinset.card≥ 20)
(H_edges: dens H≥ (32/(p'*ε) ))
(pe_bound: 32/(p'*ε)≤  1 )
--(epos: ε>0)
(esmall: ε≤ 1/4)
:
∃ (K: Subgraph G),
(K≤ H)
∧
(vv K≥  q*(vv H)/4)
∧
(
(dens K≥ (dens H)*(vv H / vv K)*(1-ε *(vv H-vv K)/ (vv K)))
)
:= by









  L: List (Subgraph G)
  Nested: ∀ (i: ℕ ), i+1< L.length→ L.get! (i)≥ L.get! (i+1)
  Density_Increase: ∀ (i: ℕ ), i+1< L.length→
    dens (L.get! (i+1))≥ (dens (L.get! (i)))*(vv (L.get! (i)) / vv (L.get! (i+1)))*(1-ε *(vv (L.get! (i))-vv (L.get! (i+1)))/ (vv (L.get! (i+1))))
  Strictily_Decreasing:  ∀ (i: ℕ ), i+1< L.length→ vv (L.get! (i))> vv (L.get! (i+1))
  Order_decrease:  ∀ (i: ℕ ), i+1< L.length→ vv (L.get! (i+1))≥  q*(vv (L.get! (i))/4)
  --LargeLimit: ℕ
  --DenseLimit: ℕ
  Large: ∀ (i: ℕ ), i+1<L.length→  vv (L.get! i)≥ β  * n
  Dense: ∀ (i: ℕ ), i+1<L.length→  dens (L.get! i)≥ q



noncomputable def  v ( B: Finset V):ℚ  :=B.card
noncomputable def  e (H: Subgraph G) ( B: Finset V):ℚ  :=(H.induce B).edgeSet.toFinset.card
noncomputable def  vv (H: Subgraph G):ℚ  := H.verts.toFinset.card
noncomputable def ee (H: Subgraph G):ℚ := H.edgeSet.toFinset.card
--noncomputable def den (H: Subgraph G):ℚ := (e H)/(v H)^2--(H.edgeSet.toFinset.card: ℚ )/(H.verts.toFinset.card:ℚ )^2
noncomputable def eBip (H: Subgraph G) (A B: Finset V):ℚ :=
  (Rel.interedges H.Adj A B).card-/
