import MyProject

import MyProject.cut_dense_existence
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats  470000

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


lemma combined_inequality
(a b h A B H p: ℚ )
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
