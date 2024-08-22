import MyProject

import MyProject.cut_dense_2existence
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats  270000

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



theorem cut_dense_existence2
(n δ : ℚ)
(nPositive: n>0)
(δPositive: δ>0)
(δSmall: δ≤ 1)
(pd0:  2048 ≤ p*δ^3  )
(nd: n≥ 40/δ)
(H: Subgraph G)
(HEdges: dens H≥ δ )
(Hvertices: vv H=n)
:∃ (D: Subgraph G), D ≤ H ∧ (vv D≥ (64/(p*δ)) * n) ∧ cut_dense G D p:= by
have pd2: (↑p)⁻¹ * δ⁻¹ ^ 2 * 1024 ≤ δ * (1 / 2):= by
  ring_nf
  apply mult_accross_ge
  ring_nf
  apply mult_accross_ge
  simp
  ring_nf
  field_simp
  apply (div_le_div_iff _ _).2
  simp
  rw[mul_comm]
  exact pd0
  simp
  exact pPositive
  simp
  field_simp
  simp

have pd3: 64 / (↑p * δ) ≤ 1 / 4:= by
  ring_nf
  apply mult_accross_ge
  ring_nf
  apply mult_accross_ge
  simp
  ring_nf
  field_simp
  apply (div_le_div_iff _ _).2
  simp
  rw[mul_comm]
  calc
    (p:ℚ ) * δ= (p:ℚ ) * δ*1*1:= by
      ring_nf
    _≥ (p:ℚ) * δ*δ *δ := by
      gcongr
    _= (p:ℚ )*δ^3:= by ring_nf
    _≥ 2048:= by
      exact pd0
    _≥ 256:= by
      exact rfl
  simp
  exact pPositive
  simp
  field_simp
  exact δPositive
  simp


have pd4: 64 / (↑p * δ) ≤ δ  / 2:= by
  ring_nf
  apply mult_accross_ge
  ring_nf
  apply mult_accross_ge
  simp
  ring_nf
  field_simp
  apply (div_le_div_iff _ _).2
  simp
  rw[mul_comm]
  calc
    (p:ℚ ) * δ^2= (p:ℚ ) * δ*δ *1:= by
      ring_nf
    _≥ (p:ℚ) * δ*δ *δ := by
      gcongr
    _= (p:ℚ )*δ^3:= by ring_nf
    _≥ 2048:= by
      exact pd0
    _≥ 128:= by
      exact rfl
  simp
  exact pPositive
  simp
  field_simp
  exact δPositive
  simp

have pd:  256 / (p * δ ^ 2) ≤ 1:= by
  ring_nf
  apply mult_accross_ge
  ring_nf
  apply mult_accross_ge
  simp
  ring_nf
  field_simp
  apply (div_le_div_iff _ _).2
  simp
  rw[mul_comm]
  calc
    (p:ℚ ) * δ^2= (p:ℚ ) * δ*δ *1:= by
      ring_nf
    _≥ (p:ℚ) * δ*δ *δ  := by
      gcongr
    _= (p:ℚ )*δ^3:= by ring_nf
    _≥ 2048:= by
      exact pd0
    _≥ 256:= by
      exact rfl
  simp
  exact pPositive
  simp
  field_simp
  simp

apply cut_dense_existence1
repeat assumption




theorem cut_dense_existence3
(d: ℕ )
(dPositive: d>0)
(H: Subgraph G)
(hnd: H.verts.toFinset.card≥ 40*d)
(hedges: d*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
(hp: p= 2048*d^3)
:∃ (D: Subgraph G), D ≤ H ∧ (p*D.verts.toFinset.card≥ H.verts.toFinset.card) ∧ cut_dense G D p:= by
let δ : ℚ := 1/(d: ℚ)
let n : ℚ := vv H
have nPositive: n>0:= by
  dsimp[n]
  dsimp[vv]
  simp only [Nat.cast_pos]
  calc
    H.verts.toFinset.card≥ 40*d:= by assumption
    _> 0:= by
      apply mul_pos
      simp
      exact dPositive

have δPositive: δ>0:= by
  dsimp[δ]
  apply one_div_pos.2
  simp
  exact dPositive

have δSmall: δ≤ 1:= by
  dsimp[δ]
  apply (div_le_one _).2
  simp
  exact dPositive
  simp
  exact dPositive

have pd0:  2048 = p*δ^3:= by
  dsimp[δ]
  rw[hp]
  ring_nf
  field_simp

have pd0:  2048 ≤ p*δ^3:= by
  rw[pd0]

have nd: n≥ 40/δ:= by
  dsimp[n]
  dsimp[δ]
  simp
  unfold vv
  have h1 : (40: ℚ )*(d: ℚ ) = ((40*d: ℕ ):ℚ ):= by
    simp
  rw[h1]
  exact nat_le_rat (40 * d) H.verts.toFinset.card hnd

have HEdges: dens H≥ δ:= by
  dsimp[δ]
  unfold dens
  apply (div_le_div_iff _ _).2
  simp
  unfold vv
  unfold ee
  have h1 : (H.edgeSet.toFinset.card: ℚ )*(d: ℚ ) = ((H.edgeSet.toFinset.card*d: ℕ ):ℚ ):= by
    simp
  rw[h1]
  apply nat_le_rat
  ring_nf
  ring_nf at hedges
  rw[mul_comm]
  exact hedges
  simp
  exact dPositive
  dsimp[n] at nPositive
  exact sq_pos_of_pos nPositive




have hex: ∃ (D: Subgraph G), D ≤ H ∧ (vv D≥ (64/(p*δ)) * n) ∧ cut_dense G D p:= by
  apply cut_dense_existence2
  repeat assumption
  dsimp[n]

rcases hex with ⟨D, hD1, hD2, hD3⟩

use D

constructor
exact hD1
constructor
--unfold vv at hD2
dsimp [n] at hD2
--unfold vv at hD2
dsimp[δ] at hD2
have h4:p/(d*64)*(vv D)≥ vv H:= by
  calc
  p/(d*64) * vv D ≥
  (p/(d*64))* (64 / (↑p * (1 / ↑d)) * vv H):= by
    gcongr
  _= (p/(d*64))* (64 / (↑p * (1 / ↑d))) * vv H:= by ring_nf

  _=  1*vv H:= by
    congr
    calc
      _ --d / (64 * p) * (64 / (p * (1 / d)))
      = ((d:ℚ) *(1/(d:ℚ)))*((p:ℚ)/(p:ℚ)):= by
        ring_nf
        field_simp
        ring_nf
      _=
      1*1:= by
        field_simp
      _=1:= by
        ring_nf

  _= vv H:= by
    ring_nf

unfold vv at hD2

have h5: ((p * D.verts.toFinset.card:ℕ ):ℚ ) ≥ vv H:= by
  calc
    ((p * D.verts.toFinset.card:ℕ ):ℚ )
    =
    p  * vv D:= by
      unfold vv
      simp
    _=(p/1)  * vv D:= by ring_nf
    _≥  p / (d * 64) * vv D:= by
      gcongr
      apply vv_nonneg
      calc
        ((d: ℚ ) * (64: ℚ ))≥ d*1:= by
          gcongr
          simp
        _≥ 1:=by
          simp
          exact dPositive



    _≥ vv H:= by exact h4
unfold vv at h5
--simp at h5
--simp
simp only [ Nat.cast_le] at h5
exact h5

exact hD3




theorem cut_dense_existence4
--(d m: ℕ )
--(dPositive: d>0)
(H: Subgraph G)
(hnd: H.verts.toFinset.card≥ m)
(hedges: p*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
(hp: pr≥  2048*p^3)
(hm:  m≥ 40*p)
:∃ (D: Subgraph G), D ≤ H ∧ (D.verts.toFinset.card≥ m/pr) ∧ cut_dense G D pr:= by
let p':ℕ :=2048*p^3
have p'Positive: p'>0:= by
  dsimp[p']
  apply mul_pos
  simp
  exact Nat.pos_pow_of_pos 3 pPositive
have hex: ∃ (D: Subgraph G), D ≤ H ∧ (p'*D.verts.toFinset.card≥ H.verts.toFinset.card) ∧ cut_dense G D p':= by
  apply cut_dense_existence3
  assumption
  assumption
  exact pPositive

  calc
    H.verts.toFinset.card≥ m:= by assumption
    _≥ 40*p:= by assumption
  repeat assumption
  dsimp[p']
rcases hex with ⟨D, hD1, hD2, hD3⟩
use D
constructor
exact hD1
constructor
have h2: p' * D.verts.toFinset.card ≥ m:= by
  calc
    p' * D.verts.toFinset.card ≥ H.verts.toFinset.card:= by
      exact hD2
    _≥ m:= by
      assumption
have h3: D.verts.toFinset.card ≥ m/pr:= by
  calc
    D.verts.toFinset.card
    =p' * D.verts.toFinset.card/p':= by exact
      (Nat.mul_div_right D.verts.toFinset.card p'Positive).symm
    _≥ m/p':= by
      gcongr
    _≥ m/pr:= by
      gcongr
exact h3

apply Cut_Dense_monotone
have h5: p'≤ pr:= by
  dsimp[p']
  exact hp
exact h5
exact hD3




theorem cut_dense_existence5
--(d m: ℕ )
--(dPositive: d>0)
(H: Subgraph G)
(hnd: H.verts.toFinset.card≥ m/(2*p))
(hedges: p*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)
(hp: pr≥ 4096*p^4)-- (2*p)*(2048*p^3))
(hm:  m≥ 80*p^2)
:∃ (D: Subgraph G), D ≤ H ∧ (D.verts.toFinset.card≥ m/pr) ∧ cut_dense G D pr:= by
have hp: pr≥  (2*p)*(2048*p^3):= by
  calc pr≥ 4096*p^4:= by assumption
  _= (2*p)*(2048*p^3):= by
    ring_nf

have hm : m/(2*p)≥ 40*p:= by
  refine (Nat.le_div_iff_mul_le ?k0).mpr ?_
  apply mul_pos
  simp
  assumption
  ring_nf
  ring_nf at hm
  exact hm


let p':ℕ :=2048*p^3
have p'Positive: p'>0:= by
  dsimp[p']
  apply mul_pos
  simp
  exact Nat.pos_pow_of_pos 3 pPositive
have hex: ∃ (D: Subgraph G), D ≤ H ∧ (p'*D.verts.toFinset.card≥ H.verts.toFinset.card) ∧ cut_dense G D p':= by
  apply cut_dense_existence3
  assumption
  assumption
  exact pPositive

  calc
    H.verts.toFinset.card≥ m/(2*p):= by assumption
    _≥ 40*p:= by assumption
  repeat assumption
  dsimp[p']
rcases hex with ⟨D, hD1, hD2, hD3⟩
use D
constructor
exact hD1
constructor
have h2: p' * D.verts.toFinset.card ≥ m/(2*p):= by
  calc
    p' * D.verts.toFinset.card ≥ H.verts.toFinset.card:= by
      exact hD2
    _≥ m/(2*p):= by
      assumption
have h3: D.verts.toFinset.card ≥ m/pr:= by
  calc
    D.verts.toFinset.card
    =p' * D.verts.toFinset.card/p':= by exact
      (Nat.mul_div_right D.verts.toFinset.card p'Positive).symm
    _≥ m/(2*p)/p':= by
      gcongr
    _≥ m/pr:= by
      rw [Nat.div_div_eq_div_mul]
      gcongr

exact h3

apply Cut_Dense_monotone
have h5: p'≤ pr:= by
  dsimp[p']
  calc
    pr≥  (2*p)*(2048*p^3):= by assumption
    _≥ 1*(2048*p^3):= by
      gcongr
      apply Nat.one_le_of_lt
      apply mul_pos
      simp
      exact pPositive


    _= 2048*p^3:= by
      ring_nf
exact h5
exact hD3





/-

theorem near_regular_subgraph {H: Subgraph G}{p pr m:ℕ }(mggp: m≫ pr)(prggp: pr≫ p)(HEdges: p*H.edgeSet.toFinset.card≥ H.verts.toFinset.card^2)(HOrder: H.verts.toFinset.card≥ m): ∃ (H': Subgraph G), H' ≤ H ∧ near_regular H' (m/pr):= by

theorem cut_dense_existence1
(n δ : ℚ)
(nPositive: n>0)
(δPositive: δ>0)
(δSmall: δ≤ 1)
(pd:  256 / (p * δ ^ 2) ≤ 1)
(pd2: (↑p)⁻¹ * δ⁻¹ ^ 2 * 1024 ≤ δ * (1 / 2) )
(pd3: 64 / (↑p * δ) ≤ 1 / 4)
(pd4: 64 / (↑p * δ) ≤ δ  / 2)
(nd: n≥ 40/δ)
(H: Subgraph G)
(HEdges: dens H≥ δ )
(Hvertices: vv H=n)
:∃ (D: Subgraph G), D ≤ H ∧ (vv D≥ (64/(p*δ)) * n) ∧ cut_dense G D p:= by
-/
