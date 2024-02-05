{-# OPTIONS --allow-unsolved-metas #-}

import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.Strengthening-old
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa) 
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P
open import project.Properties.ValueEval Nm Ns Nf Nsf Nfa P
open import project.Properties.ValueType Nm Ns Nf Nsf Nfa P
open import project.Properties.FreeVar Nm Ns Nf Nsf Nfa P

private
    variable
        n x l   : ℕ
        M       : Fin Nm
        T T2    : Type
        t t2    : Term

rem-before :
    {Δ  : Env (suc l)}
    {Γ1 Γ2 : UEnv Δ}
    {i : Fin (suc l)}
    → HasTypeX Γ1 x T Γ2
    → ¬ x ≤ (toℕ i)
    → HasTypeX (uRemove Γ1 i) (x - 1) T (uRemove Γ2 i)
rem-before (Xz nLin)  ¬x≤i = absurd (¬x≤i z≤n)
rem-before (XzL yLin) ¬x≤i = absurd (¬x≤i z≤n)
rem-before {i = F.zero} (Xs {Γ1 = U1 u∷ Γ1} {Γ2 = U2 u∷ Γ2} htx) ¬x≤i = htx
rem-before {i = F.suc i} (Xs {x = 0} htx) ¬x≤i = absurd (¬x≤i (s≤s z≤n))
rem-before {i = F.suc i} (Xs {Γ1 = U1 u∷ Γ1} {x = suc x} {Γ2 = U2 u∷ Γ2} htx) ¬x≤i
    = Xs (rem-before htx (¬sx≤sy⇒¬x≤y ¬x≤i))

rem-after :
    {Δ  : Env (suc l)}
    {Γ1 Γ2 : UEnv Δ}
    {i : Fin (suc l)}
    → HasTypeX Γ1 x T Γ2
    → x < (toℕ i)
    → HasTypeX (uRemove Γ1 i) x T (uRemove Γ2 i)
rem-after {i = F.suc i} (Xz  {Γ = U u∷ Γ} nLin) x<i = Xz  nLin
rem-after {i = F.suc i} (XzL {Γ = U u∷ Γ} yLin) x<i = XzL yLin
rem-after {i = F.suc i} (Xs {Γ1 = U1 Typing.u∷ Γ1} {Γ2 = U2 Typing.u∷ Γ2} htx) x<i
    = Xs (rem-after htx (sx≤sy⇒x≤y x<i))



strength :
    {Δ  : Env (suc l)}
    {Γ1 Γ2 : UEnv Δ}
    {i : Fin (suc l)}
    -----------------------------------------------
    → HasType M Γ1 t2 T2 Γ2
    → (toℕ i) ∉ fv t2
    → HasType M (uRemove Γ1 i) (shift-back (toℕ i) t2) T2 (uRemove Γ2 i)

strength-vec :
    {Δ  : Env (suc l)}
    {Γ1 Γ2 : UEnv Δ}
    {ts : Vec Term n} {Ts : Vec Type n}
    {i : Fin (suc l)}
    -----------------------------------------------
    → HasTypeV M Γ1 ts Ts Γ2
    → (toℕ i) ∉ fvVec ts
    → HasTypeV M (uRemove Γ1 i) (shift-back-vec (toℕ i) ts) Ts (uRemove Γ2 i)

strength-intro :
    {Δ  : Env (suc l)}
    {Γ1 Γ2 : UEnv Δ}
    {Ts : Vec Type n}
    {i : Fin (suc l)}
    -----------------------------------------------
    → HasTypeI M Γ1 Ts t T Γ2
    → ((toℕ i) + n) ∉ fv t
    → HasTypeI M (uRemove Γ1 i) Ts (shift-back ((toℕ i) + n) t) T (uRemove Γ2 i)

strength Tnum nfv = Tnum
strength {i = i} (Tvar {x = x} htx) nfv with x <? (toℕ i)
... | yes x<i = Tvar (rem-after htx x<i)
... | no ¬x<i = Tvar (rem-before htx ¬x≤i')
    where
        ¬x≤i' = (¬x<y∧¬x≡y⇒¬x≤y ¬x<i (¬y∈fvx⇒¬y≡x (¬y∈fvx⇒¬x∈fvy nfv)))
    
strength {i = i} (TselX {x = x} htx nLin) nfv with x <? (toℕ i)
... | yes x<i = TselX (rem-after htx x<i) nLin
... | no ¬x<i = TselX (rem-before htx ¬x≤i') nLin
    where
        ¬x≤i' = (¬x<y∧¬x≡y⇒¬x≤y ¬x<i (¬y∈fvx⇒¬y≡x (¬y∈fvx⇒¬x∈fvy nfv)))
strength {i = i} (TselV {t = t} v ht nLin) nfv
    with shift-back (toℕ i) t | shift-back-val-eq {toℕ i} v
... | t' | refl = TselV v (value-type v ht) nLin

strength {i = i} (Tlet {t1 = t1} {t2 = t2} ht hti) nfv
    rewrite Eq.sym(x+1≡sx {x = (toℕ i)})
    = Tlet (strength ht
        (x∉fvlet⇒x∉fvt1 {t1 = t1} {t2 = t2} nfv))
        (strength-intro hti (x∉fvlet⇒x∉fvt2 {t1 = t1} {t2 = t2} nfv))
strength (Tpack htv) nfv = Tpack (strength-vec htv nfv)
strength {i = i} (Tstruct {ts = ts} vs htv) nfv
    with shift-back-vec (toℕ i) ts | shift-back-vec-val-eq {toℕ i} vs
... | ts' | refl = Tstruct vs (value-type-vec vs htv)
strength (Tcall htv) nfv = Tcall (strength-vec htv nfv)
strength (Tunpack {t1 = t1} {t2 = t2} ht hti) nfv
    = Tunpack (strength ht (x∉fvunp⇒x∉fvt1 {t1 = t1} {t2 = t2} nfv))
              (strength-intro hti (x∉fvunp⇒x∉fvt2 {t1 = t1} {t2 = t2} nfv))
strength (Texec ht) nfv = Texec ht
strength (Tif {t1 = t1} {t2 = t2} {t3 = t3} ht1 ht2 ht3) nfv
    = Tif (strength ht1 (¬x∈fvif⇒¬x∈fvt1 {t1 = t1} {t2 = t2} {t3 = t3} nfv))
          (strength ht2 (¬x∈fvif⇒¬x∈fvt2 {t1 = t1} {t2 = t2} {t3 = t3} nfv))
          (strength ht3 (¬x∈fvif⇒¬x∈fvt3 {t1 = t1} {t2 = t2} {t3 = t3} nfv))
strength (Tpub ht yLin) nfv = Tpub (strength ht nfv) yLin


strength-vec T[] nfv = T[]
strength-vec (_T∷_ {t = t} {ts = ts} ht htv) nfv
    = strength ht (x∉fvtts⇒x∉fvt {t = t} {ts = ts} nfv)
        T∷ strength-vec htv (x∉fvtts⇒x∉fvts {t = t} {ts = ts} nfv)


strength-intro {i = i} I[ ht ] nfv
    rewrite x+0≡x {x = (toℕ i)}
    = I[ (strength ht nfv) ]
strength-intro {Δ = T V.∷ Δ} {Γ1 = U1 u∷ Γ1} {Γ2 = U2 u∷ Γ2} {i = i} (_I∷_ {n = lTs} nLin hti) nfv
    rewrite Eq.sym(s<x+n>≡x+sn {(toℕ i)} {lTs})
    = nLin I∷ strength-intro {i = F.suc i} hti nfv
strength-intro {Δ = T V.∷ Δ} {Γ1 = U1 u∷ Γ1} {Γ2 = U2 u∷ Γ2} {i = i} (_I∷l_ {n = lTs} yLin hti) nfv
    rewrite Eq.sym (s<x+n>≡x+sn {(toℕ i)} {lTs})
    = yLin I∷l strength-intro hti nfv
 