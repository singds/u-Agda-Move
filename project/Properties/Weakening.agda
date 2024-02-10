import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.Weakening
    {Nm Ns Nf Nsf Nfa : Data.Nat.ℕ}
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include P
open import project.Properties.ValueEval P
open import project.Properties.ValueType P

private
    variable
        n l     : ℕ
        Δ       : Env l
        M       : Fin Nm
        t t2    : Term
        T T1 T2 : Type

ins-before :
    {Γ1 Γ2 : UEnv Δ}
    {U : Usage T1}
    {x : ℕ}
    {i : Fin (suc l)}
    → HasTypeX Γ1 x T Γ2
    → ¬ x < (F.toℕ i)
    → HasTypeX (uInsert Γ1 i U) (suc x) T (uInsert Γ2 i U)
ins-before {i = F.zero} (Xz nLin) ¬p = Xs (Xz nLin)
ins-before {i = F.zero} (XzL yLin) ¬p = Xs (XzL yLin)
ins-before {i = F.zero} (Xs htx) ¬p = Xs (Xs htx)
ins-before {i = F.suc i}  (Xz nLin) ¬p = absurd (¬p (s≤s z≤n))
ins-before {i = F.suc i}  (XzL yLin) ¬p = absurd (¬p (s≤s z≤n))
ins-before {suc l}  {i = F.suc i} (Xs htx) ¬p = Xs (ins-before htx (¬sx<sy⇒¬x<y ¬p))

ins-after :
    {Γ1 Γ2 : UEnv Δ}
    {U : Usage T1}
    {x : ℕ}
    {i : Fin (suc l)}
    → HasTypeX Γ1 x T Γ2
    → x < (F.toℕ i)
    → HasTypeX (uInsert Γ1 i U) x T (uInsert Γ2 i U)
ins-after {i = F.suc i} (Xz nLin) p = Xz nLin
ins-after {i = F.suc i} (XzL yLin) p = XzL yLin
ins-after {suc l} {i = F.suc i} (Xs htx) p = Xs (ins-after htx (sx≤sy⇒x≤y p))

weakening :
    {Γ1 Γ2 : UEnv Δ}
    {U : Usage T1}
    {i : Fin (suc l)}
    -----------------------------------------------
    → HasType M Γ1 t2 T2 Γ2
    → HasType M (uInsert Γ1 i U) (shift 1 (F.toℕ i) t2) T2 (uInsert Γ2 i U)
 
weakening-vec :
    {Γ1 Γ2 : UEnv Δ}
    {ts : Vec Term n} {Ts : Vec Type n}
    {U : Usage T1}
    {i : Fin (suc l)}
    -----------------------------------------------
    → HasTypeV M Γ1 ts Ts Γ2
    → HasTypeV M (uInsert Γ1 i U) (shift-vec 1 (F.toℕ i) ts) Ts (uInsert Γ2 i U)

weakening-intro :
    {Γ1 Γ2 : UEnv Δ}
    {Ts : Vec Type n}
    {U : Usage T1}
    {i : Fin (suc l)}
    -----------------------------------------------
    → HasTypeI M Γ1 Ts t T Γ2
    → HasTypeI M (uInsert Γ1 i U) Ts (shift 1 ((F.toℕ i) + n) t) T (uInsert Γ2 i U)

weakening Tnum = Tnum

weakening {i = i} (Tvar {x = x} htx) with x <? (F.toℕ i)
... | yes x<i = Tvar (ins-after htx x<i)
... | no ¬x<i
    rewrite x+1≡sx {x}
    = Tvar (ins-before htx ¬x<i)
weakening {i = i} (TselX {x = x} htx nLin) with x <? (F.toℕ i)
... | yes x<i = TselX (ins-after htx x<i) nLin
... | no ¬x<i
    rewrite x+1≡sx {x}
    = TselX (ins-before htx ¬x<i) nLin
weakening {i = i} (TselV {t = t} v ht nLin)
    with shift 1 (F.toℕ i) t | shift-val-eq {1} {F.toℕ i} v
... | t' | refl = TselV v (value-type v ht) nLin

weakening {i = i} (Tlet ht hti)
    rewrite Eq.sym (x+1≡sx {x = (F.toℕ i)})
    = Tlet (weakening ht) (weakening-intro hti)
weakening (Tpack htv)           = Tpack (weakening-vec htv)
weakening {i = i} (Tstruct {ts = ts} vs htv)
    with shift-vec 1 (F.toℕ i) ts | shift-vec-val-eq {1} {F.toℕ i} vs
... | ts' | refl = Tstruct vs (value-type-vec vs htv)
weakening (Tcall htv)           = Tcall (weakening-vec htv)
weakening (Tunpack ht hti)      = Tunpack (weakening ht) (weakening-intro hti)
weakening (Texec ht)            = Texec ht
weakening (Tif ht1 ht2 ht3)     = Tif (weakening ht1) (weakening ht2) (weakening ht3)
weakening (Tpub ht yLin)        = Tpub (weakening ht) yLin



weakening-vec T[] = T[]
weakening-vec (ht T∷ htv) = weakening ht T∷ weakening-vec htv


weakening-intro {i = i}  I[ ht ]
    rewrite x+0≡x {x = (F.toℕ i)}
    = I[ weakening ht ]
weakening-intro {i = i} (_I∷_ {n = TsiLen} nLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (F.toℕ i)} {n = TsiLen})
    = nLin I∷ weakening-intro hti
weakening-intro {i = i} ( _I∷l_ {n = TsiLen} yLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (F.toℕ i)} {n = TsiLen})
    = yLin I∷l weakening-intro hti
