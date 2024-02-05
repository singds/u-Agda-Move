import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.ValueType
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P

private
    variable
        l l2 n   : ℕ
        Δ        : Env l
        Γ        : UEnv Δ
        Δ2       : Env l2
        Γ1 Γ2    : UEnv Δ2
        t        : Term
        T        : Type
        M M1 M2  : Fin Nm

{-
If we can type a term that is a Value, we can change the current module of the
typing judgement, the input and output env., and we still get a valid typing judgement.
    M1 → M2    we change the current module
    Γ1 → Γ3      we change the env.s.
    Γ2 → Γ3
-}
value-type :
      Value t
    → HasType M1 Γ1 t T Γ2
    → HasType M2 Γ t T Γ
value-type-vec :
      {ts : Vec Term n}
      {Ts : Vec Type n}
    → ValueV ts
    → HasTypeV M1 Γ1 ts Ts Γ2
    → HasTypeV M2 Γ  ts Ts Γ

value-type Vnum Tnum = Tnum
value-type (Vstruct vv) (Tstruct vs htv) = Tstruct vs (value-type-vec vv htv)

value-type-vec V[]       T[] = T[]
value-type-vec (v V∷ vv) (ht T∷ htv) = (value-type v ht) T∷ (value-type-vec vv htv)

{-
If we type a term that is a value, the input env. is not modified.
The output env. of the typing judgement is the same as the input env.
-}
htval⇒Γ1≡Γ2 :
      Value t
    → HasType M1 Γ1 t T Γ2
    → Γ1 ≡ Γ2

htval⇒Γ1≡Γ2-vec :
      {ts : Vec Term n}
      {Ts : Vec Type n}
    → ValueV ts
    → HasTypeV M1 Γ1 ts Ts Γ2
    → Γ1 ≡ Γ2

htval⇒Γ1≡Γ2 v Tnum      = refl
htval⇒Γ1≡Γ2 (Vstruct vv) (Tstruct vs htv)
    rewrite htval⇒Γ1≡Γ2-vec vv htv = refl

htval⇒Γ1≡Γ2-vec V[] T[] = refl
htval⇒Γ1≡Γ2-vec (v V∷ vv) (ht T∷ htv) 
    rewrite htval⇒Γ1≡Γ2 v ht | htval⇒Γ1≡Γ2-vec vv htv = refl



htvLookup :
      {Δ : Env l}
      {Γ1 Γ2 : UEnv Δ}
      {n : ℕ} {ts : Vec Term n} {Ts : Vec Type n}
    → (vs  : ValueV ts)
    → (htv : HasTypeV M Γ1 ts Ts Γ2)
    → (i   : Fin n)
    → HasType M Γ1 (V.lookup ts i) (V.lookup Ts i) Γ2
htvLookup (v V∷ vs) (ht T∷ htv) i with htval⇒Γ1≡Γ2 v ht | htval⇒Γ1≡Γ2-vec vs htv
htvLookup (v V∷ vs) (ht T∷ htv) F.zero    | refl | refl = ht
htvLookup (v V∷ vs) (ht T∷ htv) (F.suc i) | refl | refl = htvLookup vs htv i
