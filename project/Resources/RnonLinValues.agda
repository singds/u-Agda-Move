import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Resources.RnonLinValues
    {Nm Ns Nf Nsf Nfa : Data.Nat.ℕ}
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    (W : Typing.WellProg Nm Ns Nf Nsf Nfa P)
    where

open import project.Properties.Include P

private
    variable
        t t'    : Term
        n l lv  : ℕ
        M M2    : Fin Nm

-- Resources of non-linear values
RnLin     :
    {Δ : Env l}
    {Γ1 Γ2 : UEnv Δ}
    {t : Term} {T : Type}
    → HasType M Γ1 t T Γ2
    → ¬ IsLinear T
    → Value t
    → R t ≡ L.[]
RnLin-vec :
    {Δ : Env l}
    {Γ1 Γ2 : UEnv Δ}
    {ts : Vec Term n}
    {Ts : Vec Type n}
    → HasTypeV M Γ1 ts Ts Γ2
    → ((j : Fin n) → ¬ IsLinear (V.lookup Ts j))
    → ValueV ts
    → Rv ts ≡ L.[]

RnLin ht nLin Vnum = refl
RnLin (Tstruct {s = s} {M2 = M2} _ htv) nLin (Vstruct {sid = sid} vs) with tyIsLin (Tst sid)
... | yes yLin  = absurd (nLin yLin)
... | no  nLin  = RnLin-vec htv f vs
    where
        f = (WellStr.nLin (WellMod.ws (W M2) s)) nLin
 
RnLin-vec ht nLin V[] = refl 
RnLin-vec (_T∷_ {t = t} {ts = ts} ht htv) nLin (v V∷ vs)
    with R t | Rv ts | RnLin ht (nLin F.zero) v with RnLin-vec htv (nLin ∘ F.suc) vs
... | .L.[] | .L.[] | refl | refl = refl
