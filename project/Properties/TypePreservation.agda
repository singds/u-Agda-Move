import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.TypePreservation
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    (W : Typing.WellProg Nm Ns Nf Nsf Nfa P)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P
open import project.Properties.ValueType Nm Ns Nf Nsf Nfa P
open import project.Properties.Substitution Nm Ns Nf Nsf Nfa P

private
    variable
        n l  : ℕ
        M    : Fin Nm
        Δ    : Env l
        t t' : Term
        T    : Type


type-preservation :
    {Γ1 Γ2 : UEnv Δ}
    → HasType M Γ1 t T Γ2
    → M ∋ t ⇒ t'
    → HasType M Γ1 t' T Γ2

type-preservation-vec :
    {Γ1 Γ2 : UEnv Δ}
    {ts ts' : Vec Term n} {Ts : Vec Type n}
    → HasTypeV M Γ1 ts Ts Γ2
    → M ∋ ts ⇒v ts'
    → HasTypeV M Γ1 ts' Ts Γ2

type-preservation (Tlet ht hti) (Elet ev)
    = Tlet (type-preservation ht ev) hti
type-preservation (Tlet ht hti) (Elet2 v)
    rewrite htval⇒Γ1≡Γ2 v ht
    = substi-multi (ht T∷ T[]) (v V∷ V[]) hti
type-preservation (Tpack htv) (Epack evf)
    = Tpack (type-preservation-vec htv evf)
type-preservation (Tpack htv) (Epacked k vs)
    rewrite htval⇒Γ1≡Γ2-vec vs htv
    = Tstruct vs (value-type-vec vs htv)
type-preservation (Tunpack ht hti) (Eunpack ev)
    = Tunpack (type-preservation ht ev) hti
type-preservation (Tunpack (Tstruct vs' htv) hti) (Eunpacked vs)
    rewrite htval⇒Γ1≡Γ2-vec vs htv
    = substi-multi htv vs hti
type-preservation (Tcall htv) (Ecall eva)
    = Tcall (type-preservation-vec htv eva)

-- Here we use the hypothesis of well-formedness of the function we are calling
type-preservation (Tcall {M2 = M2} {f = f} htv) (Ecalled vs)
    rewrite htval⇒Γ1≡Γ2-vec vs htv
    = Texec (substi-multi htv vs (wellHti W M2 f))

type-preservation (Texec ht) (Eexec ev)
    = Texec (type-preservation ht ev)
type-preservation (Texec ht) (Eexecuted v)
    = value-type v ht
type-preservation (Tif ht1 ht2 ht3) (Eif ev)
    = Tif (type-preservation ht1 ev) ht2 ht3
type-preservation (Tif ht1 ht2 ht3) (Eiftrue nz)
    rewrite htval⇒Γ1≡Γ2 Vnum ht1 = ht2
type-preservation (Tif ht1 ht2 ht3) Eiffalse
    rewrite htval⇒Γ1≡Γ2 Vnum ht1 = ht3
type-preservation (TselV {j = j} _ (Tstruct vs htv) nLin) (Eselect _)
    = htvLookup vs htv j
type-preservation (Tpub ht yLin) (Epub ev)
    = Tpub (type-preservation ht ev) yLin
type-preservation (Tpub ht yLin) (Epub2 v)
    rewrite htval⇒Γ1≡Γ2 v ht = Tnum


type-preservation-vec (ht T∷ htv) (E[ ev ] vs)
    rewrite htval⇒Γ1≡Γ2-vec vs htv
    = (type-preservation ht ev) T∷ (value-type-vec vs htv)
type-preservation-vec (ht T∷ htv) (t E∷ evv)
    = ht T∷ type-preservation-vec htv evv
 