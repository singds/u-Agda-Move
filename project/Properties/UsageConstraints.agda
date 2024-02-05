import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.UsageConstraints
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P

private
    variable
        M        : Fin Nm
        l lv n   : ℕ
        Δ        : Env l
        t t1 t2  : Term
        T T1 T2  : Type

out∘⇒in∘-x :
    {Γ1 Γ3 : UEnv Δ}
    {x : ℕ}
    {i : Fin l}
    → HasTypeX Γ1 x T Γ3
    → uLookup i Γ3 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘ 

out∘⇒in∘ :
    {Γ1 Γ3 : UEnv Δ}
    {i : Fin l}
    → HasType M Γ1 t T Γ3
    → uLookup i Γ3 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘

out∘⇒in∘-vec :
    {Γ1 Γ3 : UEnv Δ}
    {ts : Vec Term n} {Ts : Vec Type n}
    {i : Fin l}
    → HasTypeV M Γ1 ts Ts Γ3
    → uLookup i Γ3 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘

out∘⇒in∘-intro :
    {Γ1 Γ3 : UEnv Δ}
    {n : ℕ} {Ts : Vec Type n}
    {i : Fin l}
    → HasTypeI M Γ1 Ts t T Γ3
    → uLookup i Γ3 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘

out∘⇒in∘-x (Xz nLin)                 eq = eq
out∘⇒in∘-x {i = F.suc i} (XzL yLin)  eq = eq -- 'i' can't be equal to 'x' (x = 0)
out∘⇒in∘-x {i = F.zero}  (Xs htx)    eq = eq
out∘⇒in∘-x {i = F.suc i} (Xs htx)    eq = out∘⇒in∘-x htx eq


out∘⇒in∘ (Tvar htx) eq = out∘⇒in∘-x htx eq

out∘⇒in∘ {Δ = Δ} {Γ1 = Γ1} {i = i} (Tlet {Γ2 = Γ2} ht hti) eq = Γ1∘ where
    Γ2∘ : uLookup i Γ2 ≡ (V.lookup Δ i) ∘
    Γ2∘ = out∘⇒in∘-intro hti eq

    Γ1∘ : uLookup i Γ1 ≡ (V.lookup Δ i) ∘
    Γ1∘ = out∘⇒in∘ ht Γ2∘

out∘⇒in∘ Tnum eq              = eq
out∘⇒in∘ (Tpack htv) eq       = out∘⇒in∘-vec htv eq
out∘⇒in∘ (Tstruct vs htv) eq  = out∘⇒in∘-vec htv eq
out∘⇒in∘ (Tcall htv) eq       = out∘⇒in∘-vec htv eq
out∘⇒in∘ (Tunpack ht hti) eq  = out∘⇒in∘ ht (out∘⇒in∘-intro hti eq)
out∘⇒in∘ (Texec ht) eq        = eq
out∘⇒in∘ (Tif ht1 ht2 ht3) eq = out∘⇒in∘ ht1 (out∘⇒in∘ ht2 eq)
out∘⇒in∘ (Tpub ht _) eq    = out∘⇒in∘ ht eq
out∘⇒in∘ (TselX htx nLin) eq  = eq
out∘⇒in∘ (TselV v ht nLin) eq = eq


out∘⇒in∘-vec T[] eq          = eq
out∘⇒in∘-vec (ht T∷ htv) eq  = out∘⇒in∘ ht (out∘⇒in∘-vec htv eq)

out∘⇒in∘-intro I[ ht ] eq                 = out∘⇒in∘ ht eq
out∘⇒in∘-intro {i = i} (nLin I∷  hti) eq  = out∘⇒in∘-intro {i = F.suc i} hti eq
out∘⇒in∘-intro {i = i} (yLin I∷l hti) eq  = out∘⇒in∘-intro {i = F.suc i} hti eq





in•⇒out•-x :
    {Γ1 Γ3 : UEnv Δ}
    {x : ℕ}
    {i : Fin l}
    → HasTypeX Γ1 x T Γ3
    → uLookup i Γ1 ≡ (V.lookup Δ i) •
    → uLookup i Γ3 ≡ (V.lookup Δ i) •

in•⇒out• :
    {Γ1 Γ3 : UEnv Δ}
    {i : Fin l}
    → HasType M Γ1 t T Γ3
    → uLookup i Γ1 ≡ (V.lookup Δ i) •
    → uLookup i Γ3 ≡ (V.lookup Δ i) •

in•⇒out•-vec :
    {Γ1 Γ3 : UEnv Δ}
    {ts : Vec Term n} {Ts : Vec Type n}
    {i : Fin l}
    → HasTypeV M Γ1 ts Ts Γ3
    → uLookup i Γ1 ≡ (V.lookup Δ i) •
    → uLookup i Γ3 ≡ (V.lookup Δ i) •

in•⇒out•-intro :
    {Γ1 Γ3 : UEnv Δ}
    {n : ℕ} {Ts : Vec Type n}
    {i : Fin l}
    → HasTypeI M Γ1 Ts t T Γ3
    → uLookup i Γ1 ≡ (V.lookup Δ i) •
    → uLookup i Γ3 ≡ (V.lookup Δ i) •

in•⇒out•-x (Xz nLin)                   eq = eq
in•⇒out•-x {i = F.suc i} (XzL yLin)    eq = eq -- 'i' can't be equal to 'x' (x = 0)
in•⇒out•-x {i = F.zero}  (Xs htx)      eq = eq
in•⇒out•-x {i = F.suc i} (Xs htx)      eq = in•⇒out•-x htx eq

in•⇒out• Tnum eq = eq
in•⇒out• (Tvar htx) eq = in•⇒out•-x htx eq
in•⇒out• (Tpack htv) eq = in•⇒out•-vec htv eq
in•⇒out• (Tstruct vs htv) eq = in•⇒out•-vec htv eq
in•⇒out• (Tcall htv) eq = in•⇒out•-vec htv eq
in•⇒out• (Texec ht) eq = eq
in•⇒out• (Tif ht1 ht2 ht3) eq = in•⇒out• ht2 (in•⇒out• ht1 eq)
in•⇒out• (Tpub ht _) eq = in•⇒out• ht eq
in•⇒out• (TselX htx nLin) eq = eq
in•⇒out• (TselV v ht nLin) eq = eq


in•⇒out• {Δ = Δ} {Γ1 = Γ1} {Γ3 = Γ3} {i = i} (Tlet {Γ2 = Γ2} ht hti) eq = Γ3• where
    Γ2• : uLookup i Γ2 ≡ (V.lookup Δ i) •
    Γ2• = in•⇒out• ht eq

    Γ3• : uLookup i Γ3 ≡ (V.lookup Δ i) •
    Γ3• = in•⇒out•-intro hti Γ2•

in•⇒out• (Tunpack ht hti) eq = in•⇒out•-intro hti (in•⇒out• ht eq)

in•⇒out•-vec T[] eq = eq
in•⇒out•-vec (ht T∷ htv) eq = in•⇒out•-vec htv (in•⇒out• ht eq)

in•⇒out•-intro I[ ht ] eq                 = in•⇒out• ht eq
in•⇒out•-intro {i = i} (nLin I∷  hti) eq  = in•⇒out•-intro {i = F.suc i} hti eq
in•⇒out•-intro {i = i} (yLin I∷l hti) eq  = in•⇒out•-intro {i = F.suc i} hti eq




ht1ht2-in≡out⇒in≡mid≡out :
    {Γ1 Γ2 Γ3 : UEnv Δ}
    {i : Fin l}
    → HasType M Γ1 t1 T1 Γ2
    → HasType M Γ2 t2 T2 Γ3
    → uLookup i Γ1 ≡ uLookup i Γ3
    --------------------
    → (uLookup i Γ1 ≡ uLookup i Γ2) × (uLookup i Γ2 ≡ uLookup i Γ3)
ht1ht2-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht1 ht2 eq
    with uLookup i Γ1 in eq1 | uLookup i Γ3 in eq3 | eq
ht1ht2-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht1 ht2 eq
    | .(V.lookup Δ i) • | .(V.lookup Δ i) • | refl with Eq.sym (in•⇒out• {Γ3 = Γ2} {i = i} ht1 eq1)
...           | eq4 = eq4 , Eq.sym eq4
ht1ht2-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht1 ht2 eq
    | .(V.lookup Δ i) ∘ | .(V.lookup Δ i) ∘ | refl with Eq.sym (out∘⇒in∘ {Γ1 = Γ2} {i = i} ht2 eq3)
...           | eq4 = eq4 , Eq.sym eq4

htHti-in≡out⇒in≡mid≡out :
    {Γ1 Γ2 Γ3 : UEnv Δ}
    {i : Fin l}
    {Ts : Vec Type n}
    → HasType M Γ1 t1 T1 Γ2
    → HasTypeI M Γ2 Ts t2 T2 Γ3
    → uLookup i Γ1 ≡ uLookup i Γ3
    --------------------
    → (uLookup i Γ1 ≡ uLookup i Γ2) × (uLookup i Γ2 ≡ uLookup i Γ3)
htHti-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht hti eq
    with uLookup i Γ1 in eq1 | uLookup i Γ3 in eq3 | eq
htHti-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht hti eq
    | .(V.lookup Δ i) • | .(V.lookup Δ i) • | refl with Eq.sym (in•⇒out• {Γ3 = Γ2} {i = i} ht eq1)
...           | eq4 = eq4 , Eq.sym eq4
htHti-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht hti eq
    | .(V.lookup Δ i) ∘ | .(V.lookup Δ i) ∘ | refl with Eq.sym (out∘⇒in∘-intro {Γ1 = Γ2} {i = i} hti eq3)
...           | eq4 = eq4 , Eq.sym eq4

htHtv-in≡out⇒in≡mid≡out :
    {Γ1 Γ2 Γ3 : UEnv Δ}
    {i : Fin l}
    {ts : Vec Term n} {Ts : Vec Type n}
    → HasType M Γ1 t1 T1 Γ2
    → HasTypeV M Γ2 ts Ts Γ3
    → uLookup i Γ1 ≡ uLookup i Γ3
    --------------------
    → (uLookup i Γ1 ≡ uLookup i Γ2) × (uLookup i Γ2 ≡ uLookup i Γ3)
htHtv-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht htv eq
    with uLookup i Γ1 in eq1 | uLookup i Γ3 in eq3 | eq
htHtv-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht htv eq
    | .(V.lookup Δ i) • | .(V.lookup Δ i) • | refl with Eq.sym (in•⇒out• {Γ3 = Γ2} {i = i} ht eq1)
...           | eq4 = eq4 , Eq.sym eq4
htHtv-in≡out⇒in≡mid≡out {Δ = Δ} {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} {i = i} ht htv eq
    | .(V.lookup Δ i) ∘ | .(V.lookup Δ i) ∘ | refl with Eq.sym (out∘⇒in∘-vec {Γ1 = Γ2} {i = i} htv eq3)
...           | eq4 = eq4 , Eq.sym eq4



U≡T∘+U≡T•⇒⊥ : {U : Usage T} → U ≡ T ∘ → U ≡ T •
    → ⊥
U≡T∘+U≡T•⇒⊥ refl ()

U≡T∘+U'≡T•+U≡U'⇒⊥ : {U1 U2 : Usage T} → U1 ≡ T ∘ → U2 ≡ T • → U1 ≡ U2
    → ⊥
U≡T∘+U'≡T•+U≡U'⇒⊥ refl refl ()
