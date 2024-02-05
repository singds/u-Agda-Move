import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Resources.Rsubstitution
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    (W : Typing.WellProg Nm Ns Nf Nsf Nfa P)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P
open import project.Properties.UsageConstraints Nm Ns Nf Nsf Nfa P
open import project.Properties.Misc Nm Ns Nf Nsf Nfa P
open import project.Properties.Substitution Nm Ns Nf Nsf Nfa P
open import project.Resources.RnonLinValues Nm Ns Nf Nsf Nfa P W

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open PermutationReasoning

private
    variable
        n l lv  : ℕ
        M M2    : Fin Nm
        Δ       : Env l
        Δv      : Env lv
        T       : Type
        t tv t2 : Term


nLinSubsti1 :
    {Γ1 Γ2 : UEnv Δ}
    {i : Fin l}
    → HasTypeX Γ1 (toℕ i) T Γ2
    → uLookup i Γ1 Eq.≡ uLookup i Γ2
    → ¬ IsLinear T
nLinSubsti1 {i = Fin.zero}  (Xz nLin) eq = nLin
nLinSubsti1 {i = Fin.suc i} (Xs htx)  eq = nLinSubsti1 htx eq


Rsubsti1 :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ uLookup i Γ2
    → HasType M Γ1 t T Γ2
    -------------------------------
    → R (subst (toℕ i) tv t) ≡ R t

Rsubsti1-vec :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {ts : Vec Term n} {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ uLookup i Γ2
    → HasTypeV M Γ1 ts Ts Γ2
    -------------------------------
    → Rv (subst-vec (toℕ i) tv ts) ≡ Rv ts

Rsubsti1-intro :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ uLookup i Γ2
    → HasTypeI M Γ1 Ts t T Γ2
    -------------------------------
    → R (subst ((toℕ i) + n) tv t) ≡ R t

Rsubsti1 v ht' eq Tnum = refl

Rsubsti1 {i = i} v ht' eq (Tvar {x = x} htx) with x ≟ (toℕ i)
Rsubsti1 {i = i} v ht' eq (Tvar {x = x} htx) | yes refl with htxIsTy htx
Rsubsti1 {i = i} v ht' eq (Tvar {x = x} htx) | yes refl | refl rewrite RnLin ht' (nLinSubsti1 htx eq) v
    = refl
Rsubsti1 {i = i} v ht' eq (Tvar {x = x} htx) | no  ¬eq' = refl

Rsubsti1 {i = i} v ht' eq (Tlet ht hti) with htHti-in≡out⇒in≡mid≡out ht hti eq
... | ( eq12 , eq23 )
    rewrite Eq.sym(x+1≡sx {x = (toℕ i)}) | Rsubsti1 v ht' eq12 ht | Rsubsti1-intro v ht' eq23 hti
    = refl
Rsubsti1 v ht' eq (Tpack htv) = Rsubsti1-vec v ht' eq htv
Rsubsti1 v ht' eq (Tstruct {s = s} {M2 = M2} vs htv) with tyIsLin (Tst (sId M2 s))
... | yes yLin  rewrite Rsubsti1-vec v ht' eq htv = refl
... | no  nLin  rewrite Rsubsti1-vec v ht' eq htv = refl
Rsubsti1 v ht' eq (Tcall htv) = Rsubsti1-vec v ht' eq htv
Rsubsti1 v ht' eq (Tunpack ht hti) with htHti-in≡out⇒in≡mid≡out ht hti eq
... | ( eq12 , eq23 ) rewrite Rsubsti1 v ht' eq12 ht | Rsubsti1-intro v ht' eq23 hti
    = refl
Rsubsti1 v ht' eq (Texec ht) = refl
Rsubsti1 v ht' eq (Tif ht1 ht2 ht3) with ht1ht2-in≡out⇒in≡mid≡out ht1 ht2 eq
... | ( eq12 , eq23 ) rewrite Rsubsti1 v ht' eq12 ht1 | Rsubsti1 v ht' eq23 ht2
    = refl
Rsubsti1 v ht' eq (TselX htx nLin) = refl
Rsubsti1 v ht' eq (TselV v' ht nLin) = refl
Rsubsti1 v ht' eq (Tpub ht yLin) = Rsubsti1 v ht' eq ht

Rsubsti1-vec v ht' eq T[] = refl
Rsubsti1-vec {i = i} v ht' eq (ht T∷ htv) with htHtv-in≡out⇒in≡mid≡out ht htv eq
... | ( eq12 , eq23 ) rewrite Rsubsti1 v ht' eq12 ht | Rsubsti1-vec v ht' eq23 htv
    = refl


Rsubsti1-intro {i = i} v ht' eq I[ ht ] rewrite x+0≡x {toℕ i}
    = Rsubsti1 v ht' eq ht
Rsubsti1-intro {i = i} v ht' eq (_I∷_ {n = n} nLin  hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = n})
    = Rsubsti1-intro {i = F.suc i} v ht' eq hti
Rsubsti1-intro {i = i} v ht' eq (_I∷l_ {n = n} yLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = n})
    = Rsubsti1-intro {i = F.suc i} v ht' eq hti




lemPerm1 :
          {xs xs' ys zs zs' : List K}
        → xs ↭ xs'
        → ys ↭ zs L.++ zs'
        → xs L.++ ys ↭ (xs' L.++ zs) L.++ zs'
lemPerm1 {xs} {xs'} {ys} {zs} {zs'} p1 p2 = begin
    xs  L.++ ys               ↭⟨ ++⁺ʳ ys p1 ⟩
    xs' L.++ ys               ↭⟨ ++⁺ˡ xs' p2 ⟩
    xs' L.++ (zs L.++ zs')    ↭⟨ ↭-sym (++-assoc xs' zs zs') ⟩
    (xs' L.++ zs) L.++ zs'    ∎

lemPerm2 :
          {xs ys ys' zs zs' : List K}
        → xs ↭ zs L.++ zs'
        → ys ↭ ys'
        → xs L.++ ys ↭ (zs L.++ ys') L.++ zs'
lemPerm2 {xs} {ys} {ys'} {zs} {zs'} p1 p2 = begin
    xs L.++ ys                ↭⟨ ++⁺ʳ ys p1 ⟩
    (zs L.++ zs') L.++ ys     ↭⟨ ++⁺ˡ (zs L.++ zs') p2 ⟩
    (zs L.++ zs') L.++ ys'    ↭⟨ ++-assoc zs zs' ys' ⟩
    zs L.++ (zs' L.++ ys')    ↭⟨ ++⁺ˡ zs (++-comm zs' ys') ⟩
    zs L.++ (ys' L.++ zs')    ↭⟨ ↭-sym (++-assoc zs ys' zs') ⟩
    (zs L.++ ys') L.++ zs'    ∎

Rsubsti2 :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ2 ≡ (V.lookup Δ i) •
    → HasType M Γ1 t T Γ2
    -------------------------------
    → R (subst (toℕ i) tv t) ↭ R t L.++ R tv

Rsubsti2-vec :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {ts : Vec Term n} {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ2 ≡ (V.lookup Δ i) •
    → HasTypeV M Γ1 ts Ts Γ2
    -------------------------------
    → Rv (subst-vec (toℕ i) tv ts) ↭ Rv ts L.++ R tv

Rsubsti2-intro :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ2 ≡ (V.lookup Δ i) •
    → HasTypeI M Γ1 Ts t T Γ2
    -------------------------------
    → R (subst ((toℕ i) + n) tv t) ↭ R t L.++ R tv

Rsubsti2 {Δ = Δ} {Γ2 = Γ2} {i = i} v ht' eq1 eq2 Tnum
    with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i Usage.∘) | refl | ()
Rsubsti2 {Δ = Δ} {Γ2 = Γ2} {i = i} v ht' eq1 eq2 (Texec ht)
    with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i Usage.∘) | refl | ()
Rsubsti2 {Δ = Δ} {Γ2 = Γ2} {i = i} v ht' eq1 eq2 (Tstruct vs htv)
    with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i Usage.∘) | refl | ()

Rsubsti2 v ht' eq1 eq2 (Tpack htv) = Rsubsti2-vec v ht' eq1 eq2 htv
Rsubsti2 v ht' eq1 eq2 (Tcall htv) = Rsubsti2-vec v ht' eq1 eq2 htv
Rsubsti2 v ht' eq1 eq2 (Tpub ht yLin) = Rsubsti2 v ht' eq1 eq2 ht

Rsubsti2 {i = i} v ht' eq1 eq2 (Tvar {x = x} htx) with x ≟ (toℕ i)
... | yes x≡i = refl
... | no ¬x≡i with tyX-yLin-Γ≡ htx ¬x≡i
...       | eq3 = absurd (U≡T∘+U'≡T•+U≡U'⇒⊥ eq1 eq2 eq3) -- eq1 eq2 ed eq3 are in contraddiction

Rsubsti2 v ht' eq1 eq2 (TselX htx nLin)   = absurd (U≡T∘+U≡T•⇒⊥ eq1 eq2) -- eq1 eq2 are in contraddiction
Rsubsti2 v ht' eq1 eq2 (TselV v' ht nLin) = absurd (U≡T∘+U≡T•⇒⊥ eq1 eq2) -- eq1 eq2 are in contraddiction

Rsubsti2 {Δ = Δ} {i = i} v ht' eq1 eq3 (Tlet {t1 = t1} {Γ2 = Γ2} ht hti) with uLookup i Γ2 in eq2
... | .(V.lookup Δ i) ∘
    = lemPerm1 (↭-reflexive (Rsubsti1 v ht' (Eq.trans eq1 (Eq.sym eq2)) ht))
               (Rsubsti2-intro v ht' eq2 eq3 hti)
... | .(V.lookup Δ i) •
    = lemPerm2 {zs = R t1} (Rsubsti2 v ht' eq1 eq2 ht)
                           (↭-reflexive (Rsubsti1-intro v ht' (Eq.trans eq2 (Eq.sym eq3)) hti))

Rsubsti2 {Δ = Δ} {i = i} v ht' eq1 eq3 (Tunpack {t1 = t1} {Γ2 = Γ2} ht hti) with uLookup i Γ2 in eq2
... | .(V.lookup Δ i) ∘
    = lemPerm1 (↭-reflexive (Rsubsti1 v ht' (Eq.trans eq1 (Eq.sym eq2)) ht))
               (Rsubsti2-intro v ht' eq2 eq3 hti)
... | .(V.lookup Δ i) •
    = lemPerm2 {zs = R t1} (Rsubsti2 v ht' eq1 eq2 ht)
                           (↭-reflexive (Rsubsti1-intro v ht' (Eq.trans eq2 (Eq.sym eq3)) hti))

Rsubsti2 {Δ = Δ} {i = i} v ht' eq1 eq3 (Tif {t1 = t1} {Γ2 = Γ2} ht1 ht2 ht3) with uLookup i Γ2 in eq2
... | .(V.lookup Δ i) ∘
    = lemPerm1 (↭-reflexive (Rsubsti1 v ht' (Eq.trans eq1 (Eq.sym eq2)) ht1))
               (Rsubsti2 v ht' eq2 eq3 ht2)
... | .(V.lookup Δ i) •
    = lemPerm2 {zs = R t1} (Rsubsti2 v ht' eq1 eq2 ht1)
                           (↭-reflexive (Rsubsti1 v ht' (Eq.trans eq2 (Eq.sym eq3)) ht2))

Rsubsti2-vec {Δ = Δ} {Γ2 = Γ2} {i = i} v ht' eq1 eq2 T[] with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i ∘) | refl | ()
Rsubsti2-vec  {Δ = Δ} {i = i} v ht' eq1 eq3 (_T∷_ {t = t} {Γ2 = Γ2} ht htv) with uLookup i Γ2 in eq2
... | .(V.lookup Δ i) ∘
    = lemPerm1 (↭-reflexive (Rsubsti1 v ht' (Eq.trans eq1 (Eq.sym eq2)) ht))
               (Rsubsti2-vec v ht' eq2 eq3 htv)
... | .(V.lookup Δ i) •
    = lemPerm2 {zs = R t} (Rsubsti2 v ht' eq1 eq2 ht)
                          (↭-reflexive (Rsubsti1-vec v ht' (Eq.trans eq2 (Eq.sym eq3)) htv))


Rsubsti2-intro {i = i} v ht' eq1 eq2 I[ ht ]
    rewrite x+0≡x {x = (toℕ i)}
    = Rsubsti2 v ht' eq1 eq2 ht
Rsubsti2-intro {i = i} v ht' eq1 eq2 (_I∷_ {n = lTs} nLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = Rsubsti2-intro v ht' eq1 eq2 hti
Rsubsti2-intro {i = i} v ht' eq1 eq2 (_I∷l_ {n = lTs} yLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = Rsubsti2-intro v ht' eq1 eq2 hti





Rsubsti-multi :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {ts : Vec Term n} {Ts : Vec Type n}
    → HasTypeV M2 Γv1 ts Ts Γv2
    → ValueV ts
    → HasTypeI M Γ1 Ts t2 T Γ2
    → R (beta-red ts t2) ↭ R t2 L.++ Rv ts
Rsubsti-multi {t2 = t2} htv V[] I[ ht ] rewrite l++[]≡l (R t2) = refl
Rsubsti-multi {t2 = t2} (_T∷_ {t = t} {ts = ts} ht htv) (v V∷ vs) (nLin I∷ hti)
--          R t ≡ L.[]
    rewrite RnLin ht nLin v =
    begin
    R (shift-back 0 (subst 0 t (beta-red ts t2)))
        ↭⟨ ↭-reflexive (shift-back-presR 0 (subst 0 t (beta-red ts t2))) ⟩
    R (subst 0 t (beta-red ts t2))    ↭⟨ ↭-reflexive ≡2 ⟩
    R (beta-red ts t2)                ↭⟨ ↭1 ⟩
    R t2 L.++ Rv ts                   ∎
    where
        ↭1 : R (beta-red ts t2) ↭ R t2 L.++ Rv ts
        ↭1 = Rsubsti-multi htv vs hti
        
        ht' = substi-multi htv vs hti

        ≡2 : R (subst 0 t (beta-red ts t2)) ≡ R (beta-red ts t2)
        ≡2  = Rsubsti1 v ht refl ht'

Rsubsti-multi  {t2 = t2} (_T∷_ {t = t} {ts = ts} ht htv) (v V∷ vs) (yLin I∷l hti) =
    begin
    R (shift-back 0 (subst 0 t (beta-red ts t2)))
        ↭⟨ ↭-reflexive (shift-back-presR 0 (subst 0 t (beta-red ts t2))) ⟩
    R (subst 0 t (beta-red ts t2))  ↭⟨ ↭2 ⟩
    R (beta-red ts t2) L.++ R t     ↭⟨ ++⁺ʳ (R t) ↭1 ⟩
    (R t2 L.++ Rv ts)  L.++ R t     ↭⟨ ++-assoc (R t2) (Rv ts) (R t) ⟩
    R t2 L.++ (Rv ts L.++ R t)      ↭⟨ ++⁺ˡ (R t2) (++-comm (Rv ts) (R t)) ⟩
    R t2 L.++ (R t L.++ Rv ts) ∎
    where
        ↭1 : R (beta-red ts t2) ↭ R t2 L.++ Rv ts
        ↭1 = Rsubsti-multi htv vs hti
        
        ht' = substi-multi htv vs hti

        ↭2 : R (subst 0 t (beta-red ts t2)) ↭ R (beta-red ts t2) L.++ R t
        ↭2  = Rsubsti2 v ht refl refl ht'
