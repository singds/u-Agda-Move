{-# OPTIONS --allow-unsolved-metas #-}

import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.Substitution-old
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P
open import project.Properties.ValueType Nm Ns Nf Nsf Nfa P
open import project.Properties.ValueEval Nm Ns Nf Nsf Nfa P
open import project.Properties.Weakening Nm Ns Nf Nsf Nfa P
open import project.Properties.Strengthening Nm Ns Nf Nsf Nfa P
open import project.Properties.UsageConstraints Nm Ns Nf Nsf Nfa P
open import project.Properties.Misc Nm Ns Nf Nsf Nfa P

private
    variable
        n l lv   : ℕ
        M M2     : Fin Nm
        T Tx T2  : Type
        Δ        : Env l
        Δv       : Env lv
        t tv t2  : Term


mark• : Usage T → Usage T
mark• (T ∘) = T •
mark• (T •) = T •

tyX-yLin∘ :
    {Γ1 Γ2 : UEnv Δ}
    {x : Fin l}
    → HasTypeX Γ1 (toℕ x) (V.lookup Δ x) Γ2
    → IsLinear (V.lookup Δ x)
    → (uLookup x Γ1 ≡ (V.lookup Δ x) ∘)
tyX-yLin∘ {Δ = T V.∷ Δ} {x = F.zero} (Xz  nLin) yLin'      = absurd (nLin yLin')
tyX-yLin∘ {Δ = T V.∷ Δ} {x = F.zero} (XzL yLin) yLin'      = refl
tyX-yLin∘ {Δ = .(_ V.Vec.∷ _)} {x = F.suc x} (Xs htx) yLin = tyX-yLin∘ htx yLin

tyX-yLin• :
    {Γ1 Γ2 : UEnv Δ}
    {x : Fin l}
    → HasTypeX Γ1 (toℕ x) (V.lookup Δ x) Γ2
    → IsLinear (V.lookup Δ x)
    → (uLookup x Γ2 ≡ (V.lookup Δ x) •)
tyX-yLin• {Δ = T V.∷ Δ} {x = F.zero} (Xz  nLin) yLin'     = absurd (nLin yLin')
tyX-yLin• {Δ = T V.∷ Δ} {x = F.zero}  (XzL yLin) yLin'      = refl
tyX-yLin• {Δ = .(_ V.Vec.∷ _)} {x = F.suc x} (Xs htx) yLin = tyX-yLin• htx yLin

tyX-nLin-Γ≡ :
    {Γ1 Γ2 : UEnv Δ}
    {x : Fin l}
    → HasTypeX Γ1 (toℕ x) T Γ2
    → ¬ IsLinear T
    → Γ1 ≡ Γ2
tyX-nLin-Γ≡ {x = F.zero} (Xz nLin') nLin = refl
tyX-nLin-Γ≡ {x = F.zero} (XzL yLin') nLin = absurd (nLin yLin')
tyX-nLin-Γ≡ {x = F.suc x} (Xs htx) nLin with tyX-nLin-Γ≡ htx nLin
... | refl = refl

typeX :
    {Γ1 Γ2 : UEnv Δ}
    {x : Fin l}
    → HasTypeX Γ1 (toℕ x) T Γ2
    → V.lookup Δ x ≡ T
typeX {x = F.zero} (Xz nLin)  = refl
typeX {x = F.zero} (XzL yLin) = refl
typeX {x = F.suc x} (Xs htx) = typeX htx

tyX-mark• :
    {Γ1 Γ2 : UEnv Δ}
    {x : Fin l}
    → HasTypeX Γ1 (toℕ x) T Γ2
    → uLookup x Γ2 ≡ (V.lookup Δ x) •
    → (uUpdateAt x mark• Γ1) ≡ Γ2
tyX-mark• {x = F.zero}  (XzL yLin) eq = refl
tyX-mark• {x = F.suc x} (Xs htx)   eq rewrite tyX-mark• htx eq = refl

substi1-x :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {x : ℕ}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ uLookup i Γ2
    → HasTypeX Γ1 x Tx Γ2
    -------------------------------
    → HasType M Γ1 (subst (toℕ i) tv (var x)) Tx Γ2

substi1 :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {tv : Term}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ uLookup i Γ2
    → HasType M Γ1 t2 T2 Γ2
    -------------------------------
    → HasType M Γ1 (subst (toℕ i) tv t2) T2 Γ2

substi1-vec :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {ts : Vec Term n} {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ uLookup i Γ2
    → HasTypeV M Γ1 ts Ts Γ2
    -------------------------------
    → HasTypeV M Γ1 (subst-vec (toℕ i) tv ts) Ts Γ2

substi1-intro :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ uLookup i Γ2
    → HasTypeI M Γ1 Ts t2 T2 Γ2
    -------------------------------
    → HasTypeI M Γ1 Ts (subst ((toℕ i) + n) tv t2) T2 Γ2

substi1-x {x = x} {i = i} v htv eq htx with x ≟ (toℕ i)
substi1-x {x = x} {i = i} v htv eq htx | no ¬x≡i  = Tvar htx
substi1-x {Δ = Δ} {i = i} v htv eq htx | yes refl
    with typeX htx | tyIsLin (V.lookup Δ i)
substi1-x v htv eq htx | yes refl | refl | yes yLin with tyX-yLin∘ htx yLin | tyX-yLin• htx yLin
substi1-x val htv eq htx | yes refl | refl | yes yLin | eq1 | eq2
    = absurd (U≡T∘+U'≡T•+U≡U'⇒⊥ eq1 eq2 eq) -- eq, eq1 ed eq2 are in contraddiction
substi1-x val htv eq htx | yes refl | refl | no  nLin with tyX-nLin-Γ≡ htx nLin
substi1-x val htv eq htx | yes refl | refl | no  nLin | refl = value-type val htv


substi1 val htval eq Tnum = Tnum
substi1 val htval eq (Tpack htv)       = Tpack (substi1-vec val htval eq htv)
substi1 {tv = tv} {i = i} val htval eq (Tstruct {ts = ts} vs htv)
    with subst-vec (F.toℕ i) tv ts | subst-vec-val-eq {F.toℕ i} {tv} vs
... | ts' | refl = Tstruct vs (value-type-vec vs htv)
substi1 val htval eq (Tcall htv)       = Tcall (substi1-vec val htval eq htv)
substi1 val htval eq (Tpub ht yLin)    = Tpub (substi1 val htval eq ht) yLin
substi1 val htval eq (Texec ht)        = Texec ht
substi1 {i = i} val htval eq (Tif {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} ht1 ht2 ht3)
    with ht1ht2-in≡out⇒in≡mid≡out ht1 ht2 eq
... | eq12 , eq23 = Tif (substi1 val htval eq12 ht1)
                        (substi1 val htval eq23 ht2)
                        (substi1 val htval eq23 ht3)

substi1 val htval eq (Tvar htx) = substi1-x val htval eq htx

substi1 {M2 = M2} {M = M} {Γv1 = Γv1} {Γv2 = Γv2} {tv = tv} {i = i}
    val htv eq (TselX {x = x} {s = s} htx nLin)
    with x ≟ toℕ i
... | no  _    = TselX htx nLin
... | yes refl = TselV val (value-type val htv') nLin
    where
        htv' : HasType M2 Γv1 tv (Tst (sId M s)) Γv2
        htv' rewrite htxIsTy htx = htv

substi1 {tv = tv} {i = i} val htval eq (TselV {t = t} v ht nLin)
    with subst (F.toℕ i) tv t | subst-val-eq {F.toℕ i} {tv} v
... | t' | refl = TselV v ht nLin


substi1 {i = i} val htval eq (Tlet ht hti) with htHti-in≡out⇒in≡mid≡out ht hti eq
... | ( eq12 , eq23 ) rewrite Eq.sym(x+1≡sx {x = (toℕ i)})
    = Tlet (substi1 val htval eq12 ht) (substi1-intro val htval eq23 hti)

substi1 val htval eq (Tunpack ht hti) with htHti-in≡out⇒in≡mid≡out ht hti eq
... | ( eq12 , eq23 )
    = Tunpack (substi1 val htval eq12 ht) (substi1-intro val htval eq23 hti)


substi1-vec val htval eq T[] = T[]
substi1-vec val htval eq (ht T∷ htv) with htHtv-in≡out⇒in≡mid≡out ht htv eq
... | ( eq12 , eq23 )
    = substi1 val htval eq12 ht T∷ (substi1-vec val htval eq23 htv)


substi1-intro {i = i} val htval eq I[ ht ]
    rewrite x+0≡x {x = (toℕ i)}
    = I[ (substi1 val htval eq ht) ]
substi1-intro {i = i} val htval eq (_I∷_ {n = lTs} nLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = nLin I∷ substi1-intro {i = F.suc i} val htval eq hti
substi1-intro {i = i} val htval eq (_I∷l_ {n = lTs} yLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = yLin I∷l substi1-intro {i = F.suc i} val htval eq hti




substi2 :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ2 ≡ (V.lookup Δ i) •
    → HasType M Γ1 t2 T2 Γ2
    -------------------------------
    → HasType M (uUpdateAt i mark• Γ1) (subst (toℕ i) tv t2) T2 Γ2

substi2-vec :
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
    → HasTypeV M (uUpdateAt i mark• Γ1) (subst-vec (toℕ i) tv ts) Ts Γ2

substi2-intro :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → uLookup i Γ1 ≡ (V.lookup Δ i) ∘
    → uLookup i Γ2 ≡ (V.lookup Δ i) •
    → HasTypeI M Γ1 Ts t2 T2 Γ2
    -------------------------------
    → HasTypeI M (uUpdateAt i mark• Γ1) Ts (subst ((toℕ i) + V.length Ts) tv t2) T2 Γ2

substi2 {Δ = Δ} {Γ2 = Γ2} {i = i} v htV eq1 eq2 Tnum
    with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i Usage.∘) | refl | ()
substi2 {Δ = Δ} {Γ2 = Γ2} {i = i} v htV eq1 eq2 (Texec ht)
    with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i Usage.∘) | refl | ()
substi2 {Δ = Δ} {Γ2 = Γ2} {i = i} v htV eq1 eq2 (Tstruct vs htv)
    with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i Usage.∘) | refl | ()

substi2 v htV eq1 eq2 (Tpack htv)        = Tpack (substi2-vec v htV eq1 eq2 htv)
substi2 v htV eq1 eq2 (Tcall htv)        = Tcall (substi2-vec v htV eq1 eq2 htv)
substi2 v htV eq1 eq2 (Tpub ht yLin)     = Tpub  (substi2 v htV eq1 eq2 ht) yLin
substi2 {Δ = Δ} {i = i} v htV eq1 eq2 (Tif {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} ht1 ht2 ht3)
    with uLookup i Γ2 in eq3
... | .(V.lookup Δ i) ∘ = Tif {!   !} -- complicato, simila a Tlet
                              (substi2 v htV eq3 eq2 ht2)
                              (substi2 v htV eq3 eq2 ht3)
... | .(V.lookup Δ i) • = Tif (substi2 v htV eq1 eq3 ht1)
                              (substi1 v htV iΓ2≡iΓ3 ht2)
                              (substi1 v htV iΓ2≡iΓ3 ht3)
    where
        iΓ2≡iΓ3 : uLookup i Γ2 ≡ uLookup i Γ3
        iΓ2≡iΓ3 = Eq.trans eq3 (Eq.sym eq2)

substi2 {i = i} v htV eq1 eq2 (Tvar {x = x} htx)
    with x ≟ (toℕ i)
substi2 {i = i} v htV eq1 eq2 (Tvar htx) | no  ¬x≡i with tyX-yLin-Γ≡ htx ¬x≡i
-- ok: eq, eq1 ed eq2 sono in contraddizione
substi2 {i = i} v htV eq1 eq2 (Tvar htx) | no  ¬x≡i | eq
    = absurd (U≡T∘+U'≡T•+U≡U'⇒⊥ eq1 eq2 eq) -- eq eq1 ed eq2 are in contraddiction
substi2 {i = i} v htV eq1 eq2 (Tvar htx) | yes refl with typeX htx | tyX-mark• htx eq2
substi2 {i = i} v htV eq1 eq2 (Tvar htx) | yes refl | refl | refl = value-type v htV

substi2 {Γ1 = Γ1} {Γ2 = .Γ1} v htV eq1 eq2 (TselX htx nLin)    = absurd (U≡T∘+U≡T•⇒⊥ eq1 eq2) -- eq1 eq2 are in contradiction
substi2 {Γ1 = Γ1} {Γ2 = .Γ1} v htV eq1 eq2 (TselV val ht nLin) = absurd (U≡T∘+U≡T•⇒⊥ eq1 eq2) -- eq1 eq2 are in contradiction

substi2 {l = suc l} {Δ = Δ} {i = i} v htV eq1 eq2 (Tlet {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} ht hti)
    with uLookup i Γ2 in eq3
... | .(V.lookup Δ i) ∘
    rewrite Eq.sym(x+1≡sx {x = (toℕ i)})
    = Tlet {! ht3 !} (substi2-intro v htV eq3 eq2 hti) -- complicato
    where
        ht1 = substi1 v htV (Eq.trans eq1 (Eq.sym eq3)) ht
        ht2 = strength {i = i} ht1 {!   !}
        ht3 = weakening {U = (V.lookup Δ i) •} {i = i} ht2
        -- quasi: dobbiamo fargli accettare che
        -- (V.insert (V.remove Δ i) i Tv) != Δ

... | .(V.lookup Δ i) •
    rewrite Eq.sym(x+1≡sx {x = (toℕ i)})
    = Tlet (substi2 v htV eq1 eq3 ht) (substi1-intro v htV iΓ2≡iΓ3 hti)
    where
        iΓ2≡iΓ3 : uLookup i Γ2 ≡ uLookup i Γ3
        iΓ2≡iΓ3 = Eq.trans eq3 (Eq.sym eq2)
    
substi2 v htV eq1 eq2 (Tunpack ht hti) = {!   !}

substi2-vec {Δ = Δ} {Γ2 = Γ2} {i = i} v htV eq1 eq2 T[]
    with uLookup i Γ2 | eq1 | eq2
... | .(V.lookup Δ i Usage.∘) | refl | ()
substi2-vec v htV eq1 eq2 (ht T∷ htv)
    = {!   !} -- complicato, simile a Tlet e Tif

substi2-intro {i = i} v htV eq1 eq2 I[ ht ]
    rewrite x+0≡x {x = (toℕ i)}
    = I[ substi2 v htV eq1 eq2 ht ]
substi2-intro {i = i} v htV eq1 eq2 (_I∷_ {n = lTs} nLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = nLin I∷ substi2-intro {i = F.suc i} v htV eq1 eq2 hti
substi2-intro {i = i} v htV eq1 eq2 (_I∷l_ {n = lTs} yLin hti)
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = yLin I∷l substi2-intro {i = F.suc i} v htV eq1 eq2 hti



substi-multi :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {tvs : Vec Term n} {Tvs : Vec Type n}
    → HasTypeV M2 Γv1 tvs Tvs Γv2
    → ValueV tvs
    → HasTypeI M Γ1 Tvs t T Γ2
    → HasType M Γ1 (beta-red tvs t) T Γ2
substi-multi htv V[] I[ ht ] = ht
substi-multi (ht T∷ htv) (v V∷ vs) (nLin I∷ hti) = ht3
    where
        ht1 = substi-multi htv vs hti
        ht2 = substi1 {i = F.zero} v ht refl ht1
        ht3 = strength {i = F.zero} ht2 {!  !}

substi-multi (ht T∷ htv) (v V∷ vs) (yLin I∷l hti) = ht3
    where
        ht1 = substi-multi htv vs hti
        ht2 = substi2 {i = F.zero} v ht refl refl ht1
        ht3 = strength {i = F.zero} ht2 {!  !}
