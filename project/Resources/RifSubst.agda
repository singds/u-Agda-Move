import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Resources.RifSubst
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    (W : Typing.WellProg Nm Ns Nf Nsf Nfa P)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P
open import project.Resources.Rsubstitution Nm Ns Nf Nsf Nfa P W
open import project.Resources.RifValue Nm Ns Nf Nsf Nfa P
open import project.Properties.UsageConstraints Nm Ns Nf Nsf Nfa P

open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open PermutationReasoning

private
    variable
        n l lv  : ℕ
        Δ       : Env l
        Δv      : Env lv
        M M2    : Fin Nm
        t tv    : Term
        T       : Type

-- When we perform the substitution, the property is preserved
RifSubst :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {tv : Term}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → HasType M Γ1 t T Γ2
    → All tIsIf⇒Rt2↭Rt3 t
    → All tIsIf⇒Rt2↭Rt3 (subst (toℕ i) tv t)

RifSubst-vec :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {ts : Vec Term n} {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → HasTypeV M Γ1 ts Ts Γ2
    → AllV tIsIf⇒Rt2↭Rt3 ts
    → AllV tIsIf⇒Rt2↭Rt3 (subst-vec (toℕ i) tv ts)

RifSubst-intro :
    {Γ1 Γ2 : UEnv Δ}
    {Γv1 Γv2 : UEnv Δv}
    {n : ℕ} {Ts : Vec Type n}
    {i : Fin l}
    → Value tv
    → HasType M2 Γv1 tv (V.lookup Δ i) Γv2
    → HasTypeI M Γ1 Ts t T Γ2
    → All tIsIf⇒Rt2↭Rt3 t
    → All tIsIf⇒Rt2↭Rt3 (subst ((toℕ i) + n) tv t)

RifSubst v ht' Tnum a = all-num (λ ())
RifSubst {i = i} v ht' (Tvar {x = x} htx) a with x ≟ (toℕ i)
... | no  _ = all-var (λ ())
RifSubst {i = i} Vnum ht'         (Tvar {x = _}  htx) a | yes _ = all-num (λ ())
RifSubst {i = i} (Vstruct vs) ht' (Tvar {x = _} htx) a  | yes _ = all-struct (λ ()) (RifValue-vec vs)
RifSubst v ht' (Tlet ht hti) (all-let p a1 a2)
    = all-let (λ ()) (RifSubst v ht' ht a1) (RifSubst-intro v ht' hti a2)
RifSubst v ht' (Tpack htv) (all-pack p a)
    = all-pack (λ ()) (RifSubst-vec v ht' htv a)
RifSubst v ht' (Tstruct vs htv) (all-struct p a)
    = all-struct (λ ()) (RifSubst-vec v ht' htv a)
RifSubst v ht' (Tcall htv) (all-call p a)
    = all-call (λ ()) (RifSubst-vec v ht' htv a)
RifSubst v ht' (Tunpack ht hti) (all-unpack p a1 a2)
    = all-unpack (λ ()) (RifSubst v ht' ht a1) (RifSubst-intro v ht' hti a2)
RifSubst v ht' (Texec ht) (all-exec p a)
    = all-exec (λ ()) a
RifSubst {Δ = Δ} {tv = tv} {i = i} v ht' (Tif {t1 = t1} {Γ2 = Γ2} {t2 = t2} {Γ3 = Γ3} {t3 = t3} ht1 ht2 ht3) (all-if p a1 a2 a3)
    = all-if p2
        (RifSubst v ht' ht1 a1)
        (RifSubst v ht' ht2 a2)
        (RifSubst v ht' ht3 a3)
    where
        p2 : {t4 t5 t6 : Term} →
            (if (subst (toℕ i) tv t1) then (subst (toℕ i) tv t2) else (subst (toℕ i) tv t3)) ≡ (if t4 then t5 else t6) →
            R t5 ↭ R t6
        p2 {t4} {t5} {t6} refl with uLookup i Γ2 in eq2 | uLookup i Γ3 in eq3
        p2 {t4} {t5} {t6} refl | .(V.lookup Δ i) ∘ | .(V.lookup Δ i) ∘ =
            begin
            R t5 ↭⟨ ↭-reflexive (Rsubsti1 v ht' Γ1i≡Γ2i ht2) ⟩
            R t2 ↭⟨ p refl ⟩
            R t3 ↭⟨ ↭-sym (↭-reflexive (Rsubsti1 v ht' Γ1i≡Γ2i ht3)) ⟩
            R t6 ∎
            where
                Γ1i≡Γ2i = Eq.trans eq2 (Eq.sym eq3)
        p2 {t4} {t5} {t6} refl | .(V.lookup Δ i) • | .(V.lookup Δ i) • =
            begin
            R t5 ↭⟨ ↭-reflexive (Rsubsti1 v ht' Γ1i≡Γ2i ht2) ⟩
            R t2 ↭⟨ p refl ⟩
            R t3 ↭⟨ ↭-sym (↭-reflexive (Rsubsti1 v ht' Γ1i≡Γ2i ht3)) ⟩
            R t6 ∎
            where
                Γ1i≡Γ2i = Eq.trans eq2 (Eq.sym eq3)
        p2 {t4} {t5} {t6} refl | .(V.lookup Δ i) ∘ | .(V.lookup Δ i) • =
            begin
            R t5           ↭⟨ Rsubsti2 v ht' eq2 eq3 ht2 ⟩
            R t2 L.++ R tv ↭⟨ ++⁺ʳ (R tv) (p refl) ⟩
            R t3 L.++ R tv ↭⟨ ↭-sym (Rsubsti2 v ht' eq2 eq3 ht3) ⟩
            R t6 ∎
        p2 {t4} {t5} {t6} refl | .(V.lookup Δ i) • | .(V.lookup Δ i) ∘ with in•⇒out• ht2 eq2
        ...         | eq = absurd (U≡T∘+U≡T•⇒⊥ eq3 eq) -- eq and eq3 are in contraddiction

RifSubst {M = M} v ht' (TselX htx nLin) (all-· _ a) = all-· (λ ()) (RifSubst v ht' (Tvar {M = M} htx) a)
RifSubst v ht' (TselV v' ht nLin) (all-· _ a) = all-· (λ ()) (RifSubst v ht' ht a)
RifSubst v ht' (Tpub ht yLin) (all-pub _ a) = all-pub (λ ()) (RifSubst v ht' ht a)

RifSubst-vec v ht' T[] a = all-vec[]
RifSubst-vec v ht' (ht T∷ htv) (all-vec∷ a1 a2)
    = all-vec∷ (RifSubst v ht' ht a1) (RifSubst-vec v ht' htv a2)

RifSubst-intro {i = i} v ht' I[ ht ] a rewrite x+0≡x {x = (toℕ i)} = RifSubst v ht' ht a
RifSubst-intro {i = i} v ht' (_I∷_ {n = lTs} _ hti) a
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = RifSubst-intro v ht' hti a
RifSubst-intro {i = i} v ht' (_I∷l_ {n = lTs} _ hti) a
    rewrite Eq.sym (s<x+n>≡x+sn {x = (toℕ i)} {n = lTs})
    = RifSubst-intro v ht' hti a

