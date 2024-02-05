import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.Misc
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P

private
    variable
        M : Fin Nm
        l : ℕ

tyX-yLin-Γ≡ :
    {Δ : Env l} {Γ1 Γ2 : UEnv Δ}
    {i : Fin l}
    {x : ℕ}
    {T : Type}
    → HasTypeX Γ1 x T Γ2
    → ¬ (x ≡ toℕ i)
    → uLookup i Γ1 ≡ uLookup i Γ2
tyX-yLin-Γ≡ (Xz  nLin) ¬eq = refl
tyX-yLin-Γ≡ {i = F.zero}  (XzL yLin) ¬eq = absurd (¬eq refl)
tyX-yLin-Γ≡ {i = F.suc i} (XzL yLin) ¬eq = refl
tyX-yLin-Γ≡ {i = F.zero}  (Xs htx)   ¬eq = refl
tyX-yLin-Γ≡ {i = F.suc i} {x = suc x} (Xs htx)   ¬eq = tyX-yLin-Γ≡ htx (¬sx≡sy⇒¬x≡y ¬eq)
