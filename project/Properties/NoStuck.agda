import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.NoStuck
    {Nm Ns Nf Nsf Nfa : Data.Nat.ℕ}
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    (W : Typing.WellProg Nm Ns Nf Nsf Nfa P)
    where

open import project.Properties.Include P
open import project.Properties.TypePreservation P W
open import project.Properties.Progress P

private
    variable
        M     : Fin Nm
        t1 t2 : Term
        T     : Type


type-preservation* :
      HasType M [] t1 T []
    → M ∋ t1 ⇒* t2
    → HasType M [] t2 T []

type-preservation* ht e-refl           = ht
type-preservation* ht (e-trans evs ev) = type-preservation (type-preservation* ht evs) ev


no-stuck :
      HasType M [] t1 T []
    → M ∋ t1 ⇒* t2
    → (Value t2) ⊎ (P.∃ λ t3 → M ∋ t2 ⇒ t3)

no-stuck ht evs = progress (type-preservation* ht evs)
