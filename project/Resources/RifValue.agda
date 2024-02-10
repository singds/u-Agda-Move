import Data.Nat
import project.Syntax as Syntax

module project.Resources.RifValue
    {Nm Ns Nf Nsf Nfa : Data.Nat.ℕ}
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include P

private
    variable
        n   : ℕ
        ts  : Vec Term n
        t   : Term

-- All the values satisfy the All tIsIf⇒Rt2↭Rt3 property (trivially)
RifValue     : Value t   → All  tIsIf⇒Rt2↭Rt3 t
RifValue-vec : ValueV ts → AllV tIsIf⇒Rt2↭Rt3 ts

RifValue Vnum = all-num (λ ())
RifValue (Vstruct vs) = all-struct (λ ()) (RifValue-vec vs)
RifValue-vec V[] = all-vec[]
RifValue-vec (v V∷ vs) = all-vec∷ (RifValue v) (RifValue-vec vs)
