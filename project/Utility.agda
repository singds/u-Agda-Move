
open import Data.Nat as Nat using (ℕ; suc; _<_)
import project.Syntax as Syntax

module project.Utility
    (Nm Ns Nf Nsf Nfa : ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open Syntax Nm Ns Nf Nsf Nfa

open import Data.Fin as Fin using (Fin; #_)
open import Data.Vec as V using (Vec; lookup)
open import Data.Bool as B using (Bool; true; false)
open import Data.Empty as Empty using (⊥; ⊥-elim)

mod : (m : Fin Nm) → Module
mod m = lookup (Program.modDefs P) m

-- Get the stducts defined in a module
strs : (m : Fin Nm) → Vec StrDef Ns
strs m = Module.strDefs (mod m)

-- Get a struct
str : (m : Fin Nm) → (s : Fin Ns) → StrDef
str m s = lookup (strs m) s

-- Check if a struct is linear
isLin : (m : Fin Nm) → (s : Fin Ns) → Bool
isLin m s = StrDef.isLin (lookup (strs m) s)

-- Get the list of fields of a struct
fieldsT : (m : Fin Nm) → (s : Fin Ns) → Vec Type Nsf
fieldsT m s = StrDef.fieldsT (str m s)



-- Get the functions defined in a module
funs : (m : Fin Nm) → Vec FunDef Nf
funs m = Module.funDefs (mod m)

-- Get a function
fun : (m : Fin Nm) → (f : Fin Nf) → FunDef
fun m f = lookup (funs m) f

argsT : (m : Fin Nm) → (f : Fin Nf) → Vec Type Nfa
argsT m f = FunDef.argsT (fun m f)

retT : (m : Fin Nm) → (f : Fin Nf) → Type
retT m f = FunDef.retT (fun m f)

body : (m : Fin Nm) → (f : Fin Nf) → LTerm
body m f = FunDef.body (fun m f)

absurd = ⊥-elim
