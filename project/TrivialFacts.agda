open import project.IncludeBase

module project.TrivialFacts where

postulate
    sx≤sy⇒x≤y : {x y : ℕ} → suc x ≤ suc y → x ≤ y
    ¬sx≤sy⇒¬x≤y : {x y : ℕ} → ¬ (suc x ≤ suc y) → ¬ (x ≤ y)
    x≤y⇒sx≤sy : {x y : ℕ} → x ≤ y → suc x ≤ suc y
    ¬sx<sy⇒¬x<y : {x y : ℕ} → ¬ (suc x < suc y) → ¬ (x < y)
    sx<sy⇒x<y : {x y : ℕ} → suc x < suc y → x < y
    ¬x<y∧¬x≡y⇒¬x≤y : {x y : ℕ} → ¬ (x < y) → ¬ (x ≡ y) → ¬ (x ≤ y)
    ¬sx≡sy⇒¬x≡y : {x y : ℕ} → ¬ (suc x ≡ suc y) → ¬ (x ≡ y)
    ¬sx≡z : {x : ℕ} → ¬ (suc x ≡ 0)
    s<x+n>≡x+sn : {x n : ℕ} → suc (x + n) ≡ x + suc n
    l++[]≡l : {A : Set} → (l : List A) → l L.++ L.[] ≡ l

x+1≡sx : ∀ {x} → x + 1 ≡ suc x
x+1≡sx {0} = refl
x+1≡sx {suc x} rewrite x+1≡sx {x} = refl

x+0≡x : ∀ {x} → x + 0 ≡ x
x+0≡x {0} = refl
x+0≡x {suc x} = cong suc (x+0≡x {x})
