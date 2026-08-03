-- Discrete intermediate-value theorem for the stack profile.
-- In a normal PDA the profile sᵢ is a ±1 path, so between any two
-- positions every intermediate height is attained at some position.
-- This is what makes lp(h)/fp(h) exist in Case 2.
module PDA.Pumping.IVT where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-pred; ≰⇒>;
                                       <-≤-trans; m≤m+n; +-identityʳ; +-suc; m≤n⇒m≤1+n; n≤1+n)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import PDA.Base using (PDA; Config; _⊢ₚ_⟹*_; compLen)
open import PDA.Normal using (IsNormalPDA)
open import PDA.Trace using (sₕ; sₕ-step)

private
  variable
    Q T Γ : Set

-- Discrete IVT: along the path from a to a+steps, every height h between
-- the endpoints (in either order) occurs at some position p ∈ [a, a+steps].
ivt : {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ} (norm : IsNormalPDA M)
      (d : M ⊢ₚ c₁ ⟹* c₂)
    → (a steps : ℕ) → a + steps ≤ compLen d → (h : ℕ)
    → (sₕ (a + steps) d ≤ h × h ≤ sₕ a d) ⊎ (sₕ a d ≤ h × h ≤ sₕ (a + steps) d)
    → ∃ λ p → (a ≤ p) × (p ≤ a + steps) × (sₕ p d ≡ h)
ivt norm d a zero bnd h dir
  rewrite +-identityʳ a = a , ≤-refl , ≤-refl , antisym dir
  where
    antisym : (sₕ a d ≤ h × h ≤ sₕ a d) ⊎ (sₕ a d ≤ h × h ≤ sₕ a d) → sₕ a d ≡ h
    antisym (inj₁ (le , ge)) = ≤-antisym le ge
    antisym (inj₂ (le , ge)) = ≤-antisym le ge
ivt {M = M} norm d a (suc s) bnd h dir
  rewrite +-suc a s =
  go (sₕ-step norm a d (<-≤-trans (m≤m+n (suc a) s) bnd)) dir
  where
    Goal = ∃ λ p → (a ≤ p) × (p ≤ suc a + s) × (sₕ p d ≡ h)
    rec : (sₕ (suc a + s) d ≤ h × h ≤ sₕ (suc a) d)
        ⊎ (sₕ (suc a) d ≤ h × h ≤ sₕ (suc a + s) d) → Goal
    rec dn = let p , 1+a≤p , p≤ , hp = ivt norm d (suc a) s bnd h dn
             in p , ≤-trans (n≤1+n a) 1+a≤p , p≤ , hp
    retA : sₕ a d ≡ h → Goal
    retA eq = a , ≤-refl , m≤n⇒m≤1+n (m≤m+n a s) , eq
    go : (sₕ a d ≡ suc (sₕ (suc a) d)) ⊎ (sₕ (suc a) d ≡ suc (sₕ a d))
       → (sₕ (suc a + s) d ≤ h × h ≤ sₕ a d) ⊎ (sₕ a d ≤ h × h ≤ sₕ (suc a + s) d)
       → Goal
    go (inj₁ saeq) (inj₂ (sa≤h , h≤sb)) =
      rec (inj₂ (≤-trans (subst (sₕ (suc a) d ≤_) (sym saeq) (n≤1+n _)) sa≤h , h≤sb))
    go (inj₂ s1eq) (inj₁ (sb≤h , h≤sa)) =
      rec (inj₁ (sb≤h , ≤-trans h≤sa (subst (sₕ a d ≤_) (sym s1eq) (n≤1+n _))))
    go (inj₁ saeq) (inj₁ (sb≤h , h≤sa)) with h ≤? sₕ (suc a) d
    ... | yes h≤s1 = rec (inj₁ (sb≤h , h≤s1))
    ... | no ¬h≤s1 = retA (≤-antisym (subst (_≤ h) (sym saeq) (≰⇒> ¬h≤s1)) h≤sa)
    go (inj₂ s1eq) (inj₂ (sa≤h , h≤sb)) with sₕ (suc a) d ≤? h
    ... | yes s1≤h = rec (inj₂ (s1≤h , h≤sb))
    ... | no ¬s1≤h = retA (≤-antisym sa≤h (≤-pred (subst (h <_) s1eq (≰⇒> ¬s1≤h))))
