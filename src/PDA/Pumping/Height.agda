-- Height bound for Case 1: the maximum height H of a (normal) accepting
-- computation satisfies H ≤ l + 1, where l is the level.
--
-- Idea: the height reaches 0 only at the end (empty stack = no step), so
-- the whole run [0 .. compLen−1] is an "arc" over base 1 whose peak
-- is the maximum height H; that is an (H−1)-level, hence l ≥ H−1.
--
-- This file: the basic profile lemmas.
module PDA.Pumping.Height where

open import Data.List using (List; []; _∷_; length)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _∸_; _+_; s≤s; z≤n; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; m≤n⇒m<n∨m≡n; ≰⇒≥; m≤n⇒m≤1+n;
                                       ≤∧≢⇒<; m+[n∸m]≡n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)

open import PDA.Base using (PDA; Config; _⊢ₚ_⟹_; _⊢ₚ_⟹*_; read; eps; ε; _◅_; compLen)
open import PDA.Normal using (stkOf; IsNormalPDA)
open import PDA.Trace using (configAt; stackAt; sₕ; stepAt; sₕ-step)
open import PDA.Pumping.Level using (IsNLevel)

-- Every step starts from a non-empty stack (it needs a top symbol).
step-src-nonempty : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                  → M ⊢ₚ c₁ ⟹ c₂ → 1 ≤ length (stkOf c₁)
step-src-nonempty (read _) = s≤s z≤n
step-src-nonempty (eps _) = s≤s z≤n

-- Before the end the height is ≥ 1 (there is a step from there).
height-pos : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
           → (d : M ⊢ₚ c₁ ⟹* c₂) (n : ℕ) → n < compLen d → 1 ≤ sₕ n d
height-pos d n lt = step-src-nonempty (stepAt n d lt)

-- The configuration at the last position is the target of the computation.
configAt-last : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
              → (d : M ⊢ₚ c₁ ⟹* c₂) → configAt (compLen d) d ≡ c₂
configAt-last ε = refl
configAt-last (_ ◅ d) = configAt-last d

-- Height at the last position = height of the final stack.
sₕ-last : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → (d : M ⊢ₚ c₁ ⟹* c₂) → sₕ (compLen d) d ≡ length (stkOf c₂)
sₕ-last d = cong (λ c → length (stkOf c)) (configAt-last d)

-- ────────────────────────────────────────────────────────────────
-- Peak: a position of maximum height in [0..m]
-- ────────────────────────────────────────────────────────────────

private
  ≤suc-split : ∀ {n m} → n ≤ suc m → n ≤ m ⊎ n ≡ suc m
  ≤suc-split {n} {m} n≤ with m≤n⇒m<n∨m≡n n≤
  ... | inj₁ n<sm = inj₁ (≤-pred n<sm)
  ... | inj₂ n≡sm = inj₂ n≡sm

-- Initial height = 1 (the stack z ∷ []).
sₕ-start : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ : Q} {w : List T} {z : Γ}
           {c₂ : Config Q T Γ}
         → (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* c₂) → sₕ 0 d ≡ 1
sₕ-start d = refl

-- Height at the last position = 0 (rewritten via compLen ≡ suc m').
sₕ-suc-end : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ q_f : Q} {w : List T} {z : Γ}
           → (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
           → (m' : ℕ) → compLen d ≡ suc m' → sₕ (suc m') d ≡ 0
sₕ-suc-end d m' eq = trans (cong (λ x → sₕ x d) (sym eq)) (sₕ-last d)

-- Height at the position just before the end (empty stack) = 1.
sₕ-pre-end : {Q T Γ : Set} {M : PDA Q T Γ} (norm : IsNormalPDA M)
             {q₀ q_f : Q} {w : List T} {z : Γ}
           → (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
           → (m' : ℕ) → compLen d ≡ suc m' → sₕ m' d ≡ 1
sₕ-pre-end norm d m' eq with sₕ-step norm m' d (subst (m' <_) (sym eq) ≤-refl)
... | inj₁ p = trans p (cong suc (sₕ-suc-end d m' eq))
... | inj₂ p with trans (sym p) (sₕ-suc-end d m' eq)
... | ()

argmax : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
       → (d : M ⊢ₚ c₁ ⟹* c₂) (m : ℕ)
       → Σ ℕ (λ j → j ≤ m × (∀ n → n ≤ m → sₕ n d ≤ sₕ j d))
argmax d zero = zero , z≤n , bound
  where
    bound : ∀ n → n ≤ zero → sₕ n d ≤ sₕ zero d
    bound zero z≤n = ≤-refl
    bound (suc _) ()
argmax d (suc m) with argmax d m
... | j , j≤m , isMax with sₕ (suc m) d ≤? sₕ j d
... | yes le = j , m≤n⇒m≤1+n j≤m , bound
        where
          bound : ∀ n → n ≤ suc m → sₕ n d ≤ sₕ j d
          bound n n≤ with ≤suc-split n≤
          ... | inj₁ n≤m = isMax n n≤m
          ... | inj₂ refl = le
... | no gt = suc m , ≤-refl , bound
        where
          bound : ∀ n → n ≤ suc m → sₕ n d ≤ sₕ (suc m) d
          bound n n≤ with ≤suc-split n≤
          ... | inj₁ n≤m = ≤-trans (isMax n n≤m) (≰⇒≥ gt)
          ... | inj₂ refl = ≤-refl

-- ────────────────────────────────────────────────────────────────
-- Height bound: for a normal accepting computation there is a B bounding
-- every height, and (if B ≥ 2) B−1 is realized as a level.
-- Hence the maximum height H satisfies H ≤ l + 1 (l = maximum level).
-- ────────────────────────────────────────────────────────────────

height-cota : {Q T Γ : Set} {M : PDA Q T Γ} (norm : IsNormalPDA M)
              {q₀ q_f : Q} {w : List T} {z : Γ}
            → (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
            → Σ ℕ (λ B → (∀ n → n ≤ compLen d → sₕ n d ≤ B)
                        × (2 ≤ B → ∃ λ j → IsNLevel d (B ∸ 1) 0 j (compLen d ∸ 1)))
height-cota norm d@(st ◅ d') with argmax d (compLen d)
... | jmax , jmax≤cl , isMax = sₕ jmax d , isMax , mkLevel
  where
    m' : ℕ
    m' = compLen d'
    pre1 : sₕ m' d ≡ 1
    pre1 = sₕ-pre-end norm d m' refl
    end0 : sₕ (suc m') d ≡ 0
    end0 = sₕ-suc-end d m' refl
    mkLevel : 2 ≤ sₕ jmax d → ∃ λ j → IsNLevel d (sₕ jmax d ∸ 1) 0 j (compLen d ∸ 1)
    mkLevel 2≤B =
      jmax , 0<jmax , jmax<m' , m≤n⇒m≤1+n ≤-refl , sym pre1 , eqN , leftB , rightB
      where
        abs : ∀ {v} → sₕ jmax d ≡ v → v ≤ 1 → ⊥
        abs eq v≤1 with ≤-trans 2≤B (subst (_≤ 1) (sym eq) v≤1)
        ... | s≤s ()
        1≤B : 1 ≤ sₕ jmax d
        1≤B = ≤-trans (s≤s z≤n) 2≤B
        eqN : sₕ jmax d ≡ sₕ 0 d + (sₕ jmax d ∸ 1)
        eqN = sym (m+[n∸m]≡n 1≤B)
        0<jmax : 0 < jmax
        0<jmax = ≤∧≢⇒< z≤n (λ eq → abs (cong (λ x → sₕ x d) (sym eq)) ≤-refl)
        jmax<m' : jmax < m'
        jmax<m' =
          ≤∧≢⇒< (≤-pred (≤∧≢⇒< jmax≤cl
                          (λ eq → abs (trans (cong (λ x → sₕ x d) eq) end0) z≤n)))
                (λ eq → abs (trans (cong (λ x → sₕ x d) eq) pre1) ≤-refl)
        leftB : ∀ n → 0 ≤ n → n ≤ jmax → (sₕ 0 d ≤ sₕ n d) × (sₕ n d ≤ sₕ jmax d)
        leftB n _ n≤j =
            height-pos d n (≤-trans (s≤s n≤j) (≤-trans jmax<m' (m≤n⇒m≤1+n ≤-refl)))
          , isMax n (≤-trans n≤j jmax≤cl)
        rightB : ∀ n → jmax ≤ n → n ≤ m' → (sₕ m' d ≤ sₕ n d) × (sₕ n d ≤ sₕ jmax d)
        rightB n _ n≤m' =
            subst (_≤ sₕ n d) (sym pre1) (height-pos d n (s≤s n≤m'))
          , isMax n (≤-trans n≤m' (m≤n⇒m≤1+n ≤-refl))
