-- compLen lemmas for the well-founded recursion securing |vy|≥1 (Part 2):
-- swap-input / append-stack / strip / subst all preserve compLen.
module PDA.Pumping.Shorten where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (<-irrefl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import PDA.Base using (PDA; Config; _⊢ₚ_⟹_; _⊢ₚ_⟹*_; ε; _◅_; read; eps; compLen)
open import PDA.Trace using (swap-input; append-stack; strip; sₕ)

private
  variable
    Q T Γ : Set

-- subst on any component of the configuration preserves compLen.
compLen-substℓ : {M : PDA Q T Γ} {X : Set}
                 (F G : X → Config Q T Γ) {a b : X} (eq : a ≡ b)
                 (d : M ⊢ₚ F a ⟹* G a)
               → compLen (subst (λ x → M ⊢ₚ F x ⟹* G x) eq d) ≡ compLen d
compLen-substℓ F G refl d = refl

-- swap-input preserves compLen (it only relabels the input).
compLen-swap : {M : PDA Q T Γ} {q q' : Q} {w w' : List T} {s s' : List Γ}
               (r' : List T) (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
             → compLen (swap-input r' d) ≡ compLen d
compLen-swap r' ε = refl
compLen-swap r' (read mem ◅ d) = cong suc (compLen-swap r' d)
compLen-swap r' (eps mem ◅ d) = cong suc (compLen-swap r' d)

-- append-stack preserves compLen (it only pads the bottom of the stack).
compLen-append : {M : PDA Q T Γ} {q q' : Q} {w w' : List T} {s s' : List Γ}
                 (δ : List Γ) (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
               → compLen (append-stack δ d) ≡ compLen d
compLen-append δ ε = refl
compLen-append δ (read mem ◅ d) = cong suc (compLen-append δ d)
compLen-append δ (eps mem ◅ d) = cong suc (compLen-append δ d)

-- strip preserves compLen (it keeps every step, only reframing the stack).
compLen-strip : {M : PDA Q T Γ}
                (δ : List Γ) {q q' : Q} {w w' : List T} {s α s' : List Γ}
                (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
                (eq : s ≡ α ++ δ)
                (hyp : ∀ k → k < compLen d → length δ < sₕ k d)
              → compLen (proj₂ (proj₂ (strip δ {α = α} d eq hyp))) ≡ compLen d
compLen-strip δ {α = α} ε eq hyp = refl
compLen-strip δ {α = []} (s ◅ d) refl hyp = ⊥-elim (<-irrefl refl (hyp 0 (s≤s z≤n)))
compLen-strip δ {α = A' ∷ α_t} (read {β = β} {γ = γ} mem ◅ d') refl hyp =
  cong suc (compLen-strip δ {α = β ++ α_t} d'
              (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt)))
compLen-strip δ {α = A' ∷ α_t} (eps {β = β} {γ = γ} mem ◅ d') refl hyp =
  cong suc (compLen-strip δ {α = β ++ α_t} d'
              (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt)))
