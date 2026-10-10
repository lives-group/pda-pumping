-- Excursions: the structural decomposition of a computation that empties
-- a one-symbol stack.  Used by the bounded theorem (PDA.Pumping.Bounded)
-- to locate a pumpable segment whose input has bounded length.
--
-- An *excursion* of A is a computation (q , w , A ∷ []) ⟹* (q_f , w_f , []).
-- In a normal PDA its first step either pops A (and the excursion ends) or
-- pushes some X above A; in the latter case the run continues with an
-- excursion of X (the *child*, over the floor A ∷ []) and then, back at
-- A ∷ [], with the rest of the excursion of A.  The child is returned
-- already stripped of its floor.
module PDA.Pumping.Excursion where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; length-++; ++-cancelʳ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

open import PDA.Base
open import PDA.Normal using (IsNormalPDA)
open import PDA.Trace using (consumed; consumed-correct; append-stack)

private
  variable
    Q T Γ : Set

-- ────────────────────────────────────────────────────────────────
-- Generic facts about consumption
-- ────────────────────────────────────────────────────────────────

consumed-trans : {M : PDA Q T Γ} {c₁ c₂ c₃ : Config Q T Γ}
               → (d₁ : M ⊢ₚ c₁ ⟹* c₂) (d₂ : M ⊢ₚ c₂ ⟹* c₃)
               → consumed (⟹*ₚ-trans d₁ d₂) ≡ consumed d₁ ++ consumed d₂
consumed-trans ε d₂ = refl
consumed-trans (read _ ◅ d₁) d₂ = cong (_ ∷_) (consumed-trans d₁ d₂)
consumed-trans (eps _ ◅ d₁) d₂ = consumed-trans d₁ d₂

-- What a run consumes is determined by its input endpoints.
consumed-unique : {M : PDA Q T Γ} {q q' r r' : Q} {w w' : List T} {s s' t t' : List Γ}
                → (d₁ : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
                → (d₂ : M ⊢ₚ (r , w , t) ⟹* (r' , w' , t'))
                → consumed d₁ ≡ consumed d₂
consumed-unique {w' = w'} d₁ d₂ =
  ++-cancelʳ w' (consumed d₁) (consumed d₂)
    (trans (sym (consumed-correct d₁)) (consumed-correct d₂))

consumed-append : {M : PDA Q T Γ} (δ : List Γ) {q q' : Q} {w w' : List T} {s s' : List Γ}
                → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
                → consumed (append-stack δ d) ≡ consumed d
consumed-append δ d = consumed-unique (append-stack δ d) d

-- A computation reading exactly what it consumes (final input []).
exact : {M : PDA Q T Γ} {q q' : Q} {w w' : List T} {s s' : List Γ}
      → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
      → M ⊢ₚ (q , consumed d , s) ⟹* (q' , [] , s')
exact ε = ε
exact (read mem ◅ d) = read mem ◅ exact d
exact (eps mem ◅ d) = eps mem ◅ exact d

compLen-exact : {M : PDA Q T Γ} {q q' : Q} {w w' : List T} {s s' : List Γ}
              → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
              → compLen (exact d) ≡ compLen d
compLen-exact ε = refl
compLen-exact (read _ ◅ d) = cong suc (compLen-exact d)
compLen-exact (eps _ ◅ d) = cong suc (compLen-exact d)

-- The dual: a run that exhausts its input can be given any passive tail.
extend-input : {M : PDA Q T Γ} {q q' : Q} {w : List T} {s s' : List Γ}
             → (d : M ⊢ₚ (q , w , s) ⟹* (q' , [] , s')) (r : List T)
             → M ⊢ₚ (q , w ++ r , s) ⟹* (q' , r , s')
extend-input ε r = ε
extend-input (read mem ◅ d) r = read mem ◅ extend-input d r
extend-input (eps mem ◅ d) r = eps mem ◅ extend-input d r

-- ────────────────────────────────────────────────────────────────
-- firstReturn: a run from α ++ A ∷ δ to the empty stack first reaches the
-- stack A ∷ δ; up to that point it only rewrites α.  (Any PDA.)
-- ────────────────────────────────────────────────────────────────

firstReturn : {M : PDA Q T Γ} {q q_f : Q} {w w_f : List T} {s : List Γ}
              (α : List Γ) (A : Γ) (δ : List Γ)
            → (d : M ⊢ₚ (q , w , s) ⟹* (q_f , w_f , []))
            → s ≡ α ++ A ∷ δ
            → ∃ λ q₁ → ∃ λ w₁
            → Σ (M ⊢ₚ (q , w , α) ⟹* (q₁ , w₁ , [])) λ c
            → Σ (M ⊢ₚ (q₁ , w₁ , A ∷ δ) ⟹* (q_f , w_f , [])) λ e
            → (consumed d ≡ consumed c ++ consumed e)
            × (compLen d ≡ compLen c + compLen e)
firstReturn [] A δ d refl = _ , _ , ε , d , refl , refl
firstReturn (B ∷ αt) A δ ε ()
firstReturn (B ∷ αt) A δ (read {β = β} mem ◅ d') refl
  with firstReturn (β ++ αt) A δ d' (sym (++-assoc β αt (A ∷ δ)))
... | q₁ , w₁ , c , e , ceq , leq =
  q₁ , w₁ , read mem ◅ c , e , cong (_ ∷_) ceq , cong suc leq
firstReturn (B ∷ αt) A δ (eps {β = β} mem ◅ d') refl
  with firstReturn (β ++ αt) A δ d' (sym (++-assoc β αt (A ∷ δ)))
... | q₁ , w₁ , c , e , ceq , leq =
  q₁ , w₁ , eps mem ◅ c , e , ceq , cong suc leq

-- ────────────────────────────────────────────────────────────────
-- The first block of an excursion (normal PDA)
-- ────────────────────────────────────────────────────────────────

-- From the empty stack no step is possible.
nil-stuck : {M : PDA Q T Γ} {q : Q} {w : List T} {c : Config Q T Γ}
          → (d : M ⊢ₚ (q , w , []) ⟹* c) → consumed d ≡ []
nil-stuck ε = refl
nil-stuck (() ◅ _)

-- Either the excursion is a single pop (reading at most one symbol), or it
-- starts with a push of X (the step `st`), followed by the child excursion
-- of X (stripped of the floor A ∷ []) and the rest `e'` of the excursion of A.
Block : {Q T Γ : Set} (M : PDA Q T Γ) (q : Q) (w : List T) (A : Γ) (q_f : Q) (w_f : List T)
      → M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , w_f , []) → Set
Block {Q} {T} {Γ} M q w A q_f w_f e =
  ∃ λ (X : Γ) → ∃ λ (r : Q) → ∃ λ (w₁ : List T) → ∃ λ (q₂ : Q) → ∃ λ (w₂ : List T)
  → Σ (M ⊢ₚ (q , w , A ∷ []) ⟹* (r , w₁ , X ∷ A ∷ [])) λ st
  → Σ (M ⊢ₚ (r , w₁ , X ∷ []) ⟹* (q₂ , w₂ , [])) λ c
  → Σ (M ⊢ₚ (q₂ , w₂ , A ∷ []) ⟹* (q_f , w_f , [])) λ e'
  → length (consumed st) ≤ 1
  × compLen st ≡ 1
  × consumed e ≡ consumed st ++ consumed c ++ consumed e'
  × compLen e ≡ compLen st + (compLen c + compLen e')

private
  pushed : {M : PDA Q T Γ} {q r q_f : Q} {w w₁ w_f : List T} {A X : Γ}
         → (st : M ⊢ₚ (q , w , A ∷ []) ⟹ (r , w₁ , X ∷ A ∷ []))
         → (rest : M ⊢ₚ (r , w₁ , X ∷ A ∷ []) ⟹* (q_f , w_f , []))
         → length (consumed (st ◅ ε)) ≤ 1
         → Block M q w A q_f w_f (st ◅ rest)
  consumed-cons : {M : PDA Q T Γ} {c₁ c₂ c₃ : Config Q T Γ}
                  (s : M ⊢ₚ c₁ ⟹ c₂) (d : M ⊢ₚ c₂ ⟹* c₃)
                → consumed (s ◅ d) ≡ consumed (s ◅ ε) ++ consumed d
  consumed-cons (read _) d = refl
  consumed-cons (eps _) d = refl

  pushed {X = X} st rest le with firstReturn (X ∷ []) _ [] rest refl
  ... | q₂ , w₂ , c , e' , ceq , leq =
    X , _ , _ , q₂ , w₂ , st ◅ ε , c , e' , le , refl
    , trans (consumed-cons st rest) (cong (consumed (st ◅ ε) ++_) ceq)
    , cong suc leq

excView : {M : PDA Q T Γ} → IsNormalPDA M
        → {q q_f : Q} {w w_f : List T} {A : Γ}
        → (e : M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , w_f , []))
        → (length (consumed e) ≤ 1) ⊎ Block M q w A q_f w_f e
excView norm (read {q = q} {a = a} {A = A} mem ◅ rest) with norm q (just a) A mem
... | inj₁ refl rewrite nil-stuck rest = inj₁ ≤-one
  where ≤-one = s≤s z≤n
... | inj₂ (X , refl) = inj₂ (pushed (read mem) rest (s≤s z≤n))
excView norm (eps {q = q} {A = A} mem ◅ rest) with norm q nothing A mem
... | inj₁ refl rewrite nil-stuck rest = inj₁ z≤n
... | inj₂ (X , refl) = inj₂ (pushed (eps mem) rest z≤n)
