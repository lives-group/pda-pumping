module PDA.Trace where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (<-irrefl; m≤n⇒m≤1+n; +-suc; m+[n∸m]≡n)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

open import PDA.Base
open import PDA.Normal using (stkOf; IsNormalPDA; StackStep; normal-step; stackStep-±1;
                              IsNormalPDA⁺; read-pops; eps-pushes)

-- ────────────────────────────────────────────────────────────────
-- The sequence of configurations of a computation
--   |configs d| = compLen d + 1; o último elemento é c₂.
-- ────────────────────────────────────────────────────────────────

configs : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → M ⊢ₚ c₁ ⟹* c₂ → List (Config Q T Γ)
configs {c₁ = c₁} ε = c₁ ∷ []
configs {c₁ = c₁} (_ ◅ d) = c₁ ∷ configs d

configs-length : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
               → (d : M ⊢ₚ c₁ ⟹* c₂) → length (configs d) ≡ suc (compLen d)
configs-length ε = refl
configs-length (_ ◅ d) = cong suc (configs-length d)

-- ────────────────────────────────────────────────────────────────
-- Length and concatenation
-- ────────────────────────────────────────────────────────────────

compLen-trans : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ c₃ : Config Q T Γ}
              → (d₁ : M ⊢ₚ c₁ ⟹* c₂) (d₂ : M ⊢ₚ c₂ ⟹* c₃)
              → compLen (⟹*ₚ-trans d₁ d₂) ≡ compLen d₁ + compLen d₂
compLen-trans ε d₂ = refl
compLen-trans (_ ◅ d₁) d₂ = cong suc (compLen-trans d₁ d₂)

-- ────────────────────────────────────────────────────────────────
-- Splitting a computation at its k-th step (clamped at c₂)
-- ────────────────────────────────────────────────────────────────

splitAt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → ℕ → (d : M ⊢ₚ c₁ ⟹* c₂)
        → ∃ λ c → (M ⊢ₚ c₁ ⟹* c) × (M ⊢ₚ c ⟹* c₂)
splitAt zero d = _ , ε , d
splitAt (suc _) ε = _ , ε , ε
splitAt (suc k) (s ◅ d) with splitAt k d
... | _ , d₁ , d₂ = _ , s ◅ d₁ , d₂

-- Os dois pedaços somam o comprimento original.
splitAt-compLen : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                → (k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂)
                → let r = splitAt k d
                  in compLen (proj₁ (proj₂ r)) + compLen (proj₂ (proj₂ r)) ≡ compLen d
splitAt-compLen zero d = refl
splitAt-compLen (suc _) ε = refl
splitAt-compLen (suc k) (s ◅ d) = cong suc (splitAt-compLen k d)

-- ────────────────────────────────────────────────────────────────
-- Input consumed along a computation (used to factor w = uvxyz)
-- ────────────────────────────────────────────────────────────────

consumed : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
         → M ⊢ₚ c₁ ⟹* c₂ → List T
consumed ε = []
consumed (read {a = a} _ ◅ d) = a ∷ consumed d
consumed (eps _ ◅ d) = consumed d

-- A entrada inicial é o consumido seguido da entrada final.
consumed-correct : {Q T Γ : Set} {M : PDA Q T Γ}
                   {q q' : Q} {w w' : List T} {s s' : List Γ}
                 → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
                 → w ≡ consumed d ++ w'
consumed-correct ε = refl
consumed-correct (read {a = a} _ ◅ d) = cong (a ∷_) (consumed-correct d)
consumed-correct (eps _ ◅ d) = consumed-correct d

-- Consumption is additive along the splitAt factorization.
consumed-split : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
               → (k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂)
               → let r = splitAt k d
                 in consumed (proj₁ (proj₂ r)) ++ consumed (proj₂ (proj₂ r)) ≡ consumed d
consumed-split zero d = refl
consumed-split (suc _) ε = refl
consumed-split (suc k) (read _ ◅ d) = cong (_ ∷_) (consumed-split k d)
consumed-split (suc k) (eps _ ◅ d) = consumed-split k d

-- In a computation that exhausts the input, the word is exactly what was consumed.
accepted-word : {Q T Γ : Set} {M : PDA Q T Γ}
                {q₀ q_f : Q} {w : List T} {s₀ sf : List Γ}
              → (d : M ⊢ₚ (q₀ , w , s₀) ⟹* (q_f , [] , sf)) → w ≡ consumed d
accepted-word d = trans (consumed-correct d) (++-identityʳ (consumed d))

-- The consumed input is no longer than the number of steps.
consumed-length : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                → (d : M ⊢ₚ c₁ ⟹* c₂) → length (consumed d) ≤ compLen d
consumed-length ε = z≤n
consumed-length (read _ ◅ d) = s≤s (consumed-length d)
consumed-length (eps _ ◅ d) = m≤n⇒m≤1+n (consumed-length d)

-- Número de ε-passos (pushes, na forma normal⁺).
numEps : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
       → M ⊢ₚ c₁ ⟹* c₂ → ℕ
numEps ε = 0
numEps (read _ ◅ d) = numEps d
numEps (eps _ ◅ d) = suc (numEps d)

-- compLen = #leituras + #ε-passos.
compLen-reads-eps : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                  → (d : M ⊢ₚ c₁ ⟹* c₂) → compLen d ≡ length (consumed d) + numEps d
compLen-reads-eps ε = refl
compLen-reads-eps (read _ ◅ d) = cong suc (compLen-reads-eps d)
compLen-reads-eps (eps _ ◅ d) = trans (cong suc (compLen-reads-eps d))
                                       (sym (+-suc (length (consumed d)) (numEps d)))

-- O primeiro pedaço de splitAt k tem exatamente k passos (quando k ≤ compLen).
compLen-splitAt-fst : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                    → (k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂) → k ≤ compLen d
                    → compLen (proj₁ (proj₂ (splitAt k d))) ≡ k
compLen-splitAt-fst zero d _ = refl
compLen-splitAt-fst (suc k) (s ◅ d) (s≤s le) = cong suc (compLen-splitAt-fst k d le)

-- consumed is invariant under subst on the source / target configuration.
consumed-subst-tgt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ c₂' : Config Q T Γ}
                   → (eq : c₂ ≡ c₂') (d : M ⊢ₚ c₁ ⟹* c₂)
                   → consumed (subst (λ c → M ⊢ₚ c₁ ⟹* c) eq d) ≡ consumed d
consumed-subst-tgt refl d = refl

consumed-subst-src : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₁' c₂ : Config Q T Γ}
                   → (eq : c₁ ≡ c₁') (d : M ⊢ₚ c₁ ⟹* c₂)
                   → consumed (subst (λ c → M ⊢ₚ c ⟹* c₂) eq d) ≡ consumed d
consumed-subst-src refl d = refl

-- The remaining input is "passive": a computation reading `consumed d` and
-- leaving r induces, for any tail r', one reading `consumed d` and leaving r'.
-- (Dual of append-stack, on the input side; it reattaches the input tail.)
swap-input : {Q T Γ : Set} {M : PDA Q T Γ}
             {q q' : Q} {w w' : List T} {s s' : List Γ}
             (r' : List T)
           → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
           → M ⊢ₚ (q , consumed d ++ r' , s) ⟹* (q' , r' , s')
swap-input r' ε = ε
swap-input r' (read mem ◅ d) = read mem ◅ swap-input r' d
swap-input r' (eps mem ◅ d) = eps mem ◅ swap-input r' d

-- ────────────────────────────────────────────────────────────────
-- splice: skip a loop whose endpoints carry the SAME state and the SAME
-- stack (the exact/regular case).  If d₁ ends at (q,s) and d₃ starts at
-- (q,s), we obtain a computation reading only consumed d₁ ++ consumed d₃,
-- removing the loop between them.  (The core of regular pumping; together
-- with strip+append-stack it handles the case where the stack grows.)
-- ────────────────────────────────────────────────────────────────

splice : {Q T Γ : Set} {M : PDA Q T Γ}
         {q₀ q q_f : Q} {w₁ w₂ wf : List T} {s₀ s sf : List Γ} {w : List T}
       → (d₁ : M ⊢ₚ (q₀ , w , s₀) ⟹* (q , w₁ , s))
       → (d₃ : M ⊢ₚ (q , w₂ , s) ⟹* (q_f , wf , sf))
       → M ⊢ₚ (q₀ , consumed d₁ ++ consumed d₃ ++ wf , s₀) ⟹* (q_f , wf , sf)
splice {wf = wf} d₁ d₃ = ⟹*ₚ-trans (swap-input (consumed d₃ ++ wf) d₁) (swap-input wf d₃)

-- Input repetition (vⁿ).
rep : {T : Set} → ℕ → List T → List T
rep zero _ = []
rep (suc n) v = v ++ rep n v

-- loop-rep: a loop with equal endpoints (state q, stack s) can be repeated
-- n times, reading (consumed d₂)ⁿ.  The "pump-up" direction of regular
-- pumping; with splice (removal) it covers uvⁿx in the exact case.
loop-rep : {Q T Γ : Set} {M : PDA Q T Γ}
           {q : Q} {w₁ w₂ : List T} {s : List Γ}
         → (d₂ : M ⊢ₚ (q , w₁ , s) ⟹* (q , w₂ , s))
         → (n : ℕ) (r : List T)
         → M ⊢ₚ (q , rep n (consumed d₂) ++ r , s) ⟹* (q , r , s)
loop-rep d₂ zero r = ε
loop-rep {q = q} d₂ (suc n) r
  rewrite ++-assoc (consumed d₂) (rep n (consumed d₂)) r =
  ⟹*ₚ-trans (swap-input (rep n (consumed d₂) ++ r) d₂) (loop-rep d₂ n r)

-- Configuration / stack / height at position k.
configAt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
         → ℕ → M ⊢ₚ c₁ ⟹* c₂ → Config Q T Γ
configAt k d = proj₁ (splitAt k d)

-- In an empty computation every position is the one configuration.
configAt-ε : {Q T Γ : Set} {M : PDA Q T Γ} {c : Config Q T Γ}
           → (n : ℕ) → configAt n (ε {M = M} {c = c}) ≡ c
configAt-ε zero = refl
configAt-ε (suc n) = refl

-- splitAt compõe: descartar i e indexar k = indexar i+k.
configAt-drop : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
              → (i k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂)
              → configAt k (proj₂ (proj₂ (splitAt i d))) ≡ configAt (i + k) d
configAt-drop zero k d = refl
configAt-drop {M = M} {c₁ = c} (suc i) k ε =
  trans (configAt-ε {M = M} {c = c} k) (sym (configAt-ε {M = M} {c = c} (suc (i + k))))
configAt-drop (suc i) k (s ◅ d) = configAt-drop i k d

-- In the prefix (take m), indexing at k ≤ m agrees with indexing at k in d.
configAt-take : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
              → (m k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂) → k ≤ m
              → configAt k (proj₁ (proj₂ (splitAt m d))) ≡ configAt k d
configAt-take m zero d _ = refl
configAt-take zero (suc k) d ()
configAt-take (suc m) (suc k) ε (s≤s _) = refl
configAt-take (suc m) (suc k) (s ◅ d) (s≤s le) = configAt-take m k d le

-- Position k in the segment take m (drop a d) ≡ position a+k in d (k ≤ m).
configAt-segment : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                 → (a m k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂) → k ≤ m
                 → configAt k (proj₁ (proj₂ (splitAt m (proj₂ (proj₂ (splitAt a d))))))
                   ≡ configAt (a + k) d
configAt-segment a m k d k≤m =
  trans (configAt-take m k (proj₂ (proj₂ (splitAt a d))) k≤m) (configAt-drop a k d)

stackAt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → ℕ → M ⊢ₚ c₁ ⟹* c₂ → List Γ
stackAt k d = stkOf (configAt k d)

-- The input still remaining at position k.
inputOf : {Q T Γ : Set} → Config Q T Γ → List T
inputOf (_ , w , _) = w

inputAt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → ℕ → M ⊢ₚ c₁ ⟹* c₂ → List T
inputAt k d = inputOf (configAt k d)

-- Consumption window: the input at a is what is read over the window [a,b]
-- followed by the input at b.  Chained, this factors w = uw ++ vw ++ xw ++ yw ++ zw.
consumed-window : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                  (a b : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂) → a ≤ b → b ≤ compLen d
                → inputAt a d
                  ≡ consumed (proj₁ (proj₂ (splitAt (b ∸ a) (proj₂ (proj₂ (splitAt a d))))))
                    ++ inputAt b d
consumed-window a b d a≤b b≤cl =
  trans (consumed-correct seg) (cong (consumed seg ++_) (cong inputOf endEq))
  where
    seg = proj₁ (proj₂ (splitAt (b ∸ a) (proj₂ (proj₂ (splitAt a d)))))
    endEq = trans (configAt-drop a (b ∸ a) d)
                  (cong (λ m → configAt m d) (m+[n∸m]≡n a≤b))

-- The height in the sub-computation (drop i) matches the height at position i+k of d.
sₕ-drop : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → (i k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂)
        → length (stkOf (configAt k (proj₂ (proj₂ (splitAt i d))))) ≡ length (stkOf (configAt (i + k) d))
sₕ-drop i k d = cong (λ c → length (stkOf c)) (configAt-drop i k d)

stateOf : {Q T Γ : Set} → Config Q T Γ → Q
stateOf (q , _ , _) = q

stateAt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → ℕ → M ⊢ₚ c₁ ⟹* c₂ → Q
stateAt k d = stateOf (configAt k d)

-- The stack profile sᵢ.
sₕ : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
   → ℕ → M ⊢ₚ c₁ ⟹* c₂ → ℕ
sₕ k d = length (stackAt k d)

-- ────────────────────────────────────────────────────────────────
-- Frame lemma: padding the bottom of the stack does not affect the
-- computation, since every step touches only the top.
-- ────────────────────────────────────────────────────────────────

append-stack₁ : {Q T Γ : Set} {M : PDA Q T Γ}
                (δ : List Γ) {q q' : Q} {w w' : List T} {s s' : List Γ}
              → M ⊢ₚ (q , w , s) ⟹ (q' , w' , s')
              → M ⊢ₚ (q , w , s ++ δ) ⟹ (q' , w' , s' ++ δ)
append-stack₁ δ (read {β = β} {γ = γ} mem) rewrite ++-assoc β γ δ = read mem
append-stack₁ δ (eps {β = β} {γ = γ} mem) rewrite ++-assoc β γ δ = eps mem

append-stack : {Q T Γ : Set} {M : PDA Q T Γ}
               (δ : List Γ) {q q' : Q} {w w' : List T} {s s' : List Γ}
             → M ⊢ₚ (q , w , s) ⟹* (q' , w' , s')
             → M ⊢ₚ (q , w , s ++ δ) ⟹* (q' , w' , s' ++ δ)
append-stack δ ε = ε
append-stack δ (s ◅ d) = append-stack₁ δ s ◅ append-stack δ d

-- ────────────────────────────────────────────────────────────────
-- The k-th step of a computation, and the stack profile as a ±1 path
-- ────────────────────────────────────────────────────────────────

stepAt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
       → (k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂) → k < compLen d
       → M ⊢ₚ configAt k d ⟹ configAt (suc k) d
stepAt zero (s ◅ _) _ = s
stepAt (suc k) (_ ◅ d) (s≤s lt) = stepAt k d lt

-- The profile sᵢ changes by exactly ±1 at every step of a normal PDA.
sₕ-step : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → IsNormalPDA M → (k : ℕ) (d : M ⊢ₚ c₁ ⟹* c₂) → k < compLen d
        → (sₕ k d ≡ suc (sₕ (suc k) d)) ⊎ (sₕ (suc k) d ≡ suc (sₕ k d))
sₕ-step norm k d lt = stackStep-±1 (normal-step norm (stepAt k d lt))

-- Balance (normal⁺ form): initial height + #pushes = final height + #reads.
-- (Reads pop, −1; ε-moves push, +1.)
balance : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → IsNormalPDA⁺ M → (d : M ⊢ₚ c₁ ⟹* c₂)
        → sₕ 0 d + numEps d ≡ sₕ (compLen d) d + length (consumed d)
balance n⁺ ε = refl
balance n⁺ (read {q = q} {a = a} {A = A} mem ◅ d)
  rewrite read-pops n⁺ q a A mem =
  trans (cong suc (balance n⁺ d)) (sym (+-suc _ _))
balance n⁺ (eps {q = q} {A = A} {γ = γ} mem ◅ d) with eps-pushes n⁺ q A mem
... | X , refl = trans (+-suc (suc (length γ)) (numEps d)) (balance n⁺ d)

-- ────────────────────────────────────────────────────────────────
-- Floor lemma (strip): a computation whose stack never descends to the floor δ
-- preserves δ as a suffix and is equivalent to the "active" computation above δ.
--
-- Together with append-stack, this is the operator that removes/repeats loops:
-- strip extracts the active loop; append-stack replants it over another floor.
-- (It holds for any PDA; normality is not required.)
-- ────────────────────────────────────────────────────────────────

strip : {Q T Γ : Set} {M : PDA Q T Γ}
        (δ : List Γ) {q q' : Q} {w w' : List T} {s α s' : List Γ}
      → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
      → s ≡ α ++ δ
      → (∀ k → k < compLen d → length δ < sₕ k d)
      → ∃ λ α' → s' ≡ α' ++ δ × M ⊢ₚ (q , w , α) ⟹* (q' , w' , α')
strip δ {α = α} ε eq hyp = α , eq , ε
strip δ {α = []} (_ ◅ _) eq hyp =
  ⊥-elim (<-irrefl refl (subst (length δ <_) (cong length eq) (hyp 0 (s≤s z≤n))))
strip δ {α = A' ∷ α_t} (read {β = β} {γ = γ} mem ◅ d') refl hyp
  with strip δ {α = β ++ α_t} d' (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt))
... | α' , eq' , d'' = α' , eq' , read mem ◅ d''
strip δ {α = A' ∷ α_t} (eps {β = β} {γ = γ} mem ◅ d') refl hyp
  with strip δ {α = β ++ α_t} d' (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt))
... | α' , eq' , d'' = α' , eq' , eps mem ◅ d''

-- ────────────────────────────────────────────────────────────────
-- bottom-kept: the NON-strict version of strip (normal⁺ form).  If the
-- height never falls below |δ| (even touching the top of δ, which the
-- normal⁺ push restores), then δ is preserved as a suffix of s'.
-- It yields stack equality between positions of equal height (S_g, S_h).
-- ────────────────────────────────────────────────────────────────

-- (holds for IsNormalPDA: every step is a pop β≡[] or a push β≡X∷A∷[], on read OR ε.)
bottom-kept : {Q T Γ : Set} {M : PDA Q T Γ} (norm : IsNormalPDA M)
              (δ : List Γ) {q q' : Q} {w w' : List T} {s α s' : List Γ}
            → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
            → s ≡ α ++ δ
            → (∀ k → k ≤ compLen d → length δ ≤ sₕ k d)
            → ∃ λ α' → s' ≡ α' ++ δ
bottom-kept norm δ {α = α} ε refl hyp = α , refl
-- pop (β ≡ []): α = [] violates the floor; α = A∷α_t descends to α_t.
bottom-kept norm δ {α = []} (read {q = q} {a = a} {A = A} {γ = γ} mem ◅ rest) refl hyp
  with norm q (just a) A mem
... | inj₁ refl = ⊥-elim (<-irrefl refl (hyp 1 (s≤s z≤n)))
... | inj₂ (_ , refl) = bottom-kept norm δ {α = _ ∷ []} rest refl (λ k k≤ → hyp (suc k) (s≤s k≤))
bottom-kept norm δ {α = []} (eps {q = q} {A = A} mem ◅ rest) refl hyp
  with norm q nothing A mem
... | inj₁ refl = ⊥-elim (<-irrefl refl (hyp 1 (s≤s z≤n)))
... | inj₂ (_ , refl) = bottom-kept norm δ {α = _ ∷ []} rest refl (λ k k≤ → hyp (suc k) (s≤s k≤))
bottom-kept norm δ {α = A ∷ α_t} (read {q = q} {a = a} {A = A'} {γ = γ} mem ◅ rest) refl hyp
  with norm q (just a) A' mem
... | inj₁ refl = bottom-kept norm δ {α = α_t} rest refl (λ k k≤ → hyp (suc k) (s≤s k≤))
... | inj₂ (_ , refl) = bottom-kept norm δ {α = _ ∷ A' ∷ α_t} rest refl (λ k k≤ → hyp (suc k) (s≤s k≤))
bottom-kept norm δ {α = A ∷ α_t} (eps {q = q} {A = A'} mem ◅ rest) refl hyp
  with norm q nothing A' mem
... | inj₁ refl = bottom-kept norm δ {α = α_t} rest refl (λ k k≤ → hyp (suc k) (s≤s k≤))
... | inj₂ (_ , refl) = bottom-kept norm δ {α = _ ∷ A' ∷ α_t} rest refl (λ k k≤ → hyp (suc k) (s≤s k≤))

-- strip preserves the consumed input (it mirrors the definition of strip).
consumed-strip : {Q T Γ : Set} {M : PDA Q T Γ}
                 (δ : List Γ) {q q' : Q} {w w' : List T} {s α s' : List Γ}
               → (d : M ⊢ₚ (q , w , s) ⟹* (q' , w' , s'))
               → (eq : s ≡ α ++ δ)
               → (hyp : ∀ k → k < compLen d → length δ < sₕ k d)
               → consumed (proj₂ (proj₂ (strip δ d eq hyp))) ≡ consumed d
consumed-strip δ {α = α} ε eq hyp = refl
consumed-strip δ {α = []} (_ ◅ _) eq hyp =
  ⊥-elim (<-irrefl refl (subst (length δ <_) (cong length eq) (hyp 0 (s≤s z≤n))))
consumed-strip δ {α = A' ∷ α_t} (read {a = a} {β = β} {γ = γ} mem ◅ d') refl hyp
  with strip δ {α = β ++ α_t} d' (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt))
     | consumed-strip δ {α = β ++ α_t} d' (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt))
... | α' , eq' , d'' | ih = cong (a ∷_) ih
consumed-strip δ {α = A' ∷ α_t} (eps {β = β} {γ = γ} mem ◅ d') refl hyp
  with strip δ {α = β ++ α_t} d' (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt))
     | consumed-strip δ {α = β ++ α_t} d' (sym (++-assoc β α_t δ)) (λ k lt → hyp (suc k) (s≤s lt))
... | α' , eq' , d'' | ih = ih
