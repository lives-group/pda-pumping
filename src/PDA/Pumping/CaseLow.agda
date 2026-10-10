-- Case 1 of the pumping lemma (level l < p′).
--
-- To begin, the pumping conclusion for the exact-stack case: given a
-- decomposition of the accepting computation into a prefix d₁, a loop d₂
-- (same state and the VERY SAME stack at both ends) and a suffix d₃ (down
-- to the empty stack), we build, for every n, an accepting computation of
-- u ++ vⁿ ++ x  (u = consumed d₁, v = consumed d₂, x = consumed d₃).
module PDA.Pumping.CaseLow where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _∸_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (<⇒≤; <-trans; <-≤-trans; m+[n∸m]≡n; +-cancelˡ-≡;
                                       m<n⇒0<n∸m; ∸-monoˡ-≤; m+n∸m≡n; +-monoˡ-<; +-monoʳ-<)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

open import CFG.Base using (Finite; elems)
open import PDA.Base using (PDA; Config; _⊢ₚ_⟹*_; ⟹*ₚ-trans; compLen)
open import PDA.Normal using (stkOf; IsNormalPDA⁺)
open import PDA.Trace using (consumed; consumed-correct; consumed-split; consumed-length;
                              accepted-word; swap-input; loop-rep; rep; compLen-trans;
                              splitAt; splitAt-compLen; compLen-splitAt-fst;
                              configAt; configAt-drop; stackAt; stateOf; stateAt; inputOf; sₕ;
                              consumed-subst-tgt; consumed-subst-src;
                              numEps; balance; compLen-reads-eps)
open import PDA.Pumping.Level using (Cfg; finite-Cfg; cfgAt; topl-inj; config-collision)
open import PDA.Pumping.Height using (sₕ-last)
open import PDA.Pumping.Shorten using (compLen-substℓ)

-- ────────────────────────────────────────────────────────────────
-- pump-exact: pumping (in both directions) in the exact-stack case.
--   n = 0 removes the loop (u ++ x);  n ≥ 1 repeats it (u ++ vⁿ ++ x).
-- ────────────────────────────────────────────────────────────────

pump-exact : {Q T Γ : Set} {M : PDA Q T Γ}
             {q₀ q q_f : Q} {w w₁ w₂ : List T} {s₀ s : List Γ}
           → (d₁ : M ⊢ₚ (q₀ , w , s₀) ⟹* (q , w₁ , s))
           → (d₂ : M ⊢ₚ (q , w₁ , s) ⟹* (q , w₂ , s))
           → (d₃ : M ⊢ₚ (q , w₂ , s) ⟹* (q_f , [] , []))
           → (n : ℕ)
           → M ⊢ₚ (q₀ , consumed d₁ ++ rep n (consumed d₂) ++ consumed d₃ , s₀)
                ⟹* (q_f , [] , [])
pump-exact {M = M} {q = q} {q_f = q_f} {s = s} d₁ d₂ d₃ n =
  ⟹*ₚ-trans (swap-input (rep n (consumed d₂) ++ consumed d₃) d₁)
    (⟹*ₚ-trans (loop-rep d₂ n (consumed d₃)) d₃')
  where
    d₃' : M ⊢ₚ (q , consumed d₃ , s) ⟹* (q_f , [] , [])
    d₃' = subst (λ inp → M ⊢ₚ (q , inp , s) ⟹* (q_f , [] , []))
                (trans (consumed-correct d₃) (++-identityʳ (consumed d₃)))
                d₃

-- ────────────────────────────────────────────────────────────────
-- find-loop: the bridge.  From the configuration collision (config-collision)
-- under the height bound (topl-inj makes the top-L view faithful), it extracts
-- an EXACT-STACK loop: positions î<ĵ with the same state and the same stack.
-- ────────────────────────────────────────────────────────────────

find-loop : {Q T Γ : Set} {M : PDA Q T Γ} (finQ : Finite Q) (finΓ : Finite Γ)
            {q₀ q_f : Q} {w : List T} {z : Γ}
          → (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
          → (L : ℕ)
          → (∀ n → n ≤ compLen d → length (stackAt n d) ≤ L)
          → length (elems (finite-Cfg finQ finΓ L)) < compLen d
          → ∃ λ A → ∃ λ B
          → Σ (M ⊢ₚ (q₀ , w , z ∷ []) ⟹* A) λ d₁
          → Σ (M ⊢ₚ A ⟹* B) λ d₂
          → Σ (M ⊢ₚ B ⟹* (q_f , [] , [])) λ d₃
          → 0 < compLen d₂
          × stateOf A ≡ stateOf B
          × stkOf A ≡ stkOf B
          × consumed d ≡ consumed d₁ ++ consumed d₂ ++ consumed d₃
          × compLen d ≡ compLen d₁ + (compLen d₂ + compLen d₃)
find-loop {M = M} finQ finΓ {q₀} {q_f} {w} {z} d L bound long
  with config-collision (finite-Cfg finQ finΓ L) (λ k → cfgAt L k d) (compLen d) long
... | î , ĵ , î<ĵ , ĵ<cl , cfgeq =
  configAt î d , B , d₁ , d₂ , d₃ , pos , qeq , seq , weq , compeq
  where
    spi = splitAt î d
    d₁ = proj₁ (proj₂ spi)
    dr = proj₂ (proj₂ spi)
    spj = splitAt (ĵ ∸ î) dr
    B = proj₁ spj
    d₂ = proj₁ (proj₂ spj)
    d₃ = proj₂ (proj₂ spj)
    Beq : B ≡ configAt ĵ d
    Beq = trans (configAt-drop î (ĵ ∸ î) d)
                (cong (λ m → configAt m d) (m+[n∸m]≡n (<⇒≤ î<ĵ)))
    qeq : stateOf (configAt î d) ≡ stateOf B
    qeq = trans (cong proj₁ cfgeq) (sym (cong stateOf Beq))
    seq : stkOf (configAt î d) ≡ stkOf B
    seq = trans (topl-inj L (bound î (<⇒≤ (<-trans î<ĵ ĵ<cl))) (bound ĵ (<⇒≤ ĵ<cl))
                           (cong proj₂ cfgeq))
                (sym (cong stkOf Beq))
    sumeq : î + compLen dr ≡ compLen d
    sumeq = trans (cong (_+ compLen dr) (sym (compLen-splitAt-fst î d (<⇒≤ (<-trans î<ĵ ĵ<cl)))))
                  (splitAt-compLen î d)
    drge : (ĵ ∸ î) ≤ compLen dr
    drge = subst ((ĵ ∸ î) ≤_) (m+n∸m≡n î (compLen dr))
                 (∸-monoˡ-≤ î (subst (ĵ ≤_) (sym sumeq) (<⇒≤ ĵ<cl)))
    pos : 0 < compLen d₂
    pos = subst (0 <_) (sym (compLen-splitAt-fst (ĵ ∸ î) dr drge)) (m<n⇒0<n∸m î<ĵ)
    weq : consumed d ≡ consumed d₁ ++ consumed d₂ ++ consumed d₃
    weq = trans (sym (consumed-split î d))
                (cong (consumed d₁ ++_) (sym (consumed-split (ĵ ∸ î) dr)))
    compeq : compLen d ≡ compLen d₁ + (compLen d₂ + compLen d₃)
    compeq = trans (sym (splitAt-compLen î d))
                   (cong (compLen d₁ +_) (sym (splitAt-compLen (ĵ ∸ î) dr)))

-- ────────────────────────────────────────────────────────────────
-- pump-from-loop: connects find-loop to pump-exact.  It transports the loop
-- (equal state/stack by qeq/seq) into the exact-stack shape and applies
-- pump-exact, obtaining for every n the accepting computation of u ++ vⁿ ++ x.
-- ────────────────────────────────────────────────────────────────

pump-from-loop : {Q T Γ : Set} {M : PDA Q T Γ} {A B : Config Q T Γ}
                 {q₀ q_f : Q} {w : List T} {z : Γ}
               → (d₁ : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* A)
               → (d₂ : M ⊢ₚ A ⟹* B)
               → (d₃ : M ⊢ₚ B ⟹* (q_f , [] , []))
               → stateOf A ≡ stateOf B → stkOf A ≡ stkOf B
               → (n : ℕ)
               → M ⊢ₚ (q₀ , consumed d₁ ++ rep n (consumed d₂) ++ consumed d₃ , z ∷ [])
                    ⟹* (q_f , [] , [])
pump-from-loop {M = M} {A} {B} {q₀} {q_f} {w} {z} d₁ d₂ d₃ qeq seq n =
  subst (λ word → M ⊢ₚ (q₀ , word , z ∷ []) ⟹* (q_f , [] , [])) word-eq run
  where
    Beq : B ≡ (stateOf A , proj₁ (proj₂ B) , stkOf A)
    Beq = cong₂ (λ q s → (q , proj₁ (proj₂ B) , s)) (sym qeq) (sym seq)
    d₂' = subst (λ c → M ⊢ₚ A ⟹* c) Beq d₂
    d₃' = subst (λ c → M ⊢ₚ c ⟹* (q_f , [] , [])) Beq d₃
    run = pump-exact d₁ d₂' d₃' n
    word-eq : consumed d₁ ++ rep n (consumed d₂') ++ consumed d₃'
            ≡ consumed d₁ ++ rep n (consumed d₂) ++ consumed d₃
    word-eq = cong₂ (λ v x → consumed d₁ ++ rep n v ++ x)
                    (consumed-subst-tgt Beq d₂) (consumed-subst-src Beq d₃)

-- ────────────────────────────────────────────────────────────────
-- |v| ≥ 1 without minimality: in the normal⁺ form (read=pop, ε=push), a loop
-- whose endpoints have equal stack height has #reads = #pushes, so being
-- non-empty it consumes ≥ 1 symbol.
-- ────────────────────────────────────────────────────────────────

private
  0<a+a : ∀ a → 0 < a + a → 0 < a
  0<a+a zero ()
  0<a+a (suc _) _ = s≤s z≤n

loop-consumes : {Q T Γ : Set} {M : PDA Q T Γ} (n⁺ : IsNormalPDA⁺ M) {A B : Config Q T Γ}
              → (d₂ : M ⊢ₚ A ⟹* B) → stkOf A ≡ stkOf B → 0 < compLen d₂
              → 0 < length (consumed d₂)
loop-consumes n⁺ {A} {B} d₂ seq pos = 0<a+a (length (consumed d₂)) (subst (0 <_) ce pos)
  where
    heq : sₕ 0 d₂ ≡ sₕ (compLen d₂) d₂
    heq = trans (cong length seq) (sym (sₕ-last d₂))
    ne : numEps d₂ ≡ length (consumed d₂)
    ne = +-cancelˡ-≡ (sₕ (compLen d₂) d₂) _ _
           (subst (λ h → h + numEps d₂ ≡ sₕ (compLen d₂) d₂ + length (consumed d₂))
                  heq (balance n⁺ d₂))
    ce : compLen d₂ ≡ length (consumed d₂) + length (consumed d₂)
    ce = trans (compLen-reads-eps d₂) (cong (length (consumed d₂) +_) ne)

-- ────────────────────────────────────────────────────────────────
-- Case 1 theorem.  If every height is ≤ p′ (no p′-level) and
-- |w| > card-Cfg p′, then w = u v x with |v| ≥ 1 and ∀n  u vⁿ x ∈ L(M).
-- (The uvxyz shape with x = y = ε; here x is the paper's suffix z.)
-- ────────────────────────────────────────────────────────────────

caseLow : {Q T Γ : Set} {M : PDA Q T Γ} (n⁺ : IsNormalPDA⁺ M)
          (finQ : Finite Q) (finΓ : Finite Γ)
          {q₀ q_f : Q} {w : List T} {z : Γ}
        → (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
        → (p' : ℕ)
        → (∀ n → n ≤ compLen d → length (stackAt n d) ≤ p')
        → length (elems (finite-Cfg finQ finΓ p')) < length w
        → ∃ λ u → ∃ λ v → ∃ λ x
        → w ≡ u ++ v ++ x
        × 0 < length v
        × (∀ n → M ⊢ₚ (q₀ , u ++ rep n v ++ x , z ∷ []) ⟹* (q_f , [] , []))
caseLow {M = M} n⁺ finQ finΓ {q₀} {q_f} {w} {z} d p' hb cardlt
  with find-loop finQ finΓ d p' hb
         (<-≤-trans cardlt
           (subst (_≤ compLen d) (sym (cong length (accepted-word d))) (consumed-length d)))
... | _ , _ , d₁ , d₂ , d₃ , pos , qeq , seq , weq , _ =
    consumed d₁ , consumed d₂ , consumed d₃
  , trans (accepted-word d) weq
  , loop-consumes n⁺ d₂ seq pos
  , pump-from-loop d₁ d₂ d₃ qeq seq

-- ────────────────────────────────────────────────────────────────
-- caseLow-N: the IsNormalPDA version (without ⁺).  It does not prove |v|≥1
-- by balance; it returns EITHER the factorization with |v|≥1 (when the loop
-- reads ≥1) OR a STRICTLY shorter accepting run of the same w (when the loop
-- reads 0 ⇒ A≡B ⇒ direct splice), for the well-founded recursion.
-- (find-loop/pump-from-loop are generic; norm⁺ is never used.)
-- ────────────────────────────────────────────────────────────────

private
  nilOrPos : {T : Set} (xs : List T) → (0 < length xs) ⊎ (xs ≡ [])
  nilOrPos [] = inj₂ refl
  nilOrPos (_ ∷ _) = inj₁ (s≤s z≤n)

caseLow-N : {Q T Γ : Set} {M : PDA Q T Γ}
            (finQ : Finite Q) (finΓ : Finite Γ)
            {q₀ q_f : Q} {w : List T} {z : Γ}
          → (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
          → (p' : ℕ)
          → (∀ n → n ≤ compLen d → length (stackAt n d) ≤ p')
          → length (elems (finite-Cfg finQ finΓ p')) < length w
          → (∃ λ u → ∃ λ v → ∃ λ x
               → w ≡ u ++ v ++ x × 0 < length v
               × (∀ n → M ⊢ₚ (q₀ , u ++ rep n v ++ x , z ∷ []) ⟹* (q_f , [] , [])))
          ⊎ (Σ (M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
                        λ d' → compLen d' < compLen d)
caseLow-N {M = M} finQ finΓ {q₀} {q_f} {w} {z} d p' hb cardlt
  with find-loop finQ finΓ d p' hb
         (<-≤-trans cardlt
           (subst (_≤ compLen d) (sym (cong length (accepted-word d))) (consumed-length d)))
... | A , B , d₁ , d₂ , d₃ , pos , qeq , seq , weq , compeq with nilOrPos (consumed d₂)
... | inj₁ pos-v =
      inj₁ (consumed d₁ , consumed d₂ , consumed d₃
           , trans (accepted-word d) weq , pos-v
           , pump-from-loop d₁ d₂ d₃ qeq seq)
... | inj₂ v≡[] = inj₂ (shorter , compLen<)
  where
    inputeq : inputOf A ≡ inputOf B
    inputeq = trans (consumed-correct d₂) (cong (_++ inputOf B) v≡[])
    A≡B : A ≡ B
    A≡B = cong₂ _,_ qeq (cong₂ _,_ inputeq seq)
    d₃' : M ⊢ₚ A ⟹* (q_f , [] , [])
    d₃' = subst (λ c → M ⊢ₚ c ⟹* (q_f , [] , [])) (sym A≡B) d₃
    shorter : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , [])
    shorter = ⟹*ₚ-trans d₁ d₃'
    cl-d₃' : compLen d₃' ≡ compLen d₃
    cl-d₃' = compLen-substℓ (λ c → c) (λ _ → (q_f , [] , [])) (sym A≡B) d₃
    clS : compLen shorter ≡ compLen d₁ + compLen d₃
    clS = trans (compLen-trans d₁ d₃') (cong (compLen d₁ +_) cl-d₃')
    lt : compLen d₁ + compLen d₃ < compLen d₁ + (compLen d₂ + compLen d₃)
    lt = +-monoʳ-< (compLen d₁) (+-monoˡ-< (compLen d₃) pos)
    compLen< : compLen shorter < compLen d
    compLen< = subst₂ _<_ (sym clS) (sym compeq) lt
