-- An application of the pumping lemma: the language { aⁿ bⁿ cⁿ | n ∈ ℕ }
-- is not the empty-stack language of any pushdown automaton.
--
-- Take w = aᵐ bᵐ cᵐ with m = p + 1.  Since |vxy| ≤ p < m, the factor vxy
-- cannot contain both an a and a c.  Pumping down (k = 0) removes the
-- non-empty v y, so the result is shorter than w, yet it keeps all m copies
-- of the letter that vxy misses: it cannot be of the form aⁿ bⁿ cⁿ.
module Examples.ABC where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Properties using (++-assoc; length-++; length-replicate; ∷-injective; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-trans; <⇒≤; m≤m+n; m≤n⇒m≤1+n; +-mono-≤; ≰⇒>; +-cancelˡ-≡;
         +-identityʳ; m+n≡0⇒m≡0; m+n≡0⇒n≡0; <⇒≢; *-zeroʳ; *-suc)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import CFG.Base using (Finite; mkFinite)
open import Utils.AllDistinct using (AllDistinct; []; _∷_)
open import PDA.Base using (PDA)
open import PDA.Language using (AccES)
open import PDA.Trace using (rep)
open import PDA.Pumping.Arbitrary using (pumping-pda)

-- ────────────────────────────────────────────────────────────────
-- The alphabet and the language
-- ────────────────────────────────────────────────────────────────

data Σ₃ : Set where
  a b c : Σ₃

finΣ₃ : Finite Σ₃
finΣ₃ = mkFinite (a ∷ b ∷ c ∷ []) complete₃ distinct₃
  where
    complete₃ : ∀ s → s ∈ (a ∷ b ∷ c ∷ [])
    complete₃ a = here refl
    complete₃ b = there (here refl)
    complete₃ c = there (there (here refl))
    distinct₃ : AllDistinct (a ∷ b ∷ c ∷ [])
    distinct₃ = (λ { (here ()) ; (there (here ())) ; (there (there ())) })
              ∷ (λ { (here ()) ; (there ()) })
              ∷ (λ ())
              ∷ []

abc : ℕ → List Σ₃
abc n = replicate n a ++ replicate n b ++ replicate n c

L-abc : List Σ₃ → Set
L-abc w = ∃ λ n → w ≡ abc n

-- ────────────────────────────────────────────────────────────────
-- Counting letters
-- ────────────────────────────────────────────────────────────────

private
  δ : Σ₃ → Σ₃ → ℕ
  δ a a = 1
  δ b b = 1
  δ c c = 1
  δ a b = 0
  δ a c = 0
  δ b a = 0
  δ b c = 0
  δ c a = 0
  δ c b = 0

  # : Σ₃ → List Σ₃ → ℕ
  # s [] = 0
  # s (t ∷ w) = δ s t + # s w

  #-++ : ∀ s xs ys → # s (xs ++ ys) ≡ # s xs + # s ys
  #-++ s [] ys = refl
  #-++ s (t ∷ xs) ys = trans (cong (δ s t +_) (#-++ s xs ys)) (sym (+-assocʳ (δ s t) _ _))
    where
      +-assocʳ : ∀ x y z → x + y + z ≡ x + (y + z)
      +-assocʳ = solve-∀

  #-rep : ∀ s t n → # s (replicate n t) ≡ δ s t * n
  #-rep s t zero = sym (*-zeroʳ (δ s t))
  #-rep s t (suc n) = trans (cong (δ s t +_) (#-rep s t n)) (sym (*-suc (δ s t) n))

  -- The five-factor decomposition, for any additive measure on words.
  arith5 : ∀ u v x y z → u + (v + (x + (y + z))) ≡ (u + (x + z)) + (v + y)
  arith5 = solve-∀

  split5 : (f : List Σ₃ → ℕ) → (∀ xs ys → f (xs ++ ys) ≡ f xs + f ys)
         → ∀ u v x y z → f (u ++ v ++ x ++ y ++ z) ≡ f (u ++ x ++ z) + (f v + f y)
  split5 f hom u v x y z =
    trans (trans (hom u _) (cong (f u +_) (trans (hom v _) (cong (f v +_)
            (trans (hom x _) (cong (f x +_) (hom y z)))))))
      (trans (arith5 (f u) (f v) (f x) (f y) (f z))
             (cong (_+ (f v + f y)) (sym (trans (hom u _) (cong (f u +_) (hom x z))))))

  #-split : ∀ s u v x y z → # s (u ++ v ++ x ++ y ++ z) ≡ # s (u ++ x ++ z) + (# s v + # s y)
  #-split s = split5 (# s) (#-++ s)

  len-split : ∀ (u v x y z : List Σ₃)
            → length (u ++ v ++ x ++ y ++ z) ≡ length (u ++ x ++ z) + (length v + length y)
  len-split = split5 length (λ xs ys → length-++ xs)

  #a-abc : ∀ n → # a (abc n) ≡ n
  #a-abc n = trans (#-++ a (replicate n a) _)
               (trans (cong₂ _+_ (#-rep a a n)
                                 (trans (#-++ a (replicate n b) _) (cong₂ _+_ (#-rep a b n) (#-rep a c n))))
                      (trans (+-identityʳ (n + 0)) (+-identityʳ n)))

  #c-abc : ∀ n → # c (abc n) ≡ n
  #c-abc n = trans (#-++ c (replicate n a) _)
               (trans (cong₂ _+_ (#-rep c a n)
                                 (trans (#-++ c (replicate n b) _) (cong₂ _+_ (#-rep c b n) (#-rep c c n))))
                      (+-identityʳ n))

  len-abc : ∀ n → length (abc n) ≡ n + (n + n)
  len-abc n = trans (length-++ (replicate n a))
                (cong₂ _+_ (length-replicate n)
                  (trans (length-++ (replicate n b)) (cong₂ _+_ (length-replicate n) (length-replicate n))))

-- ────────────────────────────────────────────────────────────────
-- A short factor of aᵐ bᵐ cᵐ misses the a's or the c's
-- ────────────────────────────────────────────────────────────────

private
  -- If xs is at least as long as P, the suffix S of P ++ S ends with ys.
  split-≥ : (P xs ys S : List Σ₃) → length P ≤ length xs → xs ++ ys ≡ P ++ S
          → ∃ λ r → S ≡ r ++ ys
  split-≥ [] xs ys S _ eq = xs , sym eq
  split-≥ (p ∷ P) (x ∷ xs) ys S (s≤s le) eq = split-≥ P xs ys S le (∷-injectiveʳ eq)

  -- If xs is at most as long as P, then P starts with xs.
  split-≤ : (xs ys P S : List Σ₃) → length xs ≤ length P → xs ++ ys ≡ P ++ S
          → ∃ λ r → P ≡ xs ++ r
  split-≤ [] ys P S _ eq = P , refl
  split-≤ (x ∷ xs) ys (p ∷ P) S (s≤s le) eq with ∷-injective eq
  ... | x≡p , eq' with split-≤ xs ys P S le eq'
  ...   | r , P≡ = r , cong₂ _∷_ (sym x≡p) P≡

  #-zero : ∀ s xs ys zs → # s (xs ++ ys ++ zs) ≡ 0 → # s ys ≡ 0
  #-zero s xs ys zs eq =
    m+n≡0⇒m≡0 (# s ys) (m+n≡0⇒n≡0 (# s xs)
      (trans (cong (# s xs +_) (sym (#-++ s ys zs))) (trans (sym (#-++ s xs _)) eq)))

  no-a-and-c : ∀ m (u f z : List Σ₃) → u ++ f ++ z ≡ abc m → length f ≤ m
             → (# a f ≡ 0) ⊎ (# c f ≡ 0)
  no-a-and-c m u f z eq lf with m ≤? length u
  ... | yes m≤u with split-≥ (replicate m a) u (f ++ z) (replicate m b ++ replicate m c)
                          (subst (_≤ length u) (sym (length-replicate m)) m≤u) eq
  ...   | r , S≡ = inj₁ (#-zero a r f z (trans (cong (# a) (sym S≡)) noA))
    where
      noA : # a (replicate m b ++ replicate m c) ≡ 0
      noA = trans (#-++ a (replicate m b) _) (cong₂ _+_ (#-rep a b m) (#-rep a c m))
  no-a-and-c m u f z eq lf | no m>u
    with split-≤ (u ++ f) z (replicate m a ++ replicate m b) (replicate m c) lenUF
           (trans (++-assoc u f z) (trans eq (sym (++-assoc (replicate m a) _ _))))
    where
      lenUF : length (u ++ f) ≤ length (replicate m a ++ replicate m b)
      lenUF = subst (_≤ _) (sym (length-++ u))
                (subst (length u + length f ≤_)
                       (sym (trans (length-++ (replicate m a))
                                   (cong₂ _+_ (length-replicate m) (length-replicate m))))
                       (+-mono-≤ (<⇒≤ (≰⇒> m>u)) lf))
  ...   | r , P≡ = inj₂ (#-zero c u f r (trans (cong (# c) (trans (sym (++-assoc u f r)) (sym P≡))) noC))
    where
      noC : # c (replicate m a ++ replicate m b) ≡ 0
      noC = trans (#-++ c (replicate m a) _) (cong₂ _+_ (#-rep c a m) (#-rep c b m))

-- ────────────────────────────────────────────────────────────────
-- The contradiction, from one pumped-down word
-- ────────────────────────────────────────────────────────────────

private
  core : ∀ m n (u v x y z : List Σ₃)
       → abc m ≡ u ++ v ++ x ++ y ++ z
       → 0 < length v + length y
       → length (v ++ x ++ y) ≤ m
       → u ++ x ++ z ≡ abc n
       → ⊥
  core m n u v x y z weq vy vxy w'eq =
    <⇒≢ vy (+-cancelˡ-≡ (length (abc m)) 0 (length v + length y)
             (trans (+-identityʳ _) (trans lenEq (cong (_+ (length v + length y)) lenW'))))
    where
      f = v ++ x ++ y
      eq3 : u ++ v ++ x ++ y ++ z ≡ u ++ f ++ z
      eq3 = cong (u ++_) (sym (trans (++-assoc v (x ++ y) z) (cong (v ++_) (++-assoc x y z))))
      lenEq : length (abc m) ≡ length (u ++ x ++ z) + (length v + length y)
      lenEq = trans (cong length weq) (len-split u v x y z)
      -- the letter s missed by vxy is still present m times after pumping down
      keep : ∀ s → # s (abc m) ≡ m → # s (abc n) ≡ n → # s f ≡ 0 → n ≡ m
      keep s hm hn h0 =
        trans (sym hn)
          (trans (cong (# s) (sym w'eq))
            (trans (sym (+-identityʳ _))
              (trans (cong (# s (u ++ x ++ z) +_) (sym vy0))
                (trans (sym (#-split s u v x y z)) (trans (cong (# s) (sym weq)) hm)))))
        where
          hv : # s v + # s (x ++ y) ≡ 0
          hv = trans (sym (#-++ s v (x ++ y))) h0
          vy0 : # s v + # s y ≡ 0
          vy0 = cong₂ _+_ (m+n≡0⇒m≡0 (# s v) hv)
                          (m+n≡0⇒n≡0 (# s x) (trans (sym (#-++ s x y)) (m+n≡0⇒n≡0 (# s v) hv)))
      n≡m : n ≡ m
      n≡m with no-a-and-c m u f z (trans (sym eq3) (sym weq)) vxy
      ... | inj₁ a0 = keep a (#a-abc m) (#a-abc n) a0
      ... | inj₂ c0 = keep c (#c-abc m) (#c-abc n) c0
      lenW' : length (u ++ x ++ z) ≡ length (abc m)
      lenW' = trans (cong length w'eq) (cong (λ k → length (abc k)) n≡m)

-- ────────────────────────────────────────────────────────────────
-- THEOREM: no PDA accepts { aⁿ bⁿ cⁿ } by empty stack.
-- ────────────────────────────────────────────────────────────────

-- The argument only uses the pumping statement for SOME p: keeping p
-- abstract stops Agda from normalising the (huge) concrete pumping length.
PumpingFor : {Q Γ : Set} (M : PDA Q Σ₃ Γ) (p : ℕ) → Set
PumpingFor M p = ∀ {w : List Σ₃} → AccES M w → p < length w
                 → ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
                    → w ≡ u ++ v ++ x ++ y ++ z
                    × 0 < length v + length y
                    × length (v ++ x ++ y) ≤ p
                    × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))

private
  refute : {Q Γ : Set} (M : PDA Q Σ₃ Γ)
         → (∀ w → AccES M w → L-abc w) → (∀ w → L-abc w → AccES M w)
         → (p : ℕ) → PumpingFor M p → ⊥
  refute M sound cmp p pump with pump {abc (suc p)} (cmp _ (suc p , refl)) long
    where
      long : p < length (abc (suc p))
      long = subst (p <_) (sym (len-abc (suc p))) (m≤m+n (suc p) _)
  ... | u , v , x , y , z , weq , vy , vxy , runs with sound _ (runs 0)
  ... | n , w'eq = core (suc p) n u v x y z weq vy (m≤n⇒m≤1+n vxy) w'eq

abc-not-PDA : {Q Γ : Set} (finQ : Finite Q) (finΓ : Finite Γ) (M : PDA Q Σ₃ Γ)
            → ¬ ((∀ w → AccES M w → L-abc w) × (∀ w → L-abc w → AccES M w))
abc-not-PDA finQ finΓ M (sound , cmp) =
  refute M sound cmp (proj₁ P) (proj₂ P)
  where P = pumping-pda finQ finΣ₃ finΓ M
