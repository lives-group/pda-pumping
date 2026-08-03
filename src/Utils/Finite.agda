module Utils.Finite where

open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-map⁻)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)

open import CFG.Base using (Finite; mkFinite; elems; complete; distinct)
open import Utils.AllDistinct
  using (AllDistinct; []; _∷_; allDistinct-map; allDistinct-++; allDistinct-concatMap)
open import Utils.Fin using (allFins; allFins-complete)

private
  ∈-map-pair : {A B : Set} (a : A) {b : B} {ys : List B}
             → b ∈ ys → (a , b) ∈ map (a ,_) ys
  ∈-map-pair a (here refl) = here refl
  ∈-map-pair a (there mem) = there (∈-map-pair a mem)

-- Maybe A is finite when A is finite

finite-Maybe : {A : Set} → Finite A → Finite (Maybe A)
finite-Maybe fin = mkFinite
  (nothing ∷ map just (elems fin))
  complete-maybe
  distinct-maybe
  where
    complete-maybe : ∀ x → x ∈ (nothing ∷ map just (elems fin))
    complete-maybe nothing = here refl
    complete-maybe (just x) = there (∈-map⁺ just (complete fin x))

    distinct-maybe : AllDistinct (nothing ∷ map just (elems fin))
    distinct-maybe = nothing∉ ∷ allDistinct-map just-injective (distinct fin)
      where
        nothing∉ : nothing ∉ map just (elems fin)
        nothing∉ mem with ∈-map⁻ just mem
        ... | _ , _ , ()

-- A ⊎ B is finite when A and B are finite

finite-⊎ : {A B : Set} → Finite A → Finite B → Finite (A ⊎ B)
finite-⊎ finA finB = mkFinite
  (map inj₁ (elems finA) ++ map inj₂ (elems finB))
  complete-⊎
  distinct-⊎
  where
    complete-⊎ : ∀ x → x ∈ (map inj₁ (elems finA) ++ map inj₂ (elems finB))
    complete-⊎ (inj₁ x) = ∈-++⁺ˡ (∈-map⁺ inj₁ (complete finA x))
    complete-⊎ (inj₂ y) = ∈-++⁺ʳ _ (∈-map⁺ inj₂ (complete finB y))

    distinct-⊎ : AllDistinct (map inj₁ (elems finA) ++ map inj₂ (elems finB))
    distinct-⊎ = allDistinct-++
      (allDistinct-map inj₁-injective (distinct finA))
      (allDistinct-map inj₂-injective (distinct finB))
      disj
      where
        disj : ∀ {x} → x ∈ map inj₁ (elems finA) → x ∉ map inj₂ (elems finB)
        disj mem1 mem2 with ∈-map⁻ inj₁ mem1 | ∈-map⁻ inj₂ mem2
        ... | _ , _ , refl | _ , _ , ()

-- A × B is finite when A and B are finite

finite-× : {A B : Set} → Finite A → Finite B → Finite (A × B)
finite-× finA finB = mkFinite
  (concatMap (λ a → map (a ,_) (elems finB)) (elems finA))
  (λ { (a , b) → go (complete finA a) (complete finB b) })
  distinct-×
  where
    go : {a : _} {xs : List _}
       → a ∈ xs
       → {b : _}
       → b ∈ elems finB
       → (a , b) ∈ concatMap (λ a' → map (a' ,_) (elems finB)) xs
    go (here refl) b-in = ∈-++⁺ˡ (∈-map-pair _ b-in)
    go (there a-in) b-in = ∈-++⁺ʳ _ (go a-in b-in)

    distinct-× : AllDistinct (concatMap (λ a → map (a ,_) (elems finB)) (elems finA))
    distinct-× = allDistinct-concatMap
      (λ a → allDistinct-map (cong proj₂) (distinct finB))
      inter
      (distinct finA)
      where
        inter : ∀ {a₁ a₂} → a₁ ≢ a₂ → ∀ {p} → p ∈ map (a₁ ,_) (elems finB) → p ∉ map (a₂ ,_) (elems finB)
        inter {a₁} {a₂} a₁≢a₂ mem1 mem2 with ∈-map⁻ (a₁ ,_) mem1
        ... | _ , _ , refl with ∈-map⁻ (a₂ ,_) mem2
        ... | _ , _ , eq2 = a₁≢a₂ (cong proj₁ eq2)

-- Fin n is finite

private
  allFins-distinct : ∀ n → AllDistinct (allFins n)
  allFins-distinct zero = []
  allFins-distinct (suc n) = zero∉ ∷ allDistinct-map suc-injective (allFins-distinct n)
    where
      zero∉ : fzero {n} ∉ map fsuc (allFins n)
      zero∉ m with ∈-map⁻ fsuc m
      ... | _ , _ , ()

finite-Fin : ∀ n → Finite (Fin n)
finite-Fin n = mkFinite (allFins n) allFins-complete (allFins-distinct n)

-- Σ A B is finite when A is finite and B a is finite for every a

private
  ∈-concatMap⁺ : {A B : Set} {f : A → List B} {xs : List A} {a : A} {b : B}
               → a ∈ xs → b ∈ f a → b ∈ concatMap f xs
  ∈-concatMap⁺ (here refl) b∈ = ∈-++⁺ˡ b∈
  ∈-concatMap⁺ (there a∈) b∈ = ∈-++⁺ʳ _ (∈-concatMap⁺ a∈ b∈)

finite-Σ : {A : Set} {B : A → Set}
         → Finite A → (∀ a → Finite (B a)) → Finite (Σ A B)
finite-Σ {B = B} finA finB = mkFinite
  (concatMap (λ a → map (a ,_) (elems (finB a))) (elems finA))
  complete-Σ
  distinct-Σ
  where
    complete-Σ : ∀ p → p ∈ concatMap (λ a → map (a ,_) (elems (finB a))) (elems finA)
    complete-Σ (a , b) = ∈-concatMap⁺ (complete finA a) (∈-map⁺ (a ,_) (complete (finB a) b))

    distinct-Σ : AllDistinct (concatMap (λ a → map (a ,_) (elems (finB a))) (elems finA))
    distinct-Σ = allDistinct-concatMap
      (λ a → allDistinct-map (λ { refl → refl }) (distinct (finB a)))
      inter
      (distinct finA)
      where
        inter : ∀ {a₁ a₂} → a₁ ≢ a₂
              → ∀ {p} → p ∈ map (a₁ ,_) (elems (finB a₁))
              → p ∉ map (a₂ ,_) (elems (finB a₂))
        inter {a₁} {a₂} a₁≢a₂ m₁ m₂ with ∈-map⁻ (a₁ ,_) m₁ | ∈-map⁻ (a₂ ,_) m₂
        ... | _ , _ , refl | _ , _ , eq = a₁≢a₂ (cong proj₁ eq)
