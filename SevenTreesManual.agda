{-# OPTIONS --safe #-}

module SevenTreesManual where

open import Data.Nat
open import Data.Product
open import Data.Unit using (⊤)
open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Prelude: Isomorphism.

record _≅_ {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
    constructor iso
    field
        fun : A → B
        inv : B → A
        rightInv : ∀ b → fun (inv b) ≡ b
        leftInv  : ∀ a → inv (fun a) ≡ a

-- Def: Tree.

data Tree : Set where
    N : Tree
    C : Tree → Tree → Tree

Tree^ : ℕ → Set
Tree^ zero = ⊤
Tree^ (suc zero) = Tree
Tree^ (suc n) = Tree × Tree^ n

-- Proof of Tree to Tree⁷ bijection (manual definition).

-- Forward.
T→T⁷ : Tree → Tree^ 7
-- Case 1.
T→T⁷ (C (C (C (C (C (C t7 t6) t5) t4) t3) t2) (C t1a t1b)) = (C t1a t1b , t2 , t3 , t4 , t5 , t6 , t7)
T→T⁷ (C (C (C (C (C (C t7 t6) t5) t4) t3) (C t2a t2b)) N) = (N , C t2a t2b , t3 , t4 , t5 , t6 , t7)
T→T⁷ (C (C (C (C (C (C t7 t6) t5) t4) (C t3a t3b)) N) N) = (N , N , C t3a t3b , t4 , t5 , t6 , t7)
T→T⁷ (C (C (C (C (C (C t7 t6) t5) (C t4a t4b)) N) N) N) = (N , N , N , C t4a t4b , t5 , t6 , t7)
-- Case 2.
T→T⁷ (C (C (C (C N t7) t6) t5a) t5b) = (N , N , N , N , C t5a t5b , t6 , t7)
-- Case 3.
T→T⁷ (C (C (C (C (C (C t6a t6b) t7) N) N) N) N) = (N , N , N , N , N , C t6a t6b , t7)
-- Case 4.
T→T⁷ (C (C (C (C (C N t7a) t7b) t7c) t7d) t7e) = (N , N , N , N , N , N , C (C (C (C t7a t7b) t7c) t7d) t7e)
-- Case 5.
T→T⁷ t7 = (N , N , N , N , N , N , t7)

-- Backward.
T⁷→T : Tree^ 7 → Tree
-- Case 2.
T⁷→T (N , N , N , N , C t5a t5b , t6 , t7) = C (C (C (C N t7) t6) t5a) t5b
-- Case 3.
T⁷→T (N , N , N , N , N , C t6a t6b , t7) = C (C (C (C (C (C t6a t6b) t7) N) N) N) N
-- Case 4.
T⁷→T (N , N , N , N , N , N , C (C (C (C a b) c) d) e) = C (C (C (C (C N a) b) c) d) e
-- Case 5.
T⁷→T (N , N , N , N , N , N , t7) = t7
-- Case 1.
T⁷→T (t1 , t2 , t3 , t4 , t5 , t6 , t7) = (C (C (C (C (C (C t7 t6) t5) t4) t3) t2) t1)

-- Backward ∘ Forward ≡ id.
T→T⁷→T : ∀ (a) → T⁷→T (T→T⁷ a) ≡ a
-- Case 1.
T→T⁷→T (C (C (C (C (C (C _ _) _) _) _) _) (C _ _)) = refl
T→T⁷→T (C (C (C (C (C (C _ _) _) _) _) (C _ _)) N) = refl
T→T⁷→T (C (C (C (C (C (C _ _) _) _) (C _ _)) N) N) = refl
T→T⁷→T (C (C (C (C (C (C _ _) _) (C _ _)) N) N) N) = refl
-- Case 2.
T→T⁷→T (C (C (C (C N t7) _) _) _) = refl
-- Case 3.
T→T⁷→T (C (C (C (C (C (C _ _) _) N) N) N) N) = refl
-- Case 4.
T→T⁷→T (C (C (C (C (C N _) _) _) _) _) = refl
-- Case 5.
T→T⁷→T N = refl
T→T⁷→T (C N _) = refl
T→T⁷→T (C (C N _) _) = refl
T→T⁷→T (C (C (C N _) _) _) = refl

-- Forward ∘ Backward ≡ id.
T⁷→T→T⁷ : ∀ (b) → T→T⁷ (T⁷→T b) ≡ b
-- Case 2.
T⁷→T→T⁷ (N , N , N , N , C _ _ , _ , _) = refl
-- Case 3.
T⁷→T→T⁷ (N , N , N , N , N , C _ _ , _) = refl
-- Case 4.
T⁷→T→T⁷ (N , N , N , N , N , N , C (C (C (C _ _) _) _) _) = refl
-- Case 5.
T⁷→T→T⁷ (N , N , N , N , N , N , N) = refl
T⁷→T→T⁷ (N , N , N , N , N , N , C N _) = refl
T⁷→T→T⁷ (N , N , N , N , N , N , C (C N _) _) = refl
T⁷→T→T⁷ (N , N , N , N , N , N , C (C (C N _) _) _) = refl
-- Case 1.
T⁷→T→T⁷ (C _ _ , _ , _ , _ , _ , _ , _) = refl
T⁷→T→T⁷ (N , C _ _ , _ , _ , _ , _ , _) = refl
T⁷→T→T⁷ (N , N , C _ _ , _ , _ , _ , _) = refl
T⁷→T→T⁷ (N , N , N , C _ _ , _ , _ , _) = refl

T≅T⁷ : Tree ≅ Tree^ 7
T≅T⁷ = iso T→T⁷ T⁷→T T⁷→T→T⁷ T→T⁷→T
