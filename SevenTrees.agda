{-# OPTIONS --safe --cubical #-}

module SevenTrees where

open import Agda.Primitive renaming (_⊔_ to ℓ-max)
open import Data.Product
open import Data.Nat
open import Data.Unit using (⊤; tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


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

T→T⁷ : Tree → Tree^ 7
-- Case 3.
T→T⁷ (C (C (C (C (C (C t6a t6b) t7) N) N) N) N) = (N , N , N , N , N , C t6a t6b , t7)
-- Case 1.
T→T⁷ (C (C (C (C (C (C t7 t6) t5) t4) t3) t2) t1) = (t1 , t2 , t3 , t4 , t5 , t6 , t7)
-- Case 2.
T→T⁷ (C (C (C (C N t7) t6) t5a) t5b) = (N , N , N , N , C t5a t5b , t6 , t7)
-- Case 4.
T→T⁷ (C (C (C (C (C N t7a) t7b) t7c) t7d) t7e) = (N , N , N , N , N , N , C (C (C (C t7a t7b) t7c) t7d) t7e)
-- Case 5.
T→T⁷ t7 = (N , N , N , N , N , N , t7)


T⁷→T : Tree^ 7 → Tree
-- Case 4.
T⁷→T (N , N , N , N , N , N , C (C (C (C a b) c) d) e) = C (C (C (C (C N a) b) c) d) e
-- Case 5.
T⁷→T (N , N , N , N , N , N , t7) = t7
-- Case 3.
T⁷→T (N , N , N , N , N , t6 , t7) = C (C (C (C (C t6 t7) N) N) N) N
-- Case 2.
T⁷→T (N , N , N , N , (C t5a t5b) , t6 , t7) = C (C (C (C N t7) t6) t5a) t5b
-- Case 1.
T⁷→T (t1 , t2 , t3 , t4 , t5 , t6 , t7) = C (C (C (C (C (C t7 t6) t5) t4) t3) t2) t1

T→T⁷→T : (a : Tree) → T⁷→T (T→T⁷ a) ≡ a
-- Case 3.
T→T⁷→T (C (C (C (C (C (C t6a t6b) t7) N) N) N) N) = refl
-- Case 1.
T→T⁷→T (C (C (C (C (C (C t7 t6) t5) t4) t3) t2) t1) = {!   !}
-- Case 2.
T→T⁷→T (C (C (C (C N t7) t6) t5a) t5b) = refl
-- Case 4.
T→T⁷→T (C (C (C (C (C N t7a) t7b) t7c) t7d) t7e) = refl
-- Case 5.
T→T⁷→T t7 = {!   !}

T≅T⁷ : Tree ≅ Tree^ 7
T≅T⁷ = iso T→T⁷ T⁷→T rightInv T→T⁷→T
    where
        rightInv : (b : Tree^ 7) → T→T⁷ (T⁷→T b) ≡ b
        rightInv b = {!   !}