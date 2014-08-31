module paper where

open import Data.Bool using (Bool; not; _∨_; _∧_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

postulate
  Entity   : Set
  _⊃_      : Bool → Bool → Bool
  FORALL   : (Entity → Bool) → Bool
  EXISTS   : (Entity → Bool) → Bool
  PERSON   : Entity → Bool
  FIND     : Entity → Entity → Bool
  UNICORN  : Entity → Bool

data U : Set where S N NP : U

⟦_⟧ᵁ : U → Set
⟦ S   ⟧ᵁ = Bool
⟦ N   ⟧ᵁ = Entity → Bool
⟦ NP  ⟧ᵁ = Entity

import IntuitionisticLogic U ⟦_⟧ᵁ as IL
import LinearLogic U S ⟦_⟧ᵁ as LP
import LambekGrishinCalculus U S ⟦_⟧ᵁ as LG

open LG
open IL.Explicit using (Ctxt; _,_; ∅)
open IL.Explicit.Reify TypeReify

everyone  : ⟦ (el NP + ⇐ el N +) ⊗ el N + ⟧
everyone  = ( (λ{ (A , B) → FORALL (λ x → B x ⊃ A x) }) , PERSON )
finds     : ⟦ (el NP + ⇒ el S -) ⇐ el NP + ⟧
finds     = λ{ ((x , k) , y) → k (FIND y x) }
some      : ⟦ el NP + ⇐ el N + ⟧
some      = λ{ (A , B) → EXISTS (λ x → A x ∧ B x) }
unicorn   : ⟦ el N + ⟧
unicorn   = UNICORN

sent :
  · (el NP + ⇐ el N +) ⊗ el N +         -- everyone
  · ⊗ (· (el NP + ⇒ el S -) ⇐ el NP +  -- finds
  · ⊗ (· el NP + ⇐ el N +               -- some
  · ⊗ · el N + ·                         -- unicorn
  )) ⊢[ el S - ]
sent =
  μ (res₃ (⊗L (res₃ (μ̃* (⇐L (
    μ̃ (res₄ (res₁ (res₁ (res₃ (μ̃* (⇐L (
      μ̃ (res₂ (res₃ (μ̃* (⇐L (⇒L var covar) var))))) var))))))) var)))))

test : ([ sent ] (everyone , finds , some , unicorn , ∅))
     ≡ (λ k → FORALL (λ x₁ → PERSON x₁ ⊃ EXISTS (λ x₂ → k (FIND x₂ x₁) ∧ UNICORN x₂)))
test = refl

