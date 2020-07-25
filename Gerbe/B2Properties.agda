{-# OPTIONS --cubical --cumulativity #-}

module ELib.Gerbe.B2Properties where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group renaming (⟨_⟩ to Grp⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Functions.FunExtEquiv

open import ELib.UsefulLemmas
open import ELib.Gerbe.Base
open import ELib.Gerbe.Link
open import ELib.Gerbe.B2
open import ELib.Torsor.Trivialization

private
  variable
    ℓ ℓ' : Level

module isKG² (A : AbGroup {ℓ}) where
  module A = AbGroup A
  open Trivializations A
  X = B².Carrier torsors

  isKG² : (torsors ≡ torsors) ≃ {!!}
  isKG² = {!!}
    (torsors ≡ torsors) ≃⟨ invEquiv (B²Path A torsors torsors) ⟩
    B²Equiv A torsors torsors ≃⟨ {!GerbeTrivialization torsors !} ⟩
    {!!} ■
