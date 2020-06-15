{-# OPTIONS --cubical #-}

module ELib.ConcreteGroup.DeloopMorph where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.HITs.SetTruncation renaming (rec to recSetTrunc)
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import ELib.Connectedness.Base
open import ELib.Connectedness.Properties
open import Cubical.Homotopy.Loopspace
open import ELib.UsefulLemmas
open import ELib.ConcreteGroup.Base
--open import ELib.Group.Base

open import Cubical.Structures.Group

private
  module CG = ConcreteGroup
  variable
    ℓ ℓ' : Level

abs : ∀ {ℓ} → ConcreteGroup ℓ → Group {ℓ}
abs G = El , _∙_ , (grpd , assoc) , refl , (λ x → sym (rUnit x) , sym (lUnit x)) , λ x → sym x , rCancel x , lCancel x where
  open CG G

absHom : ∀ {ℓ} (G H : ConcreteGroup ℓ) (f : CG.Ptd G →∙ CG.Ptd H) → (GroupHom (abs G) (abs H))
absHom G H (f , p) =
  (λ q → p ⁻¹ ∙ cong f q ∙ p) , λ x y →
  p ⁻¹ ∙ cong f (x ∙ y) ∙ p
    ≡⟨ cong (λ r → p ⁻¹ ∙ r ∙ p) (cong-∙ f x y) ⟩
  p ⁻¹ ∙ (cong f x ∙ cong f y) ∙ p
    ≡⟨ cong (λ r → p ⁻¹ ∙ r) (sym (assoc _ _ _)) ⟩
  p ⁻¹ ∙ cong f x ∙ cong f y ∙ p
    ≡⟨ cong (λ r → p ⁻¹ ∙ cong f x ∙ r) (lUnit _) ⟩
  p ⁻¹ ∙ cong f x ∙ refl ∙ cong f y ∙ p
    ≡⟨ cong (λ r → p ⁻¹ ∙ cong f x ∙ r ∙ cong f y ∙ p) (sym (rCancel p)) ⟩
  p ⁻¹ ∙ cong f x ∙ (p ∙ p ⁻¹) ∙ cong f y ∙ p
    ≡⟨ cong (λ r → p ⁻¹ ∙ cong f x ∙ r) (sym (assoc _ _ _)) ⟩
  p ⁻¹ ∙ cong f x ∙ p ∙ p ⁻¹ ∙ cong f y ∙ p
    ≡⟨ assoc _ _ _ ∙ assoc _ _ _ ∙ cong (λ r → r ∙ p ⁻¹ ∙ cong f y ∙ p) (sym (assoc _ _ _)) ⟩
  (p ⁻¹ ∙ cong f x ∙ p) ∙ (p ⁻¹ ∙ cong f y ∙ p) ∎

homId : (G : Group {ℓ}) (H : Group {ℓ'}) (f : GroupHom G H) → fst f (group-id G) ≡ group-id H
homId G H (f , morph) = H.idUniqueL (f G.id) (sym (cong f (G.lUnit G.id) ∙ morph _ _)) where
  module H = GroupLemmas H
  module G = GroupLemmas G

delooping : (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ') (f : GroupHom (abs G) (abs H)) (x : CG.type G) → Type (ℓ-max ℓ ℓ')
delooping G H f x =
  Σ[ y ∈ H.type ]
  Σ[ p ∈ ((G.pnt ≡ x) → (H.pnt ≡ y)) ]
    ((ω : G.pnt ≡ G.pnt) (α : G.pnt ≡ x) → p (ω ∙ α) ≡ fst f ω ∙ p α)
  where
  module G = ConcreteGroup G
  module H = ConcreteGroup H

deloopingBis : (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ') (f : GroupHom (abs G) (abs H)) (x : CG.type G) → Type (ℓ-max ℓ ℓ')
deloopingBis G H f x =
  Σ[ y ∈ H.type ] ((p : G.pnt ≡ x → H.pnt ≡ y) (ω : G.pnt ≡ G.pnt) (α : G.pnt ≡ x) → p (ω ∙ α) ≡ fst f ω ∙ p α)
  where
  module G = ConcreteGroup G
  module H = ConcreteGroup H

deloopingContr : (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ') (ϕ : GroupHom (abs G) (abs H)) → (x : CG.type G) → isContr (delooping G H ϕ x)
deloopingContr G H ϕ x =
  recPropTrunc isPropIsContr (λ p → transport (λ i → isContr (delooping G H ϕ (p i)))
  (isOfHLevelRespectEquiv 0 (invEquiv (compEquiv equiv1 equiv2)) contr-a)) (G.conn x)
  where
  module G = ConcreteGroup G
  module H = ConcreteGroup H
  a = G.pnt
  b = H.pnt
  f = fst ϕ
  fmorph = snd ϕ
  equiv1 : delooping G H ϕ a ≃ (Σ[ y ∈ H.type ] Σ[ p ∈ (G.El → H.pnt ≡ y) ] ((ω : G.El) → p ω ≡ f ω ∙ p refl))
  equiv1 = isoToEquiv (iso
    (λ (y , p , h) → y , p , λ ω → p ω ≡⟨ cong p (rUnit ω) ⟩ p (ω ∙ refl) ≡⟨ h ω refl ⟩ f ω ∙ p refl ∎)
    (λ (y , p , h) → y , p , λ ω α →
      p (ω ∙ α)
        ≡⟨ h (ω ∙ α) ∙ cong (λ r → r ∙ p refl) (fmorph _ _) ∙ sym (assoc _ _ _)⟩
      f ω ∙ f α ∙ p refl
        ≡⟨ cong (λ r → f ω ∙ r) (sym (h α)) ⟩
      f ω ∙ p α ∎)
    (λ (y , p , h) → ΣPathP (refl , ΣProp≡ (λ _ → isPropΠ λ _ → H.isGrpd _ _ _ _) refl))
    (λ (y , p , h) → ΣPathP (refl , ΣProp≡ (λ _ → isPropΠ2 λ _ _ → H.isGrpd _ _ _ _) refl)))
  equiv2 : (Σ[ y ∈ H.type ] Σ[ p ∈ (G.El → H.pnt ≡ y) ] ((ω : G.El) → p ω ≡ f ω ∙ p refl)) ≃ (Σ[ y ∈ H.type ] (b ≡ y))
  equiv2 = isoToEquiv (iso
    (λ (y , p , h) → y , p refl)
    (λ (y , pRefl) → y , (λ ω → f ω ∙ pRefl) , λ ω → cong (λ r → f ω ∙ r) (lUnit pRefl ∙ cong (λ r → r ∙ pRefl) (sym (homId (abs G) (abs H) ϕ))))
    (λ (y , pRefl) → ΣPathP (refl , sym (lUnit _ ∙ cong (λ r → r ∙ pRefl) (sym (homId (abs G) (abs H) ϕ)))))
    λ (y , p , h) → ΣPathP (refl , ΣProp≡ (λ _ → isPropΠ λ _ → H.isGrpd _ _ _ _) (funExt λ ω → sym (h ω))))

  contr-a : isContr (Σ[ y ∈ H.type ] (b ≡ y))
  contr-a = (b , refl) , λ (b' , p) → ΣPathP (p , λ i j → p (i ∧ j))

{-
deloop : ∀ {ℓ} (G H : ConcreteGroup ℓ) (f : GroupHom (abs G) (abs H)) → (CG.Ptd G →∙ CG.Ptd H)
deloop {ℓ} Ggrp Hgrp ϕ = (λ x → fst (fst (isContrC x))) , sym (snd (fst lemma2 (fst lemma1 (fst (isContrC a))))) where
  module G = ConcreteGroup Ggrp
  module H = ConcreteGroup Hgrp
  a = G.pnt
  b = H.pnt
  f = fst ϕ
  fmorph = snd ϕ
  C : G.type → Type ℓ
  C x = Σ[ y ∈ H.type ]
        Σ[ p ∈ ((G.pnt ≡ x) → (H.pnt ≡ y)) ]
        ((ω : G.pnt ≡ G.pnt) (α : G.pnt ≡ x) → p (ω ∙ α) ≡ f ω ∙ p α)
  lemma1 : C a ≃ (Σ[ y ∈ H.type ] Σ[ p ∈ (G.El → H.pnt ≡ y) ] ((ω : G.El) → p ω ≡ f ω ∙ p refl))
  lemma1 = isoToEquiv (iso
    (λ (y , p , h) → y , p , λ ω → p ω ≡⟨ cong p (rUnit ω) ⟩ p (ω ∙ refl) ≡⟨ h ω refl ⟩ f ω ∙ p refl ∎)
    (λ (y , p , h) → y , p , λ ω α →
      p (ω ∙ α)
        ≡⟨ h (ω ∙ α) ∙ cong (λ r → r ∙ p refl) (fmorph _ _) ∙ sym (assoc _ _ _)⟩
      f ω ∙ f α ∙ p refl
        ≡⟨ cong (λ r → f ω ∙ r) (sym (h α)) ⟩
      f ω ∙ p α ∎)
    (λ (y , p , h) → ΣPathP (refl , ΣProp≡ (λ _ → isPropΠ λ _ → CG.isGrpd Hgrp _ _ _ _) refl))
    (λ (y , p , h) → ΣPathP (refl , ΣProp≡ (λ _ → isPropΠ2 λ _ _ → CG.isGrpd Hgrp _ _ _ _) refl)))
  lemma2 : (Σ[ y ∈ H.type ] Σ[ p ∈ (G.El → H.pnt ≡ y) ] ((ω : G.El) → p ω ≡ f ω ∙ p refl)) ≃ (Σ[ y ∈ H.type ] (b ≡ y))
  lemma2 = isoToEquiv (iso
    (λ (y , p , h) → y , p refl)
    (λ (y , pRefl) → y , (λ ω → f ω ∙ pRefl) , λ ω → cong (λ r → f ω ∙ r) (lUnit pRefl ∙ cong (λ r → r ∙ pRefl) (sym (homId (abs Ggrp) (abs Hgrp) ϕ))))
    (λ (y , pRefl) → ΣPathP (refl , sym (lUnit _ ∙ cong (λ r → r ∙ pRefl) (sym (homId (abs Ggrp) (abs Hgrp) ϕ)))))
    λ (y , p , h) → ΣPathP (refl , ΣProp≡ (λ _ → isPropΠ λ _ → CG.isGrpd Hgrp _ _ _ _) (funExt λ ω → sym (h ω))))
  isContrCa : isContr (C a)
  isContrCa = transport (cong isContr (sym (ua (compEquiv lemma1 (compEquiv lemma2 (isoToEquiv
    (iso (λ _ → tt) (λ _ → b , refl) (λ {tt → refl}) λ (y , p) → ΣPathP (p , λ i j → p (i ∧ j))))))))) isContrUnit
  isContrC : (x : G.type) → isContr (C x)
  isContrC x = recPropTrunc isPropIsContr (λ p → transport (cong (λ x → isContr (C x)) p) isContrCa) (G.conn x)
-}
{-deloop : ∀ {ℓ} {ℓ'} (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ') (f : CG.El G → CG.El H) → ((x y : CG.El G) → f (x ∙ y) ≡ f x ∙ f y) → (CG.type G → CG.type H)
deloop {ℓ} {ℓ'} Ggrp Hgrp f morph = {!!} where
  module G = CG Ggrp
  module H = CG Hgrp
  C : G.type → Type (ℓ-max ℓ ℓ')
  C x = Σ[ y ∈ H.type ]
        Σ[ p ∈ ((G.pnt ≡ x) → (H.pnt ≡ y)) ]
        ((ω : G.pnt ≡ G.pnt) (α : G.pnt ≡ x) → p (ω ∙ α) ≡ (f ω) ∙ p α)
-}

