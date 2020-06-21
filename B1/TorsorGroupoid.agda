
{-# OPTIONS --cubical #-}

module ELib.B1.TorsorGroupoid where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Sigma
open import Cubical.Structures.Group
open import ELib.B1.Torsor
open import ELib.Group.Morphism
open import ELib.UsefulLemmas

module BTorsor {ℓ : Level} {G : Group {ℓ}} where
  private module G = Group G
  _⨀_ = G._+_
  inv = G.-_
  B : Type (ℓ-suc ℓ)
  B = Σ[ r ∈ (RAction G) ] ∥ principalTorsor G ≡ r ∥

  T⟨_⟩ : B → Type ℓ
  T⟨ X ⟩ = fst (fst X) 

  isTorsorBElement : (x : B) → isTorsor G (fst x)
  isTorsorBElement (r , p) = recPropTrunc (isPropIsTorsor G r) (λ p → transport (cong (isTorsor G) p) (isTorsorPrincipalTorsor G)) p

  isSetBElement : (x : B) → isSet (fst (fst x))
  isSetBElement x = fst (snd (isTorsorBElement x))
  
  actionLaw : (T : B) → fst (fst T) → ⟨ G ⟩ → fst (fst T)
  actionLaw T x g = fst (snd (fst T)) x g
  syntax actionLaw T x g = x ⋆⟨ T ⟩ g

  open TorsorLoopspace G
  
  caracB≡ : (X Y : B) → (X ≡ Y) ≃ ((fst X , isTorsorBElement X) T≃T ((fst Y , isTorsorBElement Y)))
  caracB≡ X Y =
    X ≡ Y
      ≃⟨ isoToEquiv (iso (cong fst) (Σ≡Prop λ _ → propTruncIsProp) (λ _ → refl)
         (λ p → cong ΣPathP (Σ≡Prop (λ _ → isOfHLevelPathP 1 (λ i → propTruncIsProp) _ _) refl))) ⟩
    fst X ≡ fst Y
      ≃⟨ TorsorEquality.torsorEqualityEquiv G (fst X) (fst Y) (isTorsorBElement X) (isTorsorBElement Y) ⟩
    _ ■

  private
    lemmaProp : {X Y : B} (f : T⟨ X ⟩ ≃ T⟨ Y ⟩) → isProp ((x : T⟨ X ⟩) → (g : ⟨ G ⟩) → fst f (x ⋆⟨ X ⟩ g) ≡ fst f x ⋆⟨ Y ⟩ g)
    lemmaProp {X} {Y} f = isPropΠ λ _ → isPropΠ λ _ → isSetBElement Y _ _

  isGroupoidB : isGroupoid B
  isGroupoidB X Y =
    isOfHLevelRespectEquiv 2 (invEquiv (caracB≡ X Y))
    (isSetΣ (isOfHLevel≃ 2 (isSetBElement X) (isSetBElement Y)) λ f → isProp→isSet (lemmaProp {X} {Y} f))

  
  PT : B
  PT = principalTorsor G , ∣ refl ∣

  PT' : Torsor
  PT' = principalTorsor G , isTorsorBElement PT

  open TorsorEquality G (fst PT') (fst PT') (snd PT') (snd PT')

  -- Intermediate groups that will be used in the characterisation of ΩB
  ΩB : Group {ℓ-suc ℓ}
  ΩB = makeGroup (refl {x = PT}) _∙_ sym (isGroupoidB PT PT) assoc (λ x → sym (rUnit x)) (λ x → sym (lUnit x)) rCancel lCancel

  G' : Group {ℓ}
  G' = DualGroup G

  intermediateMagma : Σ[ X ∈ Type ℓ ] (X → X → X)
  intermediateMagma = PT' T≃T PT' , comp≃T {T¹ = PT'} {T² = PT'} {T³ = PT'}

  m = equivFun (caracB≡ PT PT)
  caracB≡morphism : (p q : ⟨ ΩB ⟩) → m (p ∙ q) ≡ snd intermediateMagma (m p) (m q)
  caracB≡morphism p q = Σ≡Prop (λ f → lemmaProp {PT} {PT} f) (
    fst (m (p ∙ q))
      ≡⟨ torsorEqualityEquivFst (cong fst (p ∙ q)) ⟩ -- This line is technically "refl" but it has been abstracted out
    pathToEquiv (cong fst (cong fst (p ∙ q)))
      ≡⟨ cong pathToEquiv (cong (cong fst) (cong-∙ fst p q) ∙ cong-∙ fst (cong fst p) (cong fst q)) ⟩
    pathToEquiv (cong fst (cong fst p) ∙ cong fst (cong fst q))
      ≡⟨ pathToEquiv∙ _ _ ⟩
    compEquiv (pathToEquiv (cong fst (cong fst p))) (pathToEquiv (cong fst (cong fst q)))
      ≡⟨ sym (λ i → compEquiv (torsorEqualityEquivFst (cong fst p) i) (torsorEqualityEquivFst (cong fst q) i)) ⟩
    compEquiv (fst (m p)) (fst (m q)) ∎)

  preΩB : Group {_}
  preΩB = groupStructFromIso ΩB intermediateMagma (m , snd (caracB≡ PT PT)) caracB≡morphism

  preΩB→G' : ⟨ preΩB ⟩ → ⟨ G' ⟩
  preΩB→G' ((f , equiv) , β) = f G.0g

  G'→preΩB : ⟨ G' ⟩ → ⟨ preΩB ⟩
  G'→preΩB g = isoToEquiv (iso (λ x → g ⨀ x) (λ x → inv g ⨀ x)
    (λ x → sym (sym (G.lid x) ∙ cong (λ y → y ⨀ x) (sym (G.invr g)) ∙ sym (G.assoc _ _ _)))
    (λ x → sym (sym (G.lid x) ∙ cong (λ y → y ⨀ x) (sym (G.invl g)) ∙ sym (G.assoc _ _ _)))) ,
    λ x h → (g ⨀ (x ⨀ h)) ≡⟨ G.assoc _ _ _ ⟩ ((g ⨀ x) ⨀ h) ∎

  isMorphism-G'→preΩB : isGroupHom G' preΩB G'→preΩB
  isMorphism-G'→preΩB g g' = Σ≡Prop (λ f → lemmaProp {PT} {PT} f) (equivEq _ _ (funExt λ x →
    ((g' ⨀ g) ⨀ x) ≡⟨ sym (G.assoc g' g x) ⟩ (g' ⨀ (g ⨀ x)) ∎))

  private
    retr : retract G'→preΩB preΩB→G'
    retr = G.rid

    sec : section G'→preΩB preΩB→G'
    sec ((f , equiv) , β) =
      Σ≡Prop (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetBElement PT _ _)
      (equivEq _ _ (funExt λ x →
        (f G.0g ⨀ x)
          ≡⟨ sym (β G.0g x) ⟩
        f (G.0g ⨀ x)
          ≡⟨ cong f (G.lid x) ⟩
        f x ∎))

  G'≃preΩB : GroupIso G' preΩB
  G'≃preΩB = groupiso (isoToEquiv (iso G'→preΩB preΩB→G' sec retr)) isMorphism-G'→preΩB

  ΩB≃preΩB : GroupIso ΩB preΩB
  ΩB≃preΩB = groupiso (caracB≡ PT PT) caracB≡morphism

  ΩB≃G : GroupIso ΩB G
  ΩB≃G = compGroupIso ΩB≃preΩB (compGroupIso (invGroupIso G' preΩB G'≃preΩB) (invGroupIso G G' (DualGroupIso G)))
