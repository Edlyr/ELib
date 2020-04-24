{-# OPTIONS --cubical #-}

module ELib.ConcreteGroup.Base where

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

record ConcreteGroupStruct {ℓ} (A : Type ℓ) : Type ℓ where
  constructor struct-conc-group
  field
    pnt : A
    conn : (x : A) → ∥ pnt ≡ x ∥
    grpd : isSet (pnt ≡ pnt)

  isConn : isConnected A
  isConn x y = recPropTrunc propTruncIsProp (λ px → recPropTrunc propTruncIsProp (λ py → ∣ sym px ∙ py ∣) (conn y)) (conn x)

  isGrpd : isGroupoid A
  isGrpd x y = recPropTrunc isPropIsSet (λ px → recPropTrunc isPropIsSet (λ py → transport (λ i → isSet(px i ≡ py i)) (grpd)) (conn y)) (conn x)

  El : Type ℓ
  El = pnt ≡ pnt

record ConcreteGroup ℓ : Type (ℓ-suc ℓ) where
  constructor conc-group
  field
    type : Type ℓ
    struct : ConcreteGroupStruct type
  open ConcreteGroupStruct struct public
  
  Ptd : Pointed ℓ
  Ptd = (type , pnt)

private
  module CG = ConcreteGroup

-- Group of automorphisms of a point "a" in a type "A"
Aut : ∀ {ℓ} {A : Type ℓ} (a : A) → isGroupoid A → ConcreteGroup ℓ
Aut {ℓ} {A} a p = conc-group (fst Ptd) (struct-conc-group (snd Ptd)
  (snd (isConnectedConnectedComponent (A , a))) (isOfHLevelConnectedComponent ((A , a)) 3 p _ _)) where
  Ptd = connectedComponent (A , a)

-- Abelian groups
isAbelian : ∀ {ℓ} → ConcreteGroup ℓ → Type ℓ
isAbelian G = (x y : pnt ≡ pnt) → (x ∙ y) ≡ (y ∙ x) where open ConcreteGroup G

isPropIsAbelian : ∀ {ℓ} (G : ConcreteGroup ℓ) → isProp (isAbelian G)
isPropIsAbelian G = isPropΠ2 λ _ _ → isGrpd _ _ _ _ where open ConcreteGroup G

AbConcreteGroup : ∀ {ℓ} → Type (ℓ-suc ℓ)
AbConcreteGroup {ℓ} = Σ (ConcreteGroup ℓ) isAbelian

-- Group isomorphism implies equality
-- Not a very pretty proof, mostly because Agda has a hard time inferring implicit arguments
uaGroup : ∀ {ℓ} (G H : ConcreteGroup ℓ) → (f : CG.type G ≃ CG.type H) → (fst f (CG.pnt G) ≡ CG.pnt H) → G ≡ H
uaGroup G H f p i = conc-group (ua f i) (struct-conc-group
  (toPathP {A = λ i → ua f i} {x = CG.pnt G} {y = CG.pnt H} (uaβ f (CG.pnt G) ∙ p) i)
  (toPathP {A = λ i → (x : ua f i) → ∥ toPathP {A = λ i → ua f i} {x = CG.pnt G} (transportRefl (f .fst (CG.pnt G)) ∙ p) i ≡ x ∥} {x = CG.conn G} {y = CG.conn H}
    ((isPropΠ (λ _ → propTruncIsProp)) _ _) i)
  (toPathP
    {A = λ i → (x y : toPathP {A = λ i → ua f i} {x = CG.pnt G} {y = CG.pnt H} (transportRefl (f .fst (CG.pnt G)) ∙ p) i
      ≡ toPathP {A = λ i → ua f i} {x = CG.pnt G} {y = CG.pnt H} (transportRefl (f .fst (CG.pnt G)) ∙ p) i) → isProp (x ≡ y)}
    {x = CG.grpd G} {y = CG.grpd H} (isPropIsSet _ _) i))

-- Concrete definition of the center of a group
Z : ∀ {ℓ} → ConcreteGroup ℓ → ConcreteGroup ℓ
Z G = Aut {A = (type ≃ type)} (idEquiv _) (isOfHLevel≃ 3 isGrpd isGrpd) where
  open ConcreteGroup G

Z' : ∀ {ℓ} → ConcreteGroup ℓ → ConcreteGroup (ℓ-suc ℓ)
Z' G = Aut {A = (type ≡ type)} (refl) (isOfHLevel≡ 3 isGrpd isGrpd) where
  open ConcreteGroup G

BZ'≃BZ : ∀ {ℓ} → (G : ConcreteGroup ℓ) → (CG.type (Z' G) ≃ CG.type (Z G))
BZ'≃BZ G = isoToEquiv (iso
  (λ x → pathToEquiv (fst x) , recPropTrunc propTruncIsProp (λ p → ∣ cong pathToEquiv p ∙ pathToEquivRefl ∣) (snd x))
  (λ y → ua (fst y) , recPropTrunc propTruncIsProp (λ p → ∣ cong ua p ∙ uaIdEquiv  ∣) (snd y))
  (λ y → ΣPathP (pathToEquiv-ua _ , toPathP (propTruncIsProp _ _)))
  λ x → ΣPathP (ua-pathToEquiv _ , toPathP (propTruncIsProp _ _)))

-- Inclusion homomorphism from ZG to G
𝓩 : ∀ {ℓ} (G : ConcreteGroup ℓ) → ConcreteGroup.Ptd (Z G) →∙ ConcreteGroup.Ptd G
fst (𝓩 G) ((f , _) , _) = f (ConcreteGroup.pnt G)
snd (𝓩 G) = refl

lemma𝓩SetFibers : ∀ {ℓ} (G : ConcreteGroup ℓ) (x : ConcreteGroup.type G) → isSet (fiber (fst (𝓩 G)) x)
lemma𝓩SetFibers {ℓ} G x = recPropTrunc isPropIsSet (λ p → transport (λ i → isSet (fiber (fst (𝓩 G)) (p i))) lemma) (conn x) where
  open ConcreteGroup G
  commΣ : ∀ {ℓ} {A : Type ℓ} {B C : A → Type ℓ} →
    (Σ[ x ∈ (Σ[ y ∈ A ] (B y)) ] C (fst x))
    ≡ (Σ[ x ∈ (Σ[ y ∈ A ] (C y)) ] B (fst x))
  commΣ = isoToPath (iso (λ ((a , b) , c) → ((a , c) , b)) ((λ ((a , c) , b) → ((a , b) , c))) (λ _ → refl) (λ _ → refl))
  lemma : isSet (fiber (fst (𝓩 G)) pnt)
  lemma = transport (cong isSet (sym commΣ)) (isSetΣ (transport (cong isSet commΣ)
    (isSetΣ subLemma (λ _ → isProp→isSet (isPropIsEquiv _)))) λ _ → isProp→isSet propTruncIsProp) where
    subLemma : isSet(Σ[ f ∈ (type → type) ] (f pnt ≡ pnt))
    subLemma (ϕ , p) (ψ , q) =
      transport (cong isProp (ua Σ≡))
      (transport (cong (λ x → isProp(Σ _ x)) (funExt λ _ → sym (PathP≡compPathL _ _ _)))
      λ π π' → ΣPathP (pathExt _ _ (cong sym (simplR q (snd π) ∙ sym (simplR q (snd π')))) , toPathP (isGrpd _ _ _ _ _ _))) where
        simplR : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a ≡ b} {q : b ≡ c} → (s : a ≡ c) → p ∙ q ≡ s → p ≡ s ∙ sym q
        simplR {a = a} {p = p} {q = q} = J (λ c q → (s : a ≡ c) → p ∙ q ≡ s → p ≡ s ∙ sym q) (λ _ r → rUnit _ ∙ r ∙ rUnit _) q
        eval : (ϕ ≡ ψ) → (x : type) → (ϕ x ≡ ψ x)
        eval π x i = π i x
        pathExt : (π π' : ϕ ≡ ψ) → (eval π pnt) ≡ (eval π' pnt) → π ≡ π'
        pathExt π π' p = cong funExt (funExt λ x → recPropTrunc (isGrpd _ _ _ _) (λ q →
          transport (let path : (ϕ x ≡ ψ x) ≡ (ϕ pnt ≡ ψ pnt)
                         path = λ i → ϕ (q (~ i)) ≡ ψ (q (~ i)) in
                     let fin : path ∙ refl ∙ path ⁻¹ ≡ refl
                         fin = cong (λ x → path ∙ x) (sym (lUnit _)) ∙ lCancel _ in
                     λ i → PathP (λ j → fin i j) (λ i → π i x) (λ i → π' i x)) (compPathP (cong (eval π) (sym q)) (compPathP p (cong (eval π') q)))) (conn x))

cong𝓩 : ∀ {ℓ} (G : ConcreteGroup ℓ) → ConcreteGroup.El (Z G) → ConcreteGroup.El G
cong𝓩 G = cong (fst (𝓩 G))

cong𝓩AbstractCenter : ∀ {ℓ} (G : ConcreteGroup ℓ) (x : _) (y : _) → cong𝓩 G x ∙ y ≡ y ∙ cong𝓩 G x
cong𝓩AbstractCenter Ggrp x y =
  cong𝓩 Ggrp x ∙ y
    ≡⟨ cong (λ r → cong𝓩 Ggrp x ∙ r) (lemma2 x y) ⟩
  (cong𝓩 Ggrp x ∙ (cong𝓩 Ggrp (sym x)) ∙ y ∙ (cong𝓩 Ggrp x))
    ≡⟨ assoc _ _ _ ⟩
  (cong𝓩 Ggrp x ∙ cong𝓩 Ggrp (sym x)) ∙ y ∙ (cong𝓩 Ggrp x)
    ≡⟨ cong (λ r → r ∙ y ∙ (cong𝓩 Ggrp x)) (rCancel (cong𝓩 Ggrp x)) ∙ sym (lUnit _) ⟩
  _ ∎ where
  module G = ConcreteGroup Ggrp
  module ZG = ConcreteGroup (Z Ggrp)
  
  lemma : ∀ (ϕ : ZG.type) → (p : ZG.pnt ≡ ϕ) →
    cong {x = G.pnt} {y = G.pnt} (fst (fst ϕ)) ≡ (λ q → ((λ i → fst (fst (p (~ i))) G.pnt) ∙ q ∙ (λ i → fst (fst (p i)) G.pnt)))
  lemma ϕ = J (λ ϕ p → cong {x = G.pnt} {y = G.pnt} (fst (fst ϕ)) ≡ (λ q → ((λ i → fst (fst (p (~ i))) G.pnt) ∙ q ∙ (λ i → fst (fst (p i)) G.pnt))))
    (funExt λ x → rUnit _ ∙ lUnit _)
  lemma2 : (p : ZG.El) (q : G.El) → q ≡ (cong𝓩 Ggrp (sym p)) ∙ q ∙ (cong𝓩 Ggrp p)
  lemma2 p q i = lemma ZG.pnt p i q

cong𝓩inj : ∀ {ℓ} (G : ConcreteGroup ℓ) → isEmbedding(cong𝓩 G)
cong𝓩inj G' = injEmbedding (ZG.isGrpd _ _) (G.isGrpd _ _) λ {x} {y} p → p∙q⁻¹≡refl→p≡q _ _
  let path = lemma (x ∙ y ⁻¹) (cong𝓩 G' (x ∙ y ⁻¹) ≡⟨ cong-∙ (fst (𝓩 G')) x (y ⁻¹) ⟩ (cong𝓩 G' x ∙ (cong𝓩 G' (sym y))) ≡⟨ p≡q→p∙q⁻¹≡refl _ _ p ⟩ refl ∎) in
  let simplification : path ≡ refl
      simplification = (lemma𝓩SetFibers G' G.pnt _ _ _ _) in
      fst (pathSigma→sigmaPath _ _ (cong (pathSigma→sigmaPath _ _) simplification)) where
  module G = ConcreteGroup G'
  module ZG = ConcreteGroup (Z G')

  lemma : (x : ZG.El) → (cong𝓩 G' x ≡ refl) → (Path (fiber (fst (𝓩 G')) G.pnt) (ZG.pnt , refl) (ZG.pnt , refl))
  lemma x p = ΣPathP (x , transport (sym (PathP≡compPathL _ _ _)) (sym (rUnit _) ∙ cong sym p))

-- Corollary : Z G is abelian
isAbelianZ : ∀ {ℓ} (G : ConcreteGroup ℓ) → isAbelian (Z G)
isAbelianZ G f g = fst (invEquiv (_ , cong𝓩inj G (f ∙ g) (g ∙ f))) lemma where
  ϕ = cong𝓩 G
  lemma : ϕ (f ∙ g) ≡ ϕ (g ∙ f)
  lemma = (cong-∙ (fst (𝓩 G)) f g) ∙ cong𝓩AbstractCenter G f (ϕ g) ∙ sym (cong-∙ (fst (𝓩 G)) g f)

cong𝓩surj : ∀ {ℓ} (G : ConcreteGroup ℓ) → (g : CG.El G) → ((h : CG.El G) → g ∙ h ≡ h ∙ g ) → fiber (cong𝓩 G) g
cong𝓩surj {ℓ} G g comm =
  ΣPathP (ΣPathP (funExt (λ x → fst (fst (isContrT x))) , toPathP (isPropIsEquiv _ _ _)) , toPathP (propTruncIsProp _ _)) ,
  (fst (fst (isContrT pnt)) ≡⟨ sym (rUnit _ ∙ (snd (fst (isContrT pnt)) refl) ∙ sym (lUnit _)) ⟩ (λ i → g)) where
  open ConcreteGroup G
  T : (x : type) → (x ≡ x) → Type ℓ
  T x q = (p : pnt ≡ x) → (g ∙ p ≡ p ∙ q)
  
  comm1 : ∀ (p q : pnt ≡ pnt) → (g ∙ p ≡ p ∙ q) → (g ≡ q)
  comm1 p q r = lUnit _ ∙ cong (λ x → x ∙ g) (sym (lCancel p)) ∙ sym (assoc _ _ _) ∙ cong (λ x → p ⁻¹ ∙ x) (sym (comm p) ∙ r)
    ∙ assoc _ _ _ ∙ cong (λ x → x ∙ q) (lCancel p) ∙ sym (lUnit _)
  comm2 : ∀ (p q : pnt ≡ pnt) → (g ≡ q) → (g ∙ p ≡ p ∙ q)
  comm2 p q r = comm p ∙ cong (λ x → p ∙ x) r
  
  equivT : Σ (pnt ≡ pnt) (T pnt) ≃ Unit {ℓ}
  equivT =
    Σ (pnt ≡ pnt) (T pnt)
      ≃⟨ isoToEquiv (iso (λ x → fst x , λ p → comm1 _ _ (snd x p)) (λ y → fst y , λ p → comm2 _ _ (snd y p))
        (λ x → ΣPathP (refl , funExt λ _ → isGrpd _ _ _ _ _ _)) λ x → ΣPathP (refl , funExt λ _ → isGrpd _ _ _ _ _ _)) ⟩
    Σ (pnt ≡ pnt) (λ q → (p : pnt ≡ pnt) → g ≡ q)
      ≃⟨ isoToEquiv (iso (λ x → fst x , snd x refl) (λ y → fst y , λ _ → snd y) (λ _ → refl)
        λ _ → ΣPathP (refl , funExt λ _ → isGrpd _ _ _ _ _ _)) ⟩
    Σ (pnt ≡ pnt) (λ q → g ≡ q)
      ≃⟨ isoToEquiv (iso (λ _ → tt) (λ {tt → g , (λ i → g)}) (λ {tt → refl}) λ x → ΣPathP (snd x ,
        transport (sym (PathP≡compPathR _ _ _)) (sym (lUnit _)))) ⟩
    Unit ■
  isContrT : (x : type) → isContr (Σ[ q ∈ (x ≡ x) ] (T x q))
  isContrT x = recPropTrunc isPropIsContr (λ pnt≡x → transport (cong (λ z → isContr (Σ (z ≡ z) (T z))) pnt≡x)
    (transport (cong isContr (sym (ua equivT))) isContrUnit)) (conn x)

-- Alternative definition of abelianness
isAbelian' : ∀ {ℓ} → (G : ConcreteGroup ℓ) → Type ℓ
isAbelian' G = isEquiv(fst (𝓩 G))

isPropIsAbelian' : ∀ {ℓ} → (G : ConcreteGroup ℓ) → isProp (isAbelian' G)
isPropIsAbelian' G = isPropIsEquiv _

isAbelian'→isAbelian : ∀ {ℓ} (G : ConcreteGroup ℓ) → isAbelian' G → isAbelian G
isAbelian'→isAbelian {ℓ} G p = transport (cong isAbelian (uaGroup (Z G) G (fst (𝓩 G) , p) (snd (𝓩 G)))) (isAbelianZ G)

{-
isAbelian→isAbelian' : ∀ {ℓ} (G : ConcreteGroup ℓ) → isAbelian G → isAbelian' G
isAbelian→isAbelian' Ggrp Gab .equiv-proof y = recPropTrunc isPropIsContr (λ p → transport (λ i → isContr (fiber (fst (𝓩 Ggrp)) (p i)))
  ((ZG.pnt , refl) , λ x → recPropTrunc (lemma𝓩SetFibers Ggrp G.pnt _ _) (λ q → ΣPathP (q , transport (sym (PathP≡compPathL _ _ _)) (sym (rUnit _) ∙ {!!}))) (ZG.conn (fst x)))
  ) (G.conn y) where
  module G = ConcreteGroup Ggrp
  module ZG = ConcreteGroup (Z Ggrp)
-}
