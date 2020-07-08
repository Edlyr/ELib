{-# OPTIONS --cubical #-}

module ELib.Gerbe.B2 where

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

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (A : AbGroup {ℓ}) {ℓ' : Level} where
  record B² : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    constructor b²
    field
      grb : Gerbe {ℓ'}
      lnk : Link grb A

    open Gerbe grb public
    open Link lnk public

  record B²Equiv (G H : B²) : Type (ℓ-max ℓ' ℓ) where
    constructor b²equiv
    module G = B² G
    module H = B² H
    field
      fun : G.Carrier → H.Carrier
      p : congLink G.lnk H.lnk fun ≡ grouphom (λ x → x) (λ _ _ → refl)

    abstract
      isEquiv-fun : isEquiv fun
      isEquiv-fun = isEmbedding×isSurjection→isEquiv (embed , surj) where
        lemma : (x : G.Carrier) → isEquiv (cong {x = x} {y = x} fun)
        lemma x = transport (cong isEquiv (sym p')) (snd (compEquiv (G.eq x) (invEquiv (H.eq (fun x))))) where
          p' : (cong {x = x} {y = x} fun) ≡ invEq (H.eq (fun x)) ∘ G.e x
          p' =
            cong {x = x} {y = x} fun
              ≡⟨ (λ i → funExt (secEq (H.eq (fun x))) (~ i) ∘ cong fun ∘ funExt (secEq (G.eq x)) (~ i)) ⟩
            invEq (H.eq (fun x)) ∘ H.e (fun x) ∘ cong {x = x} {y = x} fun ∘ invEq (G.eq x) ∘ G.e x
              ≡⟨ cong (λ r → invEq (H.eq (fun x)) ∘ r ∘ G.e x) (sym (cong GroupHom.fun (congLink-carac G.lnk H.lnk fun x))) ⟩
            invEq (H.eq (fun x)) ∘ GroupHom.fun (congLink G.lnk H.lnk fun) ∘ G.e x
              ≡⟨ cong (λ r → invEq (H.eq (fun x)) ∘ r ∘ G.e x) (cong GroupHom.fun p) ⟩
            invEq (H.eq (fun x)) ∘ G.e x ∎

        embed : isEmbedding fun
        embed x y = recPropTrunc (isPropIsEquiv _) (subLemma x y) (G.conn x y) where
          subLemma : (x y : _) (p : x ≡ y) → isEquiv (cong {x = x} {y = y} fun)
          subLemma x y = J (λ y p → isEquiv (cong {x = x} {y = y} fun)) (lemma x)

        surj : isSurjection fun
        surj y = recPropTrunc propTruncIsProp (λ x → recPropTrunc propTruncIsProp (λ p → ∣ x , p ∣) (H.conn (fun x) y)) (G.inhabited)

    eq : G.Carrier ≃ H.Carrier
    eq = fun , isEquiv-fun

{-  record B²Equiv (G H : B²) : Type ℓ where
    constructor b²equiv
    module G = B² G
    module H = B² H
    field
      eq : G.Carrier ≃ H.Carrier
      p : congLink G.lnk H.lnk (equivFun eq) ≡ grouphom (λ x → x) (λ _ _ → refl)
-}
isSetGroupEquiv : {A : Group {ℓ}} {B : Group {ℓ'}} → isSet (GroupEquiv A B)
isSetGroupEquiv {A = A} {B = B} = isOfHLevelRespectEquiv 2 (invEquiv lemma) (isSetΣ (isSetΠ λ _ → Group.is-set B)
  λ _ → isSetΣ (isProp→isSet (isPropIsEquiv _)) λ _ → isProp→isSet (isPropIsGroupHom A B)) where
  lemma : GroupEquiv A B ≃ (Σ[ f ∈ (Grp⟨ A ⟩ → Grp⟨ B ⟩) ] (isEquiv f) × isGroupHom A B f)
  lemma = isoToEquiv (iso (λ (groupequiv eq hom) → fst eq , snd eq , hom) (λ (f , eq , hom) → groupequiv (f , eq) hom)
    (λ _ → refl) λ _ → refl)

idGroupHom : {A : Group {ℓ}} → GroupHom A A
idGroupHom = grouphom (λ x → x) (λ _ _ → refl)

isPropIsLink : {G : Gerbe {ℓ'}} {A : AbGroup {ℓ}} {e : _} → isProp (IsLink G A e)
isPropIsLink {G = G} {A = A} {e = e} = isOfHLevelRespectEquiv 1 lemma (isProp× (isPropΠ λ _ → isPropIsEquiv _)
  (isPropΠ λ x → isPropIsGroupHom (AbGroup→Group (π G x)) (AbGroup→Group A))) where
  lemma : (((x : _) → isEquiv (e x)) × ((x : _) → isGroupHom (AbGroup→Group (π G x)) (AbGroup→Group A) (e x))) ≃ IsLink G A e
  lemma = isoToEquiv (iso (λ (a , b) → islink a b) (λ (islink a b) → a , b) (λ _ → refl) λ _ → refl)

isSetLink : {G : Gerbe {ℓ'}} {A : AbGroup {ℓ}} → isSet (Link G A)
isSetLink {G = G} {A = A} = isOfHLevelRespectEquiv 2 (invEquiv lemma) (isSetΠ λ _ → isSetGroupEquiv) where
  lemma : Link G A ≃ ((x : ⟨ G ⟩) → AbGroupEquiv (π G x) A)
  lemma = isoToEquiv (iso (λ l x → Link.group-equiv l x) (λ l → link (λ x → GroupEquiv.eq (l x) .fst)
    (islink (λ x → GroupEquiv.eq (l x) .snd) λ x → GroupEquiv.isHom (l x))) (λ _ → refl) λ _ → refl)

linkEq : {G : Gerbe {ℓ'}} {A : AbGroup {ℓ}} {l1 l2 : Link G A} → (Link.e l1 ≡ Link.e l2) → l1 ≡ l2
linkEq {G = G} {A = A} {l1 = l1} {l2 = l2} p i = link (p i) (lemma i) where
  lemma : PathP (λ i → IsLink G A (p i)) (Link.isLink l1) (Link.isLink l2)
  lemma = toPathP (isPropIsLink _ _)

module B²ΣTheory (A : AbGroup {ℓ}) {ℓ' : Level} where
  B²Struct : Type ℓ' → Type (ℓ-max ℓ ℓ')
  B²Struct X = Σ[ isGerbe ∈ IsGerbe X ] Link (gerbe X isGerbe) A

  isSetB²Struct : {X : Type ℓ'} → isSet (B²Struct X)
  isSetB²Struct {X = X} = isSetΣ (isProp→isSet isPropIsGerbe) λ _ → isSetLink

  B²Σ : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  B²Σ = TypeWithStr ℓ' B²Struct

  B²EquivStr : StrEquiv B²Struct ℓ
  B²EquivStr (X , grb , lnk) (X' , grb' , lnk') (f , eq) = congLink lnk lnk' f ≡ grouphom (λ x → x) (λ _ _ → refl)

  B²→B²Σ : B² A → B²Σ
  B²→B²Σ (b² grb lnk) = Gerbe.Carrier grb , Gerbe.isGerbe grb , lnk

  B²Σ→B² : B²Σ → B² A
  B²Σ→B² (X , grb , lnk) = b² (gerbe X grb) lnk

  open import Cubical.Foundations.Isomorphism
  open Iso
  B²IsoB²Σ : Iso (B² A) B²Σ
  B²IsoB²Σ = iso B²→B²Σ B²Σ→B² (λ _ → refl) (λ _ → refl)

  B²SNS : SNS B²Struct B²EquivStr
  B²SNS {X = X} (grb1 , lnk1) (grb2 , lnk2) = transport pathLemma (equiv grb2 lnk1' lnk2 ) where
    grb1≡grb2 : grb1 ≡ grb2
    grb1≡grb2 = isPropIsGerbe _ _
    lnk1' : Link (gerbe X grb2) A
    lnk1' = transport (λ i → Link (gerbe X (grb1≡grb2 i)) A) lnk1
    pathLemma : (B²EquivStr (X , grb2 , lnk1') (X , grb2 , lnk2) (idEquiv X) ≃ ((grb2 , lnk1') ≡ (grb2 , lnk2)))
              ≡ (B²EquivStr (X , grb1 , lnk1 ) (X , grb2 , lnk2) (idEquiv X) ≃ ((grb1 , lnk1 ) ≡ (grb2 , lnk2)))
    pathLemma i = B²EquivStr (X , finalLemma i) (X , grb2 , lnk2) (idEquiv X) ≃ (finalLemma i ≡ (grb2 , lnk2)) where
      finalLemma : (grb2 , lnk1') ≡ (grb1 , lnk1)
      finalLemma = sym (ΣPathP (grb1≡grb2 , toPathP refl))
    module _ (grb : IsGerbe X) (l1 l2 : Link (gerbe X grb) A) where
      module l1 = Link l1
      module l2 = Link l2
      G : Gerbe
      G = gerbe X grb
      α : B²Struct X
      α = grb , l1
      β : B²Struct X
      β = grb , l2

      isPropGoal : isProp (B²EquivStr (X , α) (X , β) (idEquiv X))
      isPropGoal = isSetGroupHom _ _

      fun1 : B²EquivStr (X , α) (X , β) (idEquiv X) → α ≡ β
      fun1 p = ΣPathP (refl , linkEq (funExt lemma2)) where
        lemma1 : (x : ⟨ G ⟩) → l2.e x ∘ invEq (l1.eq x) ≡ λ y → y
        lemma1 x = cong GroupHom.fun (sym (congLink-carac l1 l2 (λ y → y) x) ∙ p)
        lemma2 : (x : ⟨ G ⟩) → l1.e x ≡ l2.e x
        lemma2 x = l1.e x                            ≡⟨ cong (_∘ l1.e x) (sym (lemma1 x)) ⟩
                   l2.e x ∘ invEq (l1.eq x) ∘ l1.e x ≡⟨ cong (l2.e x ∘_) (funExt λ y → (secEq (l1.eq x) y)) ⟩
                   l2.e x ∎
      fun2 : α ≡ β → B²EquivStr (X , α) (X , β) (idEquiv X)
      fun2 p = recPropTrunc isPropGoal (λ x₀ → congLink-carac _ _ _ x₀ ∙ groupHomEq (lemma x₀)) (Gerbe.inhabited G) where
        q : l1 ≡ l2
        q = transport path (cong snd p) where
          path : PathP (λ i → Link (gerbe X (fst (p i))) A) (snd α) (snd β) ≡ PathP (λ i → Link (gerbe X grb) A) l1 l2
          path j = PathP (λ i → Link (gerbe X (isProp→isSet isPropIsGerbe grb grb (cong fst p) refl j i)) A) l1 l2
        lemma : (x : ⟨ G ⟩) → l2.e x ∘ invEq (l1.eq x) ≡ λ y → y
        lemma x = l2.e x ∘ invEq (l1.eq x) ≡⟨ (λ i → l2.e x ∘ invEq (Link.eq (q i) x)) ⟩
                  l2.e x ∘ invEq (l2.eq x) ≡⟨ (funExt λ y → retEq (l2.eq x) y) ⟩
                  (λ y → y) ∎

      equiv : (B²EquivStr (X , α) (X , β) (idEquiv X)) ≃ (α ≡ β)
      equiv = isoToEquiv (iso fun1 fun2 (λ _ → isSetB²Struct _ _ _ _) (λ _ → isPropGoal _ _))

  B²UnivalentStr : UnivalentStr B²Struct B²EquivStr
  B²UnivalentStr = SNS→UnivalentStr B²EquivStr B²SNS

  B²ΣPath : (X Y : B²Σ) → (X ≃[ B²EquivStr ] Y) ≃ (X ≡ Y)
  B²ΣPath = SIP B²UnivalentStr

  B²EquivΣ : (X Y : B² A) → Type _
  B²EquivΣ X Y = B²→B²Σ X ≃[ B²EquivStr ] B²→B²Σ Y

  B²IsoΣPath : {X Y : B² A} → Iso (B²Equiv A X Y) (B²EquivΣ X Y)
  fun B²IsoΣPath eq             = B²Equiv.eq eq , B²Equiv.p eq
  inv B²IsoΣPath (eq , p)       = b²equiv (fst eq) p
  rightInv B²IsoΣPath b         = ΣPathP (equivEq _ _ refl , refl)
  leftInv  B²IsoΣPath eq        = refl

  B²Path : (X Y : B² A) → (B²Equiv A X Y) ≃ (X ≡ Y)
  B²Path X Y =
    B²Equiv A X Y       ≃⟨ isoToEquiv B²IsoΣPath ⟩
    B²EquivΣ X Y        ≃⟨ B²ΣPath _ _ ⟩
    B²→B²Σ X ≡ B²→B²Σ Y ≃⟨ isoToEquiv (invIso (congIso B²IsoB²Σ)) ⟩
    X ≡ Y ■

  uaB² : {X Y : B² A} → B²Equiv A X Y → X ≡ Y
  uaB² = equivFun (B²Path _ _)

  carac-uaB² : {X Y : B² A} → (f : B²Equiv A X Y) → (cong B².Carrier (uaB² f)) ≡ ua (B²Equiv.eq f)
  carac-uaB² e = (refl ∙∙ ua eq ∙∙ refl) ≡⟨ sym (rUnit _) ⟩ ua eq ∎ where open B²Equiv e

open B²ΣTheory using (B²Path ; uaB² ; carac-uaB²) public

module Deloop2 (A : AbGroup {ℓ}) (B : AbGroup {ℓ'}) (f : AbGroupHom A B) {ℓG ℓH : Level}  where
  open B²
  type : B² A {ℓG} → Type _
  type G = Σ[ H ∈ B² B {ℓH} ] Σ[ g ∈ (Carrier G → Carrier H) ] congLink (B².lnk G) (B².lnk H) g ≡ f

  abstract
    isPropType : (G : B² A) → isProp (type G)
    isPropType G = recPropTrunc isPropIsProp lemma (inhabited G) where
      module G = B² G
      lG = G.lnk
      lemma : (x : G.Carrier) → isProp (type G)
      lemma x (H1 , g1 , !1) (H2 , g2 , !2) = ΣPathP (path-H , ΣPathP ((λ i → fst (path-g i)) , toPathP (isSetGroupHom _ _ _ _))) where
        module H1 = B² H1
        module H2 = B² H2
        h1 = g1 x
        h2 = g2 x
        l1 = H1.lnk
        l2 = H2.lnk

        H→ : Σ[ j ∈ (H1.Carrier → H2.Carrier) ] (h2 ≡ j h1) × (congLink l1 l2 j ≡ idGroupHom)
        H→ = deloopContr l1 l2 idGroupHom h1 h2 .fst

        equiv : B²Equiv B H1 H2
        equiv = b²equiv (H→ .fst) (H→ .snd .snd)
        module equiv = B²Equiv equiv

        path-H : H1 ≡ H2
        path-H = uaB² B equiv

        isDeloop-g1 : deloopType lG l1 f x h1
        isDeloop-g1 = g1 , refl , !1
        isDeloop-g2 : deloopType lG l2 f x h2
        isDeloop-g2 = g2 , refl , !2

        pointed : PathP (λ i → B².Carrier (path-H i)) h1 h2
        pointed = toPathP (
          transport (cong Carrier path-H) h1 ≡⟨ (λ i → transport (carac-uaB² B equiv i) h1) ⟩
          transport (ua equiv.eq) h1         ≡⟨ uaβ equiv.eq h1 ⟩
          equiv.fun h1                       ≡⟨ sym (H→ .snd .fst) ⟩
          h2 ∎)

        path-g : PathP (λ i → deloopType lG (B².lnk (path-H i)) f x (pointed i)) isDeloop-g1 isDeloop-g2
        path-g = toPathP (deloopUnique lG l2 f x h2 _ _)

    -- Any pointed gerbe in B² B gives rise to a definition of 2-delooping
    -- If ℓH is (ℓ-suc ℓ'), then the Gerbe of B-torsors will do
    2-deloop-def : (H : B² B {ℓH}) (h : B².Carrier H) (G : B² A) → type G
    2-deloop-def H h G = recPropTrunc (isPropType G) lemma (B².inhabited G) where
      module G = B² G
      module H = B² H
      lemma : B².Carrier G → type G
      lemma x = H , fst deloop , snd (snd deloop) where
        deloop : deloopType G.lnk H.lnk f x h
        deloop = deloopContr _ _ _ _ _ .fst

  2-deloop : (H : B² B) → B².Carrier H → B² A → B² B
  2-deloop H h = fst ∘ 2-deloop-def H h

module DeloopFunctoriality where
  2-deloop-id : {A : AbGroup {ℓ}} (H : B² A {ℓ'}) (h : B².Carrier H) → Deloop2.2-deloop A A (grouphom (λ x → x) (λ _ _ → refl)) H h ≡ λ x → x
  2-deloop-id {A = A} H h = funExt λ G → cong fst (isPropType G (2-deloop-def H h G) (id-deloop G)) where
    open Deloop2 A A (grouphom (λ x → x) (λ _ _ → refl))
    id-deloop : (G : B² A {ℓ'}) → type G
    id-deloop G = G , (λ x → x) , recPropTrunc (isSetGroupHom _ _) (λ x₀ →
      congLink-carac _ _ _ x₀ ∙ groupHomEq (funExt λ x →
        B².e G x₀ (invEq (B².eq G x₀) x) ≡⟨ retEq (B².eq G x₀) x ⟩ x ∎
      )) (B².inhabited G)

  2-deloop-comp : {A : AbGroup {ℓ}} {B : AbGroup {ℓ'}} {C : AbGroup {ℓ''}} {ℓG ℓH ℓF : Level}
    (H : B² B {ℓH}) (x₀ : B².Carrier H)
    (F : B² C {ℓF}) (y₀ : B².Carrier F)
    (f : AbGroupHom A B) (g : AbGroupHom B C) →
    Deloop2.2-deloop A C (compGroupHom f g) {ℓG = ℓG} F y₀ ≡ Deloop2.2-deloop B C g F y₀ ∘ Deloop2.2-deloop A B f H x₀
  2-deloop-comp {A = A} {B = B} {C = C} H x₀ F y₀ f g = funExt λ G →
    cong fst (Deloop2.isPropType A C (compGroupHom f g) G (Deloop2.2-deloop-def A C (compGroupHom f g) F y₀ G) (comp-deloop G))
    where
    open Deloop2
    comp-deloop : (G : B² A) → Deloop2.type A C (compGroupHom f g) G
    comp-deloop G =
      (2-deloop B C g F y₀ ∘ 2-deloop A B f H x₀) G ,
      (λ x → 2-deloop-def B C g F y₀ _ .snd .fst (2-deloop-def A B f H x₀ G .snd .fst x)) ,
      (congLink (B².lnk G) _ (2-deloop-def B C g F y₀ _ .snd .fst ∘ 2-deloop-def A B f H x₀ G .snd .fst)
        ≡⟨ congLink-comp _ (B².lnk H') _ (2-deloop-def A B f H x₀ G .snd .fst) (2-deloop-def B C g F y₀ _ .snd .fst) ⟩
      compGroupHom (congLink _ (B².lnk H') (2-deloop-def A B f H x₀ G .snd .fst)) (congLink (B².lnk H') (B².lnk F') (2-deloop-def B C g F y₀ _ .snd .fst))
        ≡⟨ (λ i → compGroupHom (2-deloop-def A B f H x₀ G .snd .snd i) (2-deloop-def B C g F y₀ H' .snd .snd i)) ⟩
      compGroupHom f g ∎) where
      H' = 2-deloop A B f H x₀ G
      F' = 2-deloop B C g F y₀ H'

module ΩB² (A : AbGroup {ℓ}) (G : B² A {ℓ'}) where
  module A = AbGroup A
  module G = B² G
  X = G.Carrier

  equiv1 : (f : X → X) → (congLink G.lnk G.lnk f ≡ grouphom (λ g → g) (λ _ _ → refl)) ≃ ∥ f ≡ (λ x → x) ∥
  equiv1 f = isoToEquiv (iso fun→ fun← (λ _ → propTruncIsProp _ _) λ _ → isSetGroupHom _ _ _ _) where
    fun← : ∥ f ≡ (λ x → x) ∥ → (congLink G.lnk G.lnk f ≡ grouphom (λ g → g) (λ _ _ → refl))
    fun← = recPropTrunc (isSetGroupHom _ _) λ p → cong (congLink G.lnk G.lnk) p ∙ recPropTrunc (isSetGroupHom _ _)
      (λ x₀ → congLink-carac _ _ _ x₀ ∙ groupHomEq (funExt λ g → retEq (G.eq x₀) g)) G.inhabited

    fun→ : (congLink G.lnk G.lnk f ≡ grouphom (λ g → g) (λ _ _ → refl)) → ∥ f ≡ (λ x → x) ∥
    fun→ p = recPropTrunc propTruncIsProp (λ x₀ → recPropTrunc propTruncIsProp (∣_∣ ∘ lemma x₀) (G.conn x₀ (f x₀))) G.inhabited where
      lemma : (x₀ : X) → (x₀ ≡ f x₀) → f ≡ (λ x → x)
      lemma x₀ p₀ = cong fst (deloopUnique G.lnk G.lnk (grouphom (λ x → x) (λ _ _ → refl)) x₀ x₀ f-deloop id-deloop) where
        deloopingType = deloopType G.lnk G.lnk (grouphom (λ x → x) (λ _ _ → refl)) x₀ x₀
        f-deloop : deloopingType
        f-deloop = f , p₀ , p

        id-deloop : deloopingType
        id-deloop = ((λ x → x) , refl , congLink-carac _ _ _ x₀ ∙ groupHomEq (funExt λ g → retEq (G.eq x₀) g))

  ZG : Type ℓ'
  ZG = Σ[ f ∈ X ≃ X ] ∥ f ≡ idEquiv X ∥

  equiv2 : (Σ[ f ∈ (X → X) ] ∥ f ≡ (λ x → x) ∥) ≃ ZG
  equiv2 = isoToEquiv (iso fun→ fun← sec retr) where
    fun→ : Σ[ f ∈ (X → X) ] ∥ f ≡ (λ x → x) ∥ → ZG
    fun→ (f , p) = (f , recPropTrunc (isPropIsEquiv _) (λ p → subst isEquiv (sym p) (idIsEquiv X)) p) ,
      recPropTrunc propTruncIsProp (λ p → ∣ equivEq _ _ p ∣) p

    fun← : ZG → Σ[ f ∈ (X → X) ] ∥ f ≡ (λ x → x) ∥
    fun← ((f , eq) , p) = f , recPropTrunc propTruncIsProp (λ p → ∣ cong fst p ∣) p

    sec : section fun→ fun←
    sec ((f , eq) , p) = Σ≡Prop (λ _ → propTruncIsProp) (equivEq _ _ refl)
    retr : retract fun→ fun←
    retr (f , p) = Σ≡Prop (λ _ → propTruncIsProp) refl

  ΩB²≃ZG : (G ≡ G) ≃ ZG
  ΩB²≃ZG =
    G ≡ G ≃⟨ invEquiv (B²Path A G G) ⟩
    B²Equiv A G G ≃⟨ isoToEquiv (iso (λ (b²equiv f h) → f , h) (λ (f , h) → b²equiv f h) (λ _ → refl) (λ _ → refl)) ⟩
    Σ[ f ∈ (X → X) ] (congLink G.lnk G.lnk f ≡ grouphom (λ x → x) (λ _ _ → refl)) ≃⟨ Σ-cong-equiv-snd equiv1 ⟩
    Σ[ f ∈ (X → X) ] ∥ f ≡ (λ x → x) ∥ ≃⟨ equiv2 ⟩
    ZG ■

  {-pntZG : ZG
  pntZG = idEquiv X , ∣ refl ∣
  lemma : (pntZG ≡ pntZG) ≃ ((x : X) → x ≡ x)
  lemma =
    pntZG ≡ pntZG
      ≃⟨ isoToEquiv (iso (λ p → cong fst p) (λ p → ΣPathP (p , toPathP (propTruncIsProp _ _)))
        (λ p → refl) λ p → cong ΣPathP (ΣPathP (refl , isOfHLevelPathP 1 propTruncIsProp _ _ _ _))) ⟩
    idEquiv X ≡ idEquiv X
      ≃⟨ isoToEquiv (iso (λ p → cong fst p) (λ p → ΣPathP (p , toPathP (isPropIsEquiv _ _ _)))
        (λ p → refl) λ p → cong ΣPathP (ΣPathP (refl , isOfHLevelPathP 1 (isPropIsEquiv _) _ _ _ _))) ⟩
    (λ x → x) ≡ (λ x → x)
      ≃⟨ invEquiv funExtEquiv ⟩
    ((x : X) → x ≡ x) ■

  test : ((x : X) → x ≡ x) ≃ 

  ZG-gerbe : Gerbe
  ZG-gerbe = gerbe ZG (isgerbe ∣ idEquiv X , ∣ refl ∣ ∣ {!!} {!!} {!!}) where
    pnt : ZG
    pnt = idEquiv X , ∣ refl ∣

  ZG-link : Link ZG-gerbe A
  ZG-link = makeLink-pnt (groupequiv {!!} {!!})-}
