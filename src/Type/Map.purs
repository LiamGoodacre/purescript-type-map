module Type.Map where

import Type.Proxy
import Data.Symbol (SProxy(..))



-- booleans

data Yes
data No


-- natural numbers

data Zero
data Succ nat

class IsNat ctor
instance isNatZero
  :: IsNat Zero
instance isNatSucc
  :: IsNat nat
  => IsNat (Succ nat)

class NatEq left right result | left right -> result
instance natEqZZ
  :: NatEq Zero Zero Yes
instance natEqZS
  :: NatEq Zero (Succ nat) No
instance natEqSZ
  :: NatEq (Succ nat) Zero No
instance natEqSS
  :: NatEq left right result
  => NatEq (Succ left) (Succ right) result


-- lists

data Nil
data Cons head tail

class IsList ctor
instance isListNil
  :: IsList Nil
instance isListCons
  :: IsList tail
  => IsList (Cons head tail)

class ListAppend left right out | left -> right out
instance listAppendNil
  :: ListAppend Nil r r
instance listAppendCons
  :: ListAppend tail r o
  => ListAppend (Cons head tail) r (Cons head o)

class ListMap (f :: * -> *) list out | list -> f out
instance listMapNil
  :: ListMap f Nil Nil
instance listMapCons
  :: ListMap f tail mapFTail
  => ListMap f (Cons head tail) (Cons (f head) mapFTail)

class ListLength list length | list -> length
instance listLengthNil
  :: ListLength Nil Zero
instance listLengthCons
  :: ListLength tail length
  => ListLength (Cons head tail) (Succ length)

class ListConsWhenNot cond head tail result | cond head tail -> result
instance listConsWhenNotYes
  :: ListConsWhenNot Yes head tail tail
instance listConsWhenNotNo
  :: ListConsWhenNot No head tail (Cons head tail)

class ListRejectNatEq list nat result | list nat -> result
instance listRejectNatEqNil
  :: ListRejectNatEq Nil nat Nil
instance listRejectNatEqCons
  :: (NatEq head nat isEq,
      ListRejectNatEq tail nat list,
      ListConsWhenNot isEq head list result)
  => ListRejectNatEq (Cons head tail) nat result

class NatListNub list result | list -> result
instance natListNubNil
  :: NatListNub Nil Nil
instance natListNubCons
  :: (ListRejectNatEq tail nat filtered,
      NatListNub filtered list)
  => NatListNub (Cons nat tail) (Cons nat list)


-- implementation
-- currently only supporting symbol keys and type values

data MapLeaf
data MapTwo l (k :: Symbol) v r
data MapThree l (lk :: Symbol) lv m (rk :: Symbol) rv r

class IsMap ctor
instance isMapLeaf
  :: IsMap MapLeaf
instance isMapTwo
  :: IsMap (MapTwo l k v r)
instance isMapThree
  :: IsMap (MapThree l lk lv m rk rv r)

type EmptyMap = MapLeaf

type SingletonMap (k :: Symbol) v = MapTwo EmptyMap k v EmptyMap


class IsMapEmpty map result | map -> result
instance isMapEmptyLeaf
  :: IsMapEmpty MapLeaf Yes
instance isMapEmptyTwo
  :: IsMapEmpty (MapTwo l k v r) No
instance isMapEmptyThree
  :: IsMapEmpty (MapThree l lk lv m rk rv r) No


class AllHeights map list | map -> list
instance allHeightsLeaf
  :: AllHeights MapLeaf (Cons Zero Nil)
instance allHeightsTwo
  :: (AllHeights l hl,
      AllHeights r hr,
      ListAppend hl hr hlr,
      ListMap Succ hlr shlr)
  => AllHeights (MapTwo l k v r) shlr
instance allHeightsThree
  :: (AllHeights l hl,
      AllHeights m hm,
      AllHeights r hr,
      ListAppend hm hr hmr,
      ListAppend hl hmr hlmr,
      ListMap Succ hlmr shlmr)
  => AllHeights (MapThree l lk lv m rk rv r) shlmr


class IsMapValid map result | map -> result
instance isMapValidLeaf
  :: (AllHeights map hs,
      NatListNub hs uniqueHeights,
      ListLength uniqueHeights length,
      NatEq length (Succ Zero) isOne)
  => IsMapValid map isOne


data TypeEQ
data TypeLT
data TypeGT

class IsTypeOrdering ctor
instance isTypeOrderingEQ
  :: IsTypeOrdering TypeEQ
instance isTypeOrderingLT
  :: IsTypeOrdering TypeLT
instance isTypeOrderingGT
  :: IsTypeOrdering TypeGT


class SymbolCompare (left :: Symbol) (right :: Symbol) ordering | left right -> ordering
-- some predefined instances for testing
-- these should eventually be solved by the compiler (hopefully)
instance symbolCompareAA :: SymbolCompare "A" "A" TypeEQ
instance symbolCompareBB :: SymbolCompare "B" "B" TypeEQ
instance symbolCompareCC :: SymbolCompare "C" "C" TypeEQ
instance symbolCompareAB :: SymbolCompare "A" "B" TypeLT
instance symbolCompareBA :: SymbolCompare "B" "A" TypeGT
instance symbolCompareAC :: SymbolCompare "A" "C" TypeLT
instance symbolCompareCA :: SymbolCompare "C" "A" TypeGT
instance symbolCompareBC :: SymbolCompare "B" "C" TypeLT
instance symbolCompareCB :: SymbolCompare "C" "B" TypeGT


data None
data Some value

class IsOption ctor
instance isOptionNone
  :: IsOption None
instance isOptionSome
  :: IsOption (Some value)


class MapLookupTwoOrdered ord (key :: Symbol) l (k :: Symbol) v r result | ord -> result
instance mapLookupTwoOrderedEQ
  :: MapLookupTwoOrdered TypeEQ key l k v r (Some v)
instance mapLookupTwoOrderedLT
  :: MapLookup key l result
  => MapLookupTwoOrdered TypeLT key l k v r result
instance mapLookupTwoOrderedGT
  :: MapLookup key r result
  => MapLookupTwoOrdered TypeGT key l k v r result

class MapLookupThreeOrderedSnd fst snd (key :: Symbol) l (lk :: Symbol) lv m (rk :: Symbol) rv r result | fst snd -> result
instance mapLookupThreeOrderedSndEQ
  :: MapLookupThreeOrderedSnd fst TypeEQ key l lk lv m rk rv r (Some rv)
instance mapLookupThreeOrderedSndLT
  :: MapLookup key l result
  => MapLookupThreeOrderedSnd TypeLT snd key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndGT
  :: MapLookup key r result
  => MapLookupThreeOrderedSnd fst TypeGT key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndMid
  :: MapLookup key m result
  => MapLookupThreeOrderedSnd TypeGT TypeLT key l lk lv m rk rv r result

class MapLookupThreeOrderedFst ord (key :: Symbol) l (lk :: Symbol) lv m (rk :: Symbol) rv r result | ord -> result
instance mapLookupThreeOrderedFstEQ
  :: MapLookupThreeOrderedFst TypeEQ key l lk lv m rk rv r (Some lv)
instance mapLookupThreeOrderedFstLT
  :: (SymbolCompare key rk ord,
      MapLookupThreeOrderedSnd TypeLT ord key l lk lv m rk rv r result)
  => MapLookupThreeOrderedFst TypeLT key l lk lv m rk rv r result
instance mapLookupThreeOrderedFstGT
  :: (SymbolCompare key rk ord,
      MapLookupThreeOrderedSnd TypeGT ord key l lk lv m rk rv r result)
  => MapLookupThreeOrderedFst TypeGT key l lk lv m rk rv r result

class MapLookup (key :: Symbol) map value | map -> key value
instance mapLookupLeaf
  :: MapLookup key MapLeaf None
instance mapLookupTwo
  :: (SymbolCompare key k ord,
      MapLookupTwoOrdered ord key l k v r result)
  => MapLookup key (MapTwo l k v r) result
instance mapLookupThree
  :: (SymbolCompare key lk ord,
      MapLookupThreeOrderedFst ord key l lk lv m rk rv r result)
  => MapLookup key (MapThree l lk lv m rk rv r) result


class MapInsert (key :: Symbol) value map result | map -> key value result
instance mapInsertLeaf
  :: MapInsert key value MapLeaf (MapTwo MapLeaf key value MapLeaf)
--TODO



-- play area

_A :: SProxy "A"
_A = SProxy

_B :: SProxy "B"
_B = SProxy

_C :: SProxy "C"
_C = SProxy

data A
data B
data C

checkValidMap :: forall map result. IsMapValid map result => Proxy map -> Proxy result
checkValidMap Proxy = Proxy

validEmptyMap :: Proxy Yes
validEmptyMap = checkValidMap (Proxy :: Proxy EmptyMap)

validSingletonMap :: Proxy Yes
validSingletonMap = checkValidMap (Proxy :: Proxy (SingletonMap "A" A))

validTwoMap :: Proxy Yes
validTwoMap = checkValidMap (Proxy :: Proxy (MapTwo MapLeaf "A" A MapLeaf))

validThreeMap :: Proxy Yes
validThreeMap = checkValidMap (Proxy :: Proxy (MapThree MapLeaf "A" A MapLeaf "B" B MapLeaf))


checkLookup :: forall map key value.
  (IsMapValid map Yes,
   MapLookup key map value) =>
  Proxy map -> SProxy key -> Proxy value
checkLookup _ _ = Proxy


lookupEmpty :: Proxy None
lookupEmpty = checkLookup (Proxy :: Proxy EmptyMap)
                          (SProxy :: SProxy "A")

lookupSingletonNotPresent :: Proxy None
lookupSingletonNotPresent = checkLookup (Proxy :: Proxy (SingletonMap "A" A))
                                        (SProxy :: SProxy "B")

lookupSingletonPresent :: Proxy (Some A)
lookupSingletonPresent = checkLookup (Proxy :: Proxy (SingletonMap "A" A))
                                     (SProxy :: SProxy "A")


lookupMultipleA :: Proxy (Some A)
lookupMultipleA =
  checkLookup (Proxy :: Proxy (MapThree MapLeaf "A" A MapLeaf "B" B MapLeaf))
              (SProxy :: SProxy "A")

lookupMultipleB :: Proxy (Some B)
lookupMultipleB =
  checkLookup (Proxy :: Proxy (MapThree MapLeaf "B" B MapLeaf "A" A MapLeaf))
              (SProxy :: SProxy "B")


checkValidInsert :: forall before after key value result.
  (IsMapValid before Yes,
   MapInsert key value before after,
   IsMapValid after result) =>
  Proxy before -> SProxy key -> Proxy value -> Proxy result
checkValidInsert _ _ _ = Proxy

validInsert :: Proxy Yes
validInsert = checkValidInsert (Proxy :: Proxy EmptyMap)
                               (SProxy :: SProxy "A")
                               (Proxy :: Proxy A)


