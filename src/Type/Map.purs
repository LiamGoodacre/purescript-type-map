module Type.Map where

import Type.Proxy
import Data.Symbol (SProxy(..))



-- booleans

data Yes
data No


-- optional values

data None
data Some value


-- type ordering

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


-- comparing symbols
-- some predefined instances for testing
-- these should eventually be solved by the compiler (hopefully)

class SymbolCompare (left :: Symbol) (right :: Symbol) ordering | left right -> ordering
instance symbolCompareAA :: SymbolCompare "A" "A" TypeEQ
instance symbolCompareBB :: SymbolCompare "B" "B" TypeEQ
instance symbolCompareCC :: SymbolCompare "C" "C" TypeEQ
instance symbolCompareAB :: SymbolCompare "A" "B" TypeLT
instance symbolCompareBA :: SymbolCompare "B" "A" TypeGT
instance symbolCompareAC :: SymbolCompare "A" "C" TypeLT
instance symbolCompareCA :: SymbolCompare "C" "A" TypeGT
instance symbolCompareBC :: SymbolCompare "B" "C" TypeLT
instance symbolCompareCB :: SymbolCompare "C" "B" TypeGT


-- natural numbers

data Zero
data Succ nat

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

class ListConsWhenNot cond head tail result | cond -> head tail result
instance listConsWhenNotYes
  :: ListConsWhenNot Yes head tail tail
instance listConsWhenNotNo
  :: ListConsWhenNot No head tail (Cons head tail)

class ListRejectNatEq list nat result | list -> nat result
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


class AllHeights_ map list | map -> list
instance allHeightsLeaf
  :: AllHeights_ MapLeaf (Cons Zero Nil)
instance allHeightsTwo
  :: (AllHeights_ l hl,
      AllHeights_ r hr,
      ListAppend hl hr hlr,
      ListMap Succ hlr shlr)
  => AllHeights_ (MapTwo l k v r) shlr
instance allHeightsThree
  :: (AllHeights_ l hl,
      AllHeights_ m hm,
      AllHeights_ r hr,
      ListAppend hm hr hmr,
      ListAppend hl hmr hlmr,
      ListMap Succ hlmr shlmr)
  => AllHeights_ (MapThree l lk lv m rk rv r) shlmr


class IsMapValid map result | map -> result
instance isMapValidLeaf
  :: (IsMap map,
      AllHeights_ map hs,
      NatListNub hs uniqueHeights,
      ListLength uniqueHeights length,
      NatEq length (Succ Zero) isOne)
  => IsMapValid map isOne


class MapLookupTwoOrdered_ ord (key :: Symbol) l (k :: Symbol) v r result | ord -> key l k v r result
instance mapLookupTwoOrderedEQ
  :: MapLookupTwoOrdered_ TypeEQ key l k v r (Some v)
instance mapLookupTwoOrderedLT
  :: MapLookup key l result
  => MapLookupTwoOrdered_ TypeLT key l k v r result
instance mapLookupTwoOrderedGT
  :: MapLookup key r result
  => MapLookupTwoOrdered_ TypeGT key l k v r result

class MapLookupThreeOrderedSnd_ fst snd (key :: Symbol) l (lk :: Symbol) lv m (rk :: Symbol) rv r result | fst snd -> key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndEQ
  :: MapLookupThreeOrderedSnd_ fst TypeEQ key l lk lv m rk rv r (Some rv)
instance mapLookupThreeOrderedSndLT
  :: MapLookup key l result
  => MapLookupThreeOrderedSnd_ TypeLT snd key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndGT
  :: MapLookup key r result
  => MapLookupThreeOrderedSnd_ fst TypeGT key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndMid
  :: MapLookup key m result
  => MapLookupThreeOrderedSnd_ TypeGT TypeLT key l lk lv m rk rv r result

class MapLookupThreeOrderedFst_ ord (key :: Symbol) l (lk :: Symbol) lv m (rk :: Symbol) rv r result | ord -> key l lk lv m rk rv r result
instance mapLookupThreeOrderedFstEQ
  :: MapLookupThreeOrderedFst_ TypeEQ key l lk lv m rk rv r (Some lv)
instance mapLookupThreeOrderedFstLT
  :: (SymbolCompare key rk ord,
      MapLookupThreeOrderedSnd_ TypeLT ord key l lk lv m rk rv r result)
  => MapLookupThreeOrderedFst_ TypeLT key l lk lv m rk rv r result
instance mapLookupThreeOrderedFstGT
  :: (SymbolCompare key rk ord,
      MapLookupThreeOrderedSnd_ TypeGT ord key l lk lv m rk rv r result)
  => MapLookupThreeOrderedFst_ TypeGT key l lk lv m rk rv r result

class MapLookup (key :: Symbol) map value | map -> key value
instance mapLookupLeaf
  :: MapLookup key MapLeaf None
instance mapLookupTwo
  :: (SymbolCompare key k ord,
      MapLookupTwoOrdered_ ord key l k v r result)
  => MapLookup key (MapTwo l k v r) result
instance mapLookupThree
  :: (SymbolCompare key lk ord,
      MapLookupThreeOrderedFst_ ord key l lk lv m rk rv r result)
  => MapLookup key (MapThree l lk lv m rk rv r) result


data CtxTwoLeft (k :: Symbol) v r
data CtxTwoRight l (k :: Symbol) v
data CtxThreeLeft (lk :: Symbol) lv m (rk :: Symbol) rv r
data CtxThreeMiddle l (lk :: Symbol) lv (rk :: Symbol) rv r
data CtxThreeRight l (lk :: Symbol) lv m (rk :: Symbol) rv


class FromZipperCons_ head ctx map result | head -> result
instance fromZipperConsTwoLeft
  :: FromZipper_ ctx (MapTwo map k1 v1 r) result
  => FromZipperCons_ (CtxTwoLeft k1 v1 r) ctx map result
instance fromZipperConsTwoRight
  :: FromZipper_ ctx (MapTwo l k1 v1 map) result
  => FromZipperCons_ (CtxTwoRight l k1 v1) ctx map result
instance fromZipperConsThreeLeft
  :: FromZipper_ ctx (MapThree map k1 v1 m k2 v2 r) result
  => FromZipperCons_ (CtxThreeLeft k1 v1 m k2 v2 r) ctx map result
instance fromZipperConsThreeMiddle
  :: FromZipper_ ctx (MapThree l k1 v1 map k2 v2 r) result
  => FromZipperCons_ (CtxThreeMiddle l k1 v1 k2 v2 r) ctx map result
instance fromZipperConsThreeRight
  :: FromZipper_ ctx (MapThree l k1 v1 m k2 v2 map) result
  => FromZipperCons_ (CtxThreeRight l k1 v1 m k2 v2) ctx map result

class FromZipper_ ctx map result | ctx map -> result
instance fromZipperNil
  :: FromZipper_ Nil map map
instance fromZipperCons
  :: FromZipperCons_ x ctx map result
  => FromZipper_ (Cons x ctx) map result


class MapInsertUpCons_ frame kickUp ctx map | frame -> kickUp ctx map
instance mapInsertUpConsTwoLeft
  :: FromZipper_ ctx (MapThree l k v m k1 v1 r) map
  => MapInsertUpCons_ (CtxTwoLeft k1 v1 r) (MapTwo l k v m) ctx map
instance mapInsertUpConsTwoRight
  :: FromZipper_ ctx (MapThree l k1 v1 m k v r) map
  => MapInsertUpCons_ (CtxTwoRight l k1 v1) (MapTwo m k v r) ctx map
instance mapInsertUpConsThreeLeft
  :: MapInsertUp_ ctx (MapTwo (MapTwo a k v b) k1 v1 (MapTwo c k2 v2 d)) map
  => MapInsertUpCons_ (CtxThreeLeft k1 v1 c k2 v2 d) (MapTwo a k v b) ctx map
instance mapInsertUpConsThreeMiddle
  :: MapInsertUp_ ctx (MapTwo (MapTwo a k1 v1 b) k v (MapTwo c k2 v2 d)) map
  => MapInsertUpCons_ (CtxThreeMiddle a k1 v1 k2 v2 d) (MapTwo b k v c) ctx map
instance mapInsertUpConsThreeRight
  :: MapInsertUp_ ctx (MapTwo (MapTwo a k1 v1 b) k2 v2 (MapTwo c k v d)) map
  => MapInsertUpCons_ (CtxThreeRight a k1 v1 b k2 v2) (MapTwo c k v d) ctx map

class MapInsertUp_ ctx kickUp map | ctx kickUp -> map
instance mapInsertUpNil
  :: MapInsertUp_ Nil m m
instance mapInsertUpCons
  :: MapInsertUpCons_ x kup ctx result
  => MapInsertUp_ (Cons x ctx) kup result


class MapInsertDownTwo_ ord ctx (k :: Symbol) v l (k1 :: Symbol) v1 r result | ord -> ctx k v l k1 v1 r result
instance mapInsertDownTwoEQ
  :: FromZipper_ ctx (MapTwo l k v r) result
  => MapInsertDownTwo_ TypeEQ ctx k v l k1 v1 r result
instance mapInserteDownTwoLT
  :: MapInsertDown_ (Cons (CtxTwoLeft k1 v1 r) ctx) k v l result
  => MapInsertDownTwo_ TypeLT ctx k v l k1 v1 r result
instance mapInserteDownTwoGT
  :: MapInsertDown_ (Cons (CtxTwoRight l k1 v1) ctx) k v r result
  => MapInsertDownTwo_ TypeGT ctx k v l k1 v1 r result

class MapInsertDownThreeSnd_ fst snd ctx (k :: Symbol) v l (k1 :: Symbol) v1 m (k2 :: Symbol) v2 r result | fst snd -> ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndEQ
  :: FromZipper_ ctx (MapThree l k1 v1 m k v r) result
  => MapInsertDownThreeSnd_ fst TypeEQ ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndLT
  :: MapInsertDown_ (Cons (CtxThreeLeft k1 v1 m k2 v2 r) ctx) k v l result
  => MapInsertDownThreeSnd_ TypeLT snd ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndMid
  :: MapInsertDown_ (Cons (CtxThreeMiddle l k1 v1 k2 v2 r) ctx) k v l result
  => MapInsertDownThreeSnd_ TypeGT TypeLT ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndGT
  :: MapInsertDown_ (Cons (CtxThreeRight l k1 v1 m k2 v2) ctx) k v l result
  => MapInsertDownThreeSnd_ fst TypeGT ctx k v l k1 v1 m k2 v2 r result


class MapInsertDownThreeFst_ ord ctx (k :: Symbol) v l (k1 :: Symbol) v1 m (k2 :: Symbol) v2 r result | ord -> ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeFstEQ
  :: FromZipper_ ctx (MapThree l k v m k2 v2 r) result
  => MapInsertDownThreeFst_ TypeEQ ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeFstLT
  :: (SymbolCompare k k2 ord,
      MapInsertDownThreeSnd_ TypeLT ord ctx k v l k1 v1 m k2 v2 r result)
  => MapInsertDownThreeFst_ TypeLT ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeFstGT
  :: (SymbolCompare k k2 ord,
      MapInsertDownThreeSnd_ TypeGT ord ctx k v l k1 v1 m k2 v2 r result)
  => MapInsertDownThreeFst_ TypeGT ctx k v l k1 v1 m k2 v2 r result

class MapInsertDown_ ctx (k :: Symbol) v map result | map -> ctx k v map result
instance mapInsertDownLeaf
  :: MapInsertUp_ ctx (MapTwo MapLeaf k v MapLeaf) result
  => MapInsertDown_ ctx k v MapLeaf result
instance mapInsertDownTwo
  :: (SymbolCompare k k1 ord,
      MapInsertDownTwo_ ord ctx k v l k1 v1 r result)
  => MapInsertDown_ ctx k v (MapTwo l k1 v1 r) result
instance mapInsertDownThree
  :: (SymbolCompare k k1 ord,
      MapInsertDownThreeFst_ ord ctx k v l k1 v1 m k2 v2 r result)
  => MapInsertDown_ ctx k v (MapThree l k1 v1 m k2 v2 r) result


class MapInsert (key :: Symbol) value map result | map -> key value result
instance mapInsertDef
  :: MapInsertDown_ Nil key value map result
  => MapInsert key value map result

data Field (k :: Symbol) v

class MapInsertField field map result | field -> map result
instance mapInsertField
  :: MapInsert key value map result
  => MapInsertField (Field key value) map result

class MapFromList list map | list -> map
instance mapFromListNil
  :: MapFromList Nil MapLeaf
instance mapFromListCons
  :: (MapFromList tail map,
      MapInsertField field map result)
  => MapFromList (Cons field tail) result



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
lookupEmpty = checkLookup (Proxy :: Proxy EmptyMap) _A

lookupSingletonNotPresent :: Proxy None
lookupSingletonNotPresent = checkLookup (Proxy :: Proxy (SingletonMap "A" A)) _B

lookupSingletonPresent :: Proxy (Some A)
lookupSingletonPresent = checkLookup (Proxy :: Proxy (SingletonMap "A" A)) _A


lookupMultipleA :: Proxy (Some A)
lookupMultipleA =
  checkLookup (Proxy :: Proxy (MapThree MapLeaf "A" A MapLeaf "B" B MapLeaf)) _A

lookupMultipleB :: Proxy (Some B)
lookupMultipleB =
  checkLookup (Proxy :: Proxy (MapThree MapLeaf "B" B MapLeaf "A" A MapLeaf)) _B


checkValidInsert :: forall before after key value.
  (IsMapValid before Yes,
   MapInsert key value before after,
   IsMapValid after Yes) =>
  Proxy before -> SProxy key -> Proxy value -> Proxy after
checkValidInsert _ _ _ = Proxy

validInsert :: Proxy (SingletonMap "A" A)
validInsert = checkValidInsert (Proxy :: Proxy EmptyMap)
                               (SProxy :: SProxy "A")
                               (Proxy :: Proxy A)


checkFromList :: forall list after.
  (MapFromList list after, IsMapValid after Yes) =>
  Proxy list -> Proxy after
checkFromList _ = Proxy

fromList0 :: Proxy _
fromList0 = checkFromList (Proxy :: Proxy (Cons (Field "B" B)
                                          (Cons (Field "A" A)
                                          (Cons (Field "C" C)
                                           Nil))))

