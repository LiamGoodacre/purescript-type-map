module Type.Map where

import Type.Proxy
import Data.Symbol (SProxy(..))
import Type.Data.Symbol (class CompareSymbol)
import Type.Data.Ordering (kind Ordering, LT, EQ, GT)


-- booleans

foreign import kind Bool
foreign import data True :: Bool
foreign import data False :: Bool
data BProxy (bool :: Bool) = BProxy


-- optional values

data Nothing
data Just value


-- natural numbers

{-
-- Would be this, but can't make Nil and Cons poly-kinded
foreign import kind Nat
foreign import data Zero :: Nat
foreign import data Succ :: Nat -> Nat
-}

foreign import data Zero :: *
foreign import data Succ :: * -> *

class NatEq (left :: *)
            (right :: *)
            (result :: Bool)
            | left right -> result
instance natEqZZ
  :: NatEq Zero Zero True
instance natEqZS
  :: NatEq Zero (Succ nat) False
instance natEqSZ
  :: NatEq (Succ nat) Zero False
instance natEqSS
  :: NatEq left right result
  => NatEq (Succ left) (Succ right) result


-- lists

data Nil
data Cons head tail

class ListAppend (left :: *)
                 (right :: *)
                 (out :: *)
                 | left -> right out
instance listAppendNil
  :: ListAppend Nil r r
instance listAppendCons
  :: ListAppend tail r o
  => ListAppend (Cons head tail) r (Cons head o)

class ListMap (f :: * -> *)
              (list :: *)
              (out :: *)
              | list -> f out
instance listMapNil
  :: ListMap f Nil Nil
instance listMapCons
  :: ListMap f tail mapFTail
  => ListMap f (Cons head tail) (Cons (f head) mapFTail)

class ListLength (list :: *)
                 (length :: *)
                 | list -> length
instance listLengthNil
  :: ListLength Nil Zero
instance listLengthCons
  :: ListLength tail length
  => ListLength (Cons head tail) (Succ length)

class ListConsWhenNot (cond :: Bool)
                      (head :: *)
                      (tail :: *)
                      (result :: *)
                      | cond -> head tail result
instance listConsWhenNotYes
  :: ListConsWhenNot True head tail tail
instance listConsWhenNotNo
  :: ListConsWhenNot False head tail (Cons head tail)

class ListRejectNatEq (list :: *)
                      (nat :: *)
                      (result :: *)
                      | list -> nat result
instance listRejectNatEqNil
  :: ListRejectNatEq Nil nat Nil
instance listRejectNatEqCons
  :: (NatEq head nat isEq,
      ListRejectNatEq tail nat list,
      ListConsWhenNot isEq head list result)
  => ListRejectNatEq (Cons head tail) nat result

class NatListNub (list :: *)
                 (result :: *)
                 | list -> result
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

class IsMap (ctor :: *)
instance isMapLeaf
  :: IsMap MapLeaf
instance isMapTwo
  :: IsMap (MapTwo l k v r)
instance isMapThree
  :: IsMap (MapThree l lk lv m rk rv r)


type EmptyMap = MapLeaf

type SingletonMap (k :: Symbol) v = MapTwo EmptyMap k v EmptyMap


class IsMapEmpty (map :: *)
                 (result :: Bool)
                 | map -> result
instance isMapEmptyLeaf
  :: IsMapEmpty MapLeaf True
instance isMapEmptyTwo
  :: IsMapEmpty (MapTwo l k v r) False
instance isMapEmptyThree
  :: IsMapEmpty (MapThree l lk lv m rk rv r) False


class AllHeights_ (map :: *)
                  (list :: *)
                  | map -> list
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


class IsMapValid (map :: *)
                 (result :: Bool)
                 | map -> result
instance isMapValidLeaf
  :: (IsMap map,
      AllHeights_ map hs,
      NatListNub hs uniqueHeights,
      ListLength uniqueHeights length,
      NatEq length (Succ Zero) isOne)
  => IsMapValid map isOne


class MapLookupTwoOrdered_ (ord :: Ordering)
                           (key :: Symbol)
                           (l :: *)
                           (k :: Symbol)
                           (v :: *)
                           (r :: *)
                           (result :: *)
                           | ord -> key l k v r result
instance mapLookupTwoOrderedEQ
  :: MapLookupTwoOrdered_ EQ key l k v r (Just v)
instance mapLookupTwoOrderedLT
  :: MapLookup key l result
  => MapLookupTwoOrdered_ LT key l k v r result
instance mapLookupTwoOrderedGT
  :: MapLookup key r result
  => MapLookupTwoOrdered_ GT key l k v r result

class MapLookupThreeOrderedSnd_ (fst :: Ordering)
                                (snd :: Ordering)
                                (key :: Symbol)
                                (l :: *)
                                (lk :: Symbol)
                                (lv :: *)
                                (m :: *)
                                (rk :: Symbol)
                                (rv :: *)
                                (r :: *)
                                (result :: *)
                                | fst snd -> key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndEQ
  :: MapLookupThreeOrderedSnd_ fst EQ key l lk lv m rk rv r (Just rv)
instance mapLookupThreeOrderedSndLT
  :: MapLookup key l result
  => MapLookupThreeOrderedSnd_ LT snd key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndGT
  :: MapLookup key r result
  => MapLookupThreeOrderedSnd_ fst GT key l lk lv m rk rv r result
instance mapLookupThreeOrderedSndMid
  :: MapLookup key m result
  => MapLookupThreeOrderedSnd_ GT LT key l lk lv m rk rv r result

class MapLookupThreeOrderedFst_ (ord :: Ordering)
                                (key :: Symbol)
                                (l :: *)
                                (lk :: Symbol)
                                (lv :: *)
                                (m :: *)
                                (rk :: Symbol)
                                (rv :: *)
                                (r :: *)
                                (result :: *)
                                | ord -> key l lk lv m rk rv r result
instance mapLookupThreeOrderedFstEQ
  :: MapLookupThreeOrderedFst_ EQ key l lk lv m rk rv r (Just lv)
instance mapLookupThreeOrderedFstLT
  :: (CompareSymbol key rk ord,
      MapLookupThreeOrderedSnd_ LT ord key l lk lv m rk rv r result)
  => MapLookupThreeOrderedFst_ LT key l lk lv m rk rv r result
instance mapLookupThreeOrderedFstGT
  :: (CompareSymbol key rk ord,
      MapLookupThreeOrderedSnd_ GT ord key l lk lv m rk rv r result)
  => MapLookupThreeOrderedFst_ GT key l lk lv m rk rv r result

class MapLookup (key :: Symbol)
                map
                value
                | map -> key value
instance mapLookupLeaf
  :: MapLookup key MapLeaf Nothing
instance mapLookupTwo
  :: (CompareSymbol key k ord,
      MapLookupTwoOrdered_ ord key l k v r result)
  => MapLookup key (MapTwo l k v r) result
instance mapLookupThree
  :: (CompareSymbol key lk ord,
      MapLookupThreeOrderedFst_ ord key l lk lv m rk rv r result)
  => MapLookup key (MapThree l lk lv m rk rv r) result


data CtxTwoLeft (k :: Symbol) v r
data CtxTwoRight l (k :: Symbol) v
data CtxThreeLeft (lk :: Symbol) lv m (rk :: Symbol) rv r
data CtxThreeMiddle l (lk :: Symbol) lv (rk :: Symbol) rv r
data CtxThreeRight l (lk :: Symbol) lv m (rk :: Symbol) rv


class FromZipperCons_ (head :: *)
                      (ctx :: *)
                      (map :: *)
                      (result :: *)
                      | head -> ctx map result
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

class FromZipper_ (ctx :: *)
                  (map :: *)
                  (result :: *)
                  | ctx map -> result
instance fromZipperNil
  :: FromZipper_ Nil map map
instance fromZipperCons
  :: FromZipperCons_ x ctx map result
  => FromZipper_ (Cons x ctx) map result


class MapInsertUpCons_ (frame :: *)
                       (kickUp :: *)
                       (ctx :: *)
                       (map :: *)
                       | frame -> kickUp ctx map
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

class MapInsertUp_ (ctx :: *)
                   (kickUp :: *)
                   (map :: *)
                   | ctx kickUp -> map
instance mapInsertUpNil
  :: MapInsertUp_ Nil m m
instance mapInsertUpCons
  :: MapInsertUpCons_ x kup ctx result
  => MapInsertUp_ (Cons x ctx) kup result


class MapInsertDownTwo_ (ord :: Ordering)
                        (ctx :: *)
                        (k :: Symbol)
                        (v :: *)
                        (l :: *)
                        (k1 :: Symbol)
                        (v1 :: *)
                        (r :: *)
                        (result :: *)
                        | ord -> ctx k v l k1 v1 r result
instance mapInsertDownTwoEQ
  :: FromZipper_ ctx (MapTwo l k v r) result
  => MapInsertDownTwo_ EQ ctx k v l k1 v1 r result
instance mapInserteDownTwoLT
  :: MapInsertDown_ (Cons (CtxTwoLeft k1 v1 r) ctx) k v l result
  => MapInsertDownTwo_ LT ctx k v l k1 v1 r result
instance mapInserteDownTwoGT
  :: MapInsertDown_ (Cons (CtxTwoRight l k1 v1) ctx) k v r result
  => MapInsertDownTwo_ GT ctx k v l k1 v1 r result

class MapInsertDownThreeSnd_ (fst :: Ordering)
                             (snd :: Ordering)
                             (ctx :: *)
                             (k :: Symbol)
                             (v :: *)
                             (l :: *)
                             (k1 :: Symbol)
                             (v1 :: *)
                             (m :: *)
                             (k2 :: Symbol)
                             (v2 :: *)
                             (r :: *)
                             (result :: *)
                             | fst snd -> ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndEQ
  :: FromZipper_ ctx (MapThree l k1 v1 m k v r) result
  => MapInsertDownThreeSnd_ fst EQ ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndLT
  :: MapInsertDown_ (Cons (CtxThreeLeft k1 v1 m k2 v2 r) ctx) k v l result
  => MapInsertDownThreeSnd_ LT snd ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndMid
  :: MapInsertDown_ (Cons (CtxThreeMiddle l k1 v1 k2 v2 r) ctx) k v l result
  => MapInsertDownThreeSnd_ GT LT ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeSndGT
  :: MapInsertDown_ (Cons (CtxThreeRight l k1 v1 m k2 v2) ctx) k v l result
  => MapInsertDownThreeSnd_ fst GT ctx k v l k1 v1 m k2 v2 r result


class MapInsertDownThreeFst_ (ord :: Ordering)
                             (ctx :: *)
                             (k :: Symbol)
                             (v :: *)
                             (l :: *)
                             (k1 :: Symbol)
                             (v1 :: *)
                             (m :: *)
                             (k2 :: Symbol)
                             (v2 :: *)
                             (r :: *)
                             (result :: *)
                             | ord -> ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeFstEQ
  :: FromZipper_ ctx (MapThree l k v m k2 v2 r) result
  => MapInsertDownThreeFst_ EQ ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeFstLT
  :: (CompareSymbol k k2 ord,
      MapInsertDownThreeSnd_ LT ord ctx k v l k1 v1 m k2 v2 r result)
  => MapInsertDownThreeFst_ LT ctx k v l k1 v1 m k2 v2 r result
instance mapInsertDownThreeFstGT
  :: (CompareSymbol k k2 ord,
      MapInsertDownThreeSnd_ GT ord ctx k v l k1 v1 m k2 v2 r result)
  => MapInsertDownThreeFst_ GT ctx k v l k1 v1 m k2 v2 r result

class MapInsertDown_ (ctx :: *)
                     (k :: Symbol)
                     (v :: *)
                     (map :: *)
                     (result :: *)
                     | map -> ctx k v map result
instance mapInsertDownLeaf
  :: MapInsertUp_ ctx (MapTwo MapLeaf k v MapLeaf) result
  => MapInsertDown_ ctx k v MapLeaf result
instance mapInsertDownTwo
  :: (CompareSymbol k k1 ord,
      MapInsertDownTwo_ ord ctx k v l k1 v1 r result)
  => MapInsertDown_ ctx k v (MapTwo l k1 v1 r) result
instance mapInsertDownThree
  :: (CompareSymbol k k1 ord,
      MapInsertDownThreeFst_ ord ctx k v l k1 v1 m k2 v2 r result)
  => MapInsertDown_ ctx k v (MapThree l k1 v1 m k2 v2 r) result


class MapInsert (key :: Symbol)
                (value :: *)
                (map :: *)
                (result :: *)
                | map -> key value result
instance mapInsertDef
  :: MapInsertDown_ Nil key value map result
  => MapInsert key value map result

data Field (k :: Symbol) v

class MapInsertField (field :: *)
                     (map :: *)
                     (result :: *)
                     | field -> map result
instance mapInsertField
  :: MapInsert key value map result
  => MapInsertField (Field key value) map result

class MapFromList (list :: *)
                  (map :: *)
                  | list -> map
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

checkValidMap :: forall map result. IsMapValid map result => Proxy map -> BProxy result
checkValidMap Proxy = BProxy

validEmptyMap :: BProxy True
validEmptyMap = checkValidMap (Proxy :: Proxy EmptyMap)

validSingletonMap :: BProxy True
validSingletonMap = checkValidMap (Proxy :: Proxy (SingletonMap "A" A))

validTwoMap :: BProxy True
validTwoMap = checkValidMap (Proxy :: Proxy (MapTwo MapLeaf "A" A MapLeaf))

validThreeMap :: BProxy True
validThreeMap = checkValidMap (Proxy :: Proxy (MapThree MapLeaf "A" A MapLeaf "B" B MapLeaf))


checkLookup :: forall map key value.
  (IsMapValid map True,
   MapLookup key map value) =>
  Proxy map -> SProxy key -> Proxy value
checkLookup _ _ = Proxy


lookupEmpty :: Proxy Nothing
lookupEmpty = checkLookup (Proxy :: Proxy EmptyMap) _A

lookupSingletonNotPresent :: Proxy Nothing
lookupSingletonNotPresent = checkLookup (Proxy :: Proxy (SingletonMap "A" A)) _B

lookupSingletonPresent :: Proxy (Just A)
lookupSingletonPresent = checkLookup (Proxy :: Proxy (SingletonMap "A" A)) _A


lookupMultipleA :: Proxy (Just A)
lookupMultipleA =
  checkLookup (Proxy :: Proxy (MapThree MapLeaf "A" A MapLeaf "B" B MapLeaf)) _A

lookupMultipleB :: Proxy (Just B)
lookupMultipleB =
  checkLookup (Proxy :: Proxy (MapThree MapLeaf "B" B MapLeaf "A" A MapLeaf)) _B


checkValidInsert :: forall before after key value.
  (IsMapValid before True,
   MapInsert key value before after,
   IsMapValid after True) =>
  Proxy before -> SProxy key -> Proxy value -> Proxy after
checkValidInsert _ _ _ = Proxy

validInsert :: Proxy (SingletonMap "A" A)
validInsert = checkValidInsert (Proxy :: Proxy EmptyMap)
                               (SProxy :: SProxy "A")
                               (Proxy :: Proxy A)


checkFromList :: forall list after.
  (MapFromList list after, IsMapValid after True) =>
  Proxy list -> Proxy after
checkFromList _ = Proxy

fromList0 :: Proxy _
fromList0 = checkFromList (Proxy :: Proxy (Cons (Field "B" B)
                                          (Cons (Field "A" A)
                                          (Cons (Field "C" C)
                                           Nil))))

