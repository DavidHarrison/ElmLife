module Life where

import Color
import Graphics.Element as Elem
import Graphics.Element ( Element
                        , color
                        , container
                        , empty
                        , flow
                        , middle
                        )
import List             ( (::)
                        , filterMap
                        , foldl
                        , map
                        , member
                        , reverse
                        , sum
                        )
import Maybe
import Maybe            ( Maybe(..), andThen )
import Random           ( Generator
                        , Seed
                        , customGenerator
                        , generate
                        , list
                        , initialSeed
                        , int
                        )
import Signal
import Signal           ( Signal
                        , (<~)
                        , (~)
                        , foldp
                        , sampleOn
                        )
import Text             ( plainText )
import Time             ( every
                        , inMilliseconds
                        , timestamp
                        )
import Window

type alias Zip a = { lefts  : List a
                   , center : a
                   , rights : List a
                   }

mkZip : List a -> a -> List a -> Zip a
mkZip ls c rs = { lefts  = ls
                , center = c
                , rights = rs
                }

type Zip2 a = Zip2 (Zip (Zip a))

unZip2 : Zip2 a -> Zip (Zip a)
unZip2 (Zip2 z) = z

zipToList : Zip a -> List a
zipToList z = reverse z.lefts ++ z.center :: z.rights

listToZip : List a -> Maybe (Zip a)
listToZip l = case l of
    []      -> Nothing
    (x::xs) -> Just <| mkZip [] x xs

{-
 - the following are functions that would otherwise go into type classes
 - currently Elm does not support type classes, nor does it support Rank2Types
 - making it difficult to reify typeclasses to dictionaries if the type question
 - is of kind * -> *
 -}
mapZip : (a -> b) -> Zip a -> Zip b
mapZip f x =
    { lefts  = map f x.lefts
    , center = f x.center
    , rights = map f x.rights
    }

pureZip : a -> Zip a
pureZip c = Zip [] c []

apZip : Zip (a -> b) -> Zip a -> Zip b
apZip x y =
    { lefts  = zipWith (<|) x.lefts y.lefts
    , center = x.center y.center
    , rights = zipWith (<|) x.rights y.rights
    }

zipWith : (a -> b -> c) -> List a -> List b -> List c
zipWith f xs ys =
    let zipWith' z f xs ys = case xs of
        []        -> z
        (x::xs')  -> case ys of
            []        -> z
            (y::ys')  -> zipWith' ((f x y) :: z) f xs' ys'
    in reverse <| zipWith' [] f xs ys

extractZip : Zip a -> a
extractZip z = z.center

back : Zip a -> Maybe (Zip a)
back z = case z.lefts of
        []      -> Nothing
        (l::ls) -> Just <| mkZip ls l (z.center :: z.rights)

forth : Zip a -> Maybe (Zip a)
forth z = case z.rights of
        []      -> Nothing
        (r::rs) -> Just <| mkZip (z.center :: z.lefts) r rs

extendZip : (Zip a -> b) -> Zip a -> Zip b
extendZip f z =
    let copyAp f a = (f a,a)
        ls = unfoldr (Maybe.map (copyAp f) << back)  z
        c  = f z
        rs = unfoldr (Maybe.map (copyAp f) << forth) z
    in mkZip ls c rs

duplicateZip : Zip a -> Zip (Zip a)
duplicateZip = extendZip identity

unfoldr : (b -> Maybe (a,b)) -> b -> List a
unfoldr f b =
    let unfoldr' z f b = case f b of
        Nothing     -> z
        Just (a,b') -> unfoldr' (a::z) f b'
    in reverse <| unfoldr' [] f b

mapZip2 : (a -> b) -> Zip2 a -> Zip2 b
mapZip2 f = Zip2 << mapZip (mapZip f) << unZip2

extractZip2 : Zip2 a -> a
extractZip2 = extractZip << extractZip << unZip2

-- TODO: check this is correct
extendZip2 : (Zip2 a -> b) -> Zip2 a -> Zip2 b
extendZip2 f =
    let extender = extendZip
                <| extendZip (f << Zip2)
                << sequenceZipZip
    in Zip2 << extender << unZip2

duplicateZip2 : Zip2 a -> Zip2 (Zip2 a)
duplicateZip2 = extendZip2 identity

sequenceZipZip : Zip (Zip a) -> Zip (Zip a)
sequenceZipZip x = mkZip `mapZip`
                   sequenceListZip x.center x.lefts `apZip`
                   x.center `apZip`
                   sequenceListZip x.center x.rights

sequenceListZip : Zip a -> List (Zip a) -> Zip (List a)
sequenceListZip shape = mapZip reverse
                     << foldl
                        (\x z -> (::) `mapZip` x `apZip` z)
                        (mapZip (always []) shape)

sequenceZipMaybe : Zip (Maybe a) -> Maybe (Zip a)
sequenceZipMaybe x = mkZip `Maybe.map`
                     (sequenceListMaybe x.lefts) `apMaybe`
                     x.center `apMaybe`
                     sequenceListMaybe x.rights

apMaybe : Maybe (a -> b) -> Maybe a -> Maybe b
apMaybe f x = case f of
    Nothing -> Nothing
    Just f' -> Maybe.map f' x

sequenceListMaybe : List (Maybe a) -> Maybe (List a)
sequenceListMaybe = Maybe.map reverse << foldl
        (\x z -> (::) `Maybe.map` x `apMaybe` z)
        (Just [])

left : Zip2 a -> Maybe (Zip2 a)
left  = Maybe.map Zip2 << back  << unZip2
right : Zip2 a -> Maybe (Zip2 a)
right = Maybe.map Zip2 << forth << unZip2
up : Zip2 a -> Maybe (Zip2 a)
up = Maybe.map Zip2
  << sequenceZipMaybe
  << mapZip back 
  << unZip2
down : Zip2 a -> Maybe (Zip2 a)
down = Maybe.map Zip2
    << sequenceZipMaybe
    << mapZip forth
    << unZip2

live : Zip2 Bool -> Bool
live z =
    let live = extractZip2 z
        neighbours = sum <| map (btoi << extractZip2)
                         <| filterMap identity
                [ left  z
                , right z
                , up    z
                , down  z
                , left  z `andThen` up
                , left  z `andThen` down
                , right z `andThen` up
                , right z `andThen` down
                ]
        btoi b = if b then 1 else 0
    in if
       | live && neighbours < 2            -> False
       | live && neighbours `member` [2,3] -> True
       | live && neighbours > 3            -> False
       | not live && neighbours == 3       -> True
       | otherwise                         -> False

life : Signal (Int,Int) -- board dimensions
     -> Float -- time interval
     -> Signal (Maybe (Zip2 Bool))
life dims freq =
    let fun (seed,dims) board = case board of
            Nothing -> generateBoard dims seed 
            Just b  -> Just <| extendZip2 live b
        toSeed (t,dims) =
            let seed = initialSeed <| floor <| inMilliseconds t
            in (seed,dims)
        params = toSeed
              <~ (timestamp <| sampleOn (every freq) dims)
    in foldp fun Nothing params

generateBoard : (Int,Int) -> Seed -> Maybe (Zip2 Bool)
generateBoard (w,h) seed =
    let zipList = sequenceListMaybe
               <| map listToZip
               <| fst
               <| generate (list w (list h boolGen)) seed
    in zipList `andThen` (Maybe.map Zip2 << listToZip)

boolGen : Generator Bool
boolGen =
    let fun seed = case generate (int 0 1) seed of
            (n,seed) -> (itob n,seed)
        itob = (==) 0
    in customGenerator fun

render : (Int,Int) -> Zip2 Bool -> Element
render (x,y) =
    let btoe b = color (btoc b) <| container x y middle empty
        btoc b = case b of
            True  -> Color.black
            False -> Color.white
    in flow Elem.right
    << map (flow Elem.down << map btoe << zipToList)
    << zipToList
    << unZip2

cellDims : (Int,Int) -> (Int,Int) -> (Int,Int)
cellDims (boardW,boardH) (w,h) =
    let cellW = toFloat w / toFloat boardW
        cellH = toFloat h / toFloat boardH
    in (floor cellW,floor cellH)

boardDims : Int -> (Int,Int) -> (Int,Int)
boardDims cells (w,h) =
    let ratio = (toFloat w) / (toFloat h)
        boardH = sqrt <| (toFloat cells) / ratio ^ 2
        boardW = ratio * boardH
    in (floor boardW,floor boardH)

main : Signal Element
main =
    let bdims = boardDims 30000 <~ Window.dimensions
        cdims = cellDims <~ bdims ~ Window.dimensions
        fun board cellDims = case board of
            Nothing -> plainText "Hold on a minute"
            Just b  -> render cellDims b
    in fun <~ life bdims 1000 ~ cdims
