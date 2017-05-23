module Quantify where
import Manipulation
import Rules
import AgHelpFun
import Aggregation
import System.Random
import Control.Monad
import Data.List
import Control.Arrow

manipProfTR :: Int -> Int -> IC -> AR -> Profile -> Bool
manipProfTR m i bc rule prof = let
   bs = models m bc
   x = prof !! i
   u = rule m bc prof
   (y1,y2) = splitProfile i prof
   in u /= [x] &&
      any (\z -> u /= rule m bc (y1 ++ [z] ++ y2))
      bs

manipMeasTR :: Int -> Int -> Int -> IC -> AR -> Float
manipMeasTR m n i bc rule = let
   profs = allProfiles m n bc
   manipks = filter (manipProfTR m i bc rule) profs
   in fromIntegral (length manipks) /
       fromIntegral (length profs)

manipMeasCR :: Int -> Int -> Int -> IC -> AR -> Float
manipMeasCR m n i bc rule = let
  bs = models m bc
  ks = map (\x -> ( x !! i, rule m bc x,
            splitProfile i x))
            (allProfiles m n bc)
  manipl (x, u, (y1,y2)) = any (\z -> ([0..(m-1)] \\
                      agreeSet (head u) x) `intersect`
                      agreeSet x
                      (head (rule m bc (y1 ++ [z] ++ y2)))  /= [])
                            bs
  manipks = filter manipl ks
  in fromIntegral (length manipks) /
      fromIntegral (length ks)

manipMeas :: Int -> Int -> Int -> UtilitySet -> IC ->
             AR -> Float
manipMeas m n i ui bc rule = let
  bs = models m bc
  avgU = sum (map (uSingle ui) bs) / fromIntegral (length bs)
  ps = [(p1,p2)| p1 <- replicateM i bs, p2 <- replicateM (n-i-1) bs]
  manipl p = let
    a = maximum (map (\b2 -> ui (
        rule m bc (fst p ++ [b2] ++ snd p ))) bs)
    b = maximum (map (\b1 -> ui (
        rule m bc (fst p ++ [b1] ++ snd p )))
                   (truePrefs m (uSingle ui) bc))
    in  a - b
  manipks = sum (map manipl ps)
  in (manipks /
      fromIntegral (length ps)) / avgU

data KnKind = Full | No
                deriving (Eq,Show)

testWithUi :: KnKind -> Int -> Int -> Int -> IC -> Int ->
              [Float] -> (Float,Float)
testWithUi _ _ _ _ _ 0 _ = (0,0)
testWithUi kind m n i bc num uinum =
  let
  ui b = uinum !! b2i b
  meas | kind == Full = manipMeas
       | otherwise = manipMeas0k
  in ((+) (meas m n i (uSet ui) bc priority)
    *** (+) (meas m n i (uSet ui) bc dbRule))
    (testWithUi kind m n i bc (num - 1) (drop (2 ^ m) uinum))

testM :: KnKind -> Int -> Int -> Int -> IC ->
         Int -> IO ()
testM kind m n i bc num = do
    r <- newStdGen
    print ((\(x,y) -> (x/fromIntegral num, y/fromIntegral num))
          (testWithUi kind m n i bc num (take (2^m * num)
          (randoms r :: [Float]))))

testWithUiWH :: KnKind -> Int -> Int -> Int -> IC -> Int ->
                [Float] -> [Bool] -> (Float,Float)
testWithUiWH _ _ _ _ _ 0 _ _ = (0,0)
testWithUiWH kind m n i bc num weights ballots =
  let
  w j = weights !! j
  tb = take m ballots
  ui = uHW w tb m
  meas | kind == Full = manipMeas
       | otherwise = manipMeas0k
  in ((+) (meas m n i (uSet ui) bc priority)
    *** (+) (meas m n i (uSet ui) bc dbRule))
    (testWithUiWH kind m n i bc (num - 1) (drop (2 ^ m) weights)
     (drop m ballots))

testMWH :: KnKind -> Int -> Int -> Int -> IC -> Int -> IO ()
testMWH kind m n i bc num = do
    r <- newStdGen
    print ((\(x,y) -> (x/fromIntegral num, y/fromIntegral num))
          (testWithUiWH kind m n i bc num (take (2^m * num)
          (randoms r :: [Float])) (take (m * num)
          (randoms r :: [Bool]))))

manipMeas0k :: Int -> Int -> Int -> UtilitySet -> IC ->
               AR -> Float
manipMeas0k m n i ui bc rule = let
  tps = truePrefs m (uSingle ui) bc
  bs = models m bc
  avgU = sum (map (uSingle ui) bs) / fromIntegral (length bs)
  kn = [(p1,p2)| p1 <- replicateM i bs, p2 <- replicateM (n-i-1) bs]
  expU b = expectedUBinA  (head (bestBallots bs ui kn m bc rule))
            ui kn m bc rule -
           expectedUBinA b ui kn m bc rule
  maniptot = sum (map expU tps)
  in (maniptot /
      fromIntegral (length tps)) / avgU

testWithUiWC :: KnKind -> Int -> Int -> Int -> IC -> Int ->
                [Float] -> (Float,Float)
testWithUiWC _ _ _ _ _ 0 _ = (0,0)
testWithUiWC kind m n i bc num uinum =
  let
  ui b = uinum !! b2i b
  meas | kind == Full = manipMeas
       | otherwise = manipMeas0k
  old = testWithUi kind m n i bc (num - 1) (drop (2 ^ m) uinum)
  in (maximum [meas m n i (uSet ui) bc priority, fst old],
      maximum [meas m n i (uSet ui) bc dbRule, snd old])

testMWC :: KnKind -> Int -> Int -> Int -> IC -> Int -> IO ()
testMWC kind m n i bc num = do
    r <- newStdGen
    print (testWithUiWC kind m n i bc num (take (2^m * num)
          (randoms r :: [Float])))

