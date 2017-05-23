module AgHelpFun where
import Aggregation
import Control.Monad

allProfiles :: Int -> Int -> IC -> [Profile]
allProfiles m n bc = replicateM n (models m bc)

profileSum :: Num a => (Ballot -> a) -> Profile -> a
profileSum fn profile = sum (map fn profile)

changeOnIss :: (Issue,Bool) -> Ballot -> Ballot
changeOnIss (i,b) ballot = let
  pairs = zip [0..] ballot
  f (j,e) = if i==j then (i,b) else (j,e)
  newpairs = map f pairs
 in
  map snd newpairs

changeBal :: Profile -> Agent -> Ballot -> Profile
changeBal prof i b = take i prof ++ [b] ++ drop (i+1) prof

data Quotkind = Strict | Weak
                    deriving(Eq)
quota :: Quotkind -> Float -> Int -> Issue -> Profile -> Bool
quota kind qu _ i profile = let
   n = length profile
   q = fromIntegral n * qu
   decision | kind == Weak =
                fromIntegral (length (coalition i profile)) >= q
            | otherwise =
                fromIntegral (length (coalition i profile)) > q
 in
   decision

majority :: Quotkind -> Int -> Issue -> Profile -> Bool
majority kind = quota kind 0.5

checkIndices  :: (Int,Int,Agent,Agent,Issue) -> [String]
checkIndices (m,n,j,a,i) =
  ["Agent index too large" | a >= n]
  ++ ["Agent index too small" | a < 0]
  ++ ["Cannot update knowledge about self" | a == j]
  ++ ["Issue index too large" | i >= m]
  ++ ["Issue index too small" | i < 0]

