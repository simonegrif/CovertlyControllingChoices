module Rules where
import Aggregation
import MyBasics
import AgHelpFun
import Data.List
import Data.Tuple
import Data.Ord

majResolve :: Quotkind -> AR
majResolve kind m _bc profile =
  [[majority kind m i profile | i <- [0..(m-1)] ]]

majResolveAll :: AR
majResolveAll m _ profile = majResolveAll' 0 where
    majResolveAll' i =
      if i == m then [[]]
      else
        let
          ms = majority Strict m i profile
          mw = majority Weak m i profile
        in
          if mw == ms then map (mw :) (majResolveAll' (i+1)) else
             map (ms :) (majResolveAll' (i+1)) ++
             map (mw :) (majResolveAll' (i+1))

exampleF :: Profile
exampleF = [[True,True,True],
            [True,True,True],
            [False,False,True],
            [False,False,False]]

priority :: AR
priority m bc profile =
  let
    mjS = head (majResolve Strict m n0 profile)
    mjW = head (majResolve Weak m n0 profile)
    priority' i outcomes =
      if i == m then outcomes
      else
        let
          newOutcomes = filter (\x -> agree x mjS i || agree x mjW i)
                        outcomes
        in
          if null newOutcomes then priority' (i+1) outcomes
          else priority' (i+1) newOutcomes
  in
    priority' 0 (models m bc)

exEic :: IC
exEic (x0:x1:x2:x3:_) = (x0 && x1 && x2) --> not x3
exEic _ = True

exampleE :: Profile
exampleE = [[True,True,False,True],[False,True,True,True],
            [True,False,True,True]]

hamming :: Ballot -> Ballot -> Int
hamming i j = hamming' i j 0 where
  hamming' [] _ d = d
  hamming' _ [] d = d
  hamming' (x:xs) (y:ys) d
    | x == y = hamming' xs ys d
    | otherwise = hamming' xs ys (d + 1)

dbRule :: AR
dbRule m bc profile = let
    f x = profileSum (hamming x) profile
  in
    minimaBy (comparing f) (models m bc)

mmRule :: AR
mmRule m bc profile = let
    bs = models m bc
    maxdist b = maximum (map (hamming b) profile)
  in
    minimaBy (comparing maxdist) bs

exampleProfTravel :: Profile
exampleProfTravel = [[True,True,True,True,True],
                     [True,True,True,True,True],
                     [True,True,True,True,True],
                     [True,True,True,True,False],
                     [False,False,False,False,False]]

lsRule :: AR
lsRule m bc profile = let
    sq x y = hamming x y ^ (2 :: Int)
    f x = profileSum (sq x) profile
  in
    minimaBy (comparing f) (models m bc)

type Alternative = Int
type Preference = [Alternative]

alt2iss :: (Alternative, Alternative) -> Int -> Issue
alt2iss (i,j) v = j + i * v

iss2alt :: Issue -> Int -> (Alternative,Alternative)
iss2alt i v = (div i v,rem i v)

pref2ballot :: Preference -> Ballot
pref2ballot pref = let
    v = length pref
    p2b i | i == v * v = []
          | elemIndex (fst (iss2alt i v)) pref
              < elemIndex (snd (iss2alt i v)) pref = True : p2b (i+1)
          | otherwise = False : p2b (i+1)
  in
    p2b 0

ballot2pref :: Int -> Ballot -> Preference
ballot2pref v ballot = let
    f i j | i == j = EQ
          | ballot !! alt2iss (i,j) v = LT
          | otherwise = GT
  in
    sortBy f [0..(v-1)]

ballots2prefs :: Int -> [Ballot] -> [Preference]
ballots2prefs v = map (ballot2pref v)

pref2int :: Preference -> BalInt
pref2int = b2i . pref2ballot

int2pref :: Int -> BalInt -> Preference
int2pref v = ballot2pref v . i2b (v * v)

prefs2profile :: [Preference] -> ProfInt
prefs2profile = map pref2int

profile2prefs :: Int -> ProfInt  -> [Preference]
profile2prefs v = map (int2pref v)

exampleD :: Profile
exampleD = is2bs 9 [200,104,38]

lo0 :: Int -> IC
lo0 v ballot = let
    diag = [(a,a) | a <- [0..(v-1)]]
    diagelems = [ ballot!!i | i <- [0..(v * v - 1)],
                  iss2alt i v `elem` diag]
    irrefl = all (== False) diagelems
    antisymPart i =  (iss2alt i v `elem` diag) ||
      (ballot !! i /= ballot !! alt2iss (swap (iss2alt i v)) v)
    antisym = all antisymPart [0..(v * v - 1)]
    tr i x = (ballot !!i && ballot !! x
           && fst (iss2alt x v) == snd (iss2alt i v)) -->
          ballot !! alt2iss (fst (iss2alt i v),snd (iss2alt x v)) v
    transPart i = all (tr i) [0..(v*v-1)]
    transitive = all transPart [0..(v * v - 1)]
  in
    irrefl && antisym && transitive

type SCF = Int -> Profile -> [Alternative]

copelandScore :: Alternative -> Int -> Profile -> Int
copelandScore i v profile = let
    m = v * v
    iFirst = [alt2iss (i,b) v | b <- [0..(v-1)]]
    iSnd = [alt2iss (b,i) v | b <- [0..(v-1)]]
  in
    length [j | j <- iFirst, majority Strict m j profile] -
    length [j | j <- iSnd, majority Strict m j profile]

copelandRule :: SCF
copelandRule v profile = let
    mx = maximum (map (\i -> copelandScore i v profile) [0..(v-1)])
    f i = copelandScore i v profile == mx
  in
    filter f [0..(v-1)]

