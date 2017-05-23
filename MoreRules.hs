module MoreRules where
import Aggregation
import AgHelpFun
import Rules
import Data.List

avRule :: AR
avRule _ _ profile = let
    f x = profileSum (hamming x) profile
    mindist z = f z == minimum (map f profile)
  in
    nub (filter mindist profile)

exampleB :: ProfInt
exampleB = [32,24,24,24,24,24,24,24,24,24,24,7,7,7,7,7,7,7,7,7,7]

mvRule :: AR
mvRule m _ profile = let
    f x = minimum (map (hamming x)  (majResolveAll m n0 profile))
    mindist z = f z == minimum (map f profile)
  in
    filter mindist profile

majStrengt :: Profile -> Issue -> Int
majStrengt profile i = let
    numb1 = length (coalition i profile)
    n = length profile
  in
    maximum [numb1, n - numb1]

allPerm :: Int -> [[Issue]]
allPerm m = permutations [0..(m - 1)]

sortIssues:: [Issue] -> Profile -> Issue -> Issue -> Ordering
sortIssues perm profile i j = let
    stronger = compare (majStrengt profile i)
                (majStrengt profile j)
    higherorder = compare (elemIndex i perm) (elemIndex j perm)
  in
    case stronger of
      EQ -> higherorder
      LT -> LT
      GT -> GT

ltaub :: Quotkind -> Int -> Profile -> [Issue] -> Ballot
ltaub kind m profile perm = let
    beginBallot =  head profile
    issues = sortBy (sortIssues perm profile) [0..(m-1)]
    agreeto j b1 b2 = all (agree b1 b2) (take (j+1) issues)
    existsB b j = any (agreeto j b) profile
    majB = head (majResolve kind m n0 profile)
    lpart ballot j
      | j == m = ballot
      | existsB (changeOnIss (issues!!j, majB!!(issues!!j))
            ballot) j =
          lpart (changeOnIss (issues!!j, majB!!(issues!!j))
            ballot) (j+1)
      | otherwise =
          lpart (changeOnIss (issues!!j, not (majB!!(issues!!j)))
          ballot) (j+1)
  in
    lpart beginBallot 0

rvRule :: Quotkind -> AR
rvRule kind m _ profile = nub (map (ltaub kind m profile) (allPerm m))

