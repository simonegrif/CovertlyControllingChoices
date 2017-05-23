module Aggregation where
import MyBasics
import Data.List

type Vote = Bool
type Issue = Int
type Agent = Int

type Ballot = [Vote]

type BalInt = Int

b2i :: Ballot -> BalInt
b2i = bin2int

i2b :: Int -> BalInt -> Ballot
i2b m = assert
  (\ i _ -> i < 2^m)
  (\ i _ -> "ballot "++ show i ++" does not exist")
  (\ i -> let
    bs = int2bin i
    m'  = m - length bs
  in
    replicate m' False ++ bs)

type Profile = [Ballot]
type ProfInt = [BalInt]

is2bs :: Int -> [BalInt] -> [Ballot]
is2bs m = map (i2b m)

bs2is :: [Ballot] -> [BalInt]
bs2is = map b2i

type MinIProfile = (Profile, Profile)

splitProfile :: Agent -> Profile -> MinIProfile
splitProfile i profile = (take i profile, drop (i+1) profile)

exampleA :: Profile
exampleA = is2bs 3 [4,7,1]

allBallots :: Int -> [Ballot]
allBallots 0 = [[]]
allBallots m = map (True :) allbs ++
               map (False :) allbs where
                 allbs = allBallots (m-1)

agree :: Ballot -> Ballot -> Issue -> Bool
agree b1 b2 i = b1 !! i ==  b2 !! i

agreeSet :: Ballot -> Ballot -> [Issue]
agreeSet b1 b2 = let
    m = length b1
  in [i | i <- [0..(m-1)], b1 !! i == b2 !! i]

coalition :: Issue -> Profile -> [Agent]
coalition i profile = let
    pairs = zip [0..] profile
  in
    [ ag | (ag,ballot) <- pairs, ballot!!i ]

anticoalition ::  Issue -> Profile -> [Agent]
anticoalition i profile = let
    n = length profile
  in
    [0..n-1] \\ coalition i profile

type IC = Ballot -> Bool

n0, s0, q0, r0, v0, l0, z0 :: IC
n0 _         = True
s0 (x:y:_)   = x == y
s0 _         = True -- True for single issue ballots
q0 (x:y:z:_) = ((x && z) --> y) && (y --> (x && z))
q0 _         = True -- True for 1 and 2 issue ballots
r0 (x:y:z:_) = not (x && y && z)
r0 _         = True -- True for 1 and 2 issue ballots
v0           = or
l0 (x:y:xs)    = (x && y) --> all not xs
l0 _         = True -- True for 1 and 2 issue ballots
z0 (x:y:_)   = x || y
z0 _         = True -- True for 1 issue ballots

models :: Int -> IC -> [Ballot]
models m bc = [ b | b <- allBallots m, bc b]

checkProfile :: Profile -> IC -> Bool
checkProfile profile p = all p profile

type AR = Int -> IC -> Profile -> [Ballot]

