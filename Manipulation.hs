module Manipulation where
import Aggregation
import AgHelpFun
import MyBasics
import Rules
import Data.Ord (comparing)
import Data.List
import Text.Read (readMaybe)
import Control.Arrow

exampleC :: Profile
exampleC = is2bs 5 [15,23,8]

type UtilitySingle = Ballot -> Float
type UtilitySet = [Ballot] -> Float

uSingle :: UtilitySet -> UtilitySingle
uSingle u ballot = u [ballot]

truePrefs :: Int -> UtilitySingle -> IC -> [Ballot]
truePrefs m u bc = maximaBy (comparing u) (models m bc)

uSet :: UtilitySingle  -> UtilitySet
uSet u ballots = sum (map u ballots) /
                   fromIntegral (length ballots)

uH :: Ballot -> Int -> UtilitySingle
uH tPrefs m b = fromIntegral (m - hamming tPrefs b)

type WeightF = Issue -> Float

w1 :: WeightF
w1 0 = 1
w1 1 = 1
w1 _ = 2

wHamming :: WeightF -> Int-> Ballot -> Ballot -> Float
wHamming w m b1 b2 = sum (map f [0..(m-1)]) where
  f i = if agree b1 b2 i
        then 0 else w i

uHW :: WeightF -> Ballot -> Int -> UtilitySingle
uHW w tPrefs m b = sum (map w [0..(m-1)]) - wHamming w m tPrefs b

type Knowledge = [MinIProfile]

splitProfiles :: Agent -> [Profile] -> Knowledge
splitProfiles i = map (splitProfile i)

exampleKn1 :: Knowledge
exampleKn1 = nub (splitProfiles 2 (allProfiles 5 3 l0))

exampleKn2 :: Knowledge
exampleKn2 = let
    f x = and (drop 2  (x!!1) ++
            drop 2 (head x))
  in
    nub (splitProfiles 2 (filter f (allProfiles 5 3 l0)))

updateKnowledge :: Int -> Agent -> Issue ->
              Vote -> Knowledge -> Knowledge
updateKnowledge m a i vote kn = let
    j = length (fst (head kn))
    n = length (uncurry (++) (head kn)) + 1
  in
    if null (checkIndices (m,n,j,a,i))  then let
        update (x,y) = ((x ++ [i2b m 0] ++ y) !! a) !! i == vote
      in
        filter update kn
    else
  error (unlines (checkIndices (m,n,j,a,i)))

expectedUBinA :: Ballot -> UtilitySet -> Knowledge
              -> Int -> IC -> AR -> Float
expectedUBinA b u kn m bc rule = let
    know = map (\(x,y) -> (x ++ [b] ++ y)) kn
    utility x = u  (rule m bc x)
  in
    sum (map utility know) / fromIntegral (length know)

bestBallots :: [Ballot] -> UtilitySet -> Knowledge
              -> Int -> IC -> AR -> [Ballot]
bestBallots ballots ui kn m bc rule
  | null kn = error "\nKnowledge is empty.\n"
  | otherwise =
  maximaBy (comparing f) ballots where
    f b = expectedUBinA  b ui kn m bc rule

updateBallotSet :: [Ballot] -> Issue -> Vote -> [Ballot]
updateBallotSet ballots i vote =
  filter (\x -> x !! i == vote) ballots

getAgent, getIss, getVote :: IO String
getAgent = do putStr "\nAgent :\n"
              getLine
getIss = do putStr "\nIssue :\n"
            getLine
getVote = do putStr "\nVote :\n"
             getLine

typeErr :: String
typeErr = "\nIncorrect type for input, try again\n"

manipulateAR :: Int -> Int -> Agent
                -> UtilitySet -> IC -> AR -> IO()
manipulateAR m n j uj bc rule = let
    startKnowledge = nub (splitProfiles j (allProfiles m n bc))
    startBallots = models m bc
    manipulate ballots kn = do
       putStr ("\n Press u to update knowledge,"
                ++ " r to restrict own ballot,"
                ++ " b to calculate best ballot,"
                ++ " q to quit, k to show knowledge,"
                ++ " s to show set of possible ballots\n")
       l <- getLine
       case l of
         "b" -> print (bestBallots ballots uj kn m bc rule)
         "q" -> putStr "\nBye\n"
         "k" -> do
           print kn
           manipulate ballots kn
         "s" -> do
           print ballots
           manipulate ballots kn
         "r" -> do
           i <- getIss
           vote <- getVote
           case (readMaybe i :: Maybe Issue,
                 readMaybe vote :: Maybe Vote) of
              (Just i', Just vote') -> do
                let newBallots = updateBallotSet ballots i' vote'
                manipulate newBallots kn
              _ -> do
                putStr typeErr
                manipulate ballots kn
         _ -> do
           a <- getAgent
           i <- getIss
           vote <- getVote
           case (readMaybe a :: Maybe Agent,
                 readMaybe i ::  Maybe Issue,
                 readMaybe vote :: Maybe Vote) of
              (Just a', Just i', Just vote') ->
                if null (checkIndices (m,n,j,a',i')) then do
                  putStr (unlines (checkIndices (m,n,j,a',i')) ++
                          "Try again\n")
                  manipulate ballots kn
                  else do
                  let newKnowledge =
                        updateKnowledge m a' i' vote' kn
                  manipulate ballots newKnowledge
              _ -> do
                     putStr typeErr
                     manipulate ballots kn
    in
      manipulate startBallots startKnowledge

type UtilitySCSingle = Alternative -> Float
type UtilitySCSet = [Alternative] -> Float

uSet2 :: UtilitySCSingle -> UtilitySCSet
uSet2 u alts = sum (map u alts) / fromIntegral (length alts)

truePrefsSC :: Int -> UtilitySCSingle -> [Preference]
truePrefsSC v ui = let
    combs = [(a,c)| a <- [0..(v-1)], c <- [0..(v-1)]]
    test b (a,c) = (ui a == ui c) ||
                  (b !! alt2iss (a,c) v == (ui a > ui c))
    f b = all (test b) combs
  in
    profile2prefs (v*v)
    (bs2is (filter f (models (v*v) (lo0 v))))

u0 :: UtilitySCSingle
u0 0 = 4
u0 1 = 1
u0 _ = 0

expectedUSCF :: Ballot -> UtilitySCSet -> Knowledge
              -> Int -> SCF -> Float
expectedUSCF b u kn v rule = let
    know = map (\(x,y) -> (x ++ [b] ++ y)) kn
    utility x =  u (rule v x)
  in
    sum (map utility know) / fromIntegral (length know)

exampleKn3 :: Knowledge
exampleKn3 = nub (splitProfiles 0 (allProfiles 9 3 (lo0 3)))

bestPrefs :: [Ballot] -> UtilitySCSet -> Knowledge
              -> Int -> SCF -> [Preference]
bestPrefs ballots u kn v rule = let
    f b = expectedUSCF  b u kn v rule
    sortedBallots = sortBy (comparing (\x -> u [b2i x])) ballots
  in
    ballots2prefs v (maximaBy (comparing f) sortedBallots)

exampleKn4 :: Knowledge
exampleKn4 = splitProfiles 0 (filter (\x -> x !! 1 == i2b 9 104)
          (allProfiles 9 3 (lo0 3)))

updateKnowledgePA :: Int -> Agent ->
                    (Alternative, Alternative) -> Vote
                    -> Knowledge -> Knowledge
updateKnowledgePA v a (i,j) =
  updateKnowledge (v * v) a (alt2iss (i,j) v)

getAlts :: IO (String,String)
getAlts = do putStr "\nPrefers a over b. What is a?\n"
             a <- getLine
             putStr "\n What is b? \n"
             b <- getLine
             return (a,b)

checkIndicesAlts :: (Alternative,Alternative,Int) -> String
checkIndicesAlts (a,b,v)
  | a > v-1 || b > v-1 =
    "Alternative index too large\n"
  | a < 0 || b < 0 =
    "Alternative index too small\n"
  | otherwise = ""

manipulateSCF :: Int -> Int -> Agent
                -> UtilitySCSet -> SCF -> IO()
manipulateSCF v n j uj rule = let
    m = v * v
    startKnowledge = nub (splitProfiles j (allProfiles m n (lo0 v)))
    startBallots = models m (lo0 v)
    manipulate ballots kn = do
       putStr ("\n Press u to update knowledge,"
                ++ " r to restrict own ballot,"
                ++ " b to calculate best preference order,"
                ++ " q to quit, k to show knowledge,"
                ++ " s to show set of possible ballots\n")
       l <- getLine
       case l of
         "b" -> print (bestPrefs ballots uj kn v rule)
         "q" -> putStr "\nBye\n"
         "k" -> do
           print kn
           manipulate ballots kn
         "s" -> do
           print ballots
           manipulate ballots kn
         "r" -> do
           (p1,p2) <- getAlts
           case (readMaybe p1 :: Maybe Alternative,
                 readMaybe p2 :: Maybe Alternative) of
              (Just p1', Just p2') -> do
                let i = alt2iss (p1',p2') v
                let newBallots = updateBallotSet ballots i True
                manipulate newBallots kn
              _ -> do
                putStr typeErr
                manipulate ballots kn
         _ -> do
           a <- getAgent
           (p1,p2) <- getAlts
           case (readMaybe a :: Maybe Agent,
                 readMaybe p1 :: Maybe Alternative,
                 readMaybe p2 :: Maybe Alternative) of
              (Just a', Just p1', Just p2') -> do
                let i = alt2iss (p1',p2') v
                if null (checkIndices (m,n,j,a',i)) &&
                  null (checkIndicesAlts (p1',p2',v)) then do
                  let newKnowledge =
                        updateKnowledge m a' i True kn
                  manipulate ballots newKnowledge
                  else do
                    putStr (unlines (checkIndices (m,n,j,a',i)) ++
                            checkIndicesAlts (p1',p2',v) ++
                            "Try again\n")
                    manipulate ballots kn
              _ -> do
                     putStr typeErr
                     manipulate ballots kn
    in
      manipulate startBallots startKnowledge

uDC2 :: UtilitySet
uDC2 = uSet (uDC2'.b2i) where
  uDC2' 1 = 100
  uDC2' 7 = 80
  uDC2' 4 = 70
  uDC2' _ = 0

noKnowledge :: Int -> Int -> Agent -> IC -> Knowledge
noKnowledge m n a bc = nub (splitProfiles a (allProfiles m n bc))

w2 :: WeightF
w2 0 = 1
w2 1 = 1
w2 2 = 100
w2 3 = 100
w2 _ = 100

uExHome :: UtilitySet
uExHome = uSet (uHW w2 (i2b 5 8) 5)

u0ExMaj :: UtilitySet
u0ExMaj = uSet (u0ExMaj'.b2i) where
  u0ExMaj' 2 = 100
  u0ExMaj' 3 = 90
  u0ExMaj' 1 = 55
  u0ExMaj' _ = 1

bestExpectation :: Int -> UtilitySet -> Knowledge -> IC -> AR -> Float
bestExpectation m ui kn bc rule = let
    b = head (bestBallots (models m bc) ui kn m bc rule)
  in
    expectedUBinA b ui kn m bc rule

type Agenda = [Issue]

consistentBallot :: Agenda -> Agenda -> Ballot -> Ballot
                  -> Bool
consistentBallot ag1 ag2 b1 b2 =
  all (\j -> case elemIndex (ag1 !! j) ag2 of
        Nothing -> True
        Just ix -> b1 !! j == b2 !! ix)
  [0..(length ag1-1)]

corBallots :: Agenda -> Agenda -> Int -> IC ->
                Ballot -> [Ballot]
corBallots ag1 ag2 m bc b = let
    bs = models (length ag2) (restrictIC ag2 m bc)
  in
    filter (consistentBallot ag1 ag2 b) bs

restrictBal :: Agenda -> Agenda -> Ballot -> Ballot
restrictBal ag1 ag2 b1 = head (filter (consistentBallot ag1 ag2 b1)
                         (models m n0)) where
                      m = length ag2

restrictProfile :: Agenda -> Agenda -> Profile -> Profile
restrictProfile ag1 ag2 = map (restrictBal ag1 ag2)

restrictKnowledge :: Agenda -> Agenda -> Knowledge -> Knowledge
restrictKnowledge ag1 ag2 = map (restrictProfile ag1 ag2 ***
                            restrictProfile ag1 ag2)

restrictIC :: Agenda -> Int -> IC -> IC
restrictIC ag m bc b =
    any (consistentBallot ag [0..(m-1)] b) (models m bc)

restrictUtility :: Agenda -> Agenda -> Int ->
                   IC -> UtilitySet -> UtilitySet
restrictUtility ag1 ag2 m bc u bs = let
    singleu b = u (corBallots ag2 ag1 m bc b)
  in
    uSet singleu bs

settles :: Int -> Agenda -> Agenda -> IC -> Bool
settles m ag1 ag2 bc = let
    l1 = length ag1
    ag2' = nub (ag2 ++ ag1)
    l2 = length ag2'
    bc1 = restrictIC ag1 m bc
    bc2 = restrictIC ag2' m bc
    bs1 = models l1 bc1
    bs2 = models l2 bc2
    f b = length (filter (consistentBallot ag1 ag2' b) bs2) == 1
  in
    all f bs1

allAgsForAg :: Int -> Agenda -> IC -> [Agenda]
allAgsForAg m ag' bc = filter (\ag -> settles m ag ag' bc)
              (subsequences [0..(m-1)])

minimals :: [Agenda] -> [Agenda]
minimals ags = minimals' ags ags where
  minimals' ags' [] = ags'
  minimals' ags' (x:xs) = let
      f y = x == y || not (all (`elem` y) x)
    in
      minimals' (filter f ags') xs

dbOnAg :: Agenda -> AR
dbOnAg ag m bc = let
    bc' = restrictIC ag m bc
    m' = length ag
  in
    dbRule m' bc'

bestAgendasDB :: Int -> Agenda -> IC -> UtilitySet ->
                  Knowledge -> [Agenda]
bestAgendasDB m ag' bc ui kn = let
    ags = allAgsForAg m ag' bc
    ag1 = [0..(m-1)]
    f ag = bestExpectation (length ag) (restrictUtility ag1 ag m bc ui)
          (restrictKnowledge ag1 ag kn)
          (restrictIC ag m bc) (dbOnAg ag)
  in
    maximaBy (comparing f) ags

