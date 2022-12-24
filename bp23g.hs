{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE TupleSections #-}
import Data.Map.Strict(Map, (!))
import qualified Data.Map.Strict as M
import Data.List ( find, intercalate, sort, nub, nubBy )
import qualified Data.Set as S
import Data.Bifunctor ( Bifunctor(bimap) )
import Data.Maybe (isNothing)
import Debug.Trace
import System.Process
import CmmUtils (cmmSLtWord)

--trace x y =y
main::IO()
main= print $ graphs (2, 1, 0, 1)
u=undefined

t lt a =trace (unwords lt ++ "\n") (trace $ unwords $ lt  ++ ["\n", show a]) a
tv lt a =trace (unwords (lt++[show a]) ++ "\n") a

tb lt a = a

--tv str a = t [str, show a] a

data Block = F2 Int | F3 Int | E2 Int | E3 Int deriving (Eq, Ord, Show)
data Graph = Graph GraphType (Map Block (Block, Block)) (Map Block Block) deriving (Show) -- f2, e2 edges

type GraphType = (Int, Int, Int, Int) -- F2, F3, E2, E3 blocks
data Free = Free (Map Block Int) (Maybe Int) (Maybe Int) (Maybe Int) Int
-- Int is 0,1,2,3, then free F2, F3, E3 remaining edges, note that e2 nodes are attached at begining so not free
type BlockType = Int -> Block

startGraph:: GraphType -> Int -> Int -> Graph
startGraph (gf2, gf3, ge2, ge3) a b = 
    Graph (gf2, gf3, ge2, ge3) M.empty (foldr (\n acum -> M.insert (E2 $2*a+n) (F3 $a+n) acum) g0 [1..b])
          where g0 = foldr (\n a -> insert2 (E2 $ 2*n-1, F3 n) (E2 $2*n, F3 n) a) M.empty [1..a]

frmap :: (Map Block Int -> Map Block Int) -> Free -> Free
frmap f (Free m f2 f3 e3 re) = Free (f m) f2 f3 e3 re

gmap :: (Map Block (Block, Block) -> Map Block (Block, Block)) -> Graph -> Graph
gmap f (Graph gt m1 m2) = Graph gt (f m1) m2

decFree :: Block -> Map Block Int -> Map Block Int
decFree = M.adjust (\x -> x-1)
dec2Free :: Block -> Map Block Int -> Map Block Int
dec2Free = M.adjust (\x -> x-2)

insert2 :: Ord k => (k, a) -> (k, a) -> Map k a -> Map k a
insert2 (k1, v1) (k2, v2) m = M.insert k2 v2 (M.insert k1 v1 m)

startFreeMap :: GraphType -> Int -> Int -> Map Block Int
startFreeMap (f2, f3, e2, e3) a b = M.fromList (fl F2 2 f2 ++ fl3 f3 a b ++ fl E2 0 e2 ++ fl E3 1 e3)

fl:: (Int -> Block) -> Int -> Int -> [(Block, Int)]
fl cons d num = map (\n -> (cons n, d)) [1..num]

fl3 :: Int -> Int -> Int -> [(Block, Int)]
fl3 f3 a b = map (\n -> (F3 n, 1)) [1..a] ++ map (\n -> (F3 n, 2)) [a+1..a+b] ++ map (\n -> (F3 n, 3)) [a+b+1..f3]

is3 :: Block -> Bool
is3 (F3 _) =True
is3 (E3 _) = True
is3 _ = False

graphs:: GraphType -> [Graph] -- 
graphs gt@(f2, f3, e2, e3) =
     concat [graphsH gt (F3 1) (Free (startFreeMap gt a b) (Just 1) (nz f3 2) (nz e3 1) (f2*2))
               (startGraph gt a b)| a<-[0..(div e2 2)], b<-[0..e2], 2*a+b==e2]
       where nz n min = if n>min-1 then Just min else Nothing


graphsH :: GraphType -> Block  -- current vertex
       -> Free -- freemap which tracks number of free edges at each block
       -> Graph -- current graph
       -> [Graph] -- returns completions possible from current state of graph

graphsH gt cv (Free _ _ _ _ 0) cg= [cg]
graphsH gt cv (Free freeMap (Just nextf2) nf3  ne3 remainingEdges) cg =
    let (f2, f3, f32, e3) = gt --tb ["graphsH:", show cg, "cv:", show cv, "Free:", show freeMap, show remainingEdges] gt
     in if open freeMap cv then -- cv can be an f3 or an e3, picks will be from f3, f32, e3's 
          let picks = p F3 cv nf3 f3 freeMap ++ p E3 cv ne3 e3 freeMap
              newgs pick = graphsH gt pick (Free newFreeMap (nxt nextf2 f2) nnf3 nne3 (remainingEdges-2)) newg
               where  nnf3=newNxt nf3 f3 pick F3
                      nne3=newNxt ne3 e3 pick E3
                      newg = gmap (M.insert nextf2v (cv, pick)) cg
                      nextf2v = F2 nextf2
                      newFreeMap = dec2Free nextf2v $ decFree pick $ decFree cv freeMap  -- 2/2 block has 2 edges added and 3/3 block 1 edge
             in  concatMap newgs picks
        else
          let (pick, _) = M.findMin $ M.filterWithKey (\k v -> is3 k && 0<v) freeMap
              nnf3=newNxt nf3 f3 pick F3
              nne3=newNxt ne3 e3 pick E3
          in graphsH gt pick (Free freeMap (Just nextf2) nnf3 nne3 remainingEdges) cg

graphsH _ _ _ _ = error "graphsH no match"

nxt:: Int->Int->Maybe Int
nxt v max = if v<max then Just (v+1) else Nothing

newNxt :: Maybe Int -> Int -> Block -> BlockType -> Maybe Int
newNxt (Just num) max pick bt = if pick == bt num then nxt num max else Just num
newNxt Nothing _ _ _ = Nothing --  adjust only if new Block on path is from free stock

p:: BlockType -> Block -> Maybe Int -> Int -> Map Block Int -> [Block] -- new blocks to adjoin to path
p btype cv nextFree max free =
    let blockFree n = open free (btype n) &&  (cv/=btype n || free!cv>=2) in
       case nextFree of Nothing -> btype <$> filter blockFree [1..max] -- case when no symmetric empty slots left
                        Just n -> btype <$> filter blockFree [1..n] -- vertices after n are symmetric to n

open map v =
    case M.lookup v map of
          Just 0 -> False
          Nothing -> error $ "open Nothing"++ show (v,map)
          _ -> True

connected :: BlockDiagram -> Bool
connected bdiag@(BlockDiagram (f2, _, _, _) _ _ _ _) =
        f2 == count
        where
            (_,_,count) = componentSearch initBoundary initReached initCount
            initBoundary = S.singleton $ F2 1; initReached=initBoundary; initCount=1
            componentSearch boundary reached count  =
                tb ["cs", show boundary, show reached, show count] $
                   if S.null b2 then (b2,r2,c2) else componentSearch b2 r2 c2
                where (b2,r2,c2) = foldl bdNode (S.empty, reached, count)  boundary
            bdNode (boundary, reached, count) bdn =
                tb ["bdNode", show bdn, show boundary, show reached, show count, show (f2neighbours bdn bdiag)] $
                  foldl bdNodeNbr (boundary, reached, count) (f2neighbours bdn bdiag)
            bdNodeNbr (boundary, reached, count) nbrNode = tb ["bdNodeNbr",  show nbrNode, show boundary, show reached, show count] $
                if S.member nbrNode reached
                    then (boundary, reached, count)
                    else (S.insert nbrNode boundary, S.insert nbrNode reached, count+1)

f2neighbours :: Block -> BlockDiagram -> S.Set Block
f2neighbours f2b@(F2 _) bd@(BlockDiagram gt f2m e2m f3m e3m) =
    let (n1, n2) = f2m ! f2b in S.fromList(filter isF2 $ nbrList n1 bd ++ nbrList n2 bd)
f2neighbours _ _ = error "F2neighbours"

isF2 (F2 _) = True
isF2 _ = False

nbrList b@(F2 _) (BlockDiagram _ f2m _ _ _) = [n1,n2] where (n1,n2)=f2m!b
nbrList b@(F3 _) (BlockDiagram _ _ f3m _ _) = [n1,n2,n3] where (n1,n2,n3)=f3m!b
nbrList b@(E2 _) (BlockDiagram _ _ _ e2m _) = [e2m!b]
nbrList b@(E3 _) (BlockDiagram _ _ _ _ e3m) = [e3m!b]

type MB = Maybe Block
type IB = Either Block Block -- second option is for double edge
type Edge = (IB, IB)
data BlockDiagram = BlockDiagram GraphType (Map Block (Block, Block)) (Map Block (Block, Block, Block)) (Map Block Block) (Map Block Block) deriving (Show)
  -- edges from f2, f3, e2, e3 blocks  -- valid values have only these as keys and also edges have compatibility 
data O = Plus | Minus deriving (Show, Eq)
type MapO = Map Int O -- cyclic order on edges at f3 blocks

getBlock (Left b) = b
getBlock (Right b) = b

gtobd :: Graph -> BlockDiagram
gtobd g@(Graph gt f2mg e2mg) = BlockDiagram gt f2m f3m e2m e3m
    where
        f2m = f2mg
        f3m = M.map (\(a,b,c)->(forceMaybe a, forceMaybe b, forceMaybe c)) f3mb
        e3m= M.map forceMaybe e3mb
        f3mb = M.foldrWithKey f2inf3 (M.foldrWithKey e2inf3 M.empty e2mg)  f2mg -- initial acum for outer has all e2 edges filled in 
           --(foldr (\n a -> M.insert (F3 n) (Just $ E2 n, Nothing, Nothing) a)M.empty [1..e2])
                 
        e2m = e2mg
        e3mb = M.foldrWithKey f2ine3 M.empty f2mg

        (_,_,e2,_) = gt

        f2ine3 :: Block -> (Block, Block) -> Map Block (Maybe Block) -> Map Block (Maybe Block)
        f2ine3 f2b (E3 n, _) a = M.insert (E3 n) (Just f2b) a
        f2ine3 f2b (_, E3 n) a = M.insert (E3 n) (Just f2b) a
        f2ine3 f2b _ a = a

        f2inf3 :: Block -> (Block, Block) -> Map Block (MB, MB, MB) -> Map Block (MB, MB, MB)
        f2inf3 f2b (F3 n, F3 n2) a = M.alter (t3add f2b)  (F3 n2) $ M.alter (t3add f2b) (F3 n) a
        f2inf3 f2b (F3 n, _) a = M.alter (t3add f2b) (F3 n) a
        f2inf3 f2b (_, F3 n) a = M.alter (t3add f2b) (F3 n) a
        f2inf3 f2b _ a = a

        e2inf3 :: Block -> Block -> Map Block (MB, MB, MB) -> Map Block (MB, MB, MB)
        e2inf3 e2b (F3 n) a = M.alter (t3add e2b)  (F3 n) a
        e2inf3 e2b _  _= error "e2block doesnt have f3 value"

        t3add :: Block -> Maybe (MB, MB, MB) -> Maybe (MB, MB, MB)
        t3add v Nothing = Just (Just v, Nothing, Nothing)
        t3add v (Just (Nothing, x, y)) = Just (Just v, x, y)
        t3add v (Just (x, Nothing, y)) = Just (x, Just v, y)
        t3add v (Just (x, y, Nothing)) = Just (x, y, Just v)
        t3add v curr@(Just _) = error ("t3add No space in tuple block:"++ show v++" curr:"++show curr++" g:"++show g)

emptyUsedEdges :: GraphType -> Map Block [IB]
emptyUsedEdges (f2, f3, e2, e3) = M.fromList $ ce F2 f2 ++ ce F3 f3 ++ ce E2 e2 ++ ce E3 e3
  where ce :: (Int -> Block) -> Int -> [(Block, [IB])]
        ce constructor n = (\i -> (constructor i, [])) <$> [1..n]

mos :: GraphType -> [MapO]
mos (_, 1, _, _) = M.fromList <$> [[(1,Plus)], [(1,Minus)]]
mos (f2, f3, e2, e3) = M.insert f3 Plus<$>mos (f2,f3-1,e2,e3) ++ (M.insert f3 Minus<$>mos (f2,f3-1,e2,e3))


posMO :: GraphType -> MapO
posMO (_, f3, _, _) =  M.fromList $ (, Plus) <$> [1..f3]

sigs :: Int -> [(Int, Int, Int, Int)]
sigs deg = [(i,j,k,l)|i<-[1..div deg 2], j<-[0..div deg 3], k<-[0..j], l<-[0..i], --optimization for connectivity l<=i otherwise a f2 block will have 2  e3 edges 
                      deg==2*i+k && deg==3*j+l]
freesigs deg = [(i,j,0,0)|i<-[1..div deg 2], j<-[0..div deg 3], deg==2*i && deg==3*j]

cuspSplit :: MapO -> BlockDiagram -> [Int]
cuspSplit mo bd = sort $ (`div` 2) <$> (length <$> cuspSplitEdges mo bd)

cuspSplitEdges :: MapO -> BlockDiagram -> [[IB]]
cuspSplitEdges mo bd@(BlockDiagram bt _ _ _ _) = cuspSplitH bd mo (emptyUsedEdges bt)
cuspSplitH :: BlockDiagram -> MapO -> Map Block [IB] -> [[IB]] -- returns list of loops
cuspSplitH bd@(BlockDiagram bt f2m f3m e2m e3m) mo usedEdges =
    let startEdge = tb ["csH usedEdges", show usedEdges, "startEdge",
                        show $ freeEdge usedEdges mo bd] (freeEdge usedEdges mo bd)
    in case startEdge of
        Just edge ->
            let loop = tb ["loop", show edge] $ loopFrom edge mo bd
            in  loop:cuspSplitH bd mo (addUsedEdges loop usedEdges)
        Nothing -> []

loopFrom :: Edge -> MapO -> BlockDiagram -> [IB]
loopFrom edge@(v1, v2) mo bd = -- loop is sent in reverse
    tb ["loopComplete", show v2, show v1] $ loopComplete v2 v1 []
    where
        loopComplete currV prevV loopA =
            let nextV = tb ["nextVertex", show currV, show prevV] $ nextVertex currV prevV
            in if nextV==v2 && currV==v1 then prevV:loopA else loopComplete nextV currV (prevV:loopA)
        nextVertex :: IB -> IB -> IB
        nextVertex c p = tb ["nextElt", show c, show p] $ nextElt c (glookup (getBlock c) bd) (getBlock p) mo


nextElt :: IB -> [Block] -> Block -> MapO -> IB
nextElt (Right (F3 n)) lt prev mo
     |  mo!n==Plus = cyclicNext lt (Right prev) $ head lt
     | otherwise = cyclicNext (reverse lt) (Right prev) (last lt)
nextElt (Left (F3 n)) lt prev mo
     |  mo!n==Plus = cyclicNext lt (Left prev) $ head lt
     | otherwise = cyclicNext (reverse lt) (Left prev) (last lt)
nextElt (Left (F2 _)) [a,b] prev _ = if prev==a then (if a == b then Right b else Left b) else Left a
nextElt (Right (F2 _)) [a,b] prev _ = if prev==b then Left a else error "Right used on non-repeating 2/2 block"
--nextElt (F2 _) [a,b] (Right prev) _ = if prev==b then Left a else error "Right used on non-repeating 2/2 block"
nextElt _ [a] _ _ = Left a
nextElt _ _ _ _ = error "nextElt"


cyclicNext :: [Block] -> IB -> Block -> IB -- requires first element of list to be passed through the recursion loop
cyclicNext [a] (Left findable) h = if a==findable then Left h else error "cyclicNext no findable found"
cyclicNext [a] (Right findable) h = error "Right used on non-repeating 2/2 block" -- Right should have become Left if findable was repeated
cyclicNext (a:(n:r)) (Left findable) h = if a==findable then (if findable /= n then  Left n else Right n)
                                                     else cyclicNext (n:r) (Left findable) h
cyclicNext (a:r) (Right findable) h = cyclicNext r ((if a==findable then Left else Right) findable) h
cyclicNext [] elt h = error "cyclicNext given empty list"

addUsedEdges :: [IB] -> Map Block [IB] -> Map Block [IB] -- loop is understood as reverse
addUsedEdges (h:rst) used =
     snd $ foldl (\(prevV, mapAcum) v -> (v, M.adjust (prevV:) (getBlock v) mapAcum)) (h, used) $ rst ++ [h]
addUsedEdges _ _ = error "addUsedEdges"

freeEdge :: Map Block [IB] -> MapO -> BlockDiagram -> Maybe Edge
freeEdge usedEdges mo (BlockDiagram gt f2m f3m e2m e3m) =
    firstJust
     [
    mFind (let
            fn (b, (b1, b2, b3))
              | b1/=b2 && b1/=b3 && b2/=b2 = Just . (Left b, ) =<< find (`elem` used) (Left <$> [b1, b2, b3])
              | b1==b2 = tmp b1 b3
              | b1==b3 = tmp2 b1 b2
              | b2==b3 = tmp b2 b1
              | otherwise = Nothing
              where
               used = usedEdges!b
               tmp rep other
                 | Left other `notElem` used = Just (Right b, Left other)
                 | Left rep `notElem` used = Just (Left b, Left rep)
                 | Right rep `notElem` used = Just (Left b, Right rep)
                 | otherwise = Nothing
               tmp2 rep other
                 | Left other `notElem` used = Just (Left b, Left other)
                 | Left rep `notElem` used = Just (Right b, Left rep)
                 | Right rep `notElem` used = Just (Left b, Right rep)
                 | otherwise = Nothing
           in fn)


        f3m,
    mFind (\(b, (b1, b2)) ->
           let used = usedEdges!b in
                        if b1 /= b2 then  if Left b1 `notElem` used
                                            then Just (Left b, Left b1)
                                            else if Left b2 `notElem` used
                                                  then Just (Left b, Left b2)
                                                  else Nothing
                                    else if Left b1 `notElem` used-- implies incoming Right b2 has not been used 
                                                  then Just (Right b, Left b1)
                                    else if Right b2 `notElem` used  -- implies  incoming Left b1 edge also not used 
                                            then Just (Left b, Right b2)

                                    else Nothing)
    f2m,
    mFind (\(b, b1) ->
           let used = (usedEdges!b) in if Left b1 `notElem` used then Just (Left b,Left b1) else Nothing)
        e2m,
    mFind (\(b, b1) ->
           let used = (usedEdges!b) in if Left b1 `notElem` used then Just (Left b, Left b1) else Nothing)
        e3m]

mFind :: ((k, a1) -> Maybe a2) -> Map k a1 -> Maybe a2
mFind fn map = ltFind fn (M.assocs map)

ltFind :: (t -> Maybe a) -> [t] -> Maybe a
ltFind fn [] = Nothing
ltFind fn (h:rest) = if isNothing $ fn h then ltFind fn rest else fn h

firstJust :: [Maybe a] -> Maybe a
firstJust (Just a:r) = Just a
firstJust (Nothing:r) = firstJust r
firstJust [] = Nothing

glookup :: Block -> BlockDiagram -> [Block]
glookup block bd@(BlockDiagram bt f2m f3m e2m e3m) =
    case block of
            (F2 _) -> [a,b] where (a,b) = f2m ! block
            (F3 _) -> [a,b,c] where (a,b,c) = f3m ! block
            (E2 _) -> [e2m ! block]
            (E3 _) -> [e3m ! block]

forceMaybe :: Maybe p -> p
forceMaybe (Just a) = a
forceMaybe Nothing = error "forced Nothing"

graphString :: MapO -> BlockDiagram -> String
graphString mo bd@(BlockDiagram (f2, f3, e2, e3) f2m f3m e2m e3m) = initG mo bd++f2d++f3d++e2d++e3d++f3str++e3str++"}"
    where f2d = concatMap (dline . F2) [1..f2]
          f3d = concatMap (dline . F3) [1..f3]
          e2d = concatMap (dline . E2) [1..e2]
          e3d = concatMap (dline . E3) [1..e3]
          f3str = M.foldrWithKey (\(F3 n) v s -> fn n v s) "  " f3m
          e3str = M.foldrWithKey (\e3b b1 str -> str++line e3b b1 "black")  "" e3m
          fn :: Int -> (Block, Block, Block) -> String -> String
          fn n (b1, b2, b3) str
              | mo!n==Plus = str++line f3b b1 "red" ++ line f3b b2 "green" ++ line f3b b3 "blue"
              | mo!n==Minus = str++line f3b b1 "red" ++ line f3b b3 "green" ++ line f3b b2 "blue"
              | otherwise = error "not found"
              where f3b = F3 n

initG :: MapO -> BlockDiagram -> String
initG mo bd@(BlockDiagram sig _ _ _ _) =
     "graph {\n"++ "label=\"Type: "++ show sig ++ " CuspSplit: " ++ cshow (cuspSplit mo bd) ++ "\";\n"
      where cshow lt = intercalate "+" (map show lt)
dline :: Block -> String
dline (F2 n ) = vName (F2 n) ++ "[label=\"2/2_"++show n++"\", shape=box];\n"
dline (F3 n ) = vName (F3 n) ++ "[label=\"3/3_"++show n++"\", shape=box];\n"
dline (E2 n ) = vName (E2 n) ++ "[label=\"2_"++show n++"\", shape=circle];\n"
dline (E3 n ) = vName (E3 n) ++ "[label=\"3_"++show n++"\", shape=circle];\n"

type Color =String
line :: Block -> Block -> Color -> String
line b1 b2 col = vName b1 ++ " -- " ++ vName b2 ++ "[color="++col++"];\n"

vName :: Block -> String
vName (F2 n)= "F2_"++show n
vName (F3 n)= "F3_"++show n
vName (E2 n)= "E2_"++show n
vName (E3 n)= "E3_"++show n

label :: Block -> String
label (F2 n)= "'2/2''"++show n
label (F3 n)= "'3/3''"++show n
label (E2 n)= "'2'"++show n
label (E3 n)= "'3'"++show n

bdiags sig = filter connected $ gtobd <$> graphs sig
bdiagsR deg1 deg2 = concatMap bdiags (concatMap sigs [deg1..deg2])

cuspSplits :: Int -> [[Int]]
cuspSplits deg = sort $ nub  [cuspSplit mo bd | sig <- sigs deg, bd <- bdiags sig, mo <- [posMO sig] ] --mos mo
csMap :: Int -> Int -> Map [Int] (MapO, BlockDiagram) -- maps cusp split to last blockdiagram in the list
csMap deg1 deg2 = foldl (\a (k,v) -> M.insert k v a) M.empty (concatMap csLt [deg1..deg2])
csLt :: Int -> [([Int], (MapO, BlockDiagram))] -- list of (split, BlockDiagram)
csLt deg = nubBy (\x y -> fst x == fst y) [(cuspSplit mo bd, (mo, bd)) | sig <- sigs deg, bd <- bdiags sig, mo <- mos sig ] --mos mo
csList :: Int -> Int -> [([Int], (MapO, BlockDiagram))]
csList deg1 deg2 = concatMap csLt [deg1..deg2]
csL :: Int -> [([Int], (MapO, BlockDiagram))]
csL deg = [(cuspSplit mo bd, (mo, bd)) | sig <- sigs deg, bd <- bdiags sig, mo <- mos sig ]

searchSplit :: Int -> [Int] -> [BlockDiagram]
searchSplit deg split = [bd | sig <- sigs deg, bd <- bdiags sig, mo <- [posMO sig], cuspSplit mo bd == split]
sig2 =(5,3,0,1);
show1 (a, b, c, d) = intercalate "," (map show [a,b,c,d])
sig1=(2,1,0,1)
sig3=(6,4,0,0)
sig4=(1,1,1,0)
sig=sig3
o1 = posMO sig
t0 = gtobd <$> graphs sig
t1 = filter connected $ gtobd <$> graphs sig

cgs sig = filter connected $ gtobd <$> graphs sig
cgsplits sig = sort $ nub $ [cuspSplit s bd |bd <- cgs sig, s<-mos sig]
v1= head t1
t2= (o1 `graphString` ) <$> t1

t5= head $ graphs (4,3,4,3)

fo :: [(MapO, BlockDiagram)] -> String -> IO ()
fo bds file =
     mapM_ (\n -> writeFile (fname n) (uncurry graphString (bds !! (n-1)))
               >> callCommand ("circo "++fname n++" -Tpdf -O")) [1..length bds]
     >> callCommand ("pdftk "++fstrs ++ ".pdf cat output " ++ file)
     >> callCommand "rm exs/tmp*"
     where fstrs = intercalate ".pdf " (map fname [1..length bds])

psig :: BlockDiagram -> MapO
psig (BlockDiagram gt _ _ _ _) =posMO gt

sg bd@(BlockDiagram gt _ _ _ _) =
    writeFile "exs/tmp.gv" (graphString (posMO gt) bd)
    >> callCommand ("circo "++ "exs/tmp.gv" ++ " -Tpdf -O")
    >> callCommand "evince exs/tmp.gv.pdf"

fname :: Int -> String
fname i = "exs/tmp"++show i++".gv"

t3 = (\bd -> ("Diagram", bd, cuspSplit (posMO sig) bd, "\n\n")) <$> t1

out a b= fo (map snd $ csList a b) "gFull.pdf"

outd :: Int -> IO ()
outd deg = fo (map snd $ csList deg deg) $ "pm/cs"++show deg++".pdf"