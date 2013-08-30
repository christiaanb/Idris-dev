{-# OPTIONS_GHC -Wall -Werror #-}

module IRTS.CodeGenCLaSH
  ( codeGenCLaSH
  , createBindingsCLaSH
  )
where

-- -- External imports
import           Control.Arrow           (second)
import           Control.Lens            ((^.),_3)
import           Data.Graph.Inductive    (Gr,LNode,lsuc,mkGraph,iDom)
import           Data.HashMap.Lazy       (HashMap)
import qualified Data.HashMap.Lazy       as HashMap
import qualified Data.List               as List
import           Data.Maybe              (catMaybes,listToMaybe)
import           Unbound.LocallyNameless (bind,embed,name2String,rec,runFreshM)

-- CLaSH imports
import qualified CLaSH.Core.DataCon      as C
import qualified CLaSH.Core.Pretty       as C
import qualified CLaSH.Core.Term         as C
import qualified CLaSH.Core.Type         as C
import qualified CLaSH.Core.Util         as C
import qualified CLaSH.Core.Var          as C

import CLaSH.Driver                     (generateVHDL)
import CLaSH.Driver.Types               (BindingMap)
import CLaSH.Normalize.Util             (callGraph,recursiveComponents)
import CLaSH.Primitives.Types           (PrimMap)
import CLaSH.Rewrite.Types              (DebugLevel(..))
import CLaSH.Util                       (traceIf)

-- Local imports
import Core.Evaluate
import Core.TT
import Idris.AbsSyntax                  hiding (logLvl)
import IRTS.CLaSH.Idris2Core
import IRTS.CLaSH.NetlistTypes
import IRTS.CLaSH.Util

codeGenCLaSH :: Int
             -> BindingMap
             -> PrimMap
             -> IO ()
codeGenCLaSH logLvl bindingMap primMap =
  generateVHDL bindingMap primMap idrisTypeToHWType dbgLevel
  where
    dbgLevel = case logLvl of
      0 -> DebugNone
      1 -> DebugNone
      2 -> DebugFinal
      _ -> DebugApplied

createBindingsCLaSH :: Int
                    -> IState
                    -> [Name]
                    -> PrimMap
                    -> BindingMap
createBindingsCLaSH logLvl iState used primMap =
  let ctxtList  = ctxtAlist (tt_ctxt iState)
      dcTyCons  = filter (isCon . snd) ctxtList
      decs      = filter ((`elem` used) . fst) ctxtList
      dcTcState = makeAllTyDataCons (map defToTyDataCon dcTyCons)
      terms     = catMaybes $ map (defToTerm logLvl primMap dcTcState) decs
      terms'    = termPrep terms
  in traceIf (logLvl >= 1) (unlines $ map (\(n,d) -> C.showDoc n ++ ": " ++ C.showDoc (C.dcType d)) $ HashMap.toList (dcTcState ^. _3))
     terms'


termPrep :: [(C.TmName,(C.Type,C.Term))]
            -> BindingMap
termPrep bndrs = maybe (HashMap.empty) id $ do
  (topEntity,_) <- listToMaybe $ filter (List.isSuffixOf "topEntity" . name2String . fst) bndrs
  let depGraph = callGraph [] (HashMap.fromList $ map (second snd) bndrs) topEntity
      used     = HashMap.fromList depGraph
      testInp  = filter (List.isSuffixOf "testInput" . name2String . fst) bndrs
      expOutp  = filter (List.isSuffixOf "expectedOutput" . name2String . fst) bndrs
      bndrs'   = HashMap.fromList $ concat [filter ((`HashMap.member` used) . fst) bndrs,testInp,expOutp]
      rcs      = recursiveComponents depGraph
      dropped  = map (lambdaDrop bndrs' used) rcs
      bndrs''  = foldr (\(k,v) b -> HashMap.insert k v b) bndrs' dropped
  return bndrs''

lambdaDrop :: BindingMap
           -> HashMap C.TmName [C.TmName]
           -> [C.TmName]
           -> (C.TmName,(C.Type,C.Term))
lambdaDrop bndrs cfg cyc@(root:_) = block
  where
    doms  = dominator cfg cyc
    block = blockSink bndrs doms (0,root)

lambdaDrop _ _ [] = error "Can't lambdadrop empty cycle"

blockSink :: BindingMap
          -> Gr C.TmName C.TmName
          -> LNode C.TmName
          -> (C.TmName,(C.Type,C.Term))
blockSink bndrs doms (nId,tmName) = (tmName,(ty,newTm))
  where
    (ty,tm) = bndrs HashMap.! tmName
    sucTm   = lsuc doms nId
    tmS     = map (blockSink bndrs doms) sucTm
    bnds    = map (\(tN,(ty',tm')) -> (C.Id tN (embed ty'),embed tm')) tmS
    (tmArgs,tmExpr) = runFreshM $ C.collectBndrs tm
    newTm   = case sucTm of
                [] -> tm
                _  -> C.mkAbstraction (C.Letrec $ bind (rec bnds) tmExpr) tmArgs


dominator :: HashMap C.TmName [C.TmName]
          -> [C.TmName]
          -> Gr C.TmName C.TmName
dominator cfg cyc = mkGraph nodes (map (\(e,b) -> (b,e,nodesM HashMap.! e)) doms)
  where
    nodes    = zip [0..] cyc
    nodesM   = HashMap.fromList nodes
    nodesI   = HashMap.fromList $ zip cyc [0..]
    cycEdges = HashMap.map ( map (nodesI HashMap.!)
                           . filter (`elem` cyc)
                           )
             $ HashMap.filterWithKey (\k _ -> k `elem` cyc) cfg
    edges    = concatMap (\(i,n) -> zip3 (repeat i) (cycEdges HashMap.! n) (repeat ())
                         ) nodes
    graph    = mkGraph nodes edges :: Gr C.TmName ()
    doms     = iDom graph 0
