{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module IRTS.CodeGenCLaSH
  ( codeGenCLaSH
  , createBindingsCLaSH
  )
where

-- External imports
import           Control.Applicative
import           Control.Monad.Reader         (Reader)
import qualified Control.Monad.Reader         as Reader
import           Control.Monad.State          (StateT,lift,liftIO)
import qualified Control.Monad.State.Lazy     as State
import           Data.HashMap.Lazy            (HashMap)
import qualified Data.HashMap.Lazy            as HashMap
import           Data.Maybe                   (catMaybes,fromMaybe)
import           Control.Lens                 ((%=),_1,_2,makeLenses,view)
import qualified Unbound.LocallyNameless.Name as U
import           Unbound.LocallyNameless      (Rep,bind,embed,makeName,name2String,name2Integer,runFreshM,string2Name,unbind)

import Debug.Trace

-- CLaSH-specific import
import qualified CLaSH.Core.DataCon as C
import qualified CLaSH.Core.Pretty as C
import qualified CLaSH.Core.Term as C
import qualified CLaSH.Core.TyCon as C
import qualified CLaSH.Core.Type as C
import qualified CLaSH.Core.TysPrim as C
import qualified CLaSH.Core.Var as C

import CLaSH.Driver
import CLaSH.Driver.Types
import CLaSH.Primitives.Types
import CLaSH.Primitives.Util

-- Local imports
import Core.CaseTree
import Core.Evaluate
import Core.TT

import Idris.AbsSyntax
import Idris.UnusedArgs

import Debug.Trace

type MkTyDConState = (HashMap C.TyConName C.TyCon, HashMap C.TyConName [C.DataCon])
type R    = Reader MkTyDConState
type SR a = StateT MkTyDConState R a

codeGenCLaSH :: BindingMap
             -> PrimMap
             -> IO ()
codeGenCLaSH bindingMap primMap =
  generateVHDL bindingMap HashMap.empty HashMap.empty primMap

createBindingsCLaSH :: Term
                    -> [Name]
                    -> PrimMap
                    -> Idris BindingMap
createBindingsCLaSH tm used primMap = do
  i <- getIState
  let ctxtList  = ctxtAlist (tt_ctxt i)
      dcTyCons  = filter (isCon . snd) ctxtList
      decs      = filter ((`elem` used) . fst) ctxtList
      dcTcState = makeAllTyDataCons (map defToTyDataCon dcTyCons)
      terms     = map (defToTerm primMap dcTcState) decs
  liftIO $ putStrLn (unlines $ map (\(_,t) -> show t) $ HashMap.toList $ fst dcTcState)
  liftIO $ putStrLn (unlines $ map (\(t,dcs) -> show t ++ ": " ++ show dcs) $ HashMap.toList $ snd dcTcState)
  mapM traceUnused used
  return $! HashMap.fromList (catMaybes terms)

isCon :: Def -> Bool
isCon (TyDecl _ _) = True
isCon _ = False

defToTyDataCon :: (Name,Def)
               -> (Name,NameType,Type)
defToTyDataCon (n,TyDecl nt ty) = (n,nt,ty)
defToTyDataCon nd = error $ "Not a TyDec" ++ show nd

isTyConDef :: (Name,NameType,Type)
           -> Bool
isTyConDef (_,TCon _ _,_) = True
isTyConDef _              = False

isDConDef :: (Name,NameType,Type)
          -> Bool
isDConDef (_,DCon _ _,_) = True
isDConDef _              = False

makeAllTyDataCons :: [(Name,NameType,Type)]
                  -> (HashMap C.TyConName C.TyCon,HashMap C.TyConName [C.DataCon])
makeAllTyDataCons tyDecls =
  let s = Reader.runReader (State.execStateT
                              (do mapM_ makeTyCon (filter isTyConDef tyDecls)
                                  mapM_ makeDataCon (filter isDConDef tyDecls)
                              )
                              (HashMap.empty,HashMap.empty)
                           ) s
  in  s

makeDataCon,makeTyCon :: (Name,NameType,Type) -> SR ()

makeDataCon k@(n,DCon t a,ty) = do
  dcTy <- lift $ toCoreType [] ty
  let (tyVars,argTys,resTy) = splitFunForallTy dcTy
      dc = C.MkData { C.dcName       = toCoreName n
                    , C.dcTag        = t
                    , C.dcType       = dcTy
                    , C.dcArgTys     = argTys
                    , C.dcUnivTyVars = map C.varName tyVars
                    , C.dcExtTyVars  = []
                    }
  case (C.splitTyConAppM resTy) of
    Just (tc,_) ->
      _2 %= HashMap.insertWith (++) (C.tyConName tc) [dc]
    Nothing -> error $ "Huh?: " ++ show ty

makeTyCon (n,TCon t a,ty) = do
  let tcName = toCoreName n
  dcs  <- lift $ tcDataCons tcName
  tcKi <- lift $ toCoreType [] ty
  let tc = C.AlgTyCon { C.tyConName   = tcName
                      , C.tyConKind   = tcKi
                      , C.tyConArity  = a
                      , C.algTcRhs    = C.DataTyCon dcs
                      , C.isDictTyCon = False
                      }
  _1 %= HashMap.insert tcName tc

tcDataCons :: C.TyConName
           -> R [C.DataCon]
tcDataCons tc = fmap ( fromMaybe (error $ "No DataCons found for: " ++ show tc)
                     . HashMap.lookup tc
                     )
              $ view _2

toTyCon :: C.TyConName
        -> R C.TyCon
toTyCon tcN = fmap ( fromMaybe (error $ "No TyCon named: " ++ name2String tcN)
                   . HashMap.lookup tcN
                   )
            $ view _1

toCoreName :: Rep a => Name -> U.Name a
toCoreName (UN s)   = string2Name s
toCoreName (NS n s) = prefixName (showSep "." (reverse s) ++ ".") (toCoreName n)
toCoreName (MN i s) = makeName s (toInteger i)
toCoreName NErased  = string2Name "___ERASED___"

prefixName :: String -> U.Name a -> U.Name a
prefixName p (U.Nm r (s,i)) = U.Nm r (p++s,i)
prefixName _ n              = n

replaceNameIndex :: Integer -> U.Name a -> U.Name a
replaceNameIndex i (U.Nm r (s,_)) = U.Nm r (s,i)
replaceNameIndex _ n              = n

toCoreType :: [(C.TyName,C.Kind)] -> Type -> R C.Type
toCoreType ns t@(Bind n@(MN _ _) (Pi ki) tt) = do
  let tvN = toCoreName n
  C.mkFunTy <$> (toCoreType ns ki) <*> (toCoreType ((tvN,undefined):ns) tt)
toCoreType ns t@(Bind n@(NS (UN ('!':_)) _) (Pi ki) tt) = do
  let tvN = toCoreName n
  C.mkFunTy <$> (toCoreType ns ki) <*> (toCoreType ((tvN,undefined):ns) tt)
toCoreType ns t@(Bind n (Pi ki) tt) = do
  kiC <- toCoreType ns ki
  let tvN = toCoreName n
      tv  = C.TyVar tvN (embed kiC)
  C.ForAllTy <$> (bind tv <$> toCoreType ((tvN,kiC):ns) tt)
toCoreType ns t@(TType _) = return C.liftedTypeKind
toCoreType ns t@(P (TCon _ _) n _) = C.mkTyConApp <$> toTyCon (toCoreName n) <*> pure []
toCoreType ns t@(App ty1 ty2) = C.AppTy <$> toCoreType ns ty1 <*> toCoreType ns ty2
toCoreType ns t@(V i) = return $ (uncurry . flip) C.mkTyVarTy $ (ns !! i)
toCoreType ns t = error $ "toCoreType: " ++ show t ++ (show ns) ++ showTerm t

defToTerm :: PrimMap
          -> MkTyDConState
          -> (Name,Def)
          -> Maybe (C.TmName,(String,(C.Type,C.Term)))
defToTerm _ _ _ = Nothing

toCoreTerm :: PrimMap
           -> MkTyDConState
           -> Term
           -> C.Term
toCoreTerm _ _ _ = undefined

splitFunTy :: C.Type -> ([C.Type],C.Type)
splitFunTy = go []
  where
    go args (C.tyView -> C.FunTy arg res) = go (arg:args) res
    go args ty                            = (reverse args,ty)

splitForallTy :: C.Type -> ([C.TyVar],C.Type)
splitForallTy = go []
  where
    go args (C.ForAllTy b) = let (tv,ty) = runFreshM (unbind b)
                             in  go (tv:args) ty
    go args ty             = (reverse args,ty)

splitFunForallTy :: C.Type -> ([C.TyVar],[C.Type],C.Type)
splitFunForallTy = go [] []
  where
    go tvs args (C.ForAllTy b) = let (tv,ty) = runFreshM (unbind b)
                                 in  go (tv:tvs) args ty
    go tvs args (C.tyView -> C.FunTy arg res) = go tvs (arg:args) res
    go tvs args ty                            = (reverse tvs,reverse args,ty)

collectArgs :: Term -> ([Term],Term)
collectArgs = go []
  where
    go args (App e1 e2) = go (e2:args) e1
    go args e           = (args,e)

collectBndrs :: Term -> ([Binder Term],Term)
collectBndrs = go []
 where
    go bndrs (Bind _ bndr tm) = go (bndr:bndrs) tm
    go bndrs e                = (reverse bndrs, e)

showTerm :: Term -> String
showTerm (App e1 e2)       = "App (" ++ showTerm e1 ++ ") (" ++ showTerm e2 ++ ")"
showTerm (Constant c)      = "Constant (" ++ show c ++ ")"
showTerm Impossible        = "Impossible"
showTerm Erased            = "Erased"
showTerm (P nt n tm)        = "P {" ++ show nt ++ "} " ++ show n ++ " (" ++ showTerm tm ++ ")"
showTerm (V v)             = "V " ++ show v
showTerm (Bind n bndr tm)  = "Bind " ++ show n ++ " (" ++ showBinder bndr ++ ") (" ++ showTerm tm ++ ")"
showTerm (Proj tm i)       = "Proj " ++ show i ++ " (" ++ show tm ++ ")"
showTerm (TType uexp)      = "TType " ++ show uexp

showBinder (Pi tm) = "Pi (" ++ showTerm tm ++ ")"
showBinder b       = show b
