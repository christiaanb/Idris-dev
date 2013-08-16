{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module IRTS.CodeGenCLaSH
  ( codeGenCLaSH
  , createBindingsCLaSH
  )
where

-- External imports
import           Control.Arrow                (first)
import           Control.Applicative          ((<$>),(<*>),pure)
import           Control.Monad.Trans          (MonadTrans)
import           Control.Monad.Trans.Error    (ErrorT(..))
import           Control.Monad.Trans.Maybe    (MaybeT(..),runMaybeT)
import           Control.Monad.Reader         (Reader)
import qualified Control.Monad.Reader         as Reader
import           Control.Monad.State          (StateT,lift,liftIO)
import qualified Control.Monad.State.Lazy     as State
import           Data.ByteString.Lazy.Char8   (pack)
import           Data.Either                  (lefts)
import           Data.HashMap.Lazy            (HashMap)
import qualified Data.HashMap.Lazy            as HashMap
import           Data.Maybe                   (catMaybes,fromMaybe)
import           Control.Lens                 ((%=),_1,_2,_3,makeLenses,view,(^.))
import qualified Unbound.LocallyNameless.Name as U
import           Unbound.LocallyNameless.Ops  (unsafeUnbind)
import           Unbound.LocallyNameless      (Bind,Rep,bind,embed,makeName,name2String,name2Integer,rebind,runFreshM,runFreshMT,string2Name,unembed)

import Debug.Trace

-- CLaSH-specific import
import qualified CLaSH.Core.DataCon as C
import qualified CLaSH.Core.Literal as C
import qualified CLaSH.Core.Pretty  as C
import qualified CLaSH.Core.Prim    as C
import qualified CLaSH.Core.Term    as C
import qualified CLaSH.Core.TyCon   as C
import qualified CLaSH.Core.Type    as C
import qualified CLaSH.Core.TysPrim as C
import qualified CLaSH.Core.Util    as C
import qualified CLaSH.Core.Var     as C
import qualified CLaSH.Rewrite.Util as C

import CLaSH.Driver
import CLaSH.Driver.Types
import CLaSH.Netlist.Util (coreTypeToHWType)
import CLaSH.Netlist.Types (HWType(..))
import CLaSH.Primitives.Types
import CLaSH.Primitives.Util
import CLaSH.Rewrite.Types (DebugLevel(..))
import CLaSH.Util (MonadUnique(..),curLoc,traceIf)

-- Local imports
import Core.CaseTree
import Core.Evaluate
import Core.TT

import Idris.AbsSyntax
import Idris.UnusedArgs

import Debug.Trace

type MkTyDConState = (HashMap C.TyConName C.TyCon, HashMap C.TyConName [C.DataCon], HashMap C.DcName C.DataCon)
type R    = Reader MkTyDConState
type SR a = StateT MkTyDConState R a
type CoreAlt = Bind C.Pat C.Term

instance Monad m => MonadUnique (StateT Int m) where
  getUniqueM = do
    supply <- State.get
    State.modify (+1)
    return supply

codeGenCLaSH :: BindingMap
             -> PrimMap
             -> IO ()
codeGenCLaSH bindingMap primMap =
  generateVHDL bindingMap HashMap.empty HashMap.empty primMap idrisTypeToHWType DebugNone

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
  liftIO $ putStrLn $ unlines $ map (\(n,d) -> C.showDoc n ++ ": " ++ C.showDoc (C.dcType d)) $ HashMap.toList (dcTcState ^. _3)
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
                  -> MkTyDConState
makeAllTyDataCons tyDecls =
  let s = Reader.runReader (State.execStateT
                              (do mapM_ makeTyCon (filter isTyConDef tyDecls)
                                  mapM_ makeDataCon (filter isDConDef tyDecls)
                              )
                              (HashMap.empty,HashMap.empty,HashMap.empty)
                           ) s
  in  s

makeDataCon,makeTyCon :: (Name,NameType,Type) -> SR ()

makeDataCon k@(n,DCon t a,ty) = do
  dcTyM <- lift $ runMaybeT $ toCoreType False [] [] ty
  dcTy  <- case dcTyM of
             (Just t) -> return t
             Nothing  -> error $ "makeDataCon: " ++ showTerm ty
  let (args,resTy)     = splitFunForallTy dcTy
      (C.TyConApp _ l) = C.tyView resTy
      (tvs,ids)        = splitAt (length l) args
      tyVars           = lefts tvs
      argTys           = map (either (unembed . C.varKind) id) ids
      dcName = toCoreName n
      dc = C.MkData { C.dcName       = dcName
                    , C.dcTag        = t
                    , C.dcType       = dcTy
                    , C.dcArgTys     = argTys
                    , C.dcUnivTyVars = map C.varName tyVars
                    , C.dcExtTyVars  = []
                    }

      tcName   = toCoreName n
      liftedDc = C.AlgTyCon { C.tyConName = tcName
                            , C.tyConKind = dcTy
                            , C.tyConArity = (length tyVars + length argTys)
                            , C.algTcRhs = C.DataTyCon []
                            , C.isDictTyCon = False
                            }

  case (C.splitTyConAppM resTy) of
    Just (tc,_) -> do
      _1 %= HashMap.insert tcName liftedDc
      _2 %= HashMap.insertWith (++) (C.tyConName tc) [dc]
      _3 %= HashMap.insert dcName dc
    Nothing -> error $ "Huh?: " ++ show ty

makeTyCon (n,TCon t a,ty) = do
  let tcName = toCoreName n
  dcs  <- lift $ tcDataCons tcName
  tcKiM <- lift $ runMaybeT $ toCoreType False [] [] ty
  tcKi <- case tcKiM of
             (Just k) -> return k
             Nothing  -> error $ "makeTyCon: " ++ showTerm ty
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

toDataCon :: C.DcName
          -> R C.DataCon
toDataCon dcN = fmap ( fromMaybe (error $ "No DataCon named: " ++ name2String dcN)
                   . HashMap.lookup dcN
                   )
              $ view _3

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

toCoreTypeT :: Bool -> [(C.TyName,(C.Kind,Type))] -> [(Name,Either C.Id C.TyVar)] -> Type -> MaybeT R C.Type
toCoreTypeT refKI ns bndrs t = do
  tC <- toCoreType refKI ns bndrs t
  return $! toCoreTypeT' tC

toCoreTypeT' :: C.Type -> C.Type
toCoreTypeT' tC = case (C.tyView tC) of
  (C.TyConApp tc args) -> case (name2String $ C.tyConName tc) of
      "Builtins.fromInteger" -> (last args)
      "@Builtins.Num$[Nat].0.Builtins.#!fromInteger" -> (last args)
      "@Builtins.Num$[Nat].0.Builtins.#!fromInteger.0.#fromInteger'" -> (last args)
      _ -> C.mkTyConApp tc (map toCoreTypeT' args)
  (C.FunTy arg res) -> C.mkFunTy (toCoreTypeT' arg) (toCoreTypeT' res)
  _ -> tC

toCoreType :: Bool -> [(C.TyName,(C.Kind,Type))] -> [(Name,Either C.Id C.TyVar)] -> Type -> MaybeT R C.Type
toCoreType refKI ns bndrs t@(Bind n (Pi ki) tt)
  | looksLikeKind refKI ns ki
  = do
    kiC <- toCoreKind ns ki
    let tvN = toCoreName n
        tv  = C.TyVar tvN (embed kiC)
    C.ForAllTy <$> (bind tv <$> toCoreType refKI ((tvN,(kiC,ki)):ns) bndrs tt)

toCoreType refKI ns bndrs t@(Bind n (Pi arg) res) = do
  let tvN = toCoreName n
  C.mkFunTy <$> toCoreType refKI ns bndrs arg <*> toCoreType refKI ((tvN,(error $ "unexpected kind: " ++ show arg,arg)):ns) bndrs res

toCoreType refKI ns bndrs t@(P (TCon _ _) n _) = C.mkTyConTy <$> lift (toTyCon (toCoreName n))
toCoreType refKI ns bndrs t@(P (DCon _ _) n _) = C.mkTyConTy <$> lift (toTyCon (toCoreName n))
toCoreType refKI ns bndrs t@(P Ref n _)        = return (C.mkTyConTy $ C.mkPrimTyCon (toCoreName n) C.liftedTypeKind 0 C.VoidRep)
toCoreType refKI ns bndrs t@(P Bound n _)      = case lookup n bndrs of
                                                   Just (Left id_) -> return $! C.mkTyVarTy (unembed $ C.varType id_) (U.translate $ C.varName id_)
                                                   Just (Right tv) -> return $! C.mkTyVarTy (unembed $ C.varKind tv) (C.varName tv)
                                                   Nothing -> error ("toCoreType Bound notfound: " ++ showTerm t ++ show bndrs)
toCoreType refKI ns bndrs t@(App ty1 ty2) = C.AppTy <$> toCoreType refKI ns bndrs ty1 <*> toCoreType refKI ns bndrs ty2
toCoreType refKI ns bndrs t@(V i) = let (tyN,(tyK,_)) = maybe (error ("Index(toCoreType): " ++ show i ++ " not found in: " ++ show ns)) id (safeIndex ns i)
                                    in return $! C.mkTyVarTy tyK tyN
toCoreType refKI ns bndrs t@(Constant (AType (ATInt ITBig))) = return C.intPrimTy -- return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "GHC.Integer.Type.Integer") C.liftedTypeKind 0 C.IntRep)
toCoreType refKI ns bndrs t@(Constant (AType (ATInt ITChar))) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "Char") C.liftedTypeKind 0 C.VoidRep)
toCoreType refKI ns bndrs t@(Constant (AType (ATInt ITNative))) = return C.intPrimTy -- return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "GHC.Integer.Type.Integer") C.liftedTypeKind 0 C.IntRep)
toCoreType refKI ns bndrs t@(Constant (AType (ATInt (ITFixed _)))) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name $ show t) C.liftedTypeKind 0 C.IntRep)
toCoreType refKI ns bndrs t@(Constant (AType (ATInt (ITVec _ _)))) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name $ show t) C.liftedTypeKind 0 C.IntRep)
toCoreType refKI ns bndrs t@(Constant (AType ATFloat)) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "Float") C.liftedTypeKind 0 C.VoidRep)
toCoreType refKI ns bndrs t@(Constant (Str s))               = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name s) C.liftedTypeKind 0 C.VoidRep)
toCoreType refKI ns bndrs t@(Constant StrType) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "String") C.liftedTypeKind 0 C.VoidRep)
toCoreType refKI ns bndrs t@(Constant PtrType) = return C.voidPrimTy
toCoreType refKI ns bndrs t@(Constant (BI i)) = return $! C.LitTy (C.NumTy $! fromInteger i)
toCoreType refKI ns bndrs t@(Constant c) = error $ "toCoreType: Constant(" ++ showConstant c ++ ")"
toCoreType refKI ns bndrs t@(TType _) = return C.liftedTypeKind
toCoreType refKI _ _ t = error $ "toCoreType: " ++ show t


looksLikeKind :: Bool
              -> [(C.TyName,(C.Kind,Type))]
              -> Type
              -> Bool
looksLikeKind _ ns (TType _)           = True
looksLikeKind refKI ns (Bind n (Pi ki) tt) = looksLikeKind refKI ns ki && looksLikeKind refKI ((toCoreName n,(error "lookslikekind",ki)):ns) tt
looksLikeKind _ ns (P (TCon _ _) n@(NS (UN "Nat") ["Nat","Prelude"]) _) = True
-- looksLikeKind True ns (V i) = maybe (error ("Index: " ++ show i ++ " not found in: " ++ show ns)) (looksLikeKind True ns . snd . snd) (safeIndex ns i)
looksLikeKind _ _ k                   = False

toCoreKind :: [(C.TyName,(C.Kind,Type))] -> Type -> MaybeT R C.Kind
toCoreKind ns t@(TType _) = return C.liftedTypeKind
toCoreKind ns t@(Bind n (Pi arg) res) = do
  let tvN = toCoreName n
  C.mkFunTy <$> toCoreKind ns arg <*> toCoreKind ((tvN,error $ "unexpected box: " ++ show arg):ns) res
toCoreKind ns t@(P (TCon _ _) n _) = C.mkTyConTy <$> lift (toTyCon (toCoreName n))
toCoreKind ns t@(V i) = toCoreKind ns (snd $ snd (ns !! i))
toCoreKind ns t = error ("toCoreKind: " ++ show t ++ "\n" ++ showTerm t)

defToTerm :: PrimMap
          -> MkTyDConState
          -> (Name,Def)
          -> Maybe (C.TmName,(String,(C.Type,C.Term)))
defToTerm primMap _ (n,_)
  | HashMap.member (pack $ name2String $ (toCoreName n :: C.TmName)) primMap = Nothing
defToTerm primMap s (n,CaseOp _ _ ty _ _ ns sc _ _) = trace ("== " ++ show n ++ " ==:\nTy: " ++ show ty ++ "\nBndrs: " ++ show ns ++ "\nTm:\n" ++ show sc) $ flip Reader.runReader s $ do
  let tmName   = toCoreName n
      tmString = show n
  tyC <- fmap (maybe (error $ "defToTerm: " ++ showTerm ty) id) $ runMaybeT $ toCoreTypeT False [] [] ty
  let (args,resTy) = splitFunForallTy tyC
      bndrs        = zipWith (\n ds -> case ds of { Left (C.TyVar n' t) -> Right (C.TyVar n' t)
                                                  ; Right t             -> Left  (C.Id (toCoreName n) (embed t))
                                                  }) ns args
  result <- runMaybeT $ do { scC <- scToTerm primMap [] (zip ns bndrs) sc
                           ; let termC  = C.mkAbstraction scC bndrs
                           ; let res    = (tmName,(tmString,(tyC,termC)))
                           ; let resTy  = runFreshM $ C.termType termC
                           ; trace ("CoreTy: " ++ C.showDoc tyC ++ "\nCoreTerm:\n" ++ C.showDoc termC) $
                               traceIf (tyC /= resTy) ("TYPES DIFFER for " ++ tmString ++ ":\nExpected: " ++ C.showDoc tyC ++ "\nCalculated: " ++ C.showDoc resTy) $
                                 return res
                           }
  return result
  -- return Nothing

defToTerm _ _ _ = Nothing

scToTerm :: PrimMap
         -> [(C.TyName,(C.Kind,Type))]
         -> [(Name,Either C.Id C.TyVar)]
         -> SC
         -> MaybeT R C.Term
scToTerm primMap tvs bndrs (STerm t) = toCoreTerm primMap tvs bndrs t
scToTerm primMap tvs bndrs sc@(Case n alts) = do
  let scrut = case lookup n bndrs of
                     Just (Left (C.Id n' t'))     -> C.Var (unembed t') n'
                     Just (Right (C.TyVar n' t')) -> C.Prim (C.PrimCo (C.mkTyVarTy (unembed t') n'))
                     Nothing -> error ("scrut: " ++ show bndrs ++ show sc)
  alts <- mapM (toCoreAlt primMap tvs bndrs) alts
  ty   <- MaybeT $ return (case alts of
                            { []      -> Nothing
                            ; (alt:_) -> Just $ runFreshM (C.termType (snd $ unsafeUnbind alt))
                            }
                          )
  return $! C.Case scrut ty alts


scToTerm _ _ _ sc = error ("scToTerm: " ++ show sc)

toCoreTerm :: PrimMap
           -> [(C.TyName,(C.Kind,Type))]
           -> [(Name,Either C.Id C.TyVar)]
           -> Term
           -> MaybeT R C.Term
toCoreTerm primMap = term
  where
    term :: [(C.TyName,(C.Kind,Type))] -> [(Name,Either C.Id C.TyVar)] -> Term -> MaybeT R C.Term
    term tvs bndrs (P nt n t) = pvar tvs bndrs nt n t

    term _ bndrs (V i) =
      case safeIndex bndrs i of
        Just bndr -> case snd bndr of
          Left  (C.Id n t)    -> return $! C.Var (unembed t) n
          Right (C.TyVar n t) -> return $! C.Prim (C.PrimCo (C.mkTyVarTy (unembed t) n))
        Nothing -> error ("Index(term): " ++ show i ++ " not found in: " ++ show bndrs)

    term tvs bndrs (Bind n (Lam bndr) t) =
      case looksLikeKind True tvs bndr of
        True  -> do
          bndrKi <- toCoreKind tvs bndr
          let tvN = toCoreName n
              tv  = C.TyVar tvN (embed bndrKi)
          tC     <- term ((tvN,(bndrKi,bndr)):tvs) ((n,Right tv):bndrs) t
          return $! C.TyLam $! bind tv tC
        False -> do
          bndrTy <- toCoreTypeT True tvs bndrs bndr
          let id_ = C.Id (toCoreName n) (embed bndrTy)
          tC     <- term ((toCoreName n,(error "lookslikekind",bndr)):tvs) ((n,Left id_):bndrs) t
          return $! C.Lam $! bind id_ tC

    term tvs bndrs (Bind n (Pi bndr) t) =
      case looksLikeKind True tvs bndr of
        True  -> do
          bndrKi <- toCoreKind tvs bndr
          let tvN = toCoreName n
              tv  = C.TyVar (toCoreName n) (embed bndrKi)
          tC     <- term ((tvN,(bndrKi,bndr)):tvs) ((n,Right tv):bndrs) t
          -- tC     <- term (tvs) ((n,Right tv):bndrs) t
          return $! C.TyLam $! bind tv tC
        False -> do
          bndrTy <- toCoreTypeT True tvs bndrs bndr
          let id_ = C.Id (toCoreName n) (embed bndrTy)
          tC     <- term ((toCoreName n,(error "lookslikekind",bndr)):tvs) ((n,Left id_):bndrs) t
          return $! C.Lam $! bind id_ tC

    term _ _ e@(Bind n bndr t) = error ("term(Bind n bndr t): " ++ showTerm e)

    term tvs bndrs (App t1 t2) = do
      t1C <- term tvs bndrs t1
      t2C <- term tvs bndrs t2
      tyM <- lift $ isTypeLike t2C
      case tyM of
        Nothing -> return (C.App t1C t2C)
        Just ty -> return (C.TyApp t1C $ toCoreTypeT' ty)

    term tvs bndrs (Constant c) = constant tvs bndrs c

    term tvs bndrs (Proj t i) = do
      tP <- runFreshMT $ (flip State.evalStateT) (1 :: Int) $ do { tC  <- lift $ lift $ term tvs bndrs t
                                                                 ; tP' <- C.mkSelectorCase "toCoreTerm" [] tC 1 i
                                                                 ; return tP'
                                                                 }
      return tP

    term _ _ Erased           = error $ "termErased         : "
    term _ _ Impossible       = error $ "termImpossible     : "
    term _ _ (TType _)        = error $ "termTType:"

    pvar tvs bndrs nt n t = do
      let nC   = toCoreName n :: C.TmName
          nBS  = pack (name2String nC)
      case HashMap.lookup nBS primMap of
        Just (BlackBox {}) -> do
          tC <- toCoreTypeT True tvs bndrs t
          return $ C.Prim (C.PrimFun nC tC)
        Just (Primitive _ Dictionary) -> do
          tC <- toCoreTypeT True tvs bndrs t
          let liftedFun = C.AlgTyCon { C.tyConName = toCoreName n
                                     , C.tyConKind = tC
                                     , C.tyConArity = length $ fst $ splitFunForallTy tC
                                     , C.algTcRhs = C.DataTyCon []
                                     , C.isDictTyCon = False
                                     }
          return $ C.Prim (C.PrimCo (C.mkTyConTy liftedFun))
        Nothing -> case nt of
          (DCon _ _) -> do
            dc <- lift $ toDataCon (toCoreName n)
            return $! (C.Data dc)
          Bound -> case lookup n bndrs of
            Just (Left (C.Id n' t')) -> return $! C.Var (unembed t') n'
            Just (Right (C.TyVar n' t')) -> return $! C.Prim (C.PrimCo (C.mkTyVarTy (unembed t') n'))
            Nothing -> error $ "Bound var " ++ show (n,t) ++ " not found in: " ++ show bndrs
          Ref -> do
            tC <- toCoreTypeT True tvs bndrs t
            let (_,resTy) = splitFunForallTy tC
            if resTy == C.liftedTypeKind
              then trace ("pvar REF(TY): " ++ show n ++ " : " ++ show t) $! return $! C.Prim (C.PrimCo $ C.mkTyVarTy tC (toCoreName n))
              else trace ("pvar REF(TM): " ++ show n ++ " : " ++ show t) $! return $! C.Var tC nC
          (TCon _ _) -> do
            tc <- lift $ toTyCon (toCoreName n)
            return $! C.Prim (C.PrimCo (C.mkTyConTy tc))

    constant tvs bndrs c@(AType _) = C.Prim <$> C.PrimCo <$> toCoreTypeT True tvs bndrs (Constant c)
    constant tvs bndrs c@(StrType) = C.Prim <$> C.PrimCo <$> toCoreTypeT True tvs bndrs (Constant c)
    constant tvs bndrs c@(PtrType) = C.Prim <$> C.PrimCo <$> toCoreTypeT True tvs bndrs (Constant c)
    constant tvs bndrs (BI i)      = return $! C.Literal $! C.IntegerLiteral i
    constant tvs bndrs (Str s)     = return $! C.Literal $! C.StringLiteral s
    constant tvs bndrs c           = error $ "constant: " ++ showConstant c

toCoreAlt :: PrimMap
          -> [(C.TyName,(C.Kind,Type))]
          -> [(Name,Either C.Id C.TyVar)]
          -> CaseAlt
          -> MaybeT R CoreAlt
toCoreAlt primMap tvs bndrs (ConCase n i ns sc) = do
   dc <- lift $ toDataCon (toCoreName n)
   let tys = map (either (unembed . C.varKind) id) . fst . splitFunForallTy $ C.dcType dc
       ids = zipWith (\n t -> C.Id (toCoreName n) (embed t)) ns tys
       idsR = catMaybes $ zipWith (\n t -> case t of
                                             Left _   -> Nothing
                                             Right ty -> Just $! C.Id (toCoreName n) (embed ty)
                                  ) ns (fst . splitFunForallTy $ C.dcType dc)
   t  <- scToTerm primMap tvs (zip ns (map Left ids) ++ bndrs) sc
   return $! bind (C.DataPat (embed dc) (rebind [] idsR)) t

toCoreAlt primMap tvs bndrs (ConstCase (I i) sc) = do
  t <- scToTerm primMap tvs bndrs sc
  return $! bind (C.LitPat (embed (C.IntegerLiteral $ toInteger i))) t

toCoreAlt primMap tvs bndrs (DefaultCase sc) =
  bind <$> pure C.DefaultPat <*> scToTerm primMap tvs bndrs sc

toCoreAlt _ _ _ a = error $ "OtherAlt: " ++ show a

isTypeLike :: C.Term
           -> R (Maybe C.Type)
isTypeLike (C.Prim (C.PrimCo t)) = return $! Just t
-- isTypeLike (C.Prim ())
isTypeLike (C.TyApp t ty)        = do tyM <- isTypeLike t
                                      case tyM of
                                        Just ty' -> return $! Just $! C.AppTy ty' ty
                                        Nothing  -> return $! Nothing
isTypeLike (C.Lam b)             = do let (bndr,res) = unsafeUnbind b
                                      tyM <- isTypeLike res
                                      case tyM of
                                        Just ty' -> return $! Just $! C.mkFunTy (unembed $ C.varType bndr) ty'
                                        Nothing  -> return $! Nothing
isTypeLike (C.App e (C.Data dc)) = do tyM <- isTypeLike e
                                      case tyM of
                                        Just ty' -> do tc <- toTyCon (U.translate $ C.dcName dc)
                                                       return $! Just (C.AppTy ty' (C.mkTyConTy tc))
                                        Nothing  -> return $! Nothing
isTypeLike (C.App e (C.Literal (C.IntegerLiteral i))) = do tyM <- isTypeLike e
                                                           case tyM of
                                                             Just ty' -> return $! Just (C.AppTy ty' (C.LitTy (C.NumTy $ fromInteger i)))
                                                             Nothing  -> return $! Nothing
isTypeLike t                     = return $! Nothing


idrisTypeToHWType ::
  C.Type
  -> Maybe (Either String HWType)
idrisTypeToHWType ty@(C.tyView -> C.TyConApp tc args) = runErrorT $
  case (name2String $ C.tyConName tc) of
    "__INT__" -> return Integer
    "Prelude.Vect.Vect" -> do
      let [szTy,elTy] = args
      sz     <- tyNatSize szTy
      elHWTy <- ErrorT $ return $ coreTypeToHWType idrisTypeToHWType elTy
      return $ Vector sz elHWTy
    _ -> ErrorT $ Nothing

idrisTypeToHWType _ = Nothing

tyNatSize ::
  C.Type
  -> ErrorT String Maybe Int
tyNatSize (C.LitTy (C.NumTy i)) = return i
tyNatSize t                     = fail $ $(curLoc) ++ "Can't convert tyNat: " ++ show t


splitFunTy :: C.Type -> ([C.Type],C.Type)
splitFunTy = go []
  where
    go args (C.tyView -> C.FunTy arg res) = go (arg:args) res
    go args ty                            = (reverse args,ty)

splitForallTy :: C.Type -> ([C.TyVar],C.Type)
splitForallTy = go []
  where
    go args (C.ForAllTy b) = let (tv,ty) = unsafeUnbind b
                             in  go (tv:args) ty
    go args ty             = (reverse args,ty)

splitFunForallTy :: C.Type -> ([Either C.TyVar C.Type],C.Type)
splitFunForallTy = go []
  where
    go args (C.ForAllTy b) = let (tv,ty) = unsafeUnbind b
                             in  go (Left tv:args) ty
    go args (C.tyView -> C.FunTy arg res) = go (Right arg:args) res
    go args ty                            = (reverse args,ty)

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

showSC :: SC -> String
showSC (STerm t) = showTerm t
showSC (Case n alts) = "Case " ++ show n ++ " of " ++ unlines (map showAlt alts)
showSC sc        = show sc

showAlt :: CaseAlt -> String
showAlt (ConCase n i ns sc) = show (n,i,ns) ++ " -> " ++ showSC sc
showAlt (ConstCase c sc)    = showConstant c ++ " -> " ++ showSC sc
showAlt (DefaultCase sc)    = "_ ->" ++ showSC sc
showAlt alt                 = show alt

showTerm :: Term -> String
showTerm (App e1 e2)       = "App (" ++ showTerm e1 ++ ") (" ++ showTerm e2 ++ ")"
showTerm (Constant c)      = "Constant (" ++ showConstant c ++ ")"
showTerm Impossible        = "Impossible"
showTerm Erased            = "Erased"
showTerm (P nt n tm)        = "P {" ++ show nt ++ "} " ++ show n ++ " (" ++ showTerm tm ++ ")"
showTerm (V v)             = "V " ++ show v
showTerm (Bind n bndr tm)  = "Bind " ++ show n ++ " (" ++ showBinder bndr ++ ") (" ++ showTerm tm ++ ")"
showTerm (Proj tm i)       = "Proj " ++ show i ++ " (" ++ show tm ++ ")"
showTerm (TType uexp)      = "TType " ++ show uexp

showBinder (Pi tm) = "Pi (" ++ showTerm tm ++ ")"
showBinder b       = show b

showConstant (I i)     = "(I i)"
showConstant (BI i)    = "(BI i)"
showConstant (Fl f)    = "(Fl f)"
showConstant (Ch c)    = "(Ch c)"
showConstant (Str s)   = "(Str s)"
showConstant (AType a) = "AType (" ++ showAType a ++ ")"
showConstant StrType   = "StrType"
showConstant PtrType   = "PtrType "
showConstant VoidType  = "VoidType"
showConstant Forgot    = "Forgot"
showConstant (B8 w)    = "(B8 w)"
showConstant (B16 w)   = "(B16 w)"
showConstant (B32 w)   = "(B32 w)"
showConstant (B64 w)   = "(B64 w)"

showAType (ATInt ITNative)    = "(ATInt ITNative)"
showAType (ATInt ITBig)       = "(ATInt ITBig)"
showAType (ATInt ITChar)      = "(ATInt ITChar)"
showAType (ATInt (ITFixed n)) = "(ATInt (ITFixed n))"
showAType (ATInt (ITVec e c)) = "(ATInt (ITVec e c))"
showAType ATFloat             = "ATFloat"

safeIndex :: [a] -> Int -> Maybe a
safeIndex []     _ = Nothing
safeIndex (x:_)  0 = Just x
safeIndex (_:xs) n = safeIndex xs (n-1)
