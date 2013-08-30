{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module IRTS.CLaSH.Idris2Core where

-- External Imports
import           Control.Applicative          ((<$>),(<*>),pure)
import           Control.Lens                 ((%=),_1,_2,_3,view)
import           Control.Monad.Reader         (Reader)
import qualified Control.Monad.Reader         as Reader
import           Control.Monad.State          (StateT,lift)
import qualified Control.Monad.State.Lazy     as State
import           Control.Monad.Trans.Maybe    (MaybeT(..),runMaybeT)
import           Data.ByteString.Lazy.Char8   (pack)
import           Data.Either                  (lefts)
import           Data.HashMap.Lazy            (HashMap)
import qualified Data.HashMap.Lazy            as HashMap
import           Data.Maybe                   (catMaybes,fromMaybe)
import qualified Data.Text.Lazy               as Text
import           Unbound.LocallyNameless      (Bind,bind,embed,name2String,rebind,runFreshM,runFreshMT,string2Name,unembed)
import qualified Unbound.LocallyNameless.Name as U
import           Unbound.LocallyNameless.Ops  (unsafeUnbind)

-- CLaSH Imports
import qualified CLaSH.Core.DataCon           as C
import qualified CLaSH.Core.Literal           as C
import qualified CLaSH.Core.Pretty            as C
import qualified CLaSH.Core.Term              as C
import qualified CLaSH.Core.TyCon             as C
import qualified CLaSH.Core.Type              as C
import qualified CLaSH.Core.TysPrim           as C
import qualified CLaSH.Core.Util              as C
import qualified CLaSH.Core.Var               as C
import           CLaSH.Primitives.Types       (Primitive(..),PrimMap)
import qualified CLaSH.Rewrite.Util           as C
import           CLaSH.Util                   (traceIf)

-- Local imports
import Core.CaseTree
import Core.Evaluate
import Core.TT
import IRTS.CLaSH.Show
import IRTS.CLaSH.Util

type MkTyDConState = (HashMap C.TyConName C.TyCon, HashMap C.TyConName [C.DataCon], HashMap C.DcName C.DataCon)
type R             = Reader MkTyDConState
type SR a          = StateT MkTyDConState R a
type CoreAlt       = Bind C.Pat C.Term

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

makeDataCon (n,DCon t _,ty) = do
  dcTyM <- lift $ runMaybeT $ toCoreType [] [] ty
  dcTy  <- case dcTyM of
             (Just ty') -> return ty'
             Nothing    -> error $ "makeDataCon: can't create type for: " ++ show n ++ ":\n" ++ showTerm ty
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
                            }

  case (C.splitTyConAppM resTy) of
    Just (tc,_) -> do
      _1 %= HashMap.insert tcName liftedDc
      _2 %= HashMap.insertWith (++) (C.tyConName tc) [dc]
      _3 %= HashMap.insert dcName dc
    Nothing -> error $ "makeDataCon: result is not a TyCon?" ++ show ty

makeDataCon _ = return ()

makeTyCon (n,TCon _ a,ty) = do
  let tcName = toCoreName n
  dcs  <- lift $ tcDataCons tcName
  tcKiM <- lift $ runMaybeT $ toCoreType [] [] ty
  tcKi <- case tcKiM of
             (Just k) -> return k
             Nothing  -> error $ "makeTyCon: " ++ showTerm ty
  let tc = C.AlgTyCon { C.tyConName   = tcName
                      , C.tyConKind   = tcKi
                      , C.tyConArity  = a
                      , C.algTcRhs    = C.DataTyCon dcs
                      }
  _1 %= HashMap.insert tcName tc

makeTyCon _ = return ()

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

toCoreType :: [(C.TyName,C.Kind)] -> [(Name,Either C.Id C.TyVar)] -> Type -> MaybeT R C.Type
toCoreType ns bndrs (Bind n (Pi ki) res) =
  let tvN = toCoreName n
  in case looksLikeKind ki of
    True -> do
      kiC <- toCoreKind ns ki
      let tv = C.TyVar tvN (embed kiC)
      C.ForAllTy <$> (bind tv <$> toCoreType ((tvN,kiC):ns) bndrs res)
    False ->
      C.mkFunTy <$> toCoreType ns bndrs ki <*> toCoreType ((tvN,error $ "unexpected kind: " ++ show ki):ns) bndrs res

toCoreType _ _     (P (TCon _ _) n _) = C.mkTyConTy <$> lift (toTyCon (toCoreName n))
toCoreType _ _     (P (DCon _ _) n _) = C.mkTyConTy <$> lift (toTyCon (toCoreName n))
toCoreType _ _     (P Ref n _)        = return (C.mkTyConTy $ C.PrimTyCon (toCoreName n) C.liftedTypeKind 0 C.VoidRep)
toCoreType _ bndrs t@(P Bound n _)    = case lookup n bndrs of
                                          Just (Left id_) -> return $! C.VarTy (unembed $ C.varType id_) (U.translate $ C.varName id_)
                                          Just (Right tv) -> return $! C.VarTy (unembed $ C.varKind tv)  (C.varName tv)
                                          Nothing -> error ("toCoreType Bound notfound: " ++ showTerm t ++ show bndrs)
toCoreType ns _ (V i) = let (tyN,tyK) = maybe (error ("Index(toCoreType): " ++ show i ++ " not found in: " ++ show ns)) id (safeIndex ns i)
                        in return $! C.VarTy tyK tyN

toCoreType ns bndrs (App ty1 ty2) = C.AppTy <$> toCoreType ns bndrs ty1 <*> toCoreType ns bndrs ty2

toCoreType _ _ (Constant (AType (ATInt ITBig)))         = return C.intPrimTy
toCoreType _ _ (Constant (AType (ATInt ITNative)))      = return C.intPrimTy
toCoreType _ _ t@(Constant (AType (ATInt (ITFixed _)))) = return (C.mkTyConTy $ C.PrimTyCon (string2Name $ show t) C.liftedTypeKind 0 C.IntRep)
toCoreType _ _ t@(Constant (AType (ATInt (ITVec _ _)))) = return (C.mkTyConTy $ C.PrimTyCon (string2Name $ show t) C.liftedTypeKind 0 C.IntRep)

toCoreType _ _ (Constant (AType (ATInt ITChar))) = return (C.mkTyConTy $ C.PrimTyCon (string2Name "Char") C.liftedTypeKind 0 C.VoidRep)
toCoreType _ _ (Constant (AType ATFloat))        = return (C.mkTyConTy $ C.PrimTyCon (string2Name "Float") C.liftedTypeKind 0 C.VoidRep)
toCoreType _ _ (Constant (Str s))                = return (C.mkTyConTy $ C.PrimTyCon (string2Name s) C.liftedTypeKind 0 C.VoidRep)
toCoreType _ _ (Constant StrType)                = return (C.mkTyConTy $ C.PrimTyCon (string2Name "String") C.liftedTypeKind 0 C.VoidRep)
toCoreType _ _ (Constant PtrType)                = return C.voidPrimTy

toCoreType _ _ (Constant (BI i)) = return $! C.LitTy (C.NumTy $! fromInteger i)

toCoreType _ _ (Constant c) = error $ "toCoreType: Constant(" ++ showConstant c ++ ")"

toCoreType _ _ (TType _) = return C.liftedTypeKind

toCoreType _ _ t = error $ "toCoreType: " ++ show t


looksLikeKind :: Type
              -> Bool
looksLikeKind (TType _)           = True
looksLikeKind (Bind _ (Pi ki) tt) = looksLikeKind ki && looksLikeKind tt
looksLikeKind (P (TCon _ _) (NS (UN "Nat") ["Nat","Prelude"]) _) = True
looksLikeKind _                   = False

toCoreKind :: [(C.TyName,C.Kind)] -> Type -> MaybeT R C.Kind
toCoreKind _  (TType _) = return C.liftedTypeKind
toCoreKind ns (Bind n (Pi arg) res) = do
  let tvN = toCoreName n
  C.mkFunTy <$> toCoreKind ns arg <*> toCoreKind ((tvN,error $ "unexpected box: " ++ show arg):ns) res
toCoreKind _  (P (TCon _ _) n _) = C.mkTyConTy <$> lift (toTyCon (toCoreName n))
toCoreKind ns (V i) = return $ maybe (error ("Index(toCoreKind: " ++ show i ++ " not found in: " ++ show ns)) snd (safeIndex ns i)
toCoreKind _  t = error ("toCoreKind: " ++ show t ++ "\n" ++ showTerm t)

defToTerm :: Int
          -> PrimMap
          -> MkTyDConState
          -> (Name,Def)
          -> Maybe (C.TmName,(C.Type,C.Term))
defToTerm _ primMap _ (n,_)
  | HashMap.member (pack $ name2String $ (toCoreName n :: C.TmName)) primMap = Nothing
defToTerm logLvl primMap s (n,CaseOp _ ty _ _ ns sc _ _) = traceIf (logLvl >= 1) ("== " ++ show n ++ " ==:\nTy: " ++ show ty ++ "\nBndrs: " ++ show ns ++ "\nTm:\n" ++ show sc) $ flip Reader.runReader s $ do
  let tmName   = toCoreName n
      tmString = show n
  tyC <- fmap (maybe (error $ "defToTerm: " ++ showTerm ty) id) $ runMaybeT $ toCoreType [] [] ty
  let (args,_) = splitFunForallTy tyC
      bndrs    = zipWith (\n' ds -> case ds of { Left (C.TyVar n'' t) -> Right (C.TyVar n'' t)
                                               ; Right t             -> Left  (C.Id (toCoreName n') (embed t))
                                               ; Left id_            -> error $ "Malformed type variable" ++ show id_
                                               }) ns args
  result <- runMaybeT $ do { scC <- scToTerm logLvl primMap [] (zip ns bndrs) sc
                           ; let termC   = C.mkAbstraction scC bndrs
                           ; let res     = (tmName,(tyC,termC))
                           ; let resTyC  = runFreshM $ C.termType termC
                           ; traceIf (logLvl >= 2) ("CoreTy: " ++ C.showDoc tyC ++ "\nCoreTerm:\n" ++ C.showDoc termC) $
                               traceIf (logLvl >= 1 && tyC /= resTyC) ("TYPES DIFFER for " ++ tmString ++ ":\nExpected: " ++ C.showDoc tyC ++ "\nCalculated: " ++ C.showDoc resTyC) $
                                 return res
                           }
  return result

defToTerm _ _ _ _ = Nothing

scToTerm :: Int
         -> PrimMap
         -> [(C.TyName,C.Kind)]
         -> [(Name,Either C.Id C.TyVar)]
         -> SC
         -> MaybeT R C.Term
scToTerm logLvl primMap tvs bndrs (STerm t) = toCoreTerm logLvl primMap tvs bndrs t
scToTerm logLvl primMap tvs bndrs sc@(Case n alts) = do
  let scrut = case lookup n bndrs of
                     Just (Left (C.Id n' t'))     -> C.Var (unembed t') n'
                     Just (Right (C.TyVar n' t')) -> C.Prim (string2Name "_TY_") (C.VarTy (unembed t') n')
                     _ -> error ("scrut: " ++ show bndrs ++ show sc)
  altsC <- mapM (toCoreAlt logLvl primMap tvs bndrs) alts
  ty    <- MaybeT $ return (case altsC of
                             { []      -> Nothing
                             ; (alt:_) -> Just $ runFreshM (C.termType (snd $ unsafeUnbind alt))
                             }
                           )
  return $! C.Case scrut ty altsC


scToTerm _ _ _ _ sc = error ("scToTerm: " ++ show sc)

toCoreTerm :: Int
           -> PrimMap
           -> [(C.TyName,C.Kind)]
           -> [(Name,Either C.Id C.TyVar)]
           -> Term
           -> MaybeT R C.Term
toCoreTerm logLvl primMap = term
  where
    term :: [(C.TyName,C.Kind)] -> [(Name,Either C.Id C.TyVar)] -> Term -> MaybeT R C.Term
    term tvs bndrs (P nt n t) = pvar tvs bndrs nt n t

    term _ bndrs (V i) =
      case safeIndex bndrs i of
        Just (_,Left  (C.Id n t))    -> return $! C.Var (unembed t) n
        Just (_,Right (C.TyVar n t)) -> return $! C.Prim (string2Name "_TY_") (C.VarTy (unembed t) n)
        _ -> error ("Index(term): " ++ show i ++ " not found in: " ++ show bndrs)

    term tvs bndrs (Bind n (Lam bndr) t) =
      case looksLikeKind bndr of
        True  -> do
          bndrKi <- toCoreKind tvs bndr
          let tvN = toCoreName n
              tv  = C.TyVar tvN (embed bndrKi)
          tC     <- term ((tvN,bndrKi):tvs) ((n,Right tv):bndrs) t
          return $! C.TyLam $! bind tv tC
        False -> do
          bndrTy <- toCoreType tvs bndrs bndr
          let id_ = C.Id (toCoreName n) (embed bndrTy)
          tC     <- term ((toCoreName n,error "lookslikekind"):tvs) ((n,Left id_):bndrs) t
          return $! C.Lam $! bind id_ tC

    term tvs bndrs (Bind n (Pi bndr) t) =
      case looksLikeKind bndr of
        True  -> do
          bndrKi <- toCoreKind tvs bndr
          let tvN = toCoreName n
              tv  = C.TyVar (toCoreName n) (embed bndrKi)
          tC     <- term ((tvN,bndrKi):tvs) ((n,Right tv):bndrs) t
          return $! C.TyLam $! bind tv tC
        False -> do
          bndrTy <- toCoreType tvs bndrs bndr
          let id_ = C.Id (toCoreName n) (embed bndrTy)
          tC     <- term ((toCoreName n,error "lookslikekind"):tvs) ((n,Left id_):bndrs) t
          return $! C.Lam $! bind id_ tC

    term _ _ e@(Bind _ _ _) = error ("term(Bind n bndr t): " ++ showTerm e)

    term tvs bndrs (App t1 t2) = do
      t1C <- term tvs bndrs t1
      t2C <- term tvs bndrs t2
      tyM <- lift $ isTypeLike t2C
      case tyM of
        Nothing -> return (C.App t1C t2C)
        Just ty -> return (C.TyApp t1C ty)

    term tvs bndrs (Constant c) = constant tvs bndrs c

    term tvs bndrs (Proj t i) = do
      tP <- runFreshMT $ (flip State.evalStateT) (1 :: Int) $ do { tC  <- lift $ lift $ term tvs bndrs t
                                                                 ; tP' <- C.mkSelectorCase "toCoreTerm" [] tC 1 i
                                                                 ; return tP'
                                                                 }
      return tP

    term _ _ Erased           = error $ "termErased         : "
    term _ _ Impossible       = error $ "termImpossible     : "
    term _ _ (TType _)        = return (C.Prim (string2Name "_TY_") C.liftedTypeKind)

    pvar tvs bndrs nt n t = do
      let nC   = toCoreName n :: C.TmName
          nBS  = pack (name2String nC)
      case HashMap.lookup nBS primMap of
        Just (BlackBox {}) -> do
          tC <- toCoreType tvs bndrs t
          return (C.Prim nC tC)
        Just (Primitive _ ((== Text.pack "Dictionary") -> True)) -> do
            tC <- toCoreType tvs bndrs t
            let liftedFun = C.AlgTyCon { C.tyConName = toCoreName n
                                       , C.tyConKind = tC
                                       , C.tyConArity = length $ fst $ splitFunForallTy tC
                                       , C.algTcRhs = C.DataTyCon []
                                       }
            return (C.Prim (string2Name "_TY_") (C.mkTyConTy liftedFun))

        Just (Primitive f ((== Text.pack "Function") -> True))
          | f == pack "@Prelude.Functor.Functor$[Signal].0.Prelude.Functor.#!map"              -> mapSyncTerm <$> toCoreType tvs bndrs t
          | f == pack "@Prelude.Applicative.Applicative$[Signal].0.Prelude.Applicative.#!<$>"  -> mapSyncTerm <$> toCoreType tvs bndrs t
          | f == pack "@Prelude.Applicative.Applicative$[Signal].0.Prelude.Applicative.#!pure" -> syncTerm    <$> toCoreType tvs bndrs t
          | f == pack "CLaSH.Signal.Vect.unpack" -> packUnpackVectTerm False <$> toCoreType tvs bndrs t
          | f == pack "CLaSH.Signal.Vect.pack"   -> packUnpackVectTerm True  <$> toCoreType tvs bndrs t
          | otherwise -> error $ "pvar: Function: " ++ show f

        Just (Primitive f _) -> error $ "pvar: Other primitive: " ++ show f

        Nothing -> case nt of
          (DCon _ _) -> do
            dc <- lift $ toDataCon (toCoreName n)
            return $! (C.Data dc)
          Bound -> case lookup n bndrs of
            Just (Left  (C.Id n' t'))    -> return $! C.Var (unembed t') n'
            Just (Right (C.TyVar n' t')) -> return $! C.Prim (string2Name "_TY_") (C.VarTy (unembed t') n')
            _ -> error $ "Bound var " ++ show (n,t) ++ " not found in: " ++ show bndrs
          Ref -> do
            tC <- toCoreType tvs bndrs t
            let (_,resTy) = splitFunForallTy tC
            if resTy == C.liftedTypeKind
              then traceIf (logLvl >= 2) ("pvar REF(TY): " ++ show n ++ " : " ++ show t) $! return $! C.Prim (string2Name "_TY_") (C.VarTy tC (toCoreName n))
              else traceIf (logLvl >= 2) ("pvar REF(TM): " ++ show n ++ " : " ++ show t) $! return $! C.Var tC nC
          (TCon _ _) -> do
            tc <- lift $ toTyCon (toCoreName n)
            return $! C.Prim (string2Name "_TY_") (C.mkTyConTy tc)

    constant tvs bndrs c@(AType _) = C.Prim (string2Name "_TY_") <$> toCoreType tvs bndrs (Constant c)
    constant tvs bndrs c@(StrType) = C.Prim (string2Name "_TY_") <$> toCoreType tvs bndrs (Constant c)
    constant tvs bndrs c@(PtrType) = C.Prim (string2Name "_TY_") <$> toCoreType tvs bndrs (Constant c)

    constant _   _     (BI i)      = return $! C.Literal $! C.IntegerLiteral i
    constant _   _     (I i)       = return $! C.Literal $! C.IntegerLiteral (toInteger i)

    constant _   _     (Str s)     = return $! C.Literal $! C.StringLiteral s

    constant _   _     c           = error $ "constant: " ++ showConstant c

toCoreAlt :: Int
          -> PrimMap
          -> [(C.TyName,C.Kind)]
          -> [(Name,Either C.Id C.TyVar)]
          -> CaseAlt
          -> MaybeT R CoreAlt
toCoreAlt logLvl primMap tvs bndrs (ConCase n _ ns sc) = do
   dc <- lift $ toDataCon (toCoreName n)
   let tys  = map (either (unembed . C.varKind) id) . fst . splitFunForallTy $ C.dcType dc
       ids  = zipWith (\n' t -> C.Id (toCoreName n') (embed t)) ns tys
       idsR = catMaybes $ zipWith (\n' t -> case t of
                                             Left _   -> Nothing
                                             Right ty -> Just $! C.Id (toCoreName n') (embed ty)
                                  ) ns (fst . splitFunForallTy $ C.dcType dc)
   t  <- scToTerm logLvl primMap tvs (zip ns (map Left ids) ++ bndrs) sc
   return $! bind (C.DataPat (embed dc) (rebind [] idsR)) t

toCoreAlt logLvl primMap tvs bndrs (ConstCase (I i) sc) = do
  t <- scToTerm logLvl primMap tvs bndrs sc
  return $! bind (C.LitPat (embed (C.IntegerLiteral $ toInteger i))) t

toCoreAlt logLvl primMap tvs bndrs (DefaultCase sc) =
  bind <$> pure C.DefaultPat <*> scToTerm logLvl primMap tvs bndrs sc

toCoreAlt _ _ _ _ a = error $ "OtherAlt: " ++ show a

isTypeLike :: C.Term
           -> R (Maybe C.Type)
isTypeLike (C.Prim (name2String -> "_TY_") t) = return $! Just t

isTypeLike (C.TyApp t ty) = do
  tyM <- isTypeLike t
  case tyM of
    Just ty' -> return $! Just $! C.AppTy ty' ty
    Nothing  -> return $! Nothing

isTypeLike (C.Lam b) = do
  let (bndr,res) = unsafeUnbind b
  tyM <- isTypeLike res
  case tyM of
    Just ty' -> return $! Just $! C.mkFunTy (unembed $ C.varType bndr) ty'
    Nothing  -> return $! Nothing

isTypeLike (C.App e (C.Data dc)) = do
  tyM <- isTypeLike e
  case tyM of
    Just ty' -> do tc <- toTyCon (U.translate $ C.dcName dc)
                   return $! Just (C.AppTy ty' (C.mkTyConTy tc))
    Nothing  -> return $! Nothing

isTypeLike (C.App e (C.Literal (C.IntegerLiteral i))) = do
  tyM <- isTypeLike e
  case tyM of
    Just ty' -> return $! Just (C.AppTy ty' (C.LitTy (C.NumTy $ fromInteger i)))
    Nothing  -> return $! Nothing

isTypeLike _ = return $! Nothing


mapSyncTerm :: C.Type
            -> C.Term
mapSyncTerm (C.ForAllTy tvATy) =
  let (aTV,C.ForAllTy tvBTy) = unsafeUnbind tvATy
      (bTV,C.tyView -> C.FunTy _ (C.tyView -> (C.FunTy aTy bTy))) = unsafeUnbind tvBTy
      fName = string2Name "f"
      xName = string2Name "x"
      fTy = C.mkFunTy aTy bTy
      fId = C.Id fName (embed fTy)
      xId = C.Id xName (embed aTy)
  in C.TyLam $ bind aTV $
     C.TyLam $ bind bTV $
     C.Lam   $ bind fId $
     C.Lam   $ bind xId $
     C.App (C.Var fTy fName) (C.Var aTy xName)

mapSyncTerm ty = error $ "mapSyncTerm: " ++ C.showDoc ty

syncTerm :: C.Type
         -> C.Term
syncTerm (C.ForAllTy tvTy) =
  let (aTV,C.tyView -> C.FunTy _ aTy) = unsafeUnbind tvTy
      xName = string2Name "x"
      xId = C.Id xName (embed aTy)
  in C.TyLam $ bind aTV $
     C.Lam   $ bind xId $
     C.Var   aTy xName

syncTerm ty = error $ "syncTerm: " ++ C.showDoc ty

packUnpackVectTerm :: Bool
               -> C.Type
               -> C.Term
packUnpackVectTerm isPack (C.ForAllTy tvTy) =
  let (nTV,C.ForAllTy tvATy) = unsafeUnbind tvTy
      (aTV,C.tyView -> C.FunTy inpTy outpTy) = unsafeUnbind tvATy
      xName   = string2Name "x"
      xTy     = if isPack then outpTy else inpTy
      xId     = C.Id xName (embed xTy)
      newExpr = C.TyLam $ bind nTV $
                C.TyLam $ bind aTV $
                C.Lam   $ bind xId $
                C.Var xTy xName
  in newExpr

packUnpackVectTerm _ ty = error $ "packUnpackVectTerm: " ++ C.showDoc ty
