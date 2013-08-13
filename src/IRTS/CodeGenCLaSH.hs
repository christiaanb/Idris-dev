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
import           Control.Monad.Trans.Maybe    (MaybeT,runMaybeT)
import           Control.Monad.Reader         (Reader)
import qualified Control.Monad.Reader         as Reader
import           Control.Monad.State          (StateT,lift,liftIO)
import qualified Control.Monad.State.Lazy     as State
import           Data.ByteString.Lazy.Char8   (pack)
import           Data.Either                  (partitionEithers)
import           Data.HashMap.Lazy            (HashMap)
import qualified Data.HashMap.Lazy            as HashMap
import           Data.Maybe                   (catMaybes,fromMaybe)
import           Control.Lens                 ((%=),_1,_2,_3,makeLenses,view)
import qualified Unbound.LocallyNameless.Name as U
import           Unbound.LocallyNameless      (Bind,Rep,bind,embed,makeName,name2String,name2Integer,runFreshM,runFreshMT,string2Name,unbind,unembed)

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
import CLaSH.Primitives.Types
import CLaSH.Primitives.Util
import CLaSH.Util (MonadUnique(..))

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
  mapM traceUnused used
  -- liftIO $ putStrLn $ (unlines . concat . (map ((map (\d -> C.showDoc (C.dcName d) ++ " : " ++ C.showDoc (C.dcType d))) . snd)) . HashMap.toList . snd) dcTcState
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
  dcTy <- lift $ toCoreType [] ty
  let ((tyVars,argTys),resTy) = first partitionEithers $ splitFunForallTy dcTy
      dcName = toCoreName n
      dc = C.MkData { C.dcName       = dcName
                    , C.dcTag        = t
                    , C.dcType       = dcTy
                    , C.dcArgTys     = argTys
                    , C.dcUnivTyVars = map C.varName tyVars
                    , C.dcExtTyVars  = []
                    }
      liftedDc = C.AlgTyCon { C.tyConName = dcName
                            , C.tyConKind = dcTy
                            , C.tyConArity = (length tyVars + length argTys)
                            , C.algTcRhs = C.DataTyCon []
                            , C.isDictTyCon = False
                            }
  -- trace (show n ++ ": " ++ show ty ++ "\n" ++ show n ++ ": " ++ showTerm ty) $
  case (C.splitTyConAppM resTy) of
    Just (tc,_) -> do
      _1 %= HashMap.insert dcName liftedDc
      _2 %= HashMap.insertWith (++) (C.tyConName tc) [dc]
      _3 %= HashMap.insert dcName dc
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

toCoreType :: [(C.TyName,C.Kind)] -> Type -> R C.Type
-- toCoreType ns t@(Bind n@(MN _ _) (Pi ki) tt) = do
--   let tvN = toCoreName n
--   C.mkFunTy <$> (toCoreType ns ki) <*> (toCoreType ((tvN,undefined):ns) tt)
-- toCoreType ns t@(Bind n@(NS (UN ('!':_)) _) (Pi ki) tt) = do
--   let tvN = toCoreName n
--   C.mkFunTy <$> (toCoreType ns ki) <*> (toCoreType ((tvN,undefined):ns) tt)
-- toCoreType ns t@(Bind n (Pi ki) tt) = do
--   kiC <- toCoreType ns ki
--   let tvN = toCoreName n
--       tv  = C.TyVar tvN (embed kiC)
--   C.ForAllTy <$> (bind tv <$> toCoreType ((tvN,kiC):ns) tt)
toCoreType ns t@(Bind n (Pi ki) tt)
  | looksLikeKind ki
  = do
    kiC <- toCoreKind ns ki
    let tvN = toCoreName n
        tv  = C.TyVar tvN (embed kiC)
    C.ForAllTy <$> (bind tv <$> toCoreType ((tvN,kiC):ns) tt)

toCoreType ns t@(Bind n (Pi arg) res) = do
  let tvN = toCoreName n
  C.mkFunTy <$> toCoreType ns arg <*> toCoreType ((tvN,error $ "unexpected kind: " ++ show arg):ns) res

toCoreType ns t@(P (TCon _ _) n _) = C.mkTyConTy <$> toTyCon (toCoreName n)
toCoreType ns t@(P (DCon _ _) n _) = C.mkTyConTy <$> toTyCon (toCoreName n)
toCoreType ns t@(P Ref n _)        = return C.voidPrimTy --C.mkTyConApp <$> toTyCon (toCoreName n) <*> pure []
toCoreType ns t@(App ty1 ty2) = C.AppTy <$> toCoreType ns ty1 <*> toCoreType ns ty2
toCoreType ns t@(V i) = return $ (uncurry . flip) C.mkTyVarTy $ (ns !! i)
toCoreType ns t@(Constant (AType (ATInt ITBig))) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "Integer") C.liftedTypeKind 0 C.IntRep)
toCoreType ns t@(Constant (AType (ATInt ITChar))) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "Char") C.liftedTypeKind 0 C.VoidRep)
toCoreType ns t@(Constant (AType (ATInt ITNative))) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "Int") C.liftedTypeKind 0 C.IntRep)
toCoreType ns t@(Constant (Str s))               = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name s) C.liftedTypeKind 0 C.VoidRep)
toCoreType ns t@(Constant StrType) = return (C.mkTyConTy $ C.mkPrimTyCon (string2Name "String") C.liftedTypeKind 0 C.VoidRep)
toCoreType ns t@(Constant PtrType) = return C.voidPrimTy
toCoreType ns t = error $ "toCoreType: " ++ show t ++  "\n" ++ showTerm t

looksLikeKind :: Type
              -> Bool
looksLikeKind (TType _)           = True
looksLikeKind (Bind _ (Pi ki) tt) = looksLikeKind ki && looksLikeKind tt
looksLikeKind (P (TCon _ _) n@(NS (UN "Nat") ["Nat","Prelude"]) _) = True
looksLikeKind _                   = False

toCoreKind :: [(C.TyName,C.Kind)] -> Type -> R C.Kind
toCoreKind ns t@(TType _) = return C.liftedTypeKind
toCoreKind ns t@(Bind n (Pi arg) res) = do
  let tvN = toCoreName n
  C.mkFunTy <$> toCoreKind ns arg <*> toCoreKind ((tvN,error $ "unexpected box: " ++ show arg):ns) res
toCoreKind ns t@(P (TCon _ _) n _) = C.mkTyConTy <$> toTyCon (toCoreName n)
toCoreKind ns t = error $ "toCoreKind: " ++ show t ++  "\n" ++ showTerm t

defToTerm :: PrimMap
          -> MkTyDConState
          -> (Name,Def)
          -> Maybe (C.TmName,(String,(C.Type,C.Term)))
defToTerm primMap _ (n,_)
  | HashMap.member (pack $ name2String $ (toCoreName n :: C.TmName)) primMap = Nothing
defToTerm primMap s (n,CaseOp _ _ ty _ _ _ _ ns sc) = trace ("== " ++ show n ++ " ==:\nTy: " ++ show ty ++ "\nTm:\n" ++ show sc) $ flip Reader.runReader s $ do
  let tmName   = toCoreName n
      tmString = show n
  tyC <- toCoreType [] ty
  let (args,resTy) = splitFunForallTy tyC
      bndrs        = zipWith (\n ds -> case ds of { Left (C.TyVar n' t) -> Right (C.TyVar n' t)
                                                  ; Right t             -> Left  (C.Id (toCoreName n) (embed t))
                                                  }) ns args
  result <- runMaybeT $ do { scC <- scToTerm primMap (zip ns bndrs) sc
                           ; let termC  = C.mkAbstraction scC bndrs
                           ; let res    = (tmName,(tmString,(tyC,termC)))
                           ; return res
                           }
  trace ("CoreTy: " ++ C.showDoc tyC ++ "\nbndrs: " ++ show ns ++  "\nCoreTerm:\n" ++ maybe "" (C.showDoc . snd . snd . snd) result) $ return result
  -- return Nothing

defToTerm _ _ _ = Nothing

scToTerm :: PrimMap
         -> [(Name,Either C.Id C.TyVar)]
         -> SC
         -> MaybeT R C.Term
scToTerm primMap bndrs (STerm t)     = toCoreTerm primMap bndrs t
scToTerm primMap bndrs sc@(Case n alts) = do
  let scrut = case lookup n bndrs of
                     Just (Left (C.Id n' t'))     -> C.Var (unembed t') n'
                     Just (Right (C.TyVar n' t')) -> C.Prim (C.PrimCo (C.mkTyVarTy (unembed t') n'))
                     Nothing -> error ("scrut: " ++ show bndrs ++ show sc)
  alts <- mapM (toCoreAlt primMap bndrs) alts
  error $ C.showDoc scrut


scToTerm _       _     sc            = error ("scToTerm: " ++ show sc)

toCoreTerm :: PrimMap
           -> [(Name,Either C.Id C.TyVar)]
           -> Term
           -> MaybeT R C.Term
toCoreTerm primMap = term
  where
    term :: [(Name,Either C.Id C.TyVar)] -> Term -> MaybeT R C.Term
    term bndrs (P nt n t)       = pvar bndrs n t

    term bndrs (V i)            =
      case safeIndex bndrs i of
        Just bndr -> case snd bndr of
          Left  (C.Id n t)    -> return $! C.Var (unembed t) n
          Right (C.TyVar n t) -> return $! C.Prim (C.PrimCo (C.mkTyVarTy (unembed t) n))
        Nothing -> error ("Index: " ++ show i ++ " not found in: " ++ show bndrs)

    term bndrs (Bind n (Lam bndr) t) = do
      bndrTy <- lift $ toCoreType [] bndr
      case isKindLike bndrTy of
        True  -> do
          let tv = C.TyVar (toCoreName n) (embed bndrTy)
          tC     <- term ((n,Right tv):bndrs) t
          return $! C.TyLam $! bind tv tC
        False -> do
          let bndr = C.Id (toCoreName n) (embed bndrTy)
          tC     <- term ((n,Left bndr):bndrs) t
          return $! C.Lam $! bind bndr tC

    term _ e@(Bind n bndr t) = error $ "term(Bind n bndr t): " ++ showTerm e

    term bndrs (App t1 t2)      = do
      t1C <- term bndrs t1
      t2C <- term bndrs t2
      case isTypeLike t2C of
        Nothing -> return (C.App t1C t2C)
        Just ty -> return (C.TyApp t1C ty)

    term _ (Constant c)     = constant c

    term bndrs (Proj t i)       = do
      tP <- runFreshMT $ (flip State.evalStateT) (0 :: Int) $ do { tC  <- lift $ lift $ term bndrs t
                                                                 ; tP' <- C.mkSelectorCase "toCoreTerm" [] tC 1 i
                                                                 ; return tP'
                                                                 }
      return tP

    term _ Erased           = error $ "termErased         : "
    term _ Impossible       = error $ "termImpossible     : "
    term _ (TType _)        = error $ "termTType:"

    pvar bndrs n t = do
      tC <- lift $ toCoreType [] t
      let nC  = toCoreName n :: C.TmName
          nBS = pack (name2String nC)
      case HashMap.lookup nBS primMap of
        Just (BlackBox {}) -> return $ C.Prim (C.PrimFun nC tC)
        Nothing -> case lookup n bndrs of
                     Just (Left (C.Id n' t')) -> return $! C.Var (unembed t') n'
                     Just (Right (C.TyVar n' t')) -> return $! C.Prim (C.PrimCo (C.mkTyVarTy (unembed t') n'))
                     Nothing -> trace ("pvar: " ++ show n ++ " : " ++ show t) $! return $! C.Var tC nC

    constant c@(AType _) = C.Prim <$> C.PrimCo <$> lift (toCoreType [] (Constant c))
    constant (BI i)      = return $! (C.Literal $! C.IntegerLiteral i)
    constant c           = error $ "constant: " ++ showConstant c

toCoreAlt :: PrimMap
          -> [(Name,Either C.Id C.TyVar)]
          -> CaseAlt
          -> MaybeT R CoreAlt
toCoreAlt primMap bndrs (ConCase n i ns t) = do
   dc <- lift $ toDataCon (toCoreName n)
   error $ show (dc,i,ns,t)
toCoreAlt _ _ a = error $ "OtherAlt" ++ show a

isTypeLike :: C.Term
           -> Maybe C.Type
isTypeLike (C.Prim (C.PrimCo t)) = Just t
isTypeLike _                     = Nothing

isKindLike :: C.Type
           -> Bool
isKindLike ty = False

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

splitFunForallTy :: C.Type -> ([Either C.TyVar C.Type],C.Type)
splitFunForallTy = go []
  where
    go args (C.ForAllTy b) = let (tv,ty) = runFreshM (unbind b)
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
showSC sc        = show sc

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
