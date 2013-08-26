{-# OPTIONS_GHC -Wall -Werror #-}

module IRTS.CLaSH.Show where

import Core.CaseTree
import Core.TT

showSC :: SC -> String
showSC (STerm t)     = showTerm t
showSC (Case n alts) = "Case " ++ show n ++ " of " ++ unlines (map showAlt alts)
showSC sc            = "showSC: " ++ show sc

showAlt :: CaseAlt -> String
showAlt (ConCase n i ns sc) = show (n,i,ns) ++ " -> " ++ showSC sc
showAlt (ConstCase c sc)    = showConstant c ++ " -> " ++ showSC sc
showAlt (DefaultCase sc)    = "_ ->" ++ showSC sc
showAlt alt                 = "showAlt: " ++ show alt

showTerm :: Term -> String
showTerm (App e1 e2)      = "App (" ++ showTerm e1 ++ ") (" ++ showTerm e2 ++ ")"
showTerm (Constant c)     = "Constant (" ++ showConstant c ++ ")"
showTerm Impossible       = "Impossible"
showTerm Erased           = "Erased"
showTerm (P nt n tm)      = "P {" ++ show nt ++ "} " ++ show n ++ " (" ++ showTerm tm ++ ")"
showTerm (V v)            = "V " ++ show v
showTerm (Bind n bndr tm) = "Bind " ++ show n ++ " (" ++ showBinder bndr ++ ") (" ++ showTerm tm ++ ")"
showTerm (Proj tm i)      = "Proj " ++ show i ++ " (" ++ show tm ++ ")"
showTerm (TType uexp)     = "TType " ++ show uexp

showBinder :: Binder Term -> String
showBinder (Pi tm) = "Pi (" ++ showTerm tm ++ ")"
showBinder b       = "showBinder: " ++ show b

showConstant :: Const -> String
showConstant (I _)     = "(I i)"
showConstant (BI _)    = "(BI i)"
showConstant (Fl _)    = "(Fl f)"
showConstant (Ch _)    = "(Ch c)"
showConstant (Str _)   = "(Str s)"
showConstant (AType a) = "AType (" ++ showAType a ++ ")"
showConstant StrType   = "StrType"
showConstant PtrType   = "PtrType "
showConstant VoidType  = "VoidType"
showConstant Forgot    = "Forgot"
showConstant (B8 _)    = "(B8 w)"
showConstant (B16 _)   = "(B16 w)"
showConstant (B32 _)   = "(B32 w)"
showConstant (B64 _)   = "(B64 w)"
showConstant c         = "showConstant: " ++ show c

showAType :: ArithTy -> String
showAType (ATInt ITNative)    = "(ATInt ITNative)"
showAType (ATInt ITBig)       = "(ATInt ITBig)"
showAType (ATInt ITChar)      = "(ATInt ITChar)"
showAType (ATInt (ITFixed _)) = "(ATInt (ITFixed n))"
showAType (ATInt (ITVec _ _)) = "(ATInt (ITVec e c))"
showAType ATFloat             = "ATFloat"
