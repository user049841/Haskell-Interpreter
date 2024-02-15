{-# LANGUAGE CPP #-}
-- Haskelly Test Script
-- Written by Liam O'Connor-Davis for comp3161 10s2
-- BSD3
-- Copyright (C) Liam O'Connor-Davis 2010

-- #define NOCOLOR


import Control.Exception

import System.Directory
import Control.Applicative((<$>))
import System.FilePath
import System.Environment
import Data.List
import Control.Monad
--import Diff
import System.Process
import System.Exit
import Data.Char
import Data.Maybe
import MinHS.Parse
import MinHS.Syntax
import MinHS.TyInfer
import MinHS.TCMonad
import MinHS.Subst
import Options.Applicative
import Options.Applicative.Types

import Text.PrettyPrint.ANSI.Leijen (Pretty (..),Doc, putDoc, plain)

data DI = F | S | B deriving (Show, Eq)

getDiff :: (Eq t) => [t] -> [t] -> [(DI, t)]
getDiff xs ys = []

occursFirstTy :: [String] -> Type -> Maybe String
occursFirstTy xs (Arrow ty1 ty2) =
  case occursFirstTy xs ty1 of
    Nothing -> occursFirstTy xs ty2
    res -> res
occursFirstTy xs (Prod ty1 ty2) =
  case occursFirstTy xs ty1 of
    Nothing -> occursFirstTy xs ty2
    res -> res
occursFirstTy xs (Sum ty1 ty2) =
  case occursFirstTy xs ty1 of
    Nothing -> occursFirstTy xs ty2
    res -> res
occursFirstTy xs (Base _) = Nothing
occursFirstTy xs (TypeVar x) =
  if x `elem` xs then Just x else Nothing

sortVarsExp :: Exp -> Exp
sortVarsExp (App e1 e2) = App (sortVarsExp e1) (sortVarsExp e2)
sortVarsExp (If e1 e2 e3) =
  If (sortVarsExp e1) (sortVarsExp e2) (sortVarsExp e3)
sortVarsExp (Let bs e) =
  Let (map sortVarsBind bs) (sortVarsExp e)
sortVarsExp (Letrec bs e) =
  Letrec (map sortVarsBind bs) (sortVarsExp e)  
sortVarsExp (Recfun b) = Recfun(sortVarsBind b)
sortVarsExp (Case e as) =
  Case (sortVarsExp e) (map sortVarsAlt as)
sortVarsExp e = e

sortVarsProg = map sortVarsBind

foralls :: QType -> ([String],Type)
foralls(Forall x ty) =
  let (xs,ty') = foralls ty
  in (x:xs,ty')
foralls(Ty ty) = ([],ty)

kill1 :: (a -> Bool) -> [a] -> [a]
kill1 f [] = []
kill1 f (x:xs)
  | f x       = xs
  | otherwise = x:kill1 f xs

occursSort xs ty =
  case occursFirstTy xs ty of
    Nothing -> xs
    Just x ->
      let xs' = kill1 ((==) x) xs
      in
        x:occursSort xs' ty

sortVarsBind :: Bind -> Bind
sortVarsBind (Bind f ty ys e) =
  let ty' =
        (do
            x <- ty
            let (xs,bty) = foralls x
            let xs' = occursSort xs bty
            return $ foldr Forall (Ty bty) xs'
        )
  in
    Bind f ty' ys (sortVarsExp e)

sortVarsAlt :: Alt -> Alt
sortVarsAlt (Alt y ys e) = Alt y ys (sortVarsExp e)

renameVarsExp :: [String] -> Exp -> TC Exp
renameVarsExp avoid (App e1 e2) =
  do
    e1' <- renameVarsExp avoid e1
    e2' <- renameVarsExp avoid e2
    return (App e1' e2')
renameVarsExp avoid (If e1 e2 e3) =
  do
    e1' <- renameVarsExp avoid e1
    e2' <- renameVarsExp avoid e2
    e3' <- renameVarsExp avoid e3   
    return (If e1' e2' e3')
renameVarsExp avoid (Let bs e) =
  do
    bs' <- mapM (renameVarsBind avoid) bs
    e' <- renameVarsExp avoid e
    return(Let bs' e')
renameVarsExp avoid (Letrec bs e) =
  do
    bs' <- mapM (renameVarsBind avoid) bs
    e' <- renameVarsExp avoid e
    return(Letrec bs' e')
renameVarsExp avoid (Recfun b) =
  renameVarsBind avoid b >>= return . Recfun
renameVarsExp avoid (Case e as) =
  do
    e' <- renameVarsExp avoid e
    as' <- mapM (renameVarsAlt avoid) as
    return(Case e' as')
renameVarsExp avoid e = return e

myFreshNames :: [Id]
myFreshNames = map ((++) "_x" . show) [1..]

actualFreshName :: [String] -> String
actualFreshName xs = fromJust $ find (not . flip elem xs) myFreshNames

renameVarsAlt avoid (Alt y ys e) =
  renameVarsExp avoid e >>= return . Alt y ys
renameVarsBind avoid (Bind f (Just (Forall z ty)) ys e) =
  do
    z' <- fresh
    let (TypeVar z'') = z'
    let ztemp = actualFreshName (z:avoid)
    let s1 = substQType (z=:TypeVar ztemp)
    let s2 = substQType (ztemp=:z')
    Bind f ty ys e <- renameVarsBind (z:z'':ztemp:avoid)
                                     (Bind f (Just $ s1 ty) ys (allTypes s1 e))
    return(Bind f (fmap (Forall z'' . s2) ty) ys (allTypes s2 e))
renameVarsBind avoid (Bind f ty ys e) =
  do
    e' <- renameVarsExp avoid e
    return(Bind f ty ys e')

renameVarsProg :: Program -> Either MinHS.TCMonad.TypeError Program
renameVarsProg = runTC . mapM (renameVarsBind [])

massageProg :: Program -> Either MinHS.TCMonad.TypeError Program
massageProg prog =
  do
    prog' <- renameVarsProg prog
    prog'' <- return $ sortVarsProg prog'
    renameVarsProg prog''

compareProgs :: String -> String -> Bool
compareProgs xs ys =
  let
    f msg xs = parseProgram msg xs >>= return . massageProg >>= return . either (\x -> Nothing) Just
  in
    f "<left source>" xs == f "<right source>" ys


#ifdef NOCOLOR
color v c = c
#else
color v c = v ++ c ++ "\ESC[0m"
#endif

brightWhite = "\ESC[1;97m"
darkWhite = "\ESC[37m"
darkRed = "\ESC[31m"
brightRed = "\ESC[1;91m"
brightGreen = "\ESC[1;92m"
darkYellow = "\ESC[33m"

traverseP :: String -> IO [String]
traverseP path = do
   contents <- getDirectoryContents path
   let sanitizedContents = map (path </>) $ contents \\ ["..","."]
   directories <- filterM doesDirectoryExist sanitizedContents
   files <- filterM doesFileExist sanitizedContents
   if null directories
     then return files
     else do
       traversal <- concat <$> mapM traverseP directories
       return $ traversal ++ files

foreach = flip mapM

showSummary marks = color brightWhite $ if length marks > 0 then "Passed " ++ show (length $ filter (/= 0) marks)
                                                              ++ " out of " ++ show(length marks)
                                                              ++ " tests: " ++ show(((length $ filter (/= 0) marks) * 100) `div` length marks)
                                                              ++ "% Correct. Total of " ++ show (sum marks) ++ " marks."
                                                            else "No tests run."

getSkips skips = concat <$> (foreach skips $ \skip -> map (<.> ".mhs") . map (takeDirectory skip </>) . lines <$> readFile skip)

runTests exe testdir = do
    files <- traverseP $ testdir
    let tests' = filter ((".mhs" ==) . takeExtension) files
    let skips = filter (("Skip" ==) . takeBaseName) files
    tests <- (tests' \\) <$> getSkips skips
    marks <- foreach tests $ (\test -> do
      (expect_fail, flags) <- getFlags (test `replaceFileName` "Flag")
      mark <- getMarks (test `replaceFileName` "Marks")
      putStr $ color brightWhite ("Running test: ") ++ color darkWhite (makeRelative testdir test) ++ color brightWhite (" (worth " ++ show mark ++ ") :-  ")
      let esc_test
            | all (not . isSpace) $ test
            = test
            | otherwise
            = '"':do x <- test
                     if x == '"'
                       then show "\""
                       else return x
              ++ "\""
      (exit, out, err) <- readCreateProcessWithExitCode (shell (unwords $ exe : (flags ++ ["--no-colour", esc_test]))) ""
      let check = do r1 <- doCheck ".out" "Stdout" test out
                     r2 <- doCheck ".err" "Stderr" test err
                     return $ r1 * r2 * mark
      case exit of
        ExitFailure i -> if expect_fail then check
                         else do putStrLn $ color darkRed ("Executable returned non-zero exit code(" ++ show i ++ ").")
                                 dumpOutput err out
        ExitSuccess -> if not expect_fail then check
                       else do putStrLn $ color darkRed ("Expected program failure, but it unexpectedly succeeded.")
                               dumpOutput err out)
    putStrLn $ showSummary marks
  where
    dumpOutput err out = do
      putStrLn $ color darkRed ("Stderr was:")
      putStrLn err
      putStrLn $ color darkRed ("Stdout was:")
      putStrLn out
      return 0
    doCheck ext name test out = do
      v <- doesFileExist (test `replaceExtension` ext)
      if v
        then do
          inp <- readFile (test `replaceExtension` ".out")
          res <- return $ compareProgs inp out
          if res
            then putStrLn (color brightGreen $ name ++ " Check Passed!") >> return 1
            else do putStrLn (color brightRed $ name ++ " Check Failed") >> return 0
        else if (not $ all isSpace out)
          then do
            putStrLn $ color darkYellow $ "No " ++ ext ++ " file found. Printing output..."
            putStr out
            return 1
          else return 1

getFlags filename = do
  v <- doesFileExist filename
  if v then do
         str <- lines <$> readFile filename
         return ("expect-fail" `elem` str, delete "expect-fail" str)
       else return (False, [])

getMarks filename = let readInteger s = case reads s of
                                            [(a,b)] -> a
                                            _       -> 1
                     in do v <- doesFileExist filename
                           if v then  readInteger <$> readFile filename
                                else return 1

main = do
  cd <- getCurrentDirectory
  v <- getArgs
  when ("--help" `elem` v) $ do
     putStrLn $ "Liam's Haskelly Test Runner v0.1. \n" ++
                "This program is usually accompanied by a runner shell script.\n" ++
                "  Usage: ./run_tests.sh [--no-color] [program_to_test] [test_folder_location]\n\n" ++
                "If no shell script is available, it can be run easily via runhaskell:\n" ++
                "  Usage: runhaskell -i./tests/driver -cpp [-DNOCOLOR] ./tests/driver/Check.hs [program_to_test] [test_folder_location]"
     exitSuccess
  let (dir, exe) = case filter (/= "") v of
                     [ filename ] -> (cd </> "tests", filename)
                     [ filename, tests ] -> (tests, filename)
                     [] -> (cd </> "tests", cd </> "dist" </> "build" </> "minhs-1" </> "minhs-1")
                     _ -> error (show v)
  de <- doesDirectoryExist $ cd </> "tests"
  --fe <- doesFileExist $ exe
  --when (not fe) $ error $ "I cannot find an executable. I tried:" ++ exe
  when (not de) $ error "I cannot find a `tests' directory. Exiting"
  runTests exe dir

showDiff :: [(DI,String)] -> String
showDiff diff = unlines $ map (\(a,b) -> color (colorDI a) (showDI a ++ b )) diff
 where showDI F = "+"
       showDI S = "-"
       showDI B = " "
       colorDI F = darkRed
       colorDI S = darkRed
       colorDI B = darkWhite
