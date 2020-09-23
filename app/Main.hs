{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad (when)
import PolyGen
import System.Environment (getArgs)
import System.Exit (exitSuccess)
import System.Console.GetOpt
import Text.Printf

data Options = Options
  { maxDepth :: Int
  , mainType :: Type Z
  , showHelp :: Bool
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['d'] ["max-depth"]
    (ReqArg (\arg opts -> opts { maxDepth = read arg }) "NUM")
    (printf "Search depth (default is %d)." (maxDepth defaultOptions))
  , Option ['t'] ["main-type"]
    (ReqArg (\arg opts -> opts { mainType = read arg }) "TYPE")
    (printf "Type of programs to enumerate (default is '%s')." (show (mainType defaultOptions)))
  , Option ['h'] ["help"]
    (NoArg (\opts -> opts { showHelp = True }))
    "Show this help."
  ]

defaultOptions :: Options
defaultOptions = Options
  { maxDepth = 3
  , mainType = TyVoid :-> TyVoid
  , showHelp = False
  }

usageHeader :: String
usageHeader = "Usage: [OPTION...]\n"

parseOpts :: [String] -> IO (Options, [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo usageHeader options))

main :: IO ()
main = do
  -- Parse command-line arguments
  Options{..} <- fmap fst . parseOpts =<< getArgs

  -- Print the usage info and exit
  when showHelp $ do
    putStrLn (usageInfo usageHeader options)
    exitSuccess

  -- Enumerate and print terms
  mapM_ print =<< enumClosedTm maxDepth mainType
