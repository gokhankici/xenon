module Main where

import           Data.Foldable
import qualified Data.Text.IO as TIO
import Iodine.Language.PrologParser
import           System.Environment
import           System.Exit
import           System.IO

err :: String -> IO a
err msg = hPutStrLn stderr msg >> exitFailure

getFilename :: IO FilePath
getFilename = do
  args <- getArgs
  case args of
    [filename] -> return filename
    _ -> err "usage: prolog-pretty filename"


main :: IO ()
main = do
  filename <- getFilename
  fileContents <- TIO.readFile filename
  case parseProlog filename fileContents of
    Right ms -> for_ ms print
    Left msg -> err msg
