import MinHS.Parse
import MinHS.Syntax
import MinHS.TyInfer
import MinHS.Pretty hiding (err)
import MinHS.Evaluator
import Control.Monad
import Options.Applicative
import Options.Applicative.Types

import qualified Prettyprinter as PP (Doc, unAnnotate, vcat, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle,putDoc)

type Action a b = a -> Either (IO ()) b
type Doc = PP.Doc AnsiStyle

(<^>) :: (Monoid a) => a -> a -> a
(<^>) = mappend

main :: IO ()
main = execParser argsInfo >>= main'
  where main' (pipeline, paint, file) = (pipeline paint <$> readFile file) >>= either id id

        argsInfo = info (helper <*> args)
                    (fullDesc <^> progDesc "A interpreter for a small functional language"
                              <^> header "MinHS - COMP3161 Concepts of Programming Languages")

        args =  (,,) <$> option readAction ( long "dump"
                               <^> metavar "STAGE"
                               <^> value (evaluatorAction)
                               <^> help "stage after which to dump the current state. \n                           [parser,parser-raw,type-infer,evaluator]")
                     <*> flag id PP.unAnnotate (long "no-colour"
                                     <^> help "do not use colour when pretty printing")
                     <*> argument str (metavar "FILE")
        readAction :: ReadM ((Doc -> Doc) -> Action String (IO ()))
        readAction = readerAsk >>= \x -> case x of
            "parser"      -> return $ \f -> parser >=> printer f
            "parser-raw"  -> return $ \_ -> parser >=> rawPrinter
            "type-infer"  -> return $ \f -> parser >=> typechecker f >=> printer f
            "evaluator"   -> return $ evaluatorAction
            _             -> readerAbort (ShowHelpText Nothing)

        evaluatorAction :: (Doc -> Doc) -> Action String (IO ())
        evaluatorAction f = parser >=> typechecker f >=> evaluator >=> printer f

        parser :: Action String Program
        parser = either (Left . putStrLn . show) Right . parseProgram ""

        typechecker :: (Doc -> Doc) -> Action Program Program
        typechecker f p = case infer p of
                           Left err  -> Left . (>> putStrLn "") . putDoc . f . ansipp $ err
                           Right (p', _) -> Right p'

        evaluator p = Right $ evaluate p

        rawPrinter :: (Show a) => Action a (IO ())
        rawPrinter = Right . putStrLn . show

        printer :: (ANSIPretty a) => (Doc -> Doc) -> Action a (IO ())
        printer paint = Right . (>> putStrLn "") . putDoc . paint . ansipp
