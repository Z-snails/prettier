module Example

import Text.PrettyPrint.Bernardy as BB
import Data.Maybe

data SExp = SAtom String | SList (List SExp)

Pretty SExp where
    pretty (SAtom x) = fromString x
    pretty (SList xs) = hcat ["(", !(traverse pretty xs >>= sep), ")"]

mySExp : SExp
mySExp = SList [SAtom "abcd", SAtom "efgh", SAtom "ijkl", SAtom "mnop"]

exp2 : SExp
exp2 = SList [mySExp, mySExp, mySExp]

opts : LayoutOpts
opts = Opts 40

main : IO ()
main = putStrLn $ fromMaybe "ERROR" $ BB.render opts $ runReader opts $ pretty exp2
