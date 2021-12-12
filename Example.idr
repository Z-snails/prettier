module Example

import Text.PrettyPrint.Bernardy as BB
import Data.Maybe

data SExp = SAtom String | SList (List SExp)

Pretty SExp where
    pretty (SAtom x) = fromString x
    pretty (SList xs) = hcat ["(", sep $ map pretty xs, ")"]

generateSExp : Nat -> SExp
generateSExp Z = SList [SAtom "a", SAtom "b", SAtom "c", SAtom "d", SAtom "e", SAtom "f"]
generateSExp (S k) =
    let sub = generateSExp k
     in SList [sub, sub, sub]

mySExp : SExp
mySExp = SList [SAtom "abcd", SAtom "efgh", SAtom "ijkl", SAtom "mnop"]

exp2 : SExp
exp2 = SList [mySExp, mySExp, mySExp]

opts : LayoutOpts
opts = Opts 60

main : IO ()
main = putStrLn $ fromMaybe "ERROR" $ BB.render opts $ pretty $ generateSExp 6
