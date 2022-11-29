module Example

import Data.List1
import Text.PrettyPrint.Bernardy

data SExp = SAtom String | SList (List SExp)

Pretty SExp where
    prettyPrec _ (SAtom x) = fromString x
    prettyPrec _ (SList xs) = hcat ["(", sep $ map pretty xs, ")"]

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
main = putStrLn $ Doc.render opts $ pretty $ generateSExp 9
