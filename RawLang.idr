module RawLang

import NatCmp
import Bounded

public export
Label : Type
Label = String

public export
data RStackInst = RPUSH Integer
                | RDUP
                | RCOPY Nat
                | RSWAP
                | RDISCARD
                | RSLIDE Nat

public export
data RArithInst = RADD | RSUB | RMUL | RDIV | RMOD

public export
data RHeapInst = RSTORE | RRETRIEVE

public export
data RFlowInst = RLABEL Label
               | RCALL Label
               | RJUMP Label
               | RJZ Label
               | RJNEG Label
               | RRETURN
               | REND

public export
data RIOInst = ROUTPUT | ROUTPUTNUM | RREADCHAR | RREADNUM

public export
data RInstr = RStk RStackInst
            | RAr RArithInst
            | RHp RHeapInst
            | RFl RFlowInst
            | RIOi RIOInst
