module RecordsTest

import Prelude (vtype)

-- meta level
def Sigma (A : meta) (B : A -> meta) : meta = [fst : A, snd : B fst]

def testSigma : Sigma meta (\A => A) = [fst = meta -> meta, snd = \x => x]

def res1 = testSigma.fst
def res2 : res1 = testSigma.snd
def res3 = testSigma.0
def res4 : res3 = testSigma.1

def MetaTuple : meta = [meta, meta -> meta]
def metaTuple : MetaTuple = [meta, \x => x]
def metaTupleRes = metaTuple.1

-- runtime level
def Pair (A B : vtype) : vtype = [fst : A, snd : B]

def myPair1 : Pair Int Int := [1, 2]
def myPair2 : Pair Int Int := [fst := 1, snd := 2]
def myPair3 : Pair Int Int := [snd := 2, fst := 1]

def vres1 := myPair2.fst
def vres2 := myPair2.snd
def vres3 := myPair2.0
def vres4 := myPair2.1

def Tuple : vtype = [Int, Bool]
def tuple : Tuple := [42, False]
def tupleRes := tuple.1
