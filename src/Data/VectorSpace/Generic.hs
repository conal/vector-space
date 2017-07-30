-- |
-- Module      :   Data.VectorSpace.Generic
-- Copyright   :  (c) Conal Elliott and Justus Sagemüller 2017
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net, (@) jsagemue $ uni-koeln.de
-- Stability   :  experimental
-- 
-- Underpinnings of the type that represents vector / affine / etc. spaces
-- with GHC generics

module Data.VectorSpace.Generic where


import qualified GHC.Generics as Gnrx

import Data.Void


type VRep v = Gnrx.Rep v Void
