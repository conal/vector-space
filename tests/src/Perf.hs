{-# LANGUAGE TypeOperators, MultiParamTypeClasses, UndecidableInstances, FlexibleInstances
           , TypeFamilies, FlexibleContexts
  #-}


-- This module tests *performance* of the vector-space operations, such that it is possible to catch performance regressions.


module Main where

import Control.Applicative
import System.Time
import Data.List

import Data.NumInstances ()
import Data.VectorSpace
import Data.Cross
import Data.Derivative
import Data.Basis
import Data.MemoTrie
import Data.LinearMap

type Surf s        = (s,s) -> (s,s,s)
type HeightField s = (s,s) -> s
type Curve2 s      = s -> (s,s)

type Warp1 s        = s -> s
type Warp2 s        = (s,s) -> (s,s)
type Warp3 s        = (s,s,s) -> (s,s,s)

type R = Double

cosU, sinU :: Floating s => s -> s
cosU = cos . mul2pi
sinU = sin . mul2pi

mul2pi :: Floating s => s -> s
mul2pi = (* (2*pi))

torus :: (Floating s, VectorSpace s s) => s -> s -> Surf s
torus sr cr = revolve (\ s -> (sr,0) ^+^ cr *^ circle s)

-- Try use rules to optimize?
-- # RULES "sphere" sphere1 = spec_sphere1
sphere1 :: Floating s => Surf s
sphere1 = revolve semiCircle

spec_sphere1 :: Surf ((Double,Double) :> Double)
spec_sphere1 = sphere1

semiCircle :: Floating s => Curve2 s
semiCircle = circle . (/ 2)

circle :: Floating s => Curve2 s
circle = liftA2 (,) cosU sinU

revolveG :: Floating s => (s -> Curve2 s) -> Surf s
revolveG curveF = \ (u,v) -> onXY (rotate (-2*pi*v)) (addY (curveF v) u)

revolve :: Floating s => Curve2 s -> Surf s
revolve curve = revolveG (const curve)

rotate :: Floating s => s -> Warp2 s
rotate theta = \ (x,y) -> (x * c - y * s, y * c + x * s)
 where c = cos theta
       s = sin theta

addX, addY, addZ :: Num s => (a -> Two s) -> (a -> Three s)
addX = fmap (\ (y,z) -> (0,y,z))
addY = fmap (\ (x,z) -> (x,0,z))
addZ = fmap (\ (x,y) -> (x,y,0))

addYZ,addXZ,addXY :: Num s => (a -> One s) -> (a -> Three s)
addYZ = fmap (\ x -> (x,0,0))
addXZ = fmap (\ y -> (0,y,0))
addXY = fmap (\ z -> (0,0,z))

onX,onY,onZ :: Warp1 s -> Warp3 s
onX f (x,y,z) = (f x, y, z)
onY f (x,y,z) = (x, f y, z)
onZ f (x,y,z) = (x, y, f z)

onXY,onYZ,onXZ :: Warp2 s -> Warp3 s
onXY f (x,y,z) = (x',y',z ) where (x',y') = f (x,y)
onXZ f (x,y,z) = (x',y ,z') where (x',z') = f (x,z)
onYZ f (x,y,z) = (x ,y',z') where (y',z') = f (y,z)


onX',onY',onZ' :: Warp1 s -> (a -> Three s) -> (a -> Three s)
onX' = fmap fmap onX
onY' = fmap fmap onY
onZ' = fmap fmap onZ

onXY',onXZ',onYZ' :: Warp2 s -> (a -> Three s) -> (a -> Three s)
onXY' = fmap fmap onXY
onXZ' = fmap fmap onXZ
onYZ' = fmap fmap onYZ

displace :: (InnerSpace v s, Floating s, HasNormal v, Applicative f) =>
            f v -> f s -> f v
displace = liftA2 displaceV

displaceV :: (InnerSpace v s, Floating s, HasNormal v) =>
             v -> s -> v
displaceV v s = v ^+^ s *^ normal v

------------------------------------------------------------------------------

surfs3 :: [(Surf ((Double,Double) :> Double),String)]
surfs3 = [ (displace surf hmap,m1 ++ " `displace` " ++ m2) 
	 | (surf,m1) <- surfs2
	 , (hmap,m2) <- hmaps
	 ]

surfs2 :: [(Surf ((Double,Double) :> Double),String)]
surfs2 = [ (displace surf hmap,m1 ++ " `displace` " ++ m2) 
	 | (surf,m1) <- surfs
	 , (hmap,m2) <- hmaps
	 ]

surfs :: [(Surf ((Double,Double) :> Double),String)]
surfs =
  [ (torus 1 (1/2) ,"torus")
  , (sphere1,"sphere")
  ]

hmaps :: [(HeightField ((Double,Double) :> Double),String)]
hmaps = 
  [ (\ (_,_) -> 0,"flat")
  , (\ (u,v) -> cosU u * sinU v,"eggcrate")
  ]

main :: IO ()
main = do 
	let loop msg fun t count (points:pss) = do
		sequence_ [ p1 `seq` p2 `seq` p3 `seq` n1 `seq` n2 `seq` n3 `seq` return ()
        	          | (x,y) <- points
		          , let ((p1,p2,p3),(n1,n2,n3)) = vsurf fun (x,y) ]
		diff <- currRelTime t
--		print diff
		if diff > 2
		  then do let count' = count + length points
			  putStrLn $ "Sample count rate for " ++ msg ++ " is " ++ show (fromIntegral count' / diff) ++ " (total count = " ++ show count' ++ ")"
			  return ()
		  else loop msg fun t (count + length points) pss
	    loop _ _ _ _ _ = return ()

	let samples = samples_2d

	sequence_ [ do t <- getClockTime
		       loop msg fun t 0 samples
		  | (fun,msg) <- concat [ surfs, surfs, surfs, surfs2, surfs3 ]
	 	  ]

currRelTime :: ClockTime -> IO Double
currRelTime (TOD sec0 pico0) = fmap delta getClockTime
 where
   delta (TOD sec pico) =
     fromIntegral (sec-sec0) + 1.0e-12 * fromIntegral (pico-pico0)

------------------------------------------------------------------------------

vsurf :: Surf ((R,R) :> R) -> (R,R) -> ((R,R,R),(R,R,R))
vsurf surf = toVN3 . vector3D . surf . unvector2D . idD

type SurfPt s = (s,s) :> (s,s,s)

toVN3 :: (HasBasis s s, Basis s ~ (), Floating s, InnerSpace s s)
         => SurfPt s -> ((s,s,s),(s,s,s))
toVN3 v = ( powVal v
	  , powVal (normal v)
	  )
vector3D :: (HasBasis a s, HasTrie (Basis a), VectorSpace s s) => (a :> s,a :> s,a :> s) -> (a :> (s,s,s))
vector3D (u,v,w) = liftD3 (,,) u v w
unvector2D :: (HasBasis a s, HasTrie (Basis a), VectorSpace s s) => (a :> (s,s)) -> (a :> s,a :> s) 
unvector2D d = ( (\ (x,_) -> x) <$>> d
	       , (\ (_,y) -> y) <$>> d
	       )

------------------------------------------------------------------------------

between :: [Double] -> [Double]
between xs = [ (n + m) / 2 | (n,m) <- zip xs (tail xs) ]

samples_1d :: [[Double]]
samples_1d = fn [0,1]
     where
	fn :: [Double] -> [[Double]]
	fn points = points : fn (sort (points ++ between points))

samples_2d :: [[(Double,Double)]]
samples_2d =  [ [ (a,b) 
		| a <- sam
		, b <- sam
		]
  	      | sam <- samples_1d
	      ]

-- only allows new points through.
progressive_filter :: (Ord a) => [[a]] -> [[a]]
progressive_filter xs = head sorted_xs : [ y \\ x | (x,y) <- zip sorted_xs (tail sorted_xs) ]
  where
	sorted_xs = map sort xs
