
module nn (F: real) = {
  type real = F.t

  def fromi64 (n : i64) = F.from_fraction n 1 
  def zero = fromi64 0
  def one = fromi64 1

  def sum (a : []real) : real =
    foldl (F.+) zero a

  def conv1 [In][kn]: (I : [In]real) -> (k: [kn]real) -> [In - kn + 1]real =
    \ I k ->
    let sr = In - kn + 1
    let sum_k i = sum (map (\j -> I[i+j] F.* k[j]) (iota kn))
    let r = map sum_k (iota sr)
    in r


  -- convolution with biases `b` which is a 1-d array.
  def mconv1 [In][kn][bn] : (I : [In]real) -> (k : [bn][kn]real) -> (b : [bn]real) 
                      -> [bn][In - kn + 1]real =
    \ I k b -> map (\i -> map (F.+ b[i]) (conv1 I k[i])) (iota bn)


  ----- 2d cases -----
  def sum2d (a: [][]real) : real = 
    sum (map sum a)

  def conv2d [Im][In][km][kn]: 
    (I : [Im][In]real) -> (k: [km][kn]real) -> [Im - km + 1][In - kn + 1]real =
    \ I k ->
    let rm = Im - km + 1
    let rn = In - kn + 1
    let sum_k i j =
      sum2d
        (map (\i' ->
                  map (\j' ->
                           I[i+i'][j+j']F.*k[i'][j'])
                      (iota kn))
             (iota km))
    let r = map (\i -> map (\j -> sum_k i j) (iota (In - kn + 1))) (iota (Im - km + 1))
    in r

  def mconv2d [Im][In][km][kn][kbn] 
              :  (I : [Im][In]real) -> (k : [kbn][km][kn]real)
              -> (b : [kbn]real) -> [kbn][Im - km + 1][In - kn + 1]real =
    \ I k b ->
    let add2d a b = map (\r -> map (\c -> c + b) r) a
    in map (\j ->  (conv2d I (k[j])) ) (iota kbn)


  def logistics1 [n] : (a : [n]real) -> [n]real =
     map (\e -> one F./ (one F.+ F.exp (F.neg e)))

  def logistics2 [m][n] : (a : [m][n]real) -> [m][n]real =
    map logistics1

  def logistics3 [m][n][k] : (a : [m][n][k]real) -> [m][n][k]real =
    map logistics2

  def avgp2 [m][n] : (a : [m*2][n*2]real) -> [m][n]real =
    \ a ->
    map (\i ->
         map (\j ->
              sum2d
              (map (\i' ->
                    map (\j' -> a[2*i+i'][2*j+j']) (iota 2))
                   (iota 2))
              F./ (fromi64 4))
             (iota n))
        (iota m)

  def forward :  (inp : [28][28]real) -> (k1 : [6][5][5]real)
              -> (b1 : [6]real) -> (k2 : [12][6][5][5]real)
              -> real =
    \ inp k1 b1 k2 -> 
    --let (c1 : [6][24][24]real) = logistics3 (mconv2d inp k1 b1)
    let c1 = logistics3 (mconv2d inp k1 b1)
    --let s1 : [6][12][12]real = map avgp2 c1
    let s1 = map avgp2 (c1 :> [6][12*2][12*2]F.t)
    in zero

  def main (n: i32) : real =
    fromi64 42
}

open nn (f32)


