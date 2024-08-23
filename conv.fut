
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

  -- Back convolution
  def backmconv1 [In][kn][bn] :  (dout : [bn][In-kn+1]real) -> (w : [bn][kn]real)
                              -> (I : [In]real) -> (b : [bn]real) 
                              -> ([In]real, [bn][kn]real, [bn]real) = -- ∂I ∂k ∂b
    \dout w I b ->
    -- Reverse convolution
    -- FIXME: this doesn't work
    let dI = loop r = map (\_-> zero) (iota In) for i < kn do
               loop r' = r for j < In-kn+1 do
                  r' with [i+j] = r'[i+j] F.+ sum (map (\k -> dout[k][j] F.* w[k][i]) (iota bn))
    
    let dw = map (\i -> conv1 I dout[i]) (iota bn)
    let db = map (\i -> sum dout[i]) (iota bn)
    in (I, w, b)

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


  def add2d_c [m][n] :  (a : [m][n]real)
                     -> (b : real) -> [m][n]real =
    \ a b -> map (\s1d -> map (\s0d -> s0d F.+ b) s1d) a

  def mconv2d [Im][In][km][kn][kbn] 
              :  (I : [Im][In]real) -> (k : [kbn][km][kn]real)
              -> (b : [kbn]real) -> [kbn][Im - km + 1][In - kn + 1]real =
    \ I k b ->
    map (\j -> add2d_c (conv2d I (k[j])) b[j]) (iota kbn)

  ----- 3d cases -----
  def sum3d (a: [][][]real) : real = 
    sum (map sum2d a)
  
  def conv3d [Im][In][Ik][km][kn][kk]: 
    (I : [Im][In][Ik]real) -> (k: [km][kn][kk]real) 
    -> [Im - km + 1][In - kn + 1][Ik - kk + 1]real =
    \ I weights ->
    let rm = Im - km + 1
    let rn = In - kn + 1
    let rk = Ik - kk + 1
    let sum_k i j k =
      sum3d
        (map (\i' -> 
                  map (\j' ->
                           map (\k' -> I[i+i'][j+j'][k+k']
                                       F.* weights[i'][j'][k'])
                               (iota kk)) 
                      (iota kn)) 
             (iota km))
    let r = map (\i -> 
                    map (\j ->
                            map (\k -> sum_k i j k) 
                                (iota rk)) 
                        (iota rn)) 
                (iota rm)
    in r
    
  def add3d_c [m][n][k] :  (a : [m][n][k]real)
                     -> (b : real) -> [m][n][k]real =
    \ a b -> map (\s2d -> add2d_c s2d b) a
  
  def mconv3d [Im][In][Ik][km][kn][kk][kbn] 
              :  (I : [Im][In][Ik]real) -> (weights : [kbn][km][kn][kk]real)
              -> (b : [kbn]real) -> [kbn][Im - km + 1][In - kn + 1][Ik -kk +1]real =
    \ I weights b ->
    let add3d a b = map (\s2d -> map (\s1d -> map (\s0d -> s0d + b) s1d) s2d) a
    in map (\j -> add3d_c (conv3d I (weights[j])) b[j]) (iota kbn)

 
  -- Logistics
  def logistics1 [n] : (a : [n]real) -> [n]real =
     map (\e -> one F./ (one F.+ F.exp (F.neg e)))

  def logistics2 [m][n] : (a : [m][n]real) -> [m][n]real =
    map logistics1

  def logistics3 [m][n][k] : (a : [m][n][k]real) -> [m][n][k]real =
    map logistics2

  def logistics4 [m][n][k][p] : (a : [m][n][k][p]real) -> [m][n][k][p]real =
    map logistics3

  -- Back logistics
  def backlog1 [n] : (dout : [n]real) -> (out : [n]real) -> [n]real =
     map2 (\d o -> d F.* o F.* (one F.- o))

  def backlog2 [m][n] : (dout : [m][n]real) -> (out : [m][n]real) -> [m][n]real =
     map2 backlog1

  def backlog3 [m][n][k] : (dout : [m][n][k]real) -> (out : [m][n][k]real) -> [m][n][k]real =
     map2 backlog2

  def backlog4 [m][n][k][p] : (dout : [m][n][k][p]real) -> (out : [m][n][k][p]real) -> [m][n][k][p]real =
     map2 backlog3

  -- Average pooling 2d
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

  def backavgp2 [m][n] : (dout : [m][n]real) -> [m*2][n*2]real =
    \ dout ->
    map (\i ->
         map (\j -> dout[i/2][j/2] F./ (fromi64 4))
             (iota (n*2)))     
        (iota (m*2))


  def forward :  (inp : [28][28]real) -> (k1 : [6][5][5]real)
              -> (b1 : [6]real) -> (k2 : [12][6][5][5]real)
              -> (b2 : [12]real) -> (fc : [10][12][12][4]real)
              -> (b : [10]real)
              -> [10]real =
    \ inp k1 b1 k2 b2 fc b -> 
    --let (c1 : [6][24][24]real) = logistics3 (mconv2d inp k1 b1)
    let c1 = logistics3 (mconv2d inp k1 b1)
    --let s1 : [6][12][12]real = map avgp2 c1
    let s1 = map avgp2 (c1 :> [6][12*2][12*2]real)
    --c2' : [12][1][8][8]real
    let c2' = logistics4 (mconv3d s1 k2 b2)
    -- FIXME: how do I properly get rid of the second dimension in c2'?
    --        obviously it is stupid to copy the entire array
    --        as boty arrays have identical flattening...
    let c2 = (flatten c2' :> [12][8][8]real)
    --let c2 = map (\i -> map (\j -> map (\k -> c2'[i][0][j][k]) (iota 8)) (iota 8)) (iota 12)
    --let s2 : [12][4][4]real
    let s2 = map avgp2 (c2 :> [12][4*2][4*2]real)
    --lte r : [10][1][1][1]
    let r = logistics4 (mconv3d s2 fc b)
    -- FIXME: Again, how do you reshape the array `r` into the new shape
    --        so we get rid of dimensions of length 1?
    --in map (\i -> r[i][0][0][0]) (iota 10)
    in (flatten (flatten (flatten r)) :> [10]real)

  def main (n: i32) : real =
    fromi64 42
}

open nn (f32)


