
--==== Generic Combinators ====--

def imap 'a : (n : i64) -> (i64 -> a) -> [n]a =
  \ n f -> map f (iota n)

def imap1 = imap

def imap2 'a : (m: i64) -> (n : i64) -> (i64 -> i64 -> a) -> [m][n]a =
  \ m n f -> imap m (\i -> imap n (f i))

def imap3 'a : (m: i64) -> (n : i64) -> (k : i64) 
            -> (i64 -> i64 -> i64 -> a) -> [m][n][k]a =
  \ m n k f -> imap m (\i -> imap2 n k (f i))

def imap4 'a : (m: i64) -> (n : i64) -> (k : i64) -> (l : i64)
            -> (i64 -> i64 -> i64 -> i64 -> a) -> [m][n][k][l]a =
  \ m n k l f -> imap m (\i -> imap3 n k l (f i))

def unzip7 [n] 'a 'b 'c 'd 'e 'f 'g
    : (a : [n](a, b, c, d, e, f, g)) -> ([n]a, [n]b, [n]c, [n]d, [n]e, [n]f, [n]g) =
  \ a ->
  (imap n (\i -> a[i].0),
   imap n (\i -> a[i].1),
   imap n (\i -> a[i].2),
   imap n (\i -> a[i].3),
   imap n (\i -> a[i].4),
   imap n (\i -> a[i].5),
   imap n (\i -> a[i].6))


def zipWith [n] 'a 'b 'c : (a -> b -> c) -> ([n]a) -> ([n]b) -> [n]c =
  \ f a b ->
  map (uncurry f) (zip a b)

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

  -- Back multi convolution 1d
  def backmconv1 [In][kn][bn] :  (dout : [bn][In-kn+1]real) -> (w : [bn][kn]real)
                              -> (I : [In]real) -> (b : [bn]real) 
                              -> ([In]real, [bn][kn]real, [bn]real) = -- ∂I ∂w ∂b
    \dout w I b ->
    -- Reverse convolution
    let dI = loop r = map (\_-> zero) (iota In) for i < kn do
               loop r' = r for j < In-kn+1 do
                  r' with [i+j] = copy r'[i+j] F.+ sum (map (\k -> dout[k][j] F.* w[k][i]) (iota bn))
    
    let dw = map (\i -> conv1 I dout[i]) (iota bn)
    let db = map (\i -> sum dout[i]) (iota bn)
    in (dI, (dw :> [bn][kn]real), db)

  --==== 2d cases ====--
  def sum2d (a: [][]real) : real = 
    sum (map sum a)

  def conv2d [Im][In][km][kn]: 
    (I : [Im][In]real) -> (k: [km][kn]real) -> [Im - km + 1][In - kn + 1]real =
    \ I k ->
    --let rm = Im - km + 1
    --let rn = In - kn + 1
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

  -- Back multi convolution 2d
  def backmconv2 [Im][In][km][kn][kbn] 
                 :  (dout :  [kbn][Im - km + 1][In - kn + 1]real) 
                 -> (w : [kbn][km][kn]real)
                 -> (I : [Im][In]real)
                 -> (b : [kbn]real) 
                 -> ([Im][In]real, [kbn][km][kn]real, [kbn]real) = -- ∂I ∂w ∂b
    \dout w I b ->
    -- Reverse convolution
    let dI = 
      loop r0 = map (\_-> map (\_ -> zero) (iota Im)) (iota In) for i0 < km do
      loop r1 = r0 for i1 < kn do
      loop r2 = r1 for j0 < Im-km+1 do
      loop r3 = r2 for j1 < In-kn+1 do
        r3 with [i0+j0,i1+j1] = copy r3[i0+j0][i1+j1]
             F.+ sum (map (\k -> dout[k][j0][j1] F.* w[k][i0][i1]) (iota kbn))
 
    
    let dw = map (\i -> conv2d I dout[i]) (iota kbn)
    let db = map (\i -> sum2d dout[i]) (iota kbn)
    in ((dI :> [Im][In]real), (dw :> [kbn][km][kn]real), db)

  --==== 3d cases ====--
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
    --let add3d a b = map (\s2d -> map (\s1d -> map (\s0d -> s0d + b) s1d) s2d) a
    let _ = ()
    in map (\j -> add3d_c (conv3d I (weights[j])) b[j]) (iota kbn)

  def backmconv3 [Im][In][Ik][km][kn][kk][kbn] 
                 :  (dout :  [kbn][Im-km+1][In-kn+1][Ik-kk+1]real) 
                 -> (w : [kbn][km][kn][kk]real)
                 -> (I : [Im][In][Ik]real)
                 -> (b : [kbn]real) 
                 -> ([Im][In][Ik]real, [kbn][km][kn][kk]real, [kbn]real) = -- ∂I ∂w ∂b
    \dout w I b ->
    -- Reverse convolution
    let dI = 
      loop r0 = map (\_-> map (\_ -> map (\_ -> zero) (iota Ik)) (iota In)) (iota Im) for i0 < km do
      loop r1 = r0 for i1 < kn do
      loop r2 = r1 for i2 < kk do

      loop r3 = r2 for j0 < Im-km+1 do
      loop r4 = r3 for j1 < In-kn+1 do
      loop r5 = r4 for j2 < Ik-kk+1 do
        r5 with [i0+j0,i1+j1,i2+j2] = copy r5[i0+j0][i1+j1][i2+j2]
             F.+ sum (map (\k -> dout[k][j0][j1][j2] F.* w[k][i0][i1][i2]) (iota kbn))

    let dw = map (\i -> conv3d I dout[i]) (iota kbn)
    let db = map (\i -> sum3d dout[i]) (iota kbn)
    in (trace(dI :> [Im][In][Ik]real), (dw :> [kbn][km][kn][kk]real), db)
 
  --==== Logistics ====--
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
              -> (b2 : [12]real) -> (fc : [10][12][4][4]real)
              -> (b : [10]real)
              -> [10]real =
    \ inp k1 b1 k2 b2 fc b -> 
    let c1  --: [6][24][24]real 
        = logistics3 (mconv2d inp k1 b1)
    let s1  --: [6][12][12]real 
        = map avgp2 (c1 :> [6][12*2][12*2]real)
    let c2' --: [12][1][8][8]real
        = logistics4 (mconv3d s1 k2 b2)
    let c2  --: [12][8][8]real
        = flatten c2' :> [12][8][8]real
    let s2  --: [12][4][4]real
        = map avgp2 (c2 :> [12][4*2][4*2]real)
    let r   --: [10][1][1][1] 
        = logistics4 (mconv3d s2 fc b)
    in flatten (flatten (flatten r)) :> [10]real


  def train :  (inp : [28][28]real) -> (k1 : [6][5][5]real)
              -> (b1 : [6]real) -> (k2 : [12][6][5][5]real)
              -> (b2 : [12]real) -> (fc : [10][12][4][4]real)
              -> (b : [10]real)
              -> (target : [10]real)
              -> ([6][5][5]real,       -- ∂k1
                  [6]real,             -- ∂b1
                  [12][6][5][5]real,   -- ∂k2
                  [12]real,            -- ∂b2
                  [10][12][4][4]real,  -- ∂fc
                  [10]real,            -- ∂b
                  real)                -- error
              =
    \ inp k1 b1 k2 b2 fc b target ->
    let c1  --: [6][24][24]real 
        = logistics3 (mconv2d inp k1 b1)
    let s1  --: [6][12][12]real 
        = map avgp2 (c1 :> [6][12*2][12*2]real)
    let c2' --: [12][1][8][8]real
        = logistics4 (mconv3d s1 k2 b2)
    let c2  --: [12][8][8]real
        = flatten c2' :> [12][8][8]real
    let s2  --: [12][4][4]real
        = map avgp2 (c2 :> [12][4*2][4*2]real)
    let r   --: [10][1][1][1] 
        = logistics4 (mconv3d s2 fc b)
    let out = flatten (flatten (flatten r)) :> [10]real

    let err = sum (zipWith (\x y -> let d = x F.- y in d F.* d F./ fromi64 2) out target) 
    let dout = zipWith (F.-) out target


    -- Thes conversions are fucked-up
    let (ds2, dfc, db) = backmconv3 (unflatten_4d(backlog1 dout out :> [10*(12-12+1)*(4-4+1)*(4-4+1)]real)) fc s2 b
    let dc2 = map backavgp2 ds2 :> [12][8][8]real
    let (ds1, dk2, db2) = backmconv3 (unflatten (backlog3 dc2 c2 :> [12*1][8][8]real) :> [12][6-6+1][12-5+1][12-5+1]real) k2 s1 b2
    let dc1 = map backavgp2 ds1 :> [6][24][24]real
    let (_, dk1, db1) = backmconv2 (backlog3 dc1 (c1 :> [6][24][24]real) :> [6][28-5+1][28-5+1]real) k1 inp b1

    --in (dk1, db1, dk2, db2, dfc, db, err)
    in (dk1, db1, dk2, db2, dfc, db, err)

  --def main (n: i32) : real =
  --  fromi64 42
}

open nn (f32)

-- Mnist parsing
def decode_u32_be (w: [4]u8) =
  (u32.u8 w[0] << 24)
  | (u32.u8 w[1] << 16)
  | (u32.u8 w[2] << 8)
  | (u32.u8 w[3] << 0)

def decode_label_file (s: []u8) =
  let magic = decode_u32_be (take 4 s)
  in assert (magic==2049)
            (map i8.u8 (drop 8 s))

def decode_image_file (s: []u8) =
  let magic = decode_u32_be (take 4 s)
  let n = i64.u32 (decode_u32_be (take 4 (drop 4 s)))
  let rows = i64.u32 (decode_u32_be (take 4 (drop 8 s)))
  let columns = i64.u32 (decode_u32_be (take 4 (drop 12 s)))
  let get_img i = unflatten (map f32.u8 (take (rows*columns) (drop (16+i*rows*columns) s)))
  in assert (magic==2051) (tabulate n get_img)



entry run (imgs_bytes : []u8) (lbls_bytes : []u8) =
  let imgs = decode_image_file imgs_bytes
  let lbls = decode_label_file lbls_bytes

  let imgs_num = length imgs
  let _ = assert (length lbls == imgs_num) ()

  -- Fixed initial weights as we use in SaC
  let k1 = imap3 6 5 5     (\_ _ _   -> 1.0/25.0)
  let b1 = imap1 6         (\_       -> 1.0/6.0)
  let k2 = imap4 12 6 5 5  (\_ _ _ _ -> 1.0/150.0)
  let b2 = imap1 12        (\_       -> 1.0/12.0)
  let fc = imap4 10 12 4 4 (\_ _ _ _ -> 1.0/192.0)
  let b  = imap1 10        (\_       -> 1.0/10.0)

  let epochs    = 10
  let batchsize = 100
  let trainings = 10000
  --let tests     = 10000
  let rate      = 0.05

  let gen_target i = imap 10 (\j -> if j == i then 1.0 else 0.0)

  let avg (a : []f32) = sum a / f32.i64 (length a)

  let m = loop (k1, b1, k2, b2, fc, b)
       = (k1, b1, k2, b2, fc, b) for epoch < epochs do
    let t = loop (k1, b1, k2, b2, fc, b, err)
         = (k1, b1, k2, b2, fc, b, 0.0) for i < trainings / batchsize do
      -- This is where we call trainings in parallel!
      let t = imap batchsize 
                   (\j -> 
                      let img = imgs[i*batchsize+j] :> [28][28]f32
                      let lbl = gen_target (i64.i8 lbls[i*batchsize+j])
                      in train img k1 b1 k2 b2 fc b lbl)
      let (bdk1, bdb1, bdk2, bdb2, bdfc, bdb, berr) = unzip7 t
      -- TODO: these should happen in-place, but hopefully this is not
      --       a hotspot, the arrays are rather small.
      let k1' = imap3 6 5 5 (\i j k -> 
                   k1[i][j][k] - rate * (avg (imap batchsize (\t -> bdk1[t][i][j][k]))))
      let b1' = imap1 6 (\i -> 
                   b1[i] - rate * (avg (imap batchsize (\t -> bdb1[t][i]))))
      let k2' = imap4 12 6 5 5 (\i j k l -> 
                   k2[i][j][k][l] - rate * (avg (imap batchsize (\t -> bdk2[t][i][j][k][l]))))
      let b2' = imap1 12 (\i -> 
                   b2[i] - rate * (avg (imap batchsize (\t -> bdb2[t][i]))))
      let fc' = imap4 10 12 4 4 (\i j k l -> 
                   fc[i][j][k][l] - rate * (avg (imap batchsize (\t -> bdfc[t][i][j][k][l]))))
      let b'  = imap1 10 (\i -> 
                   b[i] - rate * (avg (imap batchsize (\t -> bdb[t][i]))))

      in (k1', b1', k2', b2', fc', b', err + sum berr)
    in (t.0, t.1, t.2, t.3, t.4, t.5)

  in m.0[0][0][0] + m.1[0] + m.2[0][0][0][0] + m.3[0] + m.4[0][0][0][0] + m.5[0]
