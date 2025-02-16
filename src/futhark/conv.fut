--------- Generic Combinators ---------

def imap 'a : (n: i64) -> (i64 -> a) -> [n]a =
  \n f -> map f (iota n)

def imap1 = imap

def imap2 'a : (m: i64) -> (n: i64) -> (i64 -> i64 -> a) -> [m][n]a =
  \m n f -> imap m (\i -> imap n (f i))

def imap3 'a : (m: i64)
-> (n: i64)
-> (k: i64)
-> (i64 -> i64 -> i64 -> a) -> [m][n][k]a =
  \m n k f -> imap m (\i -> imap2 n k (f i))

def imap4 'a : (m: i64)
-> (n: i64)
-> (k: i64)
-> (l: i64)
-> (i64 -> i64 -> i64 -> i64 -> a) -> [m][n][k][l]a =
  \m n k l f -> imap m (\i -> imap3 n k l (f i))

def imap5 'a : (m: i64)
-> (n: i64)
-> (k: i64)
-> (l: i64)
-> (t: i64)
-> (i64 -> i64 -> i64 -> i64 -> i64 -> a) -> [m][n][k][l][t]a =
  \m n k l t f -> imap m (\i -> imap4 n k l t (f i))

def unzip7 [n] 'a 'b 'c 'd 'e 'f 'g : (a: [n](a, b, c, d, e, f, g)) -> ([n]a, [n]b, [n]c, [n]d, [n]e, [n]f, [n]g) =
  \a ->
    ( imap n (\i -> a[i].0)
    , imap n (\i -> a[i].1)
    , imap n (\i -> a[i].2)
    , imap n (\i -> a[i].3)
    , imap n (\i -> a[i].4)
    , imap n (\i -> a[i].5)
    , imap n (\i -> a[i].6)
    )

def zipWith [n] 'a 'b 'c : (a -> b -> c) -> ([n]a) -> ([n]b) -> [n]c =
  \f a b ->
    map (uncurry f) (zip a b)

--==== Convolution Module ====--
module nn (F: real) = {
  type real = F.t

  def fromi64 (n: i64) = F.from_fraction n 1
  def zero = fromi64 0
  def one = fromi64 1

  def isum1 : (m: i64) -> (i64 -> real) -> real =
    \m f -> loop r = zero for i < m do r F.+ f i

  def isum2 : (m: i64)
  -> (n: i64)
  -> (i64 -> i64 -> real) -> real =
    \m n f -> loop r = zero for i < m do r F.+ isum1 n (f i)

  def isum3 : (m: i64)
  -> (n: i64)
  -> (k: i64)
  -> (i64 -> i64 -> i64 -> real) -> real =
    \n m k f -> loop r = zero for i < n do r F.+ isum2 m k (f i)

  def isum4 : (m: i64)
  -> (n: i64)
  -> (k: i64)
  -> (l: i64)
  -> (i64 -> i64 -> i64 -> i64 -> real) -> real =
    \n m k l f -> loop r = zero for i < n do r F.+ isum3 m k l (f i)

  def isum5 : (m: i64)
  -> (n: i64)
  -> (k: i64)
  -> (l: i64)
  -> (t: i64)
  -> (i64 -> i64 -> i64 -> i64 -> i64 -> real) -> real =
    \n m k l t f -> loop r = zero for i < n do r F.+ isum4 m k l t (f i)

  def sum (a: []real) : real =
    reduce (F.+) zero a

  def sum1d (a: []real) : real = sum a

  def conv1 [In] [kn] : (I: [In]real) -> (k: [kn]real) -> [In - kn + 1]real =
    \I k ->
      let sum_k i = sum (imap kn (\j -> I[i + j] F.* k[j]))
      in imap (In - kn + 1) sum_k

  -- convolution with biases `b` which is a 1-d array.
  def mconv1 [In] [kn] [bn] : (I: [In]real)
  -> (k: [bn][kn]real)
  -> (b: [bn]real)
  -> [bn][In - kn + 1]real =
    \I k b -> imap bn (\i -> map (F.+ b[i]) (conv1 I k[i]))

  -- Back multi convolution 1d
  def backmconv1 [In] [kn] [bn] : (dout: [bn][In - kn + 1]real)
  -> (w: [bn][kn]real)
  -> (I: [In]real)
  -> (b: [bn]real)
  -> ([In]real, [bn][kn]real, [bn]real) =
    -- ∂I ∂w ∂b
    \dout w I b ->
      -- Reverse convolution
      let dI =
        loop r = imap In (\_ -> zero)
        for i < kn do
          loop r' = r
          for j < In - kn + 1 do
            r' with [i + j] = copy r'[i + j] F.+ sum (map (\k -> dout[k][j] F.* w[k][i]) (iota bn))
      let dw = imap bn (\i -> conv1 I dout[i])
      let db = imap bn (\i -> sum dout[i])
      in (dI, (dw :> [bn][kn]real), db)

  --==== 2d cases ====--
  def sum2d (a: [][]real) : real =
    sum (map sum a)

  --sum (flatten a)

  def conv2d [Im] [In] [km] [kn] : (I: [Im][In]real) -> (k: [km][kn]real) -> [Im - km + 1][In - kn + 1]real =
    \I k ->
      let sum_k i j = sum2d (imap2 km kn (\i' j' -> I[i + i'][j + j'] F.* k[i'][j']))
      in imap2 (Im - km + 1) (In - kn + 1) sum_k

  def add2d_c [m] [n] : (a: [m][n]real)
  -> (b: real) -> [m][n]real =
    \a b -> map (\s1d -> map (\s0d -> s0d F.+ b) s1d) a

  def mconv2d [Im] [In] [km] [kn] [kbn] : (I: [Im][In]real)
  -> (k: [kbn][km][kn]real)
  -> (b: [kbn]real) -> [kbn][Im - km + 1][In - kn + 1]real =
    \I k b ->
      imap kbn (\j -> add2d_c (conv2d I (k[j])) b[j])

  -- Back multi convolution 2d
  def backmconv2 [Im] [In] [km] [kn] [kbn] : (dout: [kbn][Im - km + 1][In - kn + 1]real)
  -> (w: [kbn][km][kn]real)
  -> (I: [Im][In]real)
  -> (b: [kbn]real)
  -> ([Im][In]real, [kbn][km][kn]real, [kbn]real) =
    -- ∂I ∂w ∂b
    \dout w I b ->
      -- Reverse convolution
      let dI =
        --loop r0 = map (\_-> map (\_ -> zero) (iota Im)) (iota In) for i0 < km do
        loop r0 = imap2 Im In (\_ _ -> zero)
        for i0 < km do
          loop r1 = r0
          for i1 < kn do
            loop r2 = r1
            for j0 < Im - km + 1 do
              loop r3 = r2
              for j1 < In - kn + 1 do
                r3 with [i0 + j0, i1 + j1] = copy r3[i0 + j0][i1 + j1]
                   F.+ sum (map (\k -> dout[k][j0][j1] F.* w[k][i0][i1]) (iota kbn))
      let dw = imap kbn (\i -> conv2d I dout[i])
      let db = imap kbn (\i -> sum2d dout[i])
      in ((dI :> [Im][In]real), (dw :> [kbn][km][kn]real), db)

  --==== 3d cases ====--
  def sum3d (a: [][][]real) : real =
    sum (map sum2d a)

  --sum (flatten (flatten a))

  def conv3d [Im] [In] [Ik] [km] [kn] [kk] : (I: [Im][In][Ik]real)
  -> (k: [km][kn][kk]real)
  -> [Im - km + 1][In - kn + 1][Ik - kk + 1]real =
    \I weights ->
      let sum_k i j k =
        sum3d (imap3 km kn kk (\i' j' k' ->
                                 I[i + i'][j + j'][k + k']
                                 F.* weights[i'][j'][k']))
      in imap3 (Im - km + 1) (In - kn + 1) (Ik - kk + 1) sum_k

  def add3d_c [m] [n] [k] : (a: [m][n][k]real)
  -> (b: real) -> [m][n][k]real =
    \a b -> map (\s2d -> add2d_c s2d b) a

  def mconv3d [Im] [In] [Ik] [km] [kn] [kk] [kbn] : (I: [Im][In][Ik]real)
  -> (weights: [kbn][km][kn][kk]real)
  -> (b: [kbn]real) -> [kbn][Im - km + 1][In - kn + 1][Ik - kk + 1]real =
    \I weights b ->
      imap kbn (\j -> add3d_c (conv3d I (weights[j])) b[j])

  def backmconv3 [Im] [In] [Ik] [km] [kn] [kk] [kbn] : (dout: [kbn][Im - km + 1][In - kn + 1][Ik - kk + 1]real)
  -> (w: [kbn][km][kn][kk]real)
  -> (I: [Im][In][Ik]real)
  -> (b: [kbn]real)
  -> ([Im][In][Ik]real, [kbn][km][kn][kk]real, [kbn]real) =
    -- ∂I ∂w ∂b
    \dout w I b ->
      -- Reverse convolution
      let dI =
        loop r0 = imap3 Im In Ik (\_ _ _ -> zero)
        for i0 < km do
          loop r1 = r0
          for i1 < kn do
            loop r2 = r1
            for i2 < kk do
              loop r3 = r2
              for j0 < Im - km + 1 do
                loop r4 = r3
                for j1 < In - kn + 1 do
                  loop r5 = r4
                  for j2 < Ik - kk + 1 do
                    r5 with [i0 + j0, i1 + j1, i2 + j2] = copy r5[i0 + j0][i1 + j1][i2 + j2]
                       F.+ sum (map (\k -> dout[k][j0][j1][j2] F.* w[k][i0][i1][i2]) (iota kbn))
      let dw = imap kbn (\i -> conv3d I dout[i])
      let db = imap kbn (\i -> sum3d dout[i])
      in ((dI :> [Im][In][Ik]real), (dw :> [kbn][km][kn][kk]real), db)

  --==== >4 dim ====--
  def sum4d (a: [][][][]real) : real =
    sum (map sum3d a)

  def sum5d (a: [][][][][]real) : real =
    sum (map sum4d a)

  --==== Logistics ====--
  def logistics : real -> real =
    \e -> one F./ (one F.+ F.exp (F.neg e))

  def logistics1 [n] : (a: [n]real) -> [n]real =
    map logistics

  def logistics2 [m] [n] : (a: [m][n]real) -> [m][n]real =
    map logistics1

  def logistics3 [m] [n] [k] : (a: [m][n][k]real) -> [m][n][k]real =
    map logistics2

  def logistics4 [m] [n] [k] [p] : (a: [m][n][k][p]real) -> [m][n][k][p]real =
    map logistics3

  -- Back logistics
  def backlog1 [n] : (dout: [n]real) -> (out: [n]real) -> [n]real =
    map2 (\d o -> d F.* o F.* (one F.- o))

  def backlog2 [m] [n] : (dout: [m][n]real) -> (out: [m][n]real) -> [m][n]real =
    map2 backlog1

  def backlog3 [m] [n] [k] : (dout: [m][n][k]real) -> (out: [m][n][k]real) -> [m][n][k]real =
    map2 backlog2

  def backlog4 [m] [n] [k] [p] : (dout: [m][n][k][p]real) -> (out: [m][n][k][p]real) -> [m][n][k][p]real =
    map2 backlog3

  -- Average pooling 2d
  def avgp2 [m] [n] : (a: [m * 2][n * 2]real) -> [m][n]real =
    \a ->
      imap2 m n (\i j -> sum2d (imap2 2 2 (\i' j' -> a[2 * i + i'][2 * j + j'])) F./ fromi64 4)

  def backavgp2 [m] [n] : (dout: [m][n]real) -> [m * 2][n * 2]real =
    \dout ->
      imap2 (m * 2) (n * 2) (\i j -> dout[i / 2][j / 2] F./ fromi64 4)

  def forward : (inp: [28][28]real)
  -> (k1: [6][5][5]real)
  -> (b1: [6]real)
  -> (k2: [12][6][5][5]real)
  -> (b2: [12]real)
  -> (fc: [10][12][4][4]real)
  -> (b: [10]real)
  -> [10]real =
    \inp k1 b1 k2 b2 fc b ->
      let c1 =
        --: [6][24][24]real
        logistics3 (mconv2d inp k1 b1)
      let s1 =
        --: [6][12][12]real
        map avgp2 (c1 :> [6][12 * 2][12 * 2]real)
      let c2' =
        --: [12][1][8][8]real
        logistics4 (mconv3d s1 k2 b2)
      let c2 =
        --: [12][8][8]real
        flatten c2' :> [12][8][8]real
      let s2 =
        --: [12][4][4]real
        map avgp2 (c2 :> [12][4 * 2][4 * 2]real)
      let r =
        --: [10][1][1][1]
        logistics4 (mconv3d s2 fc b)
      in flatten (flatten (flatten r)) :> [10]real

  def mean_sq_err [n] : (res: [n]real) -> (lbl: [n]real) -> real =
    \res lbl -> sum (zipWith (\x y -> let d = x F.- y in d F.* d F./ fromi64 2) lbl res)

  def train : (inp: [28][28]real)
  -> (k1: [6][5][5]real)
  -> (b1: [6]real)
  -> (k2: [12][6][5][5]real)
  -> (b2: [12]real)
  -> (fc: [10][12][4][4]real)
  -> (b: [10]real)
  -> (target: [10]real)
  -> ( [6][5][5]real
     , -- ∂k1
       [6]real
     , -- ∂b1
       [12][6][5][5]real
     , -- ∂k2
       [12]real
     , -- ∂b2
       [10][12][4][4]real
     , -- ∂fc
       [10]real
     , -- ∂b
       real
     ) =
    -- error

    \inp k1 b1 k2 b2 fc b target ->
      let c1 =
        --: [6][24][24]real
        logistics3 (mconv2d inp k1 b1)
      let s1 =
        --: [6][12][12]real
        map avgp2 (c1 :> [6][12 * 2][12 * 2]real)
      let c2' =
        --: [12][1][8][8]real
        logistics4 (mconv3d s1 k2 b2)
      let c2 =
        --: [12][8][8]real
        flatten c2' :> [12][8][8]real
      let s2 =
        --: [12][4][4]real
        map avgp2 (c2 :> [12][4 * 2][4 * 2]real)
      let r =
        --: [10][1][1][1]
        logistics4 (mconv3d s2 fc b)
      let out = flatten (flatten (flatten r)) :> [10]real
      let err = mean_sq_err out target
      let dout = zipWith (F.-) out target
      let (ds2, dfc, db) = backmconv3 (unflatten_4d (backlog1 dout out :> [10 * (12 - 12 + 1) * (4 - 4 + 1) * (4 - 4 + 1)]real)) fc s2 b
      let dc2 = map backavgp2 ds2 :> [12][8][8]real
      let (ds1, dk2, db2) = backmconv3 (unflatten (backlog3 dc2 c2 :> [12 * 1][8][8]real) :> [12][6 - 6 + 1][12 - 5 + 1][12 - 5 + 1]real) k2 s1 b2
      let dc1 = map backavgp2 ds1 :> [6][24][24]real
      let (_, dk1, db1) = backmconv2 (backlog3 dc1 (c1 :> [6][24][24]real) :> [6][28 - 5 + 1][28 - 5 + 1]real) k1 inp b1
      in (dk1, db1, dk2, db2, dfc, db, err)

  def train_gen : (inp: [28][28]real)
  -> (k1: [6][5][5]real)
  -> (b1: [6]real)
  -> (k2: [12][6][5][5]real)
  -> (b2: [12]real)
  -> (fc: [10][12][4][4]real)
  -> (b: [10]real)
  -> (target: [10]real)
  -> ( [6][5][5]real
     , -- ∂k1
       [6]real
     , -- ∂b1
       [12][6][5][5]real
     , -- ∂k2
       [12]real
     , -- ∂b2
       [10][12][4][4]real
     , -- ∂fc
       [10]real
     , -- ∂b
       real
     ) =
    -- error
    #[unsafe]
    \(inp: [28][28]real) (k1: [6][5][5]real) (b1: [6]real) (k2: [12][6][5][5]real) (b2: [12]real) (fc': [10][12][4][4]real) (b: [10]real) (target': [10]real) ->
      let fc = map (\a -> unflatten (a :> [12 * 1][4][4]real)) fc' :> [10][12][1][4][4]real
      let target = unflatten (unflatten (unflatten (unflatten (target' :> [10 * 1]real) :> [10 * 1][1]real) :> [10 * 1][1][1]real) :> [10 * 1][1][1][1]real) :> [10][1][1][1][1]real
      let x0 = (imap3 6 24 24 (\x1_0 x1_1 x1_2 -> ((isum2 5 5 (\x2_0 x2_1 -> (inp[(x2_0 + x1_1)][(x2_1 + x1_2)] F.* k1[x1_0][x2_0][x2_1]))) F.+ b1[x1_0])))
      let x3 = (imap3 6 24 24 (\x4_0 x4_1 x4_2 -> (logistics x0[x4_0][x4_1][x4_2])))
      let x5 = (imap3 6 12 12 (\x6_0 x6_1 x6_2 -> ((isum2 2 2 (\x7_0 x7_1 -> x3[x6_0][((x6_1 * 2) + x7_0)][((x6_2 * 2) + x7_1)])) F./ fromi64 4)))
      let x8 = (imap4 12 1 8 8 (\x9_0 x9_1 x9_2 x9_3 -> ((isum3 6 5 5 (\x10_0 x10_1 x10_2 -> (x5[(x10_0 + x9_1)][(x10_1 + x9_2)][(x10_2 + x9_3)] F.* k2[x9_0][x10_0][x10_1][x10_2]))) F.+ b2[x9_0])))
      let x11 = (imap4 12 1 8 8 (\x12_0 x12_1 x12_2 x12_3 -> (logistics x8[x12_0][x12_1][x12_2][x12_3])))
      let x13 = (imap4 12 1 4 4 (\x14_0 x14_1 x14_2 x14_3 -> ((isum2 2 2 (\x15_0 x15_1 -> x11[x14_0][x14_1][((x14_2 * 2) + x15_0)][((x14_3 * 2) + x15_1)])) F./ fromi64 4)))
      let x16 = (imap5 10 1 1 1 1 (\x17_0 x17_1 x17_2 x17_3 x17_4 -> ((isum4 12 1 4 4 (\x18_0 x18_1 x18_2 x18_3 -> (x13[(x18_0 + x17_1)][(x18_1 + x17_2)][(x18_2 + x17_3)][(x18_3 + x17_4)] F.* fc[x17_0][x18_0][x18_1][x18_2][x18_3]))) F.+ b[x17_0])))
      let x19 = (imap5 10 1 1 1 1 (\x20_0 x20_1 x20_2 x20_3 x20_4 -> (logistics x16[x20_0][x20_1][x20_2][x20_3][x20_4])))
      let x21 = (isum5 10 1 1 1 1 (\x22_0 x22_1 x22_2 x22_3 x22_4 -> (((target[x22_0][x22_1][x22_2][x22_3][x22_4] F.+ (F.neg x19[x22_0][x22_1][x22_2][x22_3][x22_4])) F.* (target[x22_0][x22_1][x22_2][x22_3][x22_4] F.+ (F.neg x19[x22_0][x22_1][x22_2][x22_3][x22_4]))) F./ fromi64 2)))
      let x23 = one
      let x24 = (imap5 10 1 1 1 1 (\x25_0 x25_1 x25_2 x25_3 x25_4 -> ((F.neg ((x23 F./ fromi64 2) F.* (target[x25_0][x25_1][x25_2][x25_3][x25_4] F.+ (F.neg x19[x25_0][x25_1][x25_2][x25_3][x25_4])))) F.+ (F.neg ((x23 F./ fromi64 2) F.* (target[x25_0][x25_1][x25_2][x25_3][x25_4] F.+ (F.neg x19[x25_0][x25_1][x25_2][x25_3][x25_4])))))))
      let x26 =
        (let x27 = x19
         --(imap5 10 1 1 1 1 (\ x29_0 x29_1 x29_2 x29_3 x29_4 -> (logistics x16[x29_0][x29_1][x29_2][x29_3][x29_4])))
         in (imap5 10 1 1 1 1 (\x28_0 x28_1 x28_2 x28_3 x28_4 -> ((x24[x28_0][x28_1][x28_2][x28_3][x28_4] F.* x27[x28_0][x28_1][x28_2][x28_3][x28_4]) F.* (one F.+ (F.neg x27[x28_0][x28_1][x28_2][x28_3][x28_4]))))))
      let x30 = (imap4 12 1 4 4 (\x33_0 x33_1 x33_2 x33_3 -> (isum1 10 (\x31_0 -> (isum4 12 1 4 4 (\x32_0 x32_1 x32_2 x32_3 -> if (x33_0 >= x32_0 && x33_1 >= x32_1 && x33_2 >= x32_2 && x33_3 >= x32_3 && (x33_0 - x32_0) < 1 && (x33_1 - x32_1) < 1 && (x33_2 - x32_2) < 1 && (x33_3 - x32_3) < 1) then (x26[x31_0][(x33_0 - x32_0)][(x33_1 - x32_1)][(x33_2 - x32_2)][(x33_3 - x32_3)] F.* fc[x31_0][x32_0][x32_1][x32_2][x32_3]) else zero))))))
      let x34 = (imap4 12 1 8 8 (\x35_0 x35_1 x35_2 x35_3 -> (x30[x35_0][x35_1][(x35_2 / 2)][(x35_3 / 2)] F./ fromi64 4)))
      let x36 =
        (let x37 = x11
         --(imap4 12 1 8 8 (\ x39_0 x39_1 x39_2 x39_3 -> (logistics x8[x39_0][x39_1][x39_2][x39_3])))
         in (imap4 12 1 8 8 (\x38_0 x38_1 x38_2 x38_3 -> ((x34[x38_0][x38_1][x38_2][x38_3] F.* x37[x38_0][x38_1][x38_2][x38_3]) F.* (one F.+ (F.neg x37[x38_0][x38_1][x38_2][x38_3]))))))
      let x40 = (imap3 6 12 12 (\x43_0 x43_1 x43_2 -> (isum1 12 (\x41_0 -> (isum3 6 5 5 (\x42_0 x42_1 x42_2 -> if (x43_0 >= x42_0 && x43_1 >= x42_1 && x43_2 >= x42_2 && (x43_0 - x42_0) < 1 && (x43_1 - x42_1) < 8 && (x43_2 - x42_2) < 8) then (x36[x41_0][(x43_0 - x42_0)][(x43_1 - x42_1)][(x43_2 - x42_2)] F.* k2[x41_0][x42_0][x42_1][x42_2]) else zero))))))
      let x44 = (imap3 6 24 24 (\x45_0 x45_1 x45_2 -> (x40[x45_0][(x45_1 / 2)][(x45_2 / 2)] F./ fromi64 4)))
      let x46 =
        (let x47 = x3
         --(imap3 6 24 24 (\ x49_0 x49_1 x49_2 -> (logistics x0[x49_0][x49_1][x49_2])))
         in (imap3 6 24 24 (\x48_0 x48_1 x48_2 -> ((x44[x48_0][x48_1][x48_2] F.* x47[x48_0][x48_1][x48_2]) F.* (one F.+ (F.neg x47[x48_0][x48_1][x48_2]))))))
      --let dinp = (imap2 28 28 (\ x52_0 x52_1 -> (isum1 6 (\ x50_0 -> (isum2 5 5 (\ x51_0 x51_1 -> if (x52_0 >= x51_0 && x52_1 >= x51_1 && (x52_0 - x51_0) < 24 && (x52_1 - x51_1) < 24) then (x46[x50_0][(x52_0 - x51_0)][(x52_1 - x51_1)] F.* k1[x50_0][x51_0][x51_1]) else zero))))))
      let dk1 = (imap3 6 5 5 (\x53_0 x53_1 x53_2 -> (isum2 24 24 (\x54_0 x54_1 -> (x46[x53_0][x54_0][x54_1] F.* inp[(x53_1 + x54_0)][(x53_2 + x54_1)])))))
      let db1 = (imap1 6 (\x55_0 -> (isum2 24 24 (\x56_0 x56_1 -> x46[x55_0][x56_0][x56_1]))))
      let dk2 = (imap4 12 6 5 5 (\x57_0 x57_1 x57_2 x57_3 -> (isum3 1 8 8 (\x58_0 x58_1 x58_2 -> (x36[x57_0][x58_0][x58_1][x58_2] F.* x5[(x57_1 + x58_0)][(x57_2 + x58_1)][(x57_3 + x58_2)])))))
      let db2 = (imap1 12 (\x59_0 -> (isum3 1 8 8 (\x60_0 x60_1 x60_2 -> x36[x59_0][x60_0][x60_1][x60_2]))))
      let dfc = (imap5 10 12 1 4 4 (\x61_0 x61_1 x61_2 x61_3 x61_4 -> (isum4 1 1 1 1 (\x62_0 x62_1 x62_2 x62_3 -> (x26[x61_0][x62_0][x62_1][x62_2][x62_3] F.* x13[(x61_1 + x62_0)][(x61_2 + x62_1)][(x61_3 + x62_2)][(x61_4 + x62_3)])))))
      let db = (imap1 10 (\x63_0 -> (isum4 1 1 1 1 (\x64_0 x64_1 x64_2 x64_3 -> x26[x63_0][x64_0][x64_1][x64_2][x64_3]))))
      --let dtarget = (imap5 10 1 1 1 1 (\ x65_0 x65_1 x65_2 x65_3 x65_4 -> (((x23 F./ fromi64 2) F.* (target[x65_0][x65_1][x65_2][x65_3][x65_4] F.+ (F.neg x19[x65_0][x65_1][x65_2][x65_3][x65_4]))) F.+ ((x23 F./ fromi64 2) F.* (target[x65_0][x65_1][x65_2][x65_3][x65_4] F.+ (F.neg x19[x65_0][x65_1][x65_2][x65_3][x65_4]))))))

      --      let x0 = (imap3 6 24 24 (\ x1_0 x1_1 x1_2 -> ((sum2d (imap2 5 5 (\ x2_0 x2_1 -> (inp[(x2_0 + x1_1)][(x2_1 + x1_2)] F.* k1[x1_0][x2_0][x2_1])))) F.+ b1[x1_0])))
      --      let x3 = (imap3 6 24 24 (\ x4_0 x4_1 x4_2 -> (logistics x0[x4_0][x4_1][x4_2])))
      --      let x5 = (imap3 6 12 12 (\ x6_0 x6_1 x6_2 -> ((sum2d (imap2 2 2 (\ x7_0 x7_1 -> x3[x6_0][((x6_1 * 2) + x7_0)][((x6_2 * 2) + x7_1)]))) F./ fromi64 4)))
      --      let x8 = (imap4 12 1 8 8 (\ x9_0 x9_1 x9_2 x9_3 -> ((sum3d (imap3 6 5 5 (\ x10_0 x10_1 x10_2 -> (x5[(x10_0 + x9_1)][(x10_1 + x9_2)][(x10_2 + x9_3)] F.* k2[x9_0][x10_0][x10_1][x10_2])))) F.+ b2[x9_0])))
      --      let x11 = (imap4 12 1 8 8 (\ x12_0 x12_1 x12_2 x12_3 -> (logistics x8[x12_0][x12_1][x12_2][x12_3])))
      --      let x13 = (imap4 12 1 4 4 (\ x14_0 x14_1 x14_2 x14_3 -> ((sum2d (imap2 2 2 (\ x15_0 x15_1 -> x11[x14_0][x14_1][((x14_2 * 2) + x15_0)][((x14_3 * 2) + x15_1)]))) F./ fromi64 4)))
      --      let x16 = (imap5 10 1 1 1 1 (\ x17_0 x17_1 x17_2 x17_3 x17_4 -> ((sum4d (imap4 12 1 4 4 (\ x18_0 x18_1 x18_2 x18_3 -> (x13[(x18_0 + x17_1)][(x18_1 + x17_2)][(x18_2 + x17_3)][(x18_3 + x17_4)] F.* fc[x17_0][x18_0][x18_1][x18_2][x18_3])))) F.+ b[x17_0])))
      --      let x19 = (imap5 10 1 1 1 1 (\ x20_0 x20_1 x20_2 x20_3 x20_4 -> (logistics x16[x20_0][x20_1][x20_2][x20_3][x20_4])))
      --      let x21 = (sum5d (imap5 10 1 1 1 1 (\ x22_0 x22_1 x22_2 x22_3 x22_4 -> (((target[x22_0][x22_1][x22_2][x22_3][x22_4] F.+ (F.neg x19[x22_0][x22_1][x22_2][x22_3][x22_4])) F.* (target[x22_0][x22_1][x22_2][x22_3][x22_4] F.+ (F.neg x19[x22_0][x22_1][x22_2][x22_3][x22_4]))) F./ fromi64 2))))
      --      let x23 = one
      --      let x24 = (imap5 10 1 1 1 1 (\ x25_0 x25_1 x25_2 x25_3 x25_4 -> ((F.neg ((x23 F./ fromi64 2) F.* (target[x25_0][x25_1][x25_2][x25_3][x25_4] F.+ (F.neg x19[x25_0][x25_1][x25_2][x25_3][x25_4])))) F.+ (F.neg ((x23 F./ fromi64 2) F.* (target[x25_0][x25_1][x25_2][x25_3][x25_4] F.+ (F.neg x19[x25_0][x25_1][x25_2][x25_3][x25_4])))))))
      --      let x26 = (let x27 = x19 --(imap5 10 1 1 1 1 (\ x29_0 x29_1 x29_2 x29_3 x29_4 -> (logistics x16[x29_0][x29_1][x29_2][x29_3][x29_4])))
      --      in (imap5 10 1 1 1 1 (\ x28_0 x28_1 x28_2 x28_3 x28_4 -> ((x24[x28_0][x28_1][x28_2][x28_3][x28_4] F.* x27[x28_0][x28_1][x28_2][x28_3][x28_4]) F.* (one F.+ (F.neg x27[x28_0][x28_1][x28_2][x28_3][x28_4]))))))
      --      let x30 = (imap4 12 1 4 4 (\ x33_0 x33_1 x33_2 x33_3 -> (sum1d (imap1 10 (\ x31_0 -> (sum4d (imap4 12 1 4 4 (\ x32_0 x32_1 x32_2 x32_3 -> if (x33_0 >= x32_0 && x33_1 >= x32_1 && x33_2 >= x32_2 && x33_3 >= x32_3 && (x33_0 - x32_0) < 1 && (x33_1 - x32_1) < 1 && (x33_2 - x32_2) < 1 && (x33_3 - x32_3) < 1) then (x26[x31_0][(x33_0 - x32_0)][(x33_1 - x32_1)][(x33_2 - x32_2)][(x33_3 - x32_3)] F.* fc[x31_0][x32_0][x32_1][x32_2][x32_3]) else zero))))))))
      --      let x34 = (imap4 12 1 8 8 (\ x35_0 x35_1 x35_2 x35_3 -> (x30[x35_0][x35_1][(x35_2 / 2)][(x35_3 / 2)] F./ fromi64 4)))
      --      let x36 = (let x37 = x11 --(imap4 12 1 8 8 (\ x39_0 x39_1 x39_2 x39_3 -> (logistics x8[x39_0][x39_1][x39_2][x39_3])))
      --      in (imap4 12 1 8 8 (\ x38_0 x38_1 x38_2 x38_3 -> ((x34[x38_0][x38_1][x38_2][x38_3] F.* x37[x38_0][x38_1][x38_2][x38_3]) F.* (one F.+ (F.neg x37[x38_0][x38_1][x38_2][x38_3]))))))
      --      let x40 = (imap3 6 12 12 (\ x43_0 x43_1 x43_2 -> (sum1d (imap1 12 (\ x41_0 -> (sum3d (imap3 6 5 5 (\ x42_0 x42_1 x42_2 -> if (x43_0 >= x42_0 && x43_1 >= x42_1 && x43_2 >= x42_2 && (x43_0 - x42_0) < 1 && (x43_1 - x42_1) < 8 && (x43_2 - x42_2) < 8) then (x36[x41_0][(x43_0 - x42_0)][(x43_1 - x42_1)][(x43_2 - x42_2)] F.* k2[x41_0][x42_0][x42_1][x42_2]) else zero))))))))
      --      let x44 = (imap3 6 24 24 (\ x45_0 x45_1 x45_2 -> (x40[x45_0][(x45_1 / 2)][(x45_2 / 2)] F./ fromi64 4)))
      --      let x46 = (let x47 = x3 --(imap3 6 24 24 (\ x49_0 x49_1 x49_2 -> (logistics x0[x49_0][x49_1][x49_2])))
      --      in (imap3 6 24 24 (\ x48_0 x48_1 x48_2 -> ((x44[x48_0][x48_1][x48_2] F.* x47[x48_0][x48_1][x48_2]) F.* (one F.+ (F.neg x47[x48_0][x48_1][x48_2]))))))
      --
      --      --let dinp = (imap2 28 28 (\ x52_0 x52_1 -> (sum1d (imap1 6 (\ x50_0 -> (sum2d (imap2 5 5 (\ x51_0 x51_1 -> if (x52_0 >= x51_0 && x52_1 >= x51_1 && (x52_0 - x51_0) < 24 && (x52_1 - x51_1) < 24) then (x46[x50_0][(x52_0 - x51_0)][(x52_1 - x51_1)] F.* k1[x50_0][x51_0][x51_1]) else zero))))))))
      --      let dk1 = (imap3 6 5 5 (\ x53_0 x53_1 x53_2 -> (sum2d (imap2 24 24 (\ x54_0 x54_1 -> (x46[x53_0][x54_0][x54_1] F.* inp[(x53_1 + x54_0)][(x53_2 + x54_1)]))))))
      --      let db1 = (imap1 6 (\ x55_0 -> (sum2d (imap2 24 24 (\ x56_0 x56_1 -> x46[x55_0][x56_0][x56_1])))))
      --      let dk2 = (imap4 12 6 5 5 (\ x57_0 x57_1 x57_2 x57_3 -> (sum3d (imap3 1 8 8 (\ x58_0 x58_1 x58_2 -> (x36[x57_0][x58_0][x58_1][x58_2] F.* x5[(x57_1 + x58_0)][(x57_2 + x58_1)][(x57_3 + x58_2)]))))))
      --      let db2 = (imap1 12 (\ x59_0 -> (sum3d (imap3 1 8 8 (\ x60_0 x60_1 x60_2 -> x36[x59_0][x60_0][x60_1][x60_2])))))
      --      let dfc = (imap5 10 12 1 4 4 (\ x61_0 x61_1 x61_2 x61_3 x61_4 -> (sum4d (imap4 1 1 1 1 (\ x62_0 x62_1 x62_2 x62_3 -> (x26[x61_0][x62_0][x62_1][x62_2][x62_3] F.* x13[(x61_1 + x62_0)][(x61_2 + x62_1)][(x61_3 + x62_2)][(x61_4 + x62_3)]))))))
      --      let db = (imap1 10 (\ x63_0 -> (sum4d (imap4 1 1 1 1 (\ x64_0 x64_1 x64_2 x64_3 -> x26[x63_0][x64_0][x64_1][x64_2][x64_3])))))
      --      --let dtarget = (imap5 10 1 1 1 1 (\ x65_0 x65_1 x65_2 x65_3 x65_4 -> (((x23 F./ fromi64 2) F.* (target[x65_0][x65_1][x65_2][x65_3][x65_4] F.+ (F.neg x19[x65_0][x65_1][x65_2][x65_3][x65_4]))) F.+ ((x23 F./ fromi64 2) F.* (target[x65_0][x65_1][x65_2][x65_3][x65_4] F.+ (F.neg x19[x65_0][x65_1][x65_2][x65_3][x65_4]))))))

      let err = x21
      let dfc' = map flatten dfc :> [10][12][4][4]real
      in (dk1, db1, dk2, db2, dfc', db, err)
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
  in assert (magic == 2049) (map i8.u8 (drop 8 s))

def decode_image_file (s: []u8) =
  let magic = decode_u32_be (take 4 s)
  let n = i64.u32 (decode_u32_be (take 4 (drop 4 s)))
  let rows = i64.u32 (decode_u32_be (take 4 (drop 8 s)))
  let columns = i64.u32 (decode_u32_be (take 4 (drop 12 s)))
  let get_img i = unflatten (map f32.u8 (take (rows * columns) (drop (16 + i * rows * columns) s)))
  in assert (magic == 2051) (tabulate n get_img)

type~ str_pair = ([]u8, []u8)

entry convert (imgs_bytes: []u8) (lbls_bytes: []u8) : str_pair =
  (imgs_bytes, lbls_bytes)

type state =
  { k1: [6][5][5]f32
  , b1: [6]f32
  , k2: [12][6][5][5]f32
  , b2: [12]f32
  , fc: [10][12][4][4]f32
  , b: [10]f32
  }

entry iteration [n] (trainings: i64) (batchsize: i64) (rate: f32) (imgs: [n][28][28]f32) (lbls: [n]i8) (s: state) : (state, f32) =
  let gen_target i = imap 10 (\j -> if j == i then 1.0 else 0.0)
  let avg (a: []f32) = sum a / f32.i64 (length a)
  let (s, err) =
    loop (s, err) = (s, 0.0)
    for i < trainings / batchsize do
      let {k1, b1, k2, b2, fc, b} = s
      -- This is where we call trainings in parallel!
      let r =
        imap batchsize (\j ->
                          let img = imgs[i * batchsize + j]
                          let lbl = gen_target (i64.i8 lbls[i * batchsize + j])
                          in train_gen img k1 b1 k2 b2 fc b lbl)
      let (bdk1, bdb1, bdk2, bdb2, bdfc, bdb, berr) = unzip7 r
      -- TODO: these should happen in-place, but hopefully this is not
      --       a hotspot, the arrays are rather small.
      let k1' =
        imap3 6 5 5 (\i j k ->
                       k1[i][j][k] - rate * (avg (imap batchsize (\t -> bdk1[t][i][j][k]))))
      let b1' =
        imap1 6 (\i ->
                   b1[i] - rate * (avg (imap batchsize (\t -> bdb1[t][i]))))
      let k2' =
        imap4 12 6 5 5 (\i j k l ->
                          k2[i][j][k][l] - rate * (avg (imap batchsize (\t -> bdk2[t][i][j][k][l]))))
      let b2' =
        imap1 12 (\i ->
                    b2[i] - rate * (avg (imap batchsize (\t -> bdb2[t][i]))))
      let fc' =
        imap4 10 12 4 4 (\i j k l ->
                           fc[i][j][k][l] - rate * (avg (imap batchsize (\t -> bdfc[t][i][j][k][l]))))
      let b' =
        imap1 10 (\i ->
                    b[i] - rate * (avg (imap batchsize (\t -> bdb[t][i]))))
      let err' = err + sum berr
      in ( {k1 = k1', b1 = b1', k2 = k2', b2 = b2', fc = fc', b = b'}
         , err'
         )
  in (s, err / 10.0 / f32.i64 trainings)

entry initial_state : state =
  let k1 = imap3 6 5 5 (\_ _ _ -> 1.0 / 25.0)
  let b1 = imap1 6 (\_ -> 1.0 / 6.0)
  let k2 = imap4 12 6 5 5 (\_ _ _ _ -> 1.0 / 150.0)
  let b2 = imap1 12 (\_ -> 1.0 / 12.0)
  let fc = imap4 10 12 4 4 (\_ _ _ _ -> 1.0 / 192.0)
  let b = imap1 10 (\_ -> 1.0 / 10.0)
  in {k1, b1, k2, b2, fc, b}
