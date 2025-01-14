
TRAIN_IMG := input/train-images-idx3-ubyte
TRAIN_LBL := input/train-labels-idx1-ubyte
TEST_IMG  := input/t10k-images-idx3-ubyte
TEST_LBL  := input/t10k-labels-idx1-ubyte

CFLAGS='-Ofast -march=native -mtune=native'

all: run

run : conv.fut $(TRAIN_IMG) $(TRAIN_LBL) 
	futhark script $< \
		'run ($$loadbytes "$(TRAIN_IMG)") ($$loadbytes "$(TRAIN_LBL)")'

run-milti : conv.fut $(TRAIN_IMG) $(TRAIN_LBL) 
	CFLAGS=$(CFLAGS) futhark script --backend=multicore $< \
		'run ($$loadbytes "$(TRAIN_IMG)") ($$loadbytes "$(TRAIN_LBL)")'

test : conv.fut $(TRAIN_IMG) $(TRAIN_LBL) 
	futhark script  $< 'test_conv'

run-bench: conv.fut $(TRAIN_IMG) $(TRAIN_LBL)
	CFLAGS=$(CFLAGS) futhark bench --backend=multicore conv.fut --json conv.json --no-tuning
