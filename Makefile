
TRAIN_IMG := input/train-images-idx3-ubyte
TRAIN_LBL := input/train-labels-idx1-ubyte
TEST_IMG  := input/t10k-images-idx3-ubyte
TEST_LBL  := input/t10k-labels-idx1-ubyte


all: run

run : conv.fut $(TRAIN_IMG) $(TRAIN_LBL) 
	futhark script $< \
		'run ($$loadbytes "$(TRAIN_IMG)") ($$loadbytes "$(TRAIN_LBL)")'

run-milti : conv.fut $(TRAIN_IMG) $(TRAIN_LBL) 
	futhark script --backend=multicore $< \
		'run ($$loadbytes "$(TRAIN_IMG)") ($$loadbytes "$(TRAIN_LBL)")'

test : conv.fut $(TRAIN_IMG) $(TRAIN_LBL) 
	futhark script  $< 'test_conv'

