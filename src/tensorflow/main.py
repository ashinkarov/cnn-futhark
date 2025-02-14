#!/usr/bin/env python3
from mnist import MNIST
import numpy as np
import tensorflow as tf
from tensorflow.keras.layers import AveragePooling2D, Conv2D, Dense, Dropout, Flatten, MaxPooling2D, Reshape, Softmax
from tensorflow.keras import Model
import argparse
import time
import logging

model = None
optimizer = None
loss_object = None
tr_loss = None
te_loss = None
te_accu = None

class ZhangCNN (Model):
    def __init__ (self, cats):
        super (ZhangCNN, self).__init__()
        init_w1 = tf.keras.initializers.Constant(1.0/25.0)
        init_w2 = tf.keras.initializers.Constant(1.0/150.0)
        init_w3 = tf.keras.initializers.Constant(1.0/192.0)
        init_b1 = tf.keras.initializers.Constant(1.0/6.0)
        init_b2 = tf.keras.initializers.Constant(1.0/12.0)
        init_b3 = tf.keras.initializers.Constant(1.0/cats)
        self.conv1 = Conv2D (filters=6, kernel_initializer=init_w1, kernel_size=(5,5), bias_initializer=init_b1, activation='sigmoid', input_shape=(28,28,1))
        self.avgp1 = AveragePooling2D (pool_size=(2,2))
        self.conv2 = Conv2D (filters=12, kernel_initializer=init_w2, kernel_size=(5,5), bias_initializer=init_b2, activation='sigmoid')
        self.avgp2 = AveragePooling2D (pool_size=(2,2))
        self.flt1 = Reshape (target_shape=[192, 1, 1])
        self.flt2 = Conv2D (filters=cats, kernel_initializer=init_w3, kernel_size=(192,1), bias_initializer=init_b3, activation='sigmoid')

    def call (self, x):
        x = self.conv1 (x)
        x = self.avgp1 (x)
        x = self.conv2 (x)
        x = self.avgp2 (x)
        x = self.flt1 (x)
        x = self.flt2 (x)
        return (x)

class LargeCNN (Model):
    def __init__ (self, cats):
        super (LargeCNN, self).__init__()
        init_w1 = tf.keras.initializers.Constant(1.0/25.0)
        init_w2 = tf.keras.initializers.Constant(1.0/150.0)
        init_w3 = tf.keras.initializers.Constant(1.0/192.0)
        init_b1 = tf.keras.initializers.Constant(1.0/6.0)
        init_b2 = tf.keras.initializers.Constant(1.0/12.0)
        init_b3 = tf.keras.initializers.Constant(1.0/cats)
        self.conv1 = Conv2D (filters=64, kernel_initializer=init_w1, kernel_size=(5,5), bias_initializer=init_b1, activation='sigmoid', input_shape=(28,28,1))
        self.avgp1 = AveragePooling2D (pool_size=(2,2))
        self.conv2 = Conv2D (filters=128, kernel_initializer=init_w2, kernel_size=(5,5), bias_initializer=init_b2, activation='sigmoid')
        self.avgp2 = AveragePooling2D (pool_size=(2,2))
        self.flt1 = Reshape (target_shape=[2048, 1, 1])
        self.flt2 = Conv2D (filters=cats, kernel_initializer=init_w3, kernel_size=(2048,1), bias_initializer=init_b3, activation='sigmoid')

    def call (self, x):
        x = self.conv1 (x)
        x = self.avgp1 (x)
        x = self.conv2 (x)
        x = self.avgp2 (x)
        x = self.flt1 (x)
        x = self.flt2 (x)
        return (x)

@tf.function
def train_cnn (images, labels):
    #tf.print (model.trainable_variables[0])
    with tf.GradientTape() as tape:
        predictions = model(images, training=True)
        loss = loss_object(labels, predictions, sample_weight=0.5)
    # minimize
    gradients = tape.gradient(loss, model.trainable_variables)
    optimizer.apply_gradients(zip(gradients, model.trainable_variables))

    tr_loss(loss)

@tf.function
def test_cnn (images, labels):
    predictions = model(images, training=False)
    t_loss = loss_object(labels, predictions, sample_weight=0.5)

    te_loss(t_loss)
    te_accu(labels, predictions)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Zhang CNN TF implementation')
    parser.add_argument('mnistpath', metavar='MNIST_PATH', type=str,
                    help='path to where mnist data is located.')
    parser.add_argument('-z', '--mnist-gzip', action='store_true', default=False,
                    help='indicate that the mnist dataset is gzipped.')
    parser.add_argument('-u', '--use-emnist', action='store_true', default=False,
                    help='use EMNIST datasets instead of MNIST.')
    parser.add_argument('-b', '--batch-size', type=int, default=100,
                    help='batch size')
    parser.add_argument('-t', '--training-size', type=int, default=10000,
                    help='training size (max 60000)')
    parser.add_argument('-e', '--evaluate-size', type=int, default=10000,
                    help='evaluation size (max 10000)')
    parser.add_argument('-p', '--epoch', type=int, default=10,
                    help='epochs to iterate')
    parser.add_argument('-r', '--training-rate', type=float, default=0.05,
                    help='rate to learn at')
    parser.add_argument('-L', '--large-cnn', action='store_true', default=False,
                    help='Use larger CNN')
    parser.add_argument('-n', '--num-thread', type=int, default=1,
                    help='number of threads to use')
    parser.add_argument('-g', '--gpu', action='store_true', default=False,
                    help='use the GPU (sets threads to 1)')

    args = parser.parse_args()
    logger = tf.get_logger()
    logger.setLevel(logging.INFO)

    if not args.use_emnist:
        if args.training_size > 60000:
            parser.error("training size must be in domain (0,60000]!")
        if args.evaluate_size > 10000:
            parser.error("evaluate size must be in domain (0,10000]!")
    else:
        logger.info ('Please double-check that training/evaluation size are correct for EMNIST')
    if args.gpu:
        logger.info ('Using GPU - setting threads to 1')
        args.num_thread = 1

    logger.info ('Running with threads({})'.format(args.num_thread))
    logger.info ('Parameters: epoch({}), batch-size({}), training-rate({:f}), training-size({}), evaluate-size({})'.format(
        args.epoch, args.batch_size, args.training_rate, args.training_size, args.evaluate_size))

    # Get data
    mndata = MNIST(args.mnistpath, return_type='numpy')
    cats = 10 # default for MNIST
    if args.use_emnist:
        mndata.select_emnist ('balanced')
        logger.info ('Using EMNIST `balanced` dataset.')
        cats = 47
    mndata.gz = args.mnist_gzip

    # set TF settings
    # comment out to run on all cores
    tf.config.threading.set_inter_op_parallelism_threads (args.num_thread)
    tf.config.threading.set_intra_op_parallelism_threads (args.num_thread)
    # get all devices
    tf.config.set_soft_device_placement (True)
    if not args.gpu: # use GPU
        tf.config.set_visible_devices([], 'GPU')

    # setup model
    if not args.large_cnn:
        model = ZhangCNN (cats)
    else:
        model = LargeCNN (cats)

    # setup loss and accuracy objects
    loss_object = tf.keras.losses.MeanSquaredError ()
    optimizer = tf.keras.optimizers.SGD (learning_rate=args.training_rate)

    tr_loss = tf.keras.metrics.Mean(name='train_loss')
    te_loss = tf.keras.metrics.Mean(name='test_loss')
    te_accu = tf.keras.metrics.CategoricalAccuracy(name='test_accuracy')

    # process data
    train_images_raw, train_labels_raw = mndata.load_training()
    test_images_raw, test_labels_raw = mndata.load_testing()
    train_images = (train_images_raw).astype (np.float32, copy=False)
    test_images = (test_images_raw).astype (np.float32, copy=False)
    train_labels = tf.one_hot (train_labels_raw, cats)
    test_labels = tf.one_hot (test_labels_raw, cats)

    # Do a single minimal pass just to force compilation of the graph.
    train_cnn (train_images[0:1,:].reshape (1, 28, 28, 1), tf.reshape(train_labels[0:1,:], (1, cats)))

    # do the training
    logger.info ('Training the model now')
    train_start = time.perf_counter ()
    for epoch in range(args.epoch):
        # Reset the metrics at the start of the next epoch
        tr_loss.reset_state()
        for i in range (0, args.training_size, args.batch_size):
            images = train_images[i:i+args.batch_size, :]
            labels = train_labels[i:i+args.batch_size, :]
            train_cnn (images.reshape (args.batch_size, 28, 28, 1), tf.reshape (labels, (args.batch_size, cats)))
        logger.info ('Epoch {}, Loss: {:f}'.format (epoch+1, tr_loss.result()))
    train_stop = time.perf_counter () - train_start

    logger.info ('Train: {:f}s'.format(train_stop))
