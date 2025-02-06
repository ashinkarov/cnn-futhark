#!/usr/bin/env python3

from __future__ import print_function
import argparse
import time
import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
import torch.multiprocessing as mp
from torchvision import datasets, transforms


class Net(nn.Module):
    def __init__(self):
        super(Net, self).__init__()
        self.conv1 = nn.Conv2d(1, 6, 5, 1)
        self.conv1.weight.data.fill_(1.0/25.0)
        self.conv1.bias.data.fill_(1.0/6.0)
        self.conv2 = nn.Conv2d(6, 12, 5, 1)
        self.conv2.weight.data.fill_(1.0/150.0)
        self.conv2.bias.data.fill_(1.0/12.0)
        self.fc1 = nn.Linear(4*4*12, 10)
        self.fc1.weight.data.fill_(1.0/192.0)
        self.fc1.bias.data.fill_(1.0/10.0)
        #self.fc2 = nn.Linear(500, 10)

    def forward(self, x):
        x = torch.sigmoid(self.conv1(x))
        x = F.max_pool2d(x, 2, 2)
        x = torch.sigmoid(self.conv2(x))
        x = F.max_pool2d(x, 2, 2)
        x = x.view(-1, 4*4*12)
        x = torch.sigmoid(self.fc1(x))
        #x = self.fc2(x)
        #return F.log_softmax(x, dim=1)
        return x

def cast_target (target, device):
    return (torch.arange(10, device=device) == target[:,None]).type(torch.float32)

def train(args, model, device, train_loader, optimizer, epoch):
    model.train()
    loss_fun = nn.MSELoss(reduction='sum')
    loss = None
    for batch_idx, (data, target) in enumerate(train_loader):
        if batch_idx > (args.train_size/args.batch_size):
            break
        data, target = data.to(device), target.to(device)
        output = model(data)
        loss = loss_fun(output, cast_target(target, device))
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
    print ('Epoch: {:d}, Loss {:.10f}'.format (epoch, loss.item()/10.0/args.batch_size))

def test(args, model, device, test_loader):
    model.eval()
    loss_fun = nn.MSELoss(reduction='sum')
    test_loss = 0
    correct = 0
    with torch.no_grad():
        for batch_idx, (data, target) in enumerate(test_loader):
            if batch_idx > (args.test_size/args.batch_size):
                break
            data, target = data.to(device), target.to(device)
            output = model(data)
            test_loss = loss_fun(output, cast_target(target, device)).item() # sum up batch loss
            pred = output.argmax(dim=1, keepdim=True) # get the index of the max log-probability
            correct += pred.eq(target.view_as(pred)).sum().item()

    test_loss /= args.batch_size

    print('\nTest set: Average loss: {:.4f}, Accuracy: {}/{} ({:.0f}%)\n'.format(
        test_loss, correct, len(test_loader.dataset),
        100. * correct / len(test_loader.dataset)))

def main():
    # Training settings
    parser = argparse.ArgumentParser(description='PyTorch MNIST Example')
    parser.add_argument('mnistpath', metavar='MNIST_PATH', type=str,
                    help='path to where mnist data is located.')
    parser.add_argument('-u', '--use-emnist', action='store_true', default=False,
                    help='use EMNIST datasets instead of MNIST.')
    parser.add_argument('--batch-size', type=int, default=100, metavar='N',
                        help='input batch size for training (default: 100)')
    parser.add_argument('--train-size', type=int, default=10000, metavar='TR',
                        help='number of data items to train over (default: 10000)')
    parser.add_argument('--test-size', type=int, default=10000, metavar='TR',
                        help='number of data items to test over (default: 10000)')
    parser.add_argument('--epochs', type=int, default=10, metavar='N',
                        help='number of epochs to train (default: 10)')
    parser.add_argument('--lr', type=float, default=0.05, metavar='LR',
                        help='learning rate (default: 0.05)')
    parser.add_argument('--no-cuda', action='store_true', default=False,
                        help='disables CUDA training')
    parser.add_argument('--seed', type=int, default=1, metavar='S',
                        help='random seed (default: 1)')
    parser.add_argument('--num-threads', type=int, default=1, metavar='NT',
                        help='number of threads to run with (default: 1)')

    args = parser.parse_args()
    use_cuda = not args.no_cuda and torch.cuda.is_available()
    if use_cuda:
        print ('Using GPU - setting threads to 1')
        args.num_threads = 1

    print ('Running with threads({})'.format(args.num_threads))
    print ('Parameters: epoch({}), batch-size({}), training-rate({:f}), training-size({}), evaluate-size({})'.format(
        args.epochs, args.batch_size, args.lr, args.train_size, args.test_size))

    torch.manual_seed(args.seed)
    torch.set_num_threads(args.num_threads)

    if use_cuda:
        torch.backends.cudnn.benchmark = True
    device = torch.device("cuda" if use_cuda else "cpu")

    kwargs = {'num_workers': 1, 'pin_memory': True} if use_cuda else {}
    if not args.use_emnist:
        train_loader = torch.utils.data.DataLoader(
            datasets.MNIST(args.mnistpath, download=True, train=True,
                           transform=transforms.Compose([
                               transforms.ToTensor()
                           ])),
            batch_size=args.batch_size, **kwargs)
        test_loader = torch.utils.data.DataLoader(
            datasets.MNIST(args.mnistpath, download=True, train=False,
                           transform=transforms.Compose([
                               transforms.ToTensor()
                           ])),
            batch_size=args.batch_size, **kwargs)
    else:
        print ('Using EMNIST `balanced` dataset')
        train_loader = torch.utils.data.DataLoader(
            datasets.EMNIST(args.mnistpath, split='balanced', train=True,
                           transform=transforms.Compose([
                               transforms.ToTensor()
                           ])),
            batch_size=args.batch_size, **kwargs)
        test_loader = torch.utils.data.DataLoader(
            datasets.EMNIST(args.mnistpath, split='balanced', train=False,
                           transform=transforms.Compose([
                               transforms.ToTensor()
                           ])),
            batch_size=args.batch_size, **kwargs)


    if use_cuda:
        model = Net().cuda()
    else:
        model = Net().cpu()
    optimizer = optim.SGD(model.parameters(), lr=args.lr, weight_decay=0.5)

    train_start = time.perf_counter ()
    for epoch in range(1, args.epochs + 1):
        train(args, model, device, train_loader, optimizer, epoch)
    train_stop = time.perf_counter () - train_start

    test_start = time.perf_counter ()
    test(args, model, device, test_loader)
    test_stop = time.perf_counter () - test_start
    print ('Train: {:f}s, Test: {:f}s'.format(train_stop, test_stop))

    #if (args.save_model):
    #    torch.save(model.state_dict(),"mnist_cnn.pt")

if __name__ == '__main__':
    main()
