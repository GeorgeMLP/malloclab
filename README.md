# Malloc Lab

## Introduction

ICS Malloc Lab, Peking University.

In this lab you will be writing a *general purpose* dynamic storage allocator for C programs; that is, your own version of the ```malloc```, ```free```, ```realloc```, and ```calloc``` functions. For more information about this lab, please refer to ```malloclab.pdf```.

## Score

Two metrics will be used to evaluate your solution:
- **Space utilization**: The peak ratio between the aggregate amount of memory used by the driver (i.e., allocated via malloc but not yet freed via free) and the size of the heap used by your allocator.
- **Throughput**: The average number of operations completed per second.

Note that the throughput for the same implementation may differ on different machines.

My score for this lab is as follows.
| Score | Performance index | Kops  | Util (%) |
| ----- | ----------------- | ----- | -------- |
| 100   | 100               | 17249 | 91       |

The throughput of my score is measured on the class machine, which may not be the same on your local machine.

My implementation uses *segregated lists* to organize the free blocks. Another implementation using *splay tree* is also provided in ```mm-splay tree.c```, which is slightly modified from [this link](https://github.com/Seterplus/CSAPP/tree/master/malloclab).
