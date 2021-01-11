import json
import random
import sys
import time
from datetime import date, datetime
from multiprocessing import Process
from pathlib import Path


def fn(t1, t2, t3):
    print(t1, t2, t3)

args = ('my', 'function', 'great')
p = Process(target=fn, args=args)
p.start()
p.join()