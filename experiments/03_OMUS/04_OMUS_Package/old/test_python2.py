from functools import wraps
import time


def time_func(f):
    @wraps(f)
    def decor(*args, **kwargs):
        # x, y = args
        start = time.time()
        res = f(*args, **kwargs)
        end_time = time.time()
        return end_time-start, res
    return decor

@time_func
def child(x, y, z = 0):
    return x, y + z

if __name__ == "__main__":
    print(child(3, 6, z = 1))
