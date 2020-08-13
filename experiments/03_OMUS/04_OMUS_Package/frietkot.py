import sys
sys.path.append('/home/crunchmonster/Documents/VUB/01_SharedProjects/01_cppy_src')
from cppy import BoolVar, Model
from pathlib import Path
import re


def frietKotProblem():
    # Construct the model.
    (mayo, ketchup, curry, andalouse, samurai) = BoolVar(5)

    Nora = mayo | ketchup
    Leander = ~samurai | mayo
    Benjamin = ~andalouse | ~curry | ~samurai
    Behrouz = ketchup | curry | andalouse
    Guy = ~ketchup | curry | andalouse
    Daan = ~ketchup | ~curry | andalouse
    Celine = ~samurai
    Anton = mayo | ~curry | ~andalouse
    Danny = ~mayo | ketchup | andalouse | samurai
    Luc = ~mayo | samurai

    allwishes = [Nora, Leander, Benjamin, Behrouz, Guy, Daan, Celine, Anton, Danny, Luc]

    model = Model(allwishes)
    # print(model)
    return model

    # stats = model.solve()
    # print("Mayonaise = ", mayo.value())
    # print("Ketchup = ", ketchup.value())
    # print("Curry Ketchup = ", curry.value())
    # print("Andalouse = ", andalouse.value())
    # print("Samurai = ", samurai.value())
