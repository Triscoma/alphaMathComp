import os
import json
import re
from queue import PriorityQueue
from pytanque import Pytanque, PytanqueMode
from openai import OpenAI, AsyncOpenAI
from concurrent.futures import ThreadPoolExecutor, TimeoutError
from threading import Lock
import time
import random
import asyncio
from pathlib import Path
import datetime

#parameters
arity = 3
beam_size = 2
iter_max = 5
nb_examples = 5
max_sample_size = 50

MAX_RANGE = 1000000 # pour ne pas itérer sur tout quand on veut juste tester

#alpha = 1
#beta = 1

prefix = 'data/output/eval_tmp/'

with open(prefix + 'filepath.json') as filepath_json :
    filepath = json.load(filepath_json)

with open(prefix + 'position.json') as position_json :
    position = json.load(position_json)

with open(prefix + 'tactic.json') as tactic_json :
    tactic = json.load(tactic_json)

with open(prefix + 'next_tactic.json') as next_tactic_json :
    next_tactic = json.load(next_tactic_json)

with open(prefix + 'statement.json') as statement_json :
    statement = json.load(statement_json)

with open(prefix + 'theorem.json') as theorem_json :
    theorem = json.load(theorem_json)

with open('data/output.json') as output_json : 
    data = json.load(output_json)

with open('confidential.json') as confidential_json :
    confidential = json.load(confidential_json)
    API_KEY = confidential["API_KEY"]

with open(prefix + 'prev_tactic.json') as prev_json:
    prev_tactic = json.load(prev_json)


def insert(tab, l, i) :
    if l >= len(tab) :
        tab.extend([[] for _ in range(2*l+1 - len(tab))])
    tab[l].append(i)


length = [[]] #tactics grouped by solution length
    

for i in range(13) :
    k = str(i)
    l = 0
    while next_tactic[k] != None :
        k = str(next_tactic[k])
        l += 1
    insert(length, l, i)

steps_lock = Lock()

sum = 0
n = 0
for i in range(len(length)) : 
    l = len(length[i])
    sum += i * l
    n += l
print(f"average : {sum / n}")

#with open("output_treefinement.dump", 'wb') as f:
#    pickle.dump(good_proof_steps, f)
